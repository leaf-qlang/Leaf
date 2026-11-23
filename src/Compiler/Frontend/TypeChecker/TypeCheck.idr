module Compiler.Frontend.TypeChecker.TypeCheck

import Compiler.Helper
import Control.Monad.State
import Data.List
import Data.SortedMap
import Data.SortedSet

import Compiler.Frontend.ScopeAndNameResolver.Data
import Compiler.Frontend.TypeChecker.Phases.BodyCheck                -- phase B
import Compiler.Frontend.TypeChecker.Data
import Compiler.Frontend.TypeChecker.Phases.EffectsCheck             -- phase E
import Compiler.Frontend.TypeChecker.Phases.OwnershipCheck           -- phase C
import Compiler.Frontend.TypeChecker.Phases.SignatureCheck           -- phase A
import Compiler.Frontend.TypeChecker.PreludeSignatures
import Compiler.Frontend.TypeChecker.State
import Compiler.Frontend.TypeChecker.Type
import Compiler.Frontend.TypeChecker.Phases.TypedAstTranslation      -- phase T
import Compiler.Frontend.ASTData
import Compiler.Frontend.ASTPhases
import Compiler.Frontend.Source
import Compiler.Frontend.Syntax.AST
import Compiler.Frontend.Syntax.Name

%default total

--------------------------------------------------------------------------------
-- Item Helpers
--------------------------------------------------------------------------------

getItemSymbolId : ResolvedItem -> SymbolId
getItemSymbolId resolvedItem =
  case resolvedItem.nodeValue of
    ItemFunction functionDeclaration => functionDeclaration.functionName.nodeValue.nameNodeSymbolId
    ItemConst constDeclaration       => constDeclaration.constName.nodeValue.nameNodeSymbolId
    ItemModule _             => notImplemented __FILE__ "getItemSymbolId" "ItemModule"
    ItemUse _                => notImplemented __FILE__ "getItemSymbolId" "ItemUse"
    ItemEnum _               => notImplemented __FILE__ "getItemSymbolId" "ItemEnum"
    ItemQEnum _              => notImplemented __FILE__ "getItemSymbolId" "ItemQEnum"
    ItemStruct _             => notImplemented __FILE__ "getItemSymbolId" "ItemStruct"
    ItemImpl _               => notImplemented __FILE__ "getItemSymbolId" "ItemImpl"

getItemNameSpan : ResolvedItem -> SourceSpan
getItemNameSpan resolvedItem =
  case resolvedItem.nodeValue of
    ItemFunction functionDeclaration => functionDeclaration.functionName.astInfo.span
    ItemConst constDeclaration       => constDeclaration.constName.astInfo.span
    ItemModule _             => notImplemented __FILE__ "getItemNameSpan" "ItemModule"
    ItemUse _                => notImplemented __FILE__ "getItemNameSpan" "ItemUse"
    ItemEnum _               => notImplemented __FILE__ "getItemNameSpan" "ItemEnum"
    ItemQEnum _              => notImplemented __FILE__ "getItemNameSpan" "ItemQEnum"
    ItemStruct _             => notImplemented __FILE__ "getItemNameSpan" "ItemStruct"
    ItemImpl _               => notImplemented __FILE__ "getItemNameSpan" "ItemImpl"

isSameItem : ResolvedItem -> ResolvedItem -> Bool
isSameItem firstItem secondItem = firstItem.astInfo.nodeId == secondItem.astInfo.nodeId

--------------------------------------------------------------------------------
-- Seeding
--------------------------------------------------------------------------------

getResolvedCodeItems : ResolvedSourceFile -> List ResolvedItem
getResolvedCodeItems (MkAstNode _ _ (MkSourceFileNode _ resolvedCodeItems)) = resolvedCodeItems

seedTypeTables : ScopeTables -> TypeTables
seedTypeTables scopeTables =
  MkTypeTables
    scopeTables.scopes
    scopeTables.nodeScopes
    (map (\symbolInfo => { symbolType := TypeNotYetResolved } symbolInfo) scopeTables.symbols)
    (map (\localVariableInfo => { quantumStorage := PendingQbitClassification } localVariableInfo) scopeTables.localVarsMeta)
    scopeTables.memberScopes
    scopeTables.references
    empty                                                -- constValues
    empty                                                -- expressionTypes
    empty                                                -- patternTypes
    empty                                                -- coercions
    empty                                                -- calls

seedPresetSymbolTypes : TypeTables -> TypeTables
seedPresetSymbolTypes typeTables = { symbols := map seedPresetSymbolType typeTables.symbols } typeTables
  where
    seedPresetSymbolType : TypedSymbolInfo -> TypedSymbolInfo
    seedPresetSymbolType symbolInfo =
      case (symbolInfo.symbolKind, symbolInfo.origin) of
        (SymbolModule, _)               => { symbolType := NoValueType } symbolInfo
        (SymbolFunction, PreludeSymbol) => { symbolType := preludeValueType symbolInfo.declaredName } symbolInfo
        _                               => symbolInfo

seedTypeCheckerState : ResolvedModule -> List ResolvedItem -> TypeCheckerState
seedTypeCheckerState resolvedModule resolvedCodeItems =
  MkTypeCheckerState
    (seedPresetSymbolTypes (seedTypeTables resolvedModule.scopeTables))
    Nothing
    emptyInferenceState
    (fromList (map (\sourceFileItem => (getItemSymbolId sourceFileItem, sourceFileItem)) resolvedCodeItems))
    empty
    empty

--------------------------------------------------------------------------------
-- Cycles
--------------------------------------------------------------------------------

-- Every blocked item waits for a symbol another blocked item declares (checked
-- by runBodyAndSignatureChecks before calling this function), so walking
-- the waits from the first blocked item must revisit a symbol; the symbols from
-- that first visit onwards are the cycle. `const A: i32 = B; const B: i32 = A;`
-- gives [B, A].
resolutionCycleTypeError : TypeTables -> List (ResolvedItem, SymbolId) -> TypeError
resolutionCycleTypeError typeTables blockedItems =
  case blockedItems of
    [] => unreachable __FILE__ {function = "resolutionCycleTypeError"} {reason = "a round without progress has blocked items"}
    (firstBlockedItem, firstAwaitedSymbol) :: _ =>
      CyclicDeclaration
        (map declaredSymbolName (collectCycleFrom (S (length blockedItems)) [] firstAwaitedSymbol))
        (getItemNameSpan firstBlockedItem)
  where
    declaredSymbolName : SymbolId -> String
    declaredSymbolName symbolId =
      case lookup symbolId typeTables.symbols of
        Just symbolInfo => symbolInfo.declaredName
        Nothing => unreachable __FILE__ "resolutionCycleTypeError" "a cycle references an unknown symbol"

    -- Each blocked item's own symbol, paired with the symbol it waits for.
    awaitedSymbolByWaitingSymbol : List (SymbolId, SymbolId)
    awaitedSymbolByWaitingSymbol =
      map (\(blockedItem, awaitedSymbol) => (getItemSymbolId blockedItem, awaitedSymbol)) blockedItems

    -- `visitedSymbols` holds the symbols walked so far, most recent first.
    collectCycleFrom : (fuel : Nat) -> (visitedSymbols : List SymbolId) -> SymbolId -> List SymbolId
    collectCycleFrom Z visitedSymbols _ = reverse visitedSymbols
    collectCycleFrom (S fuel) visitedSymbols currentSymbol =
      if elem currentSymbol visitedSymbols
        then currentSymbol :: reverse (takeWhile (/= currentSymbol) visitedSymbols)
        else case lookup currentSymbol awaitedSymbolByWaitingSymbol of
               Just awaitedSymbol => collectCycleFrom fuel (currentSymbol :: visitedSymbols) awaitedSymbol
               Nothing            => unreachable __FILE__ {function = "resolutionCycleTypeError"} {reason = "every awaited symbol belongs to a blocked item"}

--------------------------------------------------------------------------------
-- Passes A and B
--------------------------------------------------------------------------------

record RemainingWorkTodo where
  constructor MkRemainingWorkTodo
  pendingSignatureItems : List ResolvedItem     -- pass A has not recorded the signature yet, in source order
  pendingBodyItems      : List ResolvedItem     -- pass B has not checked the body or initializer yet, in source order

remainingTaskCount : RemainingWorkTodo -> Nat
remainingTaskCount remainingWork = length remainingWork.pendingSignatureItems + length remainingWork.pendingBodyItems

-- A blocked check leaves the state exactly as it was so retrying next round is safe.
runCheckRollingBackIfBlocked : StateT TypeCheckerState (Either CheckFailure) () -> StateT TypeCheckerState (Either CheckFailure) (Maybe SymbolId)
runCheckRollingBackIfBlocked itemCheck = do
  stateBeforeAttempt <- get
  case execStateT stateBeforeAttempt itemCheck of
    Right stateAfterAttempt      => put stateAfterAttempt >> pure Nothing
    Left (Blocked awaitedSymbol) => pure (Just awaitedSymbol)
    Left (Failed typeError)      => liftTypeError typeError

-- The items whose check blocked, each with the symbol it is waiting for.
runChecksAndCollectBlockedItems : (ResolvedItem -> StateT TypeCheckerState (Either CheckFailure) ()) 
    -> List ResolvedItem 
    -> StateT TypeCheckerState (Either CheckFailure) (List (ResolvedItem, SymbolId))
runChecksAndCollectBlockedItems checkItem [] = pure []
runChecksAndCollectBlockedItems checkItem (currentItem :: remainingItems) = do
  maybeAwaitedSymbol <- runCheckRollingBackIfBlocked (checkItem currentItem)
  blockedRemainingItems <- runChecksAndCollectBlockedItems checkItem remainingItems
  pure (maybe blockedRemainingItems (\awaitedSymbol => (currentItem, awaitedSymbol) :: blockedRemainingItems) maybeAwaitedSymbol)

-- One round: pass A on every pending signature, then pass B on every pending
-- body whose signature is recorded. Each productive round completes at least
-- one of the 2n entries, so 2n + 1 rounds always suffice.
runBodyAndSignatureChecks : (remainingRounds : Nat) -> RemainingWorkTodo -> StateT TypeCheckerState (Either CheckFailure) ()
runBodyAndSignatureChecks _ (MkRemainingWorkTodo [] []) = pure ()
runBodyAndSignatureChecks Z _ = unreachable __FILE__ {function = "runBodyAndSignatureChecks"} {reason = "every productive round completes an entry"}
runBodyAndSignatureChecks (S remainingRounds) remainingWork = do
  blockedSignatureItems <- runChecksAndCollectBlockedItems checkSignature remainingWork.pendingSignatureItems
  blockedBodyItems <- runChecksAndCollectBlockedItems checkBody (filter (not . signatureCheckIsBlocked blockedSignatureItems) remainingWork.pendingBodyItems)
  let isStillPending = \pendingItem => signatureCheckIsBlocked blockedSignatureItems pendingItem || bodyCheckIsBlocked blockedBodyItems pendingItem
      nextRemainingWork = MkRemainingWorkTodo (map fst blockedSignatureItems) (filter isStillPending remainingWork.pendingBodyItems)
  if remainingTaskCount nextRemainingWork < remainingTaskCount remainingWork
    then runBodyAndSignatureChecks remainingRounds nextRemainingWork
    else do
      let blockedItems = blockedSignatureItems ++ blockedBodyItems
      if all (isDeclaredByItemInRemainingWork nextRemainingWork . snd) blockedItems
        then do
          checkerState <- get
          liftTypeError (resolutionCycleTypeError checkerState.typeTables blockedItems)
        else unreachable __FILE__ {function = "runBodyAndSignatureChecks"} {reason = "a blocked check awaits a symbol that no pending item declares"}
  where
    isDeclaredByItemInRemainingWork : RemainingWorkTodo -> SymbolId -> Bool
    isDeclaredByItemInRemainingWork nextRemainingWork awaitedSymbol =
      any ((== awaitedSymbol) . getItemSymbolId) (nextRemainingWork.pendingSignatureItems ++ nextRemainingWork.pendingBodyItems)

    signatureCheckIsBlocked : List (ResolvedItem, SymbolId) -> ResolvedItem -> Bool
    signatureCheckIsBlocked blockedSignatureItems pendingItem = any (isSameItem pendingItem . fst) blockedSignatureItems

    bodyCheckIsBlocked : List (ResolvedItem, SymbolId) -> ResolvedItem -> Bool
    bodyCheckIsBlocked blockedBodyItems pendingItem = any (isSameItem pendingItem . fst) blockedBodyItems

inferAndCheckTypes : TypeCheckerState -> List ResolvedItem -> Either TypeError TypeTables
inferAndCheckTypes seededTypeCheckerState resolvedCodeItems =
  let remainingWorkTodo = MkRemainingWorkTodo resolvedCodeItems resolvedCodeItems
      remainingRounds = 2 * length resolvedCodeItems + 1
  in case execStateT seededTypeCheckerState (runBodyAndSignatureChecks remainingRounds remainingWorkTodo) of
    Right finalTypeCheckerState => Right finalTypeCheckerState.typeTables
    Left (Failed typeError)     => Left typeError
    Left (Blocked _)            => unreachable __FILE__ {function = "inferAndCheckTypes"} {reason = "runCheckRollingBackIfBlocked catches every block"}

--------------------------------------------------------------------------------
-- The pipeline
--------------------------------------------------------------------------------

||| Passes A and B run in rounds until every signature and body is checked;
export
typeCheckSignaturesAndBodies : ResolvedModule -> Either TypeError TypeTables
typeCheckSignaturesAndBodies resolvedModule = do
  let resolvedCodeItems = getResolvedCodeItems resolvedModule.ast
  let seededTypeCheckerState = seedTypeCheckerState resolvedModule resolvedCodeItems
  inferAndCheckTypes seededTypeCheckerState resolvedCodeItems                           -- A ⇄ B

||| Passes A and B run in rounds until every signature and body is checked;
||| then the typed AST is built, and effects and ownership are checked once each.
public export
typeCheck : ResolvedModule -> Either TypeError TypedModule
typeCheck resolvedModule = do 
  typeTables <- typeCheckSignaturesAndBodies resolvedModule                              -- A ⇄ B
  let typedAst = translateAst typeTables resolvedModule.ast                              -- T
  checkEffects typeTables typedAst                                                       -- E
  ownershipTables <- checkOwnership typeTables typedAst                                  -- C
  pure (MkTypedModule resolvedModule.rootSymbolId resolvedModule.rootScopeId typedAst typeTables ownershipTables)
