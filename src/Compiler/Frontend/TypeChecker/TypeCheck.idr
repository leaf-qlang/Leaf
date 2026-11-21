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

getSourceCodeItems : ResolvedSourceFile -> List ResolvedItem
getSourceCodeItems (MkAstNode _ _ (MkSourceFileNode _ sourceFileItems)) = sourceFileItems

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
seedTypeCheckerState resolvedModule sourceFileItems =
  MkTypeCheckerState
    (seedPresetSymbolTypes (seedTypeTables resolvedModule.tables))
    Nothing
    emptyInferenceState
    (fromList (map (\sourceFileItem => (getItemSymbolId sourceFileItem, sourceFileItem)) sourceFileItems))
    empty
    empty

--------------------------------------------------------------------------------
-- Cycles
--------------------------------------------------------------------------------

-- Every stuck item waits for a symbol another stuck item declares, so walking
-- the waits from the first stuck item must revisit a symbol; the symbols from
-- that first visit onwards are the cycle. `const A: i32 = B; const B: i32 = A;`
-- gives [B, A].
resolutionCycleTypeError : TypeTables -> List (ResolvedItem, SymbolId) -> TypeError
resolutionCycleTypeError typeTables stuckItems =
  case stuckItems of
    [] => unreachable __FILE__ {function = "resolutionCycleError"} {reason = "a round without progress has stuck items"}
    (firstStuckItem, firstAwaitedSymbol) :: _ =>
      CyclicDeclaration
        (map declaredSymbolName (collectCycleFrom (S (length stuckItems)) [] firstAwaitedSymbol))
        (getItemNameSpan firstStuckItem)
  where
    declaredSymbolName : SymbolId -> String
    declaredSymbolName symbolId =
      case lookup symbolId typeTables.symbols of
        Just symbolInfo => symbolInfo.declaredName
        Nothing => unreachable __FILE__ "resolutionCycleError" "a cycle references an unknown symbol"

    -- Each stuck item's own symbol, paired with the symbol it waits for.
    awaitedSymbolByWaitingSymbol : List (SymbolId, SymbolId)
    awaitedSymbolByWaitingSymbol =
      map (\(stuckItem, awaitedSymbol) => (getItemSymbolId stuckItem, awaitedSymbol)) stuckItems

    -- `visitedSymbols` holds the symbols walked so far, most recent first.
    collectCycleFrom : (fuel : Nat) -> (visitedSymbols : List SymbolId) -> SymbolId -> List SymbolId
    collectCycleFrom Z visitedSymbols _ = reverse visitedSymbols
    collectCycleFrom (S fuel) visitedSymbols currentSymbol =
      if elem currentSymbol visitedSymbols
        then currentSymbol :: reverse (takeWhile (/= currentSymbol) visitedSymbols)
        else case lookup currentSymbol awaitedSymbolByWaitingSymbol of
               Just awaitedSymbol => collectCycleFrom fuel (currentSymbol :: visitedSymbols) awaitedSymbol
               Nothing            => reverse (currentSymbol :: visitedSymbols)

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
attemptCheck : StateT TypeCheckerState (Either CheckFailure) () -> StateT TypeCheckerState (Either CheckFailure) (Maybe SymbolId)
attemptCheck itemCheck = do
  stateBeforeAttempt <- get
  case execStateT stateBeforeAttempt itemCheck of
    Right stateAfterAttempt      => put stateAfterAttempt >> pure Nothing
    Left (Blocked awaitedSymbol) => pure (Just awaitedSymbol)
    Left (Failed diagnostic)     => typeError diagnostic

-- The items whose check blocked, each with the symbol it is waiting for.
attemptAllChecks : (ResolvedItem -> StateT TypeCheckerState (Either CheckFailure) ()) 
    -> List ResolvedItem 
    -> StateT TypeCheckerState (Either CheckFailure) (List (ResolvedItem, SymbolId))
attemptAllChecks checkItem [] = pure []
attemptAllChecks checkItem (currentItem :: remainingItems) = do
  maybeAwaitedSymbol <- attemptCheck (checkItem currentItem)
  stuckRemainingItems <- attemptAllChecks checkItem remainingItems
  pure (maybe stuckRemainingItems (\awaitedSymbol => (currentItem, awaitedSymbol) :: stuckRemainingItems) maybeAwaitedSymbol)

-- One round: pass A on every pending signature, then pass B on every pending
-- body whose signature is recorded. Each productive round completes at least
-- one of the 2n entries, so 2n + 1 runBodyAndSignatureCheck always suffice.
runBodyAndSignatureChecks : (remainingRounds : Nat) -> RemainingWorkTodo -> StateT TypeCheckerState (Either CheckFailure) ()
runBodyAndSignatureChecks _ (MkRemainingWorkTodo [] []) = pure ()
runBodyAndSignatureChecks Z _ = unreachable __FILE__ {function = "runBodyAndSignatureCheck"} {reason = "every productive round completes an entry"}
runBodyAndSignatureChecks (S remainingRounds) remainingWork = do
  stuckSignatureItems <- attemptAllChecks checkSignature remainingWork.pendingSignatureItems
  let isWaitingForSignature = \pendingItem => any (isSameItem pendingItem . fst) stuckSignatureItems
  stuckBodyItems <- attemptAllChecks checkBody (filter (not . isWaitingForSignature) remainingWork.pendingBodyItems)
  let isStillPending = \pendingItem => isWaitingForSignature pendingItem || any (isSameItem pendingItem . fst) stuckBodyItems
      nextRemainingWork = MkRemainingWorkTodo (map fst stuckSignatureItems) (filter isStillPending remainingWork.pendingBodyItems)
  if remainingTaskCount nextRemainingWork < remainingTaskCount remainingWork
    then runBodyAndSignatureChecks remainingRounds nextRemainingWork
    else do
      checkerState <- get
      typeError (resolutionCycleTypeError checkerState.tables (stuckSignatureItems ++ stuckBodyItems))

resolveAndCheckTypes : TypeCheckerState -> List ResolvedItem -> Either TypeError TypeTables
resolveAndCheckTypes seededTypeCheckerState sourceFileItems =
  case execStateT seededTypeCheckerState (runBodyAndSignatureChecks (2 * length sourceFileItems + 1) (MkRemainingWorkTodo sourceFileItems sourceFileItems)) of
    Right finalTypeCheckerState => Right finalTypeCheckerState.tables
    Left (Failed diagnostic)    => Left diagnostic
    Left (Blocked _)            => unreachable __FILE__ {function = "resolveAndCheckTypes"} {reason = "attemptCheck catches every block"}

--------------------------------------------------------------------------------
-- The pipeline
--------------------------------------------------------------------------------

||| Passes A and B run in rounds until every signature and body is checked;
export
typeCheckSignaturesAndBodies : ResolvedModule -> Either TypeError TypeTables
typeCheckSignaturesAndBodies resolvedModule = do
  let sourceFileItems = getSourceCodeItems resolvedModule.ast
  let seededTypeCheckerState = seedTypeCheckerState resolvedModule sourceFileItems
  resolveAndCheckTypes seededTypeCheckerState sourceFileItems                            -- A ⇄ B

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
