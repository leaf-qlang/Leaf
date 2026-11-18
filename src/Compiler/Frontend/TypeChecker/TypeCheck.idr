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
getItemSymbolId item =
  case item.nodeValue of
    ItemFunction declaration => declaration.functionName.nodeValue.nameNodeSymbolId
    ItemConst declaration    => declaration.constName.nodeValue.nameNodeSymbolId
    ItemModule _             => notImplemented __FILE__ "getItemSymbolId" "ItemModule"
    ItemUse _                => notImplemented __FILE__ "getItemSymbolId" "ItemUse"
    ItemEnum _               => notImplemented __FILE__ "getItemSymbolId" "ItemEnum"
    ItemQEnum _              => notImplemented __FILE__ "getItemSymbolId" "ItemQEnum"
    ItemStruct _             => notImplemented __FILE__ "getItemSymbolId" "ItemStruct"
    ItemImpl _               => notImplemented __FILE__ "getItemSymbolId" "ItemImpl"

getItemNameSpan : ResolvedItem -> SourceSpan
getItemNameSpan item =
  case item.nodeValue of
    ItemFunction declaration => declaration.functionName.astInfo.span
    ItemConst declaration    => declaration.constName.astInfo.span
    ItemModule _             => notImplemented __FILE__ "getItemNameSpan" "ItemModule"
    ItemUse _                => notImplemented __FILE__ "getItemNameSpan" "ItemUse"
    ItemEnum _               => notImplemented __FILE__ "getItemNameSpan" "ItemEnum"
    ItemQEnum _              => notImplemented __FILE__ "getItemNameSpan" "ItemQEnum"
    ItemStruct _             => notImplemented __FILE__ "getItemNameSpan" "ItemStruct"
    ItemImpl _               => notImplemented __FILE__ "getItemNameSpan" "ItemImpl"

isSameItem : ResolvedItem -> ResolvedItem -> Bool
isSameItem a b = a.astInfo.nodeId == b.astInfo.nodeId

--------------------------------------------------------------------------------
-- Seeding
--------------------------------------------------------------------------------

getSourceCodeItems : ResolvedSourceFile -> List ResolvedItem
getSourceCodeItems (MkAstNode _ _ (MkSourceFileNode _ items)) = items

seedTypeTables : ScopeTables -> TypeTables
seedTypeTables scopeTables =
  MkTypeTables
    scopeTables.scopes
    scopeTables.nodeScopes
    (map (\symbol => { symbolType := TypeNotYetResolved } symbol) scopeTables.symbols)
    (map (\variable => { quantumStorage := PendingQbitClassification } variable) scopeTables.localVarsMeta)
    scopeTables.memberScopes
    scopeTables.references
    empty                                                -- constValues
    empty                                                -- expressionTypes
    empty                                                -- patternTypes
    empty                                                -- coercions
    empty                                                -- calls

seedPresetSymbolTypes : TypeTables -> TypeTables
seedPresetSymbolTypes tables = { symbols := map seedPresetSymbolType tables.symbols } tables
  where
    seedPresetSymbolType : TypedSymbolInfo -> TypedSymbolInfo
    seedPresetSymbolType symbol =
      case (symbol.symbolKind, symbol.origin) of
        (SymbolModule, _)               => { symbolType := NoValueType } symbol
        (SymbolFunction, PreludeSymbol) => { symbolType := preludeValueType symbol.declaredName } symbol
        _                               => symbol

seedTypeCheckerState : ResolvedModule -> List ResolvedItem -> TypeCheckerState
seedTypeCheckerState resolvedModule items =
  MkTypeCheckerState
    (seedPresetSymbolTypes (seedTypeTables resolvedModule.tables))
    Nothing
    emptyInferenceState
    (fromList (map (\item => (getItemSymbolId item, item)) items))
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
resolutionCycleTypeError tables stuck =
  case stuck of
    [] => unreachable __FILE__ {function = "resolutionCycleError"} {reason = "a round without progress has stuck items"}
    (first, firstWait) :: _ =>
      CyclicDeclaration (map symbolName (loopFrom (S (length stuck)) [] firstWait)) (getItemNameSpan first)
  where
    symbolName : SymbolId -> String
    symbolName symbolId =
      case lookup symbolId tables.symbols of
        Just symbol => symbol.declaredName
        Nothing => unreachable __FILE__ "resolutionCycleError" "a cycle references an unknown symbol"

    waits : List (SymbolId, SymbolId)
    waits = map (\(item, waitingFor) => (getItemSymbolId item, waitingFor)) stuck

    -- `visited` holds the symbols walked so far, most recent first.
    loopFrom : (fuel : Nat) -> (visited : List SymbolId) -> SymbolId -> List SymbolId
    loopFrom Z visited _ = reverse visited
    loopFrom (S fuel) visited symbol =
      if elem symbol visited
        then symbol :: reverse (takeWhile (/= symbol) visited)
        else case lookup symbol waits of
               Just next => loopFrom fuel (symbol :: visited) next
               Nothing   => reverse (symbol :: visited)

--------------------------------------------------------------------------------
-- Passes A and B
--------------------------------------------------------------------------------

record RemainingWorkTodo where
  constructor MkRemainingWorkTodo
  signatures : List ResolvedItem     -- pass A has not recorded the signature yet, in source order
  bodies     : List ResolvedItem     -- pass B has not checked the body or initializer yet, in source order

noRemaining : RemainingWorkTodo -> Nat
noRemaining work = length work.signatures + length work.bodies

-- A blocked check leaves the state exactly as it was so retrying next round is safe.
attemptCheck : StateT TypeCheckerState (Either CheckFailure) () -> StateT TypeCheckerState (Either CheckFailure) (Maybe SymbolId)
attemptCheck computation = do
  stateBefore <- get
  case execStateT stateBefore computation of
    Right stateAfter       => put stateAfter >> pure Nothing
    Left (Blocked symbol)  => pure (Just symbol)
    Left (Failed err)      => typeError err

-- The items whose check blocked, each with the symbol it is waiting for.
attemptAllChecks : (ResolvedItem -> StateT TypeCheckerState (Either CheckFailure) ()) 
    -> List ResolvedItem 
    -> StateT TypeCheckerState (Either CheckFailure) (List (ResolvedItem, SymbolId))
attemptAllChecks checkFunction [] = pure []
attemptAllChecks checkFunction (item :: items) = do
  outcome <- attemptCheck (checkFunction item)
  stuck <- attemptAllChecks checkFunction items
  pure (maybe stuck (\waitingFor => (item, waitingFor) :: stuck) outcome)

-- One round: pass A on every pending signature, then pass B on every pending
-- body whose signature is recorded. Each productive round completes at least
-- one of the 2n entries, so 2n + 1 runBodyAndSignatureCheck always suffice.
runBodyAndSignatureChecks : (fuel : Nat) -> RemainingWorkTodo -> StateT TypeCheckerState (Either CheckFailure) ()
runBodyAndSignatureChecks _ (MkRemainingWorkTodo [] []) = pure ()
runBodyAndSignatureChecks Z _ = unreachable __FILE__ {function = "runBodyAndSignatureCheck"} {reason = "every productive round completes an entry"}
runBodyAndSignatureChecks (S fuel) work = do
  stuckSignatures <- attemptAllChecks checkSignature work.signatures
  let waitingForSignature = \item => any (isSameItem item . fst) stuckSignatures
  stuckBodies <- attemptAllChecks checkBody (filter (not . waitingForSignature) work.bodies)
  let stillPending = \item => waitingForSignature item || any (isSameItem item . fst) stuckBodies
      next = MkRemainingWorkTodo (map fst stuckSignatures) (filter stillPending work.bodies)
  if noRemaining next < noRemaining work
    then runBodyAndSignatureChecks fuel next
    else do
      checkerState <- get
      typeError (resolutionCycleTypeError checkerState.tables (stuckSignatures ++ stuckBodies))

resolveAndCheckTypes : TypeCheckerState -> List ResolvedItem -> Either TypeError TypeTables
resolveAndCheckTypes seededState items =
  case execStateT seededState (runBodyAndSignatureChecks (2 * length items + 1) (MkRemainingWorkTodo items items)) of
    Right finalState      => Right finalState.tables
    Left (Failed typeErr) => Left typeErr
    Left (Blocked _)      => unreachable __FILE__ {function = "resolveAndCheckTypes"} {reason = "attemptCheck catches every block"}

--------------------------------------------------------------------------------
-- The pipeline
--------------------------------------------------------------------------------

||| Passes A and B run in rounds until every signature and body is checked;
export
typeCheckSignaturesAndBodies : ResolvedModule -> Either TypeError TypeTables
typeCheckSignaturesAndBodies resolvedModule = do
  let items = getSourceCodeItems resolvedModule.ast
  resolveAndCheckTypes (seedTypeCheckerState resolvedModule items) items                  -- A ⇄ B

||| Passes A and B run in rounds until every signature and body is checked;
||| then the typed AST is built, and effects and ownership are checked once each.
public export
typeCheck : ResolvedModule -> Either TypeError TypedModule
typeCheck resolvedModule = do 
  typeTables <- typeCheckSignaturesAndBodies resolvedModule                              -- A ⇄ B
  let typedAst = translateAst typeTables resolvedModule.ast                              -- T
  checkEffects typeTables typedAst                                                       -- E
  ownership <- checkOwnership typeTables typedAst                                        -- C
  pure (MkTypedModule resolvedModule.rootSymbolId resolvedModule.rootScopeId typedAst typeTables ownership)

