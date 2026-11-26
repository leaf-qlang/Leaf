module Compiler.Frontend.TypeChecker.State

import Compiler.Helper
import Control.Monad.State
import Data.List
import Data.List1
import Data.SortedMap
import Data.SortedSet

import Compiler.Frontend.ScopeAndNameResolver.Data
import Compiler.Frontend.TypeChecker.Data
import Compiler.Frontend.TypeChecker.TcType
import Compiler.Frontend.TypeChecker.Type
import Compiler.Frontend.Syntax.AST
import Compiler.Frontend.ASTData
import Compiler.Frontend.ASTPhases
import Compiler.Frontend.QuantumAnnotations
import Compiler.Frontend.Source
import Compiler.Frontend.Syntax.Common
import Compiler.Frontend.Token

%default total

--------------------------------------------------------------------------------
-- Type checker state
--------------------------------------------------------------------------------
-- Threaded through the checker in a State monad and dropped when checking
-- ends: later passes read only the TypeTables it builds.
--------------------------------------------------------------------------------

public export
data LoopContext
  = ValueLoop (Maybe TcType)     -- `loop`: the type its break values combine to so far
  | UnitLoop                     -- while / for: break takes no value

public export
record InferenceState where                                          -- per function or const initializer, emptied by writeback
  constructor MkInferenceState
  nextInferenceVariableId    : Nat                                   -- identifier of the next fresh inference variable
  inferenceVariables         : SortedMap Nat InferenceVariableState  -- inference variables by their Nat identifier: placeholders for something the type checker doesn't know yet.
  expressionTypes            : SortedMap NodeId TcType               -- type of every expression in the body being checked
  patternTypes               : SortedMap NodeId TcType               -- type of each pattern node in the body being checked
  binderTypes                : SortedMap SymbolId TcType             -- locals of the function being checked
  scratchBinders             : List SymbolId                         -- list of the local bindings in the current body that were declared with let scratch
  uncomputeModeBinders       : List SymbolId                         -- list of the variables in the current function that were declared with :=
  integerLiterals            : List (SourceSpan, NodeId, Integer)    -- list of the integer literals in the current body whose range can't be checked yet
  enclosingLoops             : List LoopContext                      -- stack of loops surrounding the code that pass B is checking right now, innermost first
  linearQualifiers           : List (SourceSpan, NodeId)             -- each remaining `let linear` qualifier's span and its pattern's NodeId, checked at writeback
  generalVariableReportSpans : SortedMap Nat SourceSpan              -- where writeback reports CannotInferType for each general variable still open

 
public export
emptyInferenceState : InferenceState
emptyInferenceState = MkInferenceState 0 empty empty empty empty [] [] [] [] [] empty

public export
record TypeCheckerState where
  constructor MkTypeCheckerState
  typeTables                  : TypeTables
  enclosingFunctionReturnType : Maybe LeafType                    -- declared return type of the function whose body pass B is checking; Nothing for a const initializer
  inferenceState              : InferenceState                    -- pass B's (BodyCheck) scratch space for the one body it is checking right now
  topLevelItems               : SortedMap SymbolId ResolvedItem   -- maps each top-level item's symbol (const and fn for now) to that item's resolved AST node
  checkedBodies               : SortedSet SymbolId                -- set of functions whose bodies pass B (BodyCheck) has already finished
  constExprs                  : SortedMap NodeId Nat              -- memo table for evaluated length expressions

public export
data CheckFailure
  = Blocked SymbolId        -- needs this symbol's signature, value or checked body first
  | Failed TypeError

export
liftTypeError : TypeError -> StateT TypeCheckerState (Either CheckFailure) a
liftTypeError typeError = lift (Left (Failed typeError))

export
blocked : SymbolId -> StateT TypeCheckerState (Either CheckFailure) a
blocked awaitedSymbol = do
  checkerState <- get
  case lookup awaitedSymbol checkerState.topLevelItems of
    Just _  => lift (Left (Blocked awaitedSymbol))
    Nothing => unreachable __FILE__ {function = "blocked"} {reason = "symbol cannot be found in the checker state top-level items"}

--------------------------------------------------------------------------------
-- Recording results
--------------------------------------------------------------------------------

updatedTypedSymbolInfo : TypedSymbolInfo -> InferredType -> TypedSymbolInfo
updatedTypedSymbolInfo symbolInfo inferredType = { symbolType := inferredType } symbolInfo

recordInferenceVariableState : (variableId : Nat) -> InferenceVariableState -> StateT InferenceState (Either TypeError) ()
recordInferenceVariableState variableId variableState =
  modify $ \currentState => { inferenceVariables := insert variableId variableState currentState.inferenceVariables } currentState

export
recordSymbolType : SymbolId -> LeafType -> StateT TypeCheckerState (Either CheckFailure) ()
recordSymbolType symbolId leafType = do
  checkerState <- get
  case lookup symbolId checkerState.typeTables.symbols of
    Nothing => unreachable __FILE__ {function = "recordSymbolType"} {reason = "symbol cannot be found in the symbol table"}
    Just symbolInfo => do
      let updatedSymbolInfo = updatedTypedSymbolInfo symbolInfo (ResolvedType leafType)
      modify $ \currentState => { typeTables.symbols := insert symbolId updatedSymbolInfo currentState.typeTables.symbols } currentState

typedLocalVarQualifiers : TypedLocalVarQualifiers -> LeafType -> TypedLocalVarQualifiers
typedLocalVarQualifiers localVarQualifiers leafType =
  if hasOwnedQbit leafType
    then { quantumStorage := AssignedQbitStorage (MkQuantumStorageProperties NoAutomaticCleanup) } localVarQualifiers
    else { quantumStorage := NotQbitLocal } localVarQualifiers

export
recordParameterStorage : SymbolId -> LeafType -> StateT TypeCheckerState (Either CheckFailure) ()
recordParameterStorage symbolId leafType = do
  checkerState <- get
  case lookup symbolId checkerState.typeTables.localVarsMeta of
    Nothing => unreachable __FILE__ {function = "recordParameterStorage"} {reason = "symbol cannot be found in the local variable metadata"}
    Just localVariableQualifiers => do
      let classifiedQualifiers = typedLocalVarQualifiers localVariableQualifiers leafType
      modify $ \currentState => { typeTables.localVarsMeta := insert symbolId classifiedQualifiers currentState.typeTables.localVarsMeta } currentState

export
recordConstValue : SymbolId -> ConstValue -> StateT TypeCheckerState (Either CheckFailure) ()
recordConstValue symbolId constValue =
  modify $ \currentState => { typeTables.constValues := insert symbolId constValue currentState.typeTables.constValues } currentState

--------------------------------------------------------------------------------
-- Inference variables
--------------------------------------------------------------------------------
-- Tracks unknown types and quantum usage qualifiers during type checking.
-- Creates inference variables, merges them (records that they represent the same
-- unknown), resolves them, checks for infinite types, applies defaults, and
-- converts resolved types to LeafType.
--------------------------------------------------------------------------------

export
liftInferenceOperation : StateT InferenceState (Either TypeError) a -> StateT TypeCheckerState (Either CheckFailure) a
liftInferenceOperation inferenceOperation = do
  checkerState <- get
  case runStateT checkerState.inferenceState inferenceOperation of
    Left typeError => liftTypeError typeError
    Right (updatedInferenceState, operationResult) => do
      put $ { inferenceState := updatedInferenceState } checkerState
      pure operationResult

allocateInferenceVariable : InferenceVariableState -> StateT InferenceState (Either TypeError) Nat
allocateInferenceVariable initialVariableState = do
  inferenceState <- get
  let variableId = inferenceState.nextInferenceVariableId
  put $ { nextInferenceVariableId := S variableId } inferenceState
  recordInferenceVariableState variableId initialVariableState
  pure variableId

||| A general variable starts with the span of the node that created it as its
||| report span, where writeback reports CannotInferType if nothing solves it.
||| A literal variable always has a default, so it gets no report span.
export
freshTypeVariable : (creatingNodeSpan : SourceSpan) -> TypeVariableDomain -> StateT InferenceState (Either TypeError) TcType
freshTypeVariable creatingNodeSpan variableDomain = do
  variableId <- allocateInferenceVariable (OpenTypeVariable variableDomain 0)
  case variableDomain of
    AnyTypeDomain =>
      modify $ \currentState => { generalVariableReportSpans := insert variableId creatingNodeSpan currentState.generalVariableReportSpans } currentState
    IntegerLiteralDomain => pure ()
    FloatLiteralDomain => pure ()
  pure (TcVariable variableId)

export
freshQuantumUsageVariable : StateT InferenceState (Either TypeError) TcQuantumUsage
freshQuantumUsageVariable = do
  variableId <- allocateInferenceVariable (OpenQuantumUsage 0)
  pure (UnknownQuantumUsage variableId)

followParentIdsToRoot : (fuel : Nat)
  -> (variableId : Nat)
  -> SortedMap Nat InferenceVariableState
  -> (visitedVariableIds : List Nat)
  -> (Nat, InferenceVariableState, List Nat)
followParentIdsToRoot fuel variableId inferenceVariables visitedVariableIds =
  case lookup variableId inferenceVariables of
    Nothing =>
      unreachable __FILE__
        {function = "followParentIdsToRoot"}
        {reason = "inference variable " ++ show variableId ++ " does not exist"}
    Just (ParentReference parentVariableId) =>
      case fuel of
        Z =>
          unreachable __FILE__
            {function = "followParentIdsToRoot"}
            {reason = "the parent references from inference variable " ++
                      show variableId ++ " form a cycle"}
        S remainingFuel =>
          followParentIdsToRoot remainingFuel parentVariableId inferenceVariables
            (variableId :: visitedVariableIds)
    Just rootState => (variableId, rootState, visitedVariableIds)

export
findInferenceVariableRoot : (variableId : Nat)
  -> StateT InferenceState (Either TypeError) (Nat, InferenceVariableState)
findInferenceVariableRoot variableId = do
  inferenceState <- get
  let (rootId, rootState, visitedVariableIds) =
        followParentIdsToRoot inferenceState.nextInferenceVariableId variableId inferenceState.inferenceVariables []
  traverse_ (\visitedVariableId => recordInferenceVariableState visitedVariableId (ParentReference rootId)) visitedVariableIds
  pure (rootId, rootState)

-- Merges two distinct open roots: the lower-ranked root goes under the other.
-- With equal ranks the second root goes under the first, whose rank grows by one.
-- The surviving root is rebuilt from its rank with openRootWithRank.
mergeOpenRootsByRank : (firstRootId : Nat)
  -> (firstRank : Nat)
  -> (secondRootId : Nat)
  -> (secondRank : Nat)
  -> (openRootWithRank : Nat -> InferenceVariableState)
  -> StateT InferenceState (Either TypeError) ()
mergeOpenRootsByRank firstRootId firstRank secondRootId secondRank openRootWithRank =
  if firstRank < secondRank
    then do
      recordInferenceVariableState firstRootId (ParentReference secondRootId)
      recordInferenceVariableState secondRootId (openRootWithRank secondRank)
    else if secondRank < firstRank
      then do
        recordInferenceVariableState secondRootId (ParentReference firstRootId)
        recordInferenceVariableState firstRootId (openRootWithRank firstRank)
      else do
        recordInferenceVariableState secondRootId (ParentReference firstRootId)
        recordInferenceVariableState firstRootId (openRootWithRank (S firstRank))

||| Makes two open type variables the same unknown, keeping the intersection of
||| their domains: a general variable merged with a literal variable takes the
||| literal's domain. An integer literal variable and a float literal variable
||| have no type in common, which is a TypeMismatch at the span, shown with the
||| literals' defaults i32 and f64. Merging a variable with itself does nothing.
||| A fixed variable cannot be merged: unify resolves it to its type first.
export
mergeTypeVariables : SourceSpan -> (expectedVariableId : Nat) -> (actualVariableId : Nat) -> StateT InferenceState (Either TypeError) ()
mergeTypeVariables sourceSpan expectedVariableId actualVariableId = do
  (expectedRootId, expectedRootState) <- findInferenceVariableRoot expectedVariableId
  (actualRootId, actualRootState) <- findInferenceVariableRoot actualVariableId
  if expectedRootId == actualRootId
    then pure ()
    else
      case (expectedRootState, actualRootState) of
        (OpenTypeVariable expectedDomain expectedRank, OpenTypeVariable actualDomain actualRank) =>
          let mergeWithDomain = \sharedDomain =>
                mergeOpenRootsByRank expectedRootId expectedRank actualRootId actualRank (OpenTypeVariable sharedDomain)
          in case (expectedDomain, actualDomain) of
               (IntegerLiteralDomain, FloatLiteralDomain) =>
                 lift (Left (TypeMismatch
                   (LeafPrimitiveType TypPrimI32)
                   (LeafPrimitiveType TypPrimF64)
                   sourceSpan))
               (FloatLiteralDomain, IntegerLiteralDomain) =>
                 lift (Left (TypeMismatch
                   (LeafPrimitiveType TypPrimF64)
                   (LeafPrimitiveType TypPrimI32)
                   sourceSpan))
               (AnyTypeDomain, _) => mergeWithDomain actualDomain
               _ => mergeWithDomain expectedDomain   -- the actual domain is AnyTypeDomain or equals the expected one
        _ =>
          unreachable __FILE__
            {function = "mergeTypeVariables"}
            {reason = "only two open type variables can be merged, not " ++
                      show expectedVariableId ++ " and " ++ show actualVariableId}

||| Makes two open quantum usage variables the same unknown. Merging a variable
||| with itself does nothing. A fixed variable cannot be merged: unify resolves it first.
export
mergeQuantumUsageVariables : (firstVariableId : Nat)
  -> (secondVariableId : Nat)
  -> StateT InferenceState (Either TypeError) ()
mergeQuantumUsageVariables firstVariableId secondVariableId = do
  (firstRootId, firstRootState) <- findInferenceVariableRoot firstVariableId
  (secondRootId, secondRootState) <- findInferenceVariableRoot secondVariableId
  if firstRootId == secondRootId
    then pure ()
    else
      case (firstRootState, secondRootState) of
        (OpenQuantumUsage firstRank, OpenQuantumUsage secondRank) =>
          mergeOpenRootsByRank firstRootId firstRank secondRootId secondRank OpenQuantumUsage
        _ =>
          unreachable __FILE__
            {function = "mergeQuantumUsageVariables"}
            {reason = "only two open quantum usage variables can be merged, not " ++
                      show firstVariableId ++ " and " ++ show secondVariableId}

export
resolveQuantumUsageThroughParentReferences : TcQuantumUsage
  -> StateT InferenceState (Either TypeError) TcQuantumUsage
resolveQuantumUsageThroughParentReferences (KnownQuantumUsage quantumUsageQualifier) =
  pure (KnownQuantumUsage quantumUsageQualifier)
resolveQuantumUsageThroughParentReferences (UnknownQuantumUsage variableId) = do
  (rootId, rootState) <- findInferenceVariableRoot variableId
  case rootState of
    OpenQuantumUsage _ => pure (UnknownQuantumUsage rootId)
    FixedQuantumUsage quantumUsageQualifier => pure (KnownQuantumUsage quantumUsageQualifier)
    OpenTypeVariable _ _ =>
      unreachable __FILE__
        {function = "resolveQuantumUsageThroughParentReferences"}
        {reason = "type variable " ++ show rootId ++ " is used as a quantum usage"}
    FixedTypeVariable _ =>
      unreachable __FILE__
        {function = "resolveQuantumUsageThroughParentReferences"}
        {reason = "type variable " ++ show rootId ++ " is used as a quantum usage"}
    ParentReference _ =>
      unreachable __FILE__
        {function = "resolveQuantumUsageThroughParentReferences"}
        {reason = "the root lookup returned a parent reference for variable " ++ show rootId}

resolveTcTypeWithFuel : (fuel : Nat) -> TcType -> StateT InferenceState (Either TypeError) TcType
resolveTcTypeWithFuel fuel tcType =
  case tcType of
    TcPrimitiveType _ => pure tcType
    TcNamedType _ => pure tcType
    TcUnitType => pure tcType
    TcTupleType elementTypes => TcTupleType <$> traverse resolveComponent elementTypes
    TcArrayType elementType arrayLength => (\resolvedElementType => TcArrayType resolvedElementType arrayLength) <$> resolveComponent elementType
    TcSliceType elementType => TcSliceType <$> resolveComponent elementType
    TcRangeType rangeShape elementType => TcRangeType rangeShape <$> resolveComponent elementType
    TcReferenceType borrowKind referencedType => TcReferenceType borrowKind <$> resolveComponent referencedType
    TcFunctionType functionEffect supportKinds parameterTypes resultType =>
      TcFunctionType functionEffect supportKinds <$> traverse resolveComponent parameterTypes <*> resolveComponent resultType
    TcQuantumQualifiedType quantumUsage qualifiedType =>
      TcQuantumQualifiedType <$> resolveQuantumUsageThroughParentReferences quantumUsage
                             <*> resolveComponent qualifiedType
    TcNeverType => pure tcType
    TcStringLiteralType => pure tcType
    TcVariable variableId => do
      (rootId, rootState) <- findInferenceVariableRoot variableId
      case rootState of
        OpenTypeVariable _ _ => pure (TcVariable rootId)
        FixedTypeVariable fixedType =>
          case fuel of
            Z =>
              unreachable __FILE__
                {function = "resolveTcTypeWithFuel"}
                {reason = "the fixed type of inference variable " ++ show rootId ++ " contains itself"}
            S remainingFuel => resolveTcTypeWithFuel remainingFuel fixedType
        OpenQuantumUsage _ =>
          unreachable __FILE__
            {function = "resolveTcTypeWithFuel"}
            {reason = "quantum usage variable " ++ show rootId ++ " is used as a type"}
        FixedQuantumUsage _ =>
          unreachable __FILE__
            {function = "resolveTcTypeWithFuel"}
            {reason = "quantum usage variable " ++ show rootId ++ " is used as a type"}
        ParentReference _ =>
          unreachable __FILE__
            {function = "resolveTcTypeWithFuel"}
            {reason = "the root lookup returned a parent reference for variable " ++ show rootId}
  where
    resolveComponent : TcType -> StateT InferenceState (Either TypeError) TcType
    resolveComponent componentType = resolveTcTypeWithFuel fuel (assert_smaller tcType componentType)

||| Replaces every fixed variable in the type by its resolved fixed type, and
||| every open variable by its root, so the result holds only open roots.
export
resolveTcTypeThroughParentReferences : TcType
  -> StateT InferenceState (Either TypeError) TcType
resolveTcTypeThroughParentReferences tcType = do
  inferenceState <- get
  resolveTcTypeWithFuel inferenceState.nextInferenceVariableId tcType

typeContainsVariable : (variableId : Nat) -> TcType -> Bool
typeContainsVariable variableId tcType =
  case tcType of
    TcPrimitiveType _ => False
    TcNamedType _ => False
    TcUnitType => False
    TcTupleType elementTypes => any recur (forget elementTypes)
    TcArrayType elementType _ => recur elementType
    TcSliceType elementType => recur elementType
    TcRangeType _ elementType => recur elementType
    TcReferenceType _ referencedType => recur referencedType
    TcFunctionType _ _ parameterTypes resultType => any recur parameterTypes || recur resultType
    TcQuantumQualifiedType _ qualifiedType => recur qualifiedType
    TcNeverType => False
    TcStringLiteralType => False
    TcVariable candidateVariableId => variableId == candidateVariableId
  where
    recur : TcType -> Bool
    recur componentType = typeContainsVariable variableId (assert_smaller tcType componentType)

||| The occurs check, run before fixing a type variable to a type: fixing it to a
||| type that contains the variable would describe an infinite type, such as a
||| variable inside its own array or function type. No finite type exists to show
||| in a TypeMismatch, so this is CannotInferType at the span. A candidate that is
||| the variable itself is not infinite and passes.
export
checkVariableDoesNotOccurInType : SourceSpan
  -> (variableId : Nat)
  -> (candidateType : TcType)
  -> StateT InferenceState (Either TypeError) ()
checkVariableDoesNotOccurInType sourceSpan variableId candidateType = do
  (rootId, _) <- findInferenceVariableRoot variableId
  resolvedCandidateType <- resolveTcTypeThroughParentReferences candidateType
  case resolvedCandidateType of
    TcVariable _ => pure ()
    _ =>
      when (typeContainsVariable rootId resolvedCandidateType) $
        lift (Left (CannotInferType sourceSpan))

||| Fixes every open root that has a default: an integer literal variable to i32,
||| a float literal variable to f64 and a quantum usage variable to linear. A general
||| variable has no default and stays open; the result is the ID of the
||| lowest-numbered one, which writeback reports as CannotInferType, or Nothing
||| when none is left.
export
defaultOpenVariables : StateT InferenceState (Either TypeError) (Maybe Nat)
defaultOpenVariables = do
  inferenceState <- get
  let variableEntries = Data.SortedMap.toList inferenceState.inferenceVariables
  traverse_ defaultVariable variableEntries
  pure (head' (mapMaybe openGeneralVariableId variableEntries))
  where
    defaultVariable : (Nat, InferenceVariableState) -> StateT InferenceState (Either TypeError) ()
    defaultVariable (variableId, variableState) =
      case variableState of
        OpenTypeVariable IntegerLiteralDomain _ => recordInferenceVariableState variableId (FixedTypeVariable (TcPrimitiveType TypPrimI32))
        OpenTypeVariable FloatLiteralDomain _ => recordInferenceVariableState variableId (FixedTypeVariable (TcPrimitiveType TypPrimF64))
        OpenQuantumUsage _ => recordInferenceVariableState variableId (FixedQuantumUsage QuantumUsageLinear)
        _ => pure ()

    openGeneralVariableId : (Nat, InferenceVariableState) -> Maybe Nat
    openGeneralVariableId (variableId, OpenTypeVariable AnyTypeDomain _) = Just variableId
    openGeneralVariableId _ = Nothing

resolvedTcTypeToLeafType : TcType -> LeafType
resolvedTcTypeToLeafType tcType =
  case tcType of
    TcPrimitiveType primitiveName => LeafPrimitiveType primitiveName
    TcNamedType symbolId => LeafNamedType symbolId
    TcUnitType => LeafUnitType
    TcTupleType elementTypes => LeafTupleType (map recur elementTypes)
    TcArrayType elementType arrayLength => LeafArrayType (recur elementType) arrayLength
    TcSliceType elementType => LeafSliceType (recur elementType)
    TcRangeType rangeShape elementType => LeafRangeType rangeShape (recur elementType)
    TcReferenceType borrowKind referencedType => LeafReferenceType borrowKind (recur referencedType)
    TcFunctionType functionEffect supportKinds parameterTypes resultType =>
      LeafFunctionType functionEffect supportKinds (map recur parameterTypes) (recur resultType)
    TcQuantumQualifiedType (KnownQuantumUsage quantumUsageQualifier) qualifiedType =>
      LeafQuantumQualifiedType quantumUsageQualifier (recur qualifiedType)
    TcQuantumQualifiedType (UnknownQuantumUsage variableId) _ =>
      unreachable __FILE__
        {function = "resolvedTcTypeToLeafType"}
        {reason = "quantum usage variable " ++ show variableId ++
                  " is still open; writeback defaults every variable before converting"}
    TcNeverType => LeafNeverType
    TcStringLiteralType => LeafStringLiteralType
    TcVariable variableId =>
      unreachable __FILE__
        {function = "resolvedTcTypeToLeafType"}
        {reason = "type variable " ++ show variableId ++
                  " is still open; writeback defaults every variable before converting"}
  where
    recur : TcType -> LeafType
    recur componentType = resolvedTcTypeToLeafType (assert_smaller tcType componentType)

||| Converts a type to a LeafType after writeback has defaulted every variable.
||| A variable still open at this point is an internal error.
export
tcTypeToLeafType : TcType -> StateT InferenceState (Either TypeError) LeafType
tcTypeToLeafType tcType = resolvedTcTypeToLeafType <$> resolveTcTypeThroughParentReferences tcType
