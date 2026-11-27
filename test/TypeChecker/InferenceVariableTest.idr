module TypeChecker.InferenceVariableTest

import Control.Monad.State
import Data.List1
import Data.SortedMap
import Data.SortedSet
import TestFramework

import Compiler.Frontend.ASTData
import Compiler.Frontend.ASTPhases
import Compiler.Frontend.TypeChecker.Data
import Compiler.Frontend.TypeChecker.Phases.BodyCheck
import Compiler.Frontend.TypeChecker.State
import Compiler.Frontend.TypeChecker.TcType
import Compiler.Frontend.TypeChecker.Type
import Compiler.Frontend.Source
import Compiler.Frontend.Syntax.AST
import Compiler.Frontend.Syntax.Common
import Compiler.Frontend.Token

%default total

-- The operations run on emptyInferenceState, which numbers variables from 0 in
-- creation order, so a test refers to its variables by those numbers. Type
-- variables and quantum usage variables share the numbering.

inferenceTestSpan : SourceSpan
inferenceTestSpan = MkSourceSpan "inference-test.rs" (MkSourcePos 1 1) (MkSourcePos 1 2)

secondInferenceTestSpan : SourceSpan
secondInferenceTestSpan = MkSourceSpan "inference-test.rs" (MkSourcePos 2 5) (MkSourcePos 2 6)

-- InferenceVariableState has no Show or Eq implementation, so tests compare
-- descriptions of the variable states.
describeVariableState : InferenceVariableState -> String
describeVariableState variableState =
  case variableState of
    OpenTypeVariable AnyTypeDomain rank => "open general, rank " ++ show rank
    OpenTypeVariable IntegerLiteralDomain rank => "open integer, rank " ++ show rank
    OpenTypeVariable FloatLiteralDomain rank => "open float, rank " ++ show rank
    FixedTypeVariable _ => "fixed type"
    OpenQuantumUsage rank => "open quantum usage, rank " ++ show rank
    FixedQuantumUsage quantumUsageQualifier => "fixed quantum usage " ++ show quantumUsageQualifier
    ParentReference parentVariableId => "parent " ++ show parentVariableId

runFromEmptyState : StateT InferenceState (Either TypeError) a -> Either String (InferenceState, a)
runFromEmptyState inferenceOperation =
  case runStateT emptyInferenceState inferenceOperation of
    Left typeError => Left (show typeError)
    Right finalStateAndResult => Right finalStateAndResult

resultFromEmptyState : StateT InferenceState (Either TypeError) a -> Either String a
resultFromEmptyState inferenceOperation = snd <$> runFromEmptyState inferenceOperation

variableStatesFromEmptyState : StateT InferenceState (Either TypeError) a -> Either String (List (Nat, String))
variableStatesFromEmptyState inferenceOperation = do
  (finalState, _) <- runFromEmptyState inferenceOperation
  pure (map (\(variableId, variableState) => (variableId, describeVariableState variableState))
            (Data.SortedMap.toList finalState.inferenceVariables))

anyTypeDomainVariableSpansFromEmptyState : StateT InferenceState (Either TypeError) a -> Either String (List (Nat, String))
anyTypeDomainVariableSpansFromEmptyState inferenceOperation = do
  (finalState, _) <- runFromEmptyState inferenceOperation
  pure (map (\(variableId, reportSpan) => (variableId, showSourceSpan reportSpan))
            (Data.SortedMap.toList finalState.anyTypeDomainVariableSpans))

-- unify runs over the whole checker state. These tests need only its inference
-- state, so the tables and the other fields start empty.
emptyTypeTables : TypeTables
emptyTypeTables = MkTypeTables empty empty empty empty empty empty empty empty empty empty empty

-- Runs a checker operation from an empty checker state, and returns the final
-- inference state with the result.
runCheckerOperationFromEmptyState : StateT TypeCheckerState (Either CheckFailure) a -> Either String (InferenceState, a)
runCheckerOperationFromEmptyState checkerOperation =
  case runStateT (MkTypeCheckerState emptyTypeTables Nothing emptyInferenceState empty Data.SortedSet.empty empty) checkerOperation of
    Left (Failed typeError) => Left (show typeError)
    Left (Blocked (MkSymbolId symbolNumber)) => Left ("blocked on symbol " ++ show symbolNumber)
    Right (finalCheckerState, operationResult) => Right (finalCheckerState.inferenceState, operationResult)

checkerResultFromEmptyState : StateT TypeCheckerState (Either CheckFailure) a -> Either String a
checkerResultFromEmptyState checkerOperation = snd <$> runCheckerOperationFromEmptyState checkerOperation

checkerVariableStatesFromEmptyState : StateT TypeCheckerState (Either CheckFailure) a -> Either String (List (Nat, String))
checkerVariableStatesFromEmptyState checkerOperation = do
  (finalInferenceState, _) <- runCheckerOperationFromEmptyState checkerOperation
  pure (map (\(variableId, variableState) => (variableId, describeVariableState variableState))
            (Data.SortedMap.toList finalInferenceState.inferenceVariables))

-- Builds a state by hand, for shapes the operations reach only after several steps.
stateWithVariables : List (Nat, InferenceVariableState) -> InferenceState
stateWithVariables variableEntries =
  { nextInferenceVariableId := length variableEntries
  , inferenceVariables := fromList variableEntries
  } emptyInferenceState

freshTypeVariables : List TypeVariableDomain -> StateT InferenceState (Either TypeError) ()
freshTypeVariables variableDomains = traverse_ (freshTypeVariable inferenceTestSpan) variableDomains

i32Type : LeafType
i32Type = LeafPrimitiveType TypPrimI32

f64Type : LeafType
f64Type = LeafPrimitiveType TypPrimF64

u8Type : LeafType
u8Type = LeafPrimitiveType TypPrimU8

typeMismatchMessage : LeafType -> LeafType -> String
typeMismatchMessage expectedType actualType = show (TypeMismatch expectedType actualType inferenceTestSpan)

export
runInferenceVariableTests : IO Bool
runInferenceVariableTests = runTests $ Test.do

  -- Fresh variables

  test "fresh variables are open roots of rank 0, numbered in creation order" $
    variableStatesFromEmptyState (do
      freshTypeVariables [AnyTypeDomain, IntegerLiteralDomain, FloatLiteralDomain]
      freshQuantumUsageVariable) `shouldBe`
      Right [(0, "open general, rank 0"), (1, "open integer, rank 0"), (2, "open float, rank 0"), (3, "open quantum usage, rank 0")]

  test "only a general variable records the span of the node that created it" $
    anyTypeDomainVariableSpansFromEmptyState (do
      _ <- freshTypeVariable inferenceTestSpan IntegerLiteralDomain
      _ <- freshTypeVariable secondInferenceTestSpan AnyTypeDomain
      freshTypeVariable inferenceTestSpan FloatLiteralDomain) `shouldBe`
      Right [(1, showSourceSpan secondInferenceTestSpan)]

  -- Unifying a variable with itself

  test "unifying a type variable with itself leaves it an open root" $
    checkerVariableStatesFromEmptyState (do
      liftInferenceOperation (freshTypeVariables [AnyTypeDomain])
      unify inferenceTestSpan (TcVariable 0) (TcVariable 0)) `shouldBe`
      Right [(0, "open general, rank 0")]

  test "unifying two type variables that already share a root changes nothing" $
    checkerVariableStatesFromEmptyState (do
      liftInferenceOperation (do
        freshTypeVariables [AnyTypeDomain, AnyTypeDomain]
        mergeTypeVariables inferenceTestSpan 0 1)
      unify inferenceTestSpan (TcVariable 1) (TcVariable 0)) `shouldBe`
      Right [(0, "open general, rank 1"), (1, "parent 0")]

  test "unifying a qualified qbit with itself leaves its quantum usage variable open" $
    checkerVariableStatesFromEmptyState (do
      _ <- liftInferenceOperation freshQuantumUsageVariable
      let qualifiedQbitType = TcQuantumQualifiedType (UnknownQuantumUsage 0) (TcPrimitiveType TypPrimQbit)
      unify inferenceTestSpan qualifiedQbitType qualifiedQbitType) `shouldBe`
      Right [(0, "open quantum usage, rank 0")]

  -- Merging a variable with itself

  test "merging a type variable with itself leaves it an open root" $
    variableStatesFromEmptyState (do
      freshTypeVariables [AnyTypeDomain]
      mergeTypeVariables inferenceTestSpan 0 0) `shouldBe`
      Right [(0, "open general, rank 0")]

  test "merging two type variables that already share a root changes nothing" $
    variableStatesFromEmptyState (do
      freshTypeVariables [AnyTypeDomain, AnyTypeDomain]
      mergeTypeVariables inferenceTestSpan 0 1
      mergeTypeVariables inferenceTestSpan 1 0) `shouldBe`
      Right [(0, "open general, rank 1"), (1, "parent 0")]

  test "merging a quantum usage variable with itself leaves it an open root" $
    variableStatesFromEmptyState (do
      _ <- freshQuantumUsageVariable
      mergeQuantumUsageVariables 0 0) `shouldBe`
      Right [(0, "open quantum usage, rank 0")]

  -- A general variable merged with a literal variable

  test "a general variable merged with an integer literal variable takes the integer domain" $
    variableStatesFromEmptyState (do
      freshTypeVariables [AnyTypeDomain, IntegerLiteralDomain]
      mergeTypeVariables inferenceTestSpan 0 1) `shouldBe`
      Right [(0, "open integer, rank 1"), (1, "parent 0")]

  test "a general variable merged with an integer literal variable defaults to i32" $
    resultFromEmptyState (do
      freshTypeVariables [AnyTypeDomain, IntegerLiteralDomain]
      mergeTypeVariables inferenceTestSpan 0 1
      openGeneralVariableId <- defaultOpenVariables
      generalVariableType <- tcTypeToLeafType (TcVariable 0)
      pure (openGeneralVariableId, generalVariableType)) `shouldBe`
      Right (Nothing, i32Type)

  -- A general variable later fixed to an integer

  test "a general variable unified with u8 is fixed to u8" $
    checkerResultFromEmptyState (do
      liftInferenceOperation (freshTypeVariables [AnyTypeDomain])
      unify inferenceTestSpan (TcPrimitiveType TypPrimU8) (TcVariable 0)
      liftInferenceOperation (tcTypeToLeafType (TcVariable 0))) `shouldBe`
      Right u8Type

  test "a general variable merged with an integer literal variable and later unified with u8 fixes both to u8" $
    checkerResultFromEmptyState (do
      liftInferenceOperation (do
        freshTypeVariables [AnyTypeDomain, IntegerLiteralDomain]
        mergeTypeVariables inferenceTestSpan 0 1)
      unify inferenceTestSpan (TcPrimitiveType TypPrimU8) (TcVariable 0)
      liftInferenceOperation (do
        openGeneralVariableId <- defaultOpenVariables
        variableTypes <- traverse tcTypeToLeafType [TcVariable 0, TcVariable 1]
        pure (openGeneralVariableId, variableTypes))) `shouldBe`
      Right (Nothing, [u8Type, u8Type])

  test "a general variable merged with an integer literal variable cannot later be fixed to bool" $
    checkerResultFromEmptyState (do
      liftInferenceOperation (do
        freshTypeVariables [AnyTypeDomain, IntegerLiteralDomain]
        mergeTypeVariables inferenceTestSpan 0 1)
      unify inferenceTestSpan (TcPrimitiveType TypPrimBool) (TcVariable 0)) `shouldBe`
      Left (typeMismatchMessage (LeafPrimitiveType TypPrimBool) i32Type)

  test "a general variable resolves to the integer type its root is fixed to" $
    resultFromEmptyState (do
      put (stateWithVariables [(0, ParentReference 1), (1, FixedTypeVariable (TcPrimitiveType TypPrimU8))])
      tcTypeToLeafType (TcArrayType (TcVariable 0) 3)) `shouldBe`
      Right (LeafArrayType u8Type 3)

  -- {integer} against {float}

  test "an expected integer literal variable against an actual float literal variable is a type mismatch" $
    resultFromEmptyState (do
      freshTypeVariables [IntegerLiteralDomain, FloatLiteralDomain]
      mergeTypeVariables inferenceTestSpan 0 1) `shouldBe`
      Left (typeMismatchMessage i32Type f64Type)

  test "an expected float literal variable against an actual integer literal variable is a type mismatch" $
    resultFromEmptyState (do
      freshTypeVariables [IntegerLiteralDomain, FloatLiteralDomain]
      mergeTypeVariables inferenceTestSpan 1 0) `shouldBe`
      Left (typeMismatchMessage f64Type i32Type)

  test "a general variable merged with an integer literal variable clashes with a float literal variable" $
    resultFromEmptyState (do
      freshTypeVariables [AnyTypeDomain, IntegerLiteralDomain, FloatLiteralDomain]
      mergeTypeVariables inferenceTestSpan 0 1
      mergeTypeVariables inferenceTestSpan 0 2) `shouldBe`
      Left (typeMismatchMessage i32Type f64Type)

  -- Merging by rank

  test "of two roots with equal ranks, the second goes under the first, whose rank grows by one" $
    variableStatesFromEmptyState (do
      freshTypeVariables [AnyTypeDomain, AnyTypeDomain]
      mergeTypeVariables inferenceTestSpan 0 1) `shouldBe`
      Right [(0, "open general, rank 1"), (1, "parent 0")]

  test "a lower-ranked root goes under a higher-ranked root, whose rank stays the same" $
    variableStatesFromEmptyState (do
      freshTypeVariables [AnyTypeDomain, AnyTypeDomain, AnyTypeDomain]
      mergeTypeVariables inferenceTestSpan 0 1
      mergeTypeVariables inferenceTestSpan 2 0) `shouldBe`
      Right [(0, "open general, rank 1"), (1, "parent 0"), (2, "parent 0")]

  test "merging through non-root variables merges their roots" $
    variableStatesFromEmptyState (do
      freshTypeVariables [AnyTypeDomain, AnyTypeDomain, AnyTypeDomain, AnyTypeDomain]
      mergeTypeVariables inferenceTestSpan 0 1
      mergeTypeVariables inferenceTestSpan 2 3
      mergeTypeVariables inferenceTestSpan 1 3) `shouldBe`
      Right [(0, "open general, rank 2"), (1, "parent 0"), (2, "parent 0"), (3, "parent 2")]

  test "the root lookup returns the root and points every visited variable directly at it" $
    resultFromEmptyState (do
      put (stateWithVariables [(0, OpenTypeVariable AnyTypeDomain 2), (1, ParentReference 0), (2, ParentReference 1), (3, ParentReference 2)])
      (rootId, _) <- findInferenceVariableRootAndShortenPath 3
      finalState <- get
      pure (rootId, map (\(variableId, variableState) => (variableId, describeVariableState variableState))
                        (Data.SortedMap.toList finalState.inferenceVariables))) `shouldBe`
      Right (0, [(0, "open general, rank 2"), (1, "parent 0"), (2, "parent 0"), (3, "parent 0")])

  -- Merged quantum usage variables

  test "merging two quantum usage variables puts the second under the first" $
    variableStatesFromEmptyState (do
      _ <- freshQuantumUsageVariable
      _ <- freshQuantumUsageVariable
      mergeQuantumUsageVariables 0 1) `shouldBe`
      Right [(0, "open quantum usage, rank 1"), (1, "parent 0")]

  test "a merged quantum usage variable resolves to the root of its group" $
    resultFromEmptyState (do
      _ <- freshQuantumUsageVariable
      _ <- freshQuantumUsageVariable
      mergeQuantumUsageVariables 0 1
      resolvedQuantumUsage <- resolveQuantumUsageThroughParentReferences (UnknownQuantumUsage 1)
      pure (case resolvedQuantumUsage of
              UnknownQuantumUsage rootId => Just rootId
              KnownQuantumUsage _ => Nothing)) `shouldBe`
      Right (Just 0)

  test "merged quantum usage variables default together to linear" $
    resultFromEmptyState (do
      _ <- freshQuantumUsageVariable
      _ <- freshQuantumUsageVariable
      mergeQuantumUsageVariables 0 1
      _ <- defaultOpenVariables
      traverse tcTypeToLeafType
        [ TcQuantumQualifiedType (UnknownQuantumUsage 0) (TcPrimitiveType TypPrimQbit)
        , TcQuantumQualifiedType (UnknownQuantumUsage 1) (TcPrimitiveType TypPrimQbit)
        ]) `shouldBe`
      Right [ LeafQuantumQualifiedType QuantumUsageLinear (LeafPrimitiveType TypPrimQbit)
            , LeafQuantumQualifiedType QuantumUsageLinear (LeafPrimitiveType TypPrimQbit)
            ]

  -- Defaulting

  test "defaulting fixes integer literal variables to i32 and float literal variables to f64" $
    resultFromEmptyState (do
      freshTypeVariables [IntegerLiteralDomain, FloatLiteralDomain]
      openGeneralVariableId <- defaultOpenVariables
      defaultedType <- tcTypeToLeafType (TcTupleType (TcVariable 0 ::: [TcVariable 1]))
      pure (openGeneralVariableId, defaultedType)) `shouldBe`
      Right (Nothing, LeafTupleType (i32Type ::: [f64Type]))

  test "defaulting fixes a root once, and the variables under it resolve to the same default" $
    resultFromEmptyState (do
      freshTypeVariables [FloatLiteralDomain, AnyTypeDomain]
      mergeTypeVariables inferenceTestSpan 0 1
      _ <- defaultOpenVariables
      tcTypeToLeafType (TcVariable 1)) `shouldBe`
      Right f64Type

  test "defaulting leaves general variables open and returns the lowest-numbered one" $
    resultFromEmptyState (do
      freshTypeVariables [IntegerLiteralDomain, AnyTypeDomain, FloatLiteralDomain, AnyTypeDomain]
      defaultOpenVariables) `shouldBe`
      Right (Just 1)

  test "defaulting leaves the states of general variables unchanged" $
    variableStatesFromEmptyState (do
      freshTypeVariables [IntegerLiteralDomain, AnyTypeDomain]
      _ <- freshQuantumUsageVariable
      defaultOpenVariables) `shouldBe`
      Right [(0, "fixed type"), (1, "open general, rank 0"), (2, "fixed quantum usage linear")]

  -- The occurs check

  test "a variable inside its own array type is an infinite type" $
    resultFromEmptyState (do
      freshTypeVariables [AnyTypeDomain]
      checkVariableDoesNotOccurInType inferenceTestSpan 0 (TcArrayType (TcVariable 0) 2)) `shouldBe`
      Left (show (CannotInferType inferenceTestSpan))

  test "a variable inside its own function type is an infinite type" $
    resultFromEmptyState (do
      freshTypeVariables [AnyTypeDomain]
      checkVariableDoesNotOccurInType inferenceTestSpan 0 (TcFunctionType EffectClassical [] [TcVariable 0] TcUnitType)) `shouldBe`
      Left (show (CannotInferType inferenceTestSpan))

  test "the occurs check finds a variable merged with the one being fixed" $
    resultFromEmptyState (do
      freshTypeVariables [AnyTypeDomain, AnyTypeDomain]
      mergeTypeVariables inferenceTestSpan 0 1
      checkVariableDoesNotOccurInType inferenceTestSpan 0 (TcTupleType (TcUnitType ::: [TcVariable 1]))) `shouldBe`
      Left (show (CannotInferType inferenceTestSpan))

  test "the occurs check accepts a type that contains another variable" $
    resultFromEmptyState (do
      freshTypeVariables [AnyTypeDomain, AnyTypeDomain]
      checkVariableDoesNotOccurInType inferenceTestSpan 0 (TcArrayType (TcVariable 1) 2)) `shouldBe`
      Right ()

  test "the occurs check accepts the variable itself" $
    resultFromEmptyState (do
      freshTypeVariables [AnyTypeDomain]
      checkVariableDoesNotOccurInType inferenceTestSpan 0 (TcVariable 0)) `shouldBe`
      Right ()
