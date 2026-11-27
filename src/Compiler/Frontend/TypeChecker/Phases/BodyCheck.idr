module Compiler.Frontend.TypeChecker.Phases.BodyCheck

import Compiler.Helper
import Data.List1
import Data.Maybe
import Data.SortedMap
import Data.SortedSet

import Control.Monad.State
import Compiler.Frontend.ScopeAndNameResolver.Data
import Compiler.Frontend.TypeChecker.Data
import Compiler.Frontend.TypeChecker.Helper
import Compiler.Frontend.TypeChecker.Numeric
import Compiler.Frontend.TypeChecker.Phases.ConstEval
import Compiler.Frontend.TypeChecker.State
import Compiler.Frontend.TypeChecker.Type
import Compiler.Frontend.ASTData
import Compiler.Frontend.ASTPhases
import Compiler.Frontend.Source
import Compiler.Frontend.TypeChecker.TcType
import Compiler.Frontend.Syntax.Attribute
import Compiler.Frontend.Syntax.AST
import Compiler.Frontend.Syntax.Contract
import Compiler.Frontend.Syntax.Common
import Compiler.Frontend.Syntax.Doc
import Compiler.Frontend.Syntax.Literal
import Compiler.Frontend.Syntax.Name
import Compiler.Frontend.Syntax.Operator
import Compiler.Frontend.Syntax.Pattern
import Compiler.Frontend.Syntax.Type
import Compiler.Frontend.Token

%default total

export
evalConstExprNat : Expr ResolvedAstPhase -> StateT TypeCheckerState (Either CheckFailure) Nat
evalConstExprNat (MkAstNode astInfo metadata expressionNode) =
  case expressionNode of
    ExprLiteral (MkAstNode literalAstInfo literalMetadata literalNode) =>
      case literalNode of
        LiteralIntegerRaw raw =>
          case integerLiteralValue raw of
            Nothing => unreachable __FILE__ {function = "evalConstExprNat"} {reason = "the lexer accepted a malformed integer literal: " ++ raw}
            Just _ =>
              case arrayLengthProblem raw of
                Just (NonUsizeLengthSuffix suffixType) => liftTypeError (IncorrectArrayLengthType (LeafPrimitiveType suffixType) astInfo.span)
                _ =>
                  case inferIntegerLiteral (Just TypPrimUsize) raw astInfo.span of
                    Left typeError => liftTypeError typeError
                    Right (primitive, value) =>
                      case checkArrayLength (LeafPrimitiveType primitive) value astInfo.span of
                        Left typeError => liftTypeError typeError
                        Right count => pure count
        LiteralFloatRaw rawLiteralText =>
          let floatLiteralType = fromMaybe TypPrimF64 (floatLiteralSuffixType rawLiteralText)
          in liftTypeError (IncorrectArrayLengthType (LeafPrimitiveType floatLiteralType) astInfo.span)
        LiteralStringRaw rawSpelling => liftTypeError (UnsupportedFeature "string literal" literalAstInfo.span)
        LiteralByteRaw rawSpelling => notImplemented __FILE__ {function = "evalConstExprNat"} {feature = "byte literals"}
        LiteralByteStringRaw rawSpelling => notImplemented __FILE__ {function = "evalConstExprNat"} {feature = "byte string literals"}
        LiteralBasisStringRaw rawSpelling => liftTypeError (UnsupportedFeature "basis-string value" literalAstInfo.span)
        LiteralBoolean value => liftTypeError (IncorrectArrayLengthType (LeafPrimitiveType TypPrimBool) astInfo.span)
        LiteralUnit => liftTypeError (IncorrectArrayLengthType LeafUnitType astInfo.span)
        LiteralQuantumState basisStateName => notImplemented __FILE__ {function = "evalConstExprNat"} {feature = "quantum state literals"}
    ExprName name => notImplemented __FILE__ {function = "evalConstExprNat"} {feature = "names in constant expressions"}
    ExprPath path => notImplemented __FILE__ {function = "evalConstExprNat"} {feature = "paths in constant expressions"}
    ExprBuiltin builtin =>
      case builtin of
        BuiltinBarrier => ?evalConstExprNatBuiltinBarrierHole
        BuiltinCtrl => ?evalConstExprNatBuiltinCtrlHole
        BuiltinOn => ?evalConstExprNatBuiltinOnHole
        BuiltinApply => ?evalConstExprNatBuiltinApplyHole
        BuiltinBasis => ?evalConstExprNatBuiltinBasisHole
        BuiltinClean => ?evalConstExprNatBuiltinCleanHole
        BuiltinDiscard => ?evalConstExprNatBuiltinDiscardHole
        BuiltinIsolated => ?evalConstExprNatBuiltinIsolatedHole
        BuiltinLen => ?evalConstExprNatBuiltinLenHole
        BuiltinMeasr => ?evalConstExprNatBuiltinMeasrHole
        BuiltinProduct => ?evalConstExprNatBuiltinProductHole
        BuiltinQAlloc => ?evalConstExprNatBuiltinQAllocHole
        BuiltinReset => ?evalConstExprNatBuiltinResetHole
        BuiltinRev => ?evalConstExprNatBuiltinRevHole
        BuiltinTensor => ?evalConstExprNatBuiltinTensorHole
        BuiltinSeparable => ?evalConstExprNatBuiltinSeparableHole
        BuiltinStabilized => ?evalConstExprNatBuiltinStabilizedHole
        BuiltinUncompute => ?evalConstExprNatBuiltinUncomputeHole
        BuiltinWeaken => ?evalConstExprNatBuiltinWeakenHole
    ExprSelf selfReceiver => notImplemented __FILE__ {function = "evalConstExprNat"} {feature = "self in constant expressions"}
    ExprParenthesized inner => unreachable __FILE__ {function = "evalConstExprNat"} {reason = "parenthesized expressions should have been removed during the desugaring phase"}
    ExprTuple elements => ?evalConstExprNatTupleHole
    ExprArray elements => ?evalConstExprNatArrayHole
    ExprRepeatedArray element count => ?evalConstExprNatRepeatedArrayHole
    ExprStructLiteral path fields => notImplemented __FILE__ {function = "evalConstExprNat"} {feature = "struct literals in constant expressions"}
    ExprCall callee arguments => ?evalConstExprNatCallHole
    ExprMethodCall receiver name arguments => notImplemented __FILE__ {function = "evalConstExprNat"} {feature = "method calls in constant expressions"}
    ExprField object name => notImplemented __FILE__ {function = "evalConstExprNat"} {feature = "field access in constant expressions"}
    ExprTupleIndex tuple indexText => ?evalConstExprNatTupleIndexHole
    ExprIndex object index => ?evalConstExprNatIndexHole
    ExprUnary operator operand => ?evalConstExprNatUnaryHole
    ExprBinary operator left right => ?evalConstExprNatBinaryHole
    ExprRange start operator end => ?evalConstExprNatRangeHole
    ExprCast operand target => ?evalConstExprNatCastHole
    ExprBlock block => ?evalConstExprNatBlockHole
    ExprIf ifNode => ?evalConstExprNatIfHole
    ExprQIf ifNode => notImplemented __FILE__ {function = "evalConstExprNat"} {feature = "qif in constant expressions"}
    ExprSIf ifNode => notImplemented __FILE__ {function = "evalConstExprNat"} {feature = "sif in constant expressions"}
    ExprMatch matchNode => notImplemented __FILE__ {function = "evalConstExprNat"} {feature = "match in constant expressions"}
    ExprQMatch matchNode => notImplemented __FILE__ {function = "evalConstExprNat"} {feature = "qmatch in constant expressions"}
    ExprSMatch matchNode => notImplemented __FILE__ {function = "evalConstExprNat"} {feature = "smatch in constant expressions"}
    ExprLoop body => ?evalConstExprNatLoopHole
    ExprWhile condition body => ?evalConstExprNatWhileHole
    ExprFor pattern iterator body => ?evalConstExprNatForHole
    ExprBreak value => ?evalConstExprNatBreakHole
    ExprContinue => ?evalConstExprNatContinueHole
    ExprReturn value => ?evalConstExprNatReturnHole
    ExprCtrl control => ?evalConstExprNatCtrlHole
    ExprAdjoint adjoint => ?evalConstExprNatAdjointHole

||| A slice type [T] has no length known at compile time, so it can't be a parameter, result or constant type on its own. 
||| A reference to a slice, &[T], is fine, a slice reference carries both a pointer to its first element and its length.
export
checkWrittenTypeIsSizedAndSupported : ResolvedTy -> StateT TypeCheckerState (Either CheckFailure) ()
checkWrittenTypeIsSizedAndSupported = walk False
  where
    walk : (unsizedAllowed : Bool) -> ResolvedTy -> StateT TypeCheckerState (Either CheckFailure) ()
    walk unsizedAllowed typeAstNode@(MkAstNode astInfo metadata typeNode) =
      case typeNode of
        TyPrimitive primitiveName => pure ()
        TyPath typePath => notImplemented __FILE__ {function = "checkWrittenTypeIsSizedAndSupported"} {feature = "structs, enums or qenums"}
        TyUnit => pure ()
        TyParenthesized innerType => unreachable __FILE__ {function = "checkWrittenTypeIsSizedAndSupported"} {reason = "parenthesized types should have been removed during the desugaring phase."}
        TyTuple elementTypes => traverse_ (\element => walk False (assert_smaller typeNode element)) elementTypes
        TyArray elementType sizeExpression => walk False (assert_smaller typeNode elementType)
        TySlice elementType =>
          if unsizedAllowed
            then walk False (assert_smaller typeNode elementType)
            else do
              leafType <- writtenLeafTypeM evalConstExprNat typeAstNode
              liftTypeError (UnsizedValue leafType astInfo.span)
        TyReference borrowKind referencedType => walk True (assert_smaller typeNode referencedType)
        TyQualified (MkAstNode qualifierInfo _ quantumUsageQualifier) qualifiedType =>
          case quantumUsageQualifier of
            QuantumUsageAffine => liftTypeError (UnsupportedFeature "affine" qualifierInfo.span)
            QuantumUsageLinear => walk unsizedAllowed (assert_smaller typeNode qualifiedType)
        TyFunction functionEffect functionParameters returnType => do
          traverse_ (\parameter => walk False (assert_smaller typeNode parameter.nodeValue.parameterType)) functionParameters
          traverse_ (\result => walk False (assert_smaller typeNode result)) returnType

isPreludeParamFunction : ResolvedExpr -> StateT TypeCheckerState (Either CheckFailure) Bool
isPreludeParamFunction (MkAstNode calleeInfo calleeMetadata (ExprName (MkAstNode nameInfo nameMetadata calleeName))) = do
  checkerState <- get
  case lookup calleeName.nameNodeSymbolId checkerState.typeTables.symbols of
    Just symbolInfo =>
      case symbolInfo.origin of
        PreludeSymbol => pure (symbolInfo.declaredName == "Param")
        _ => pure False
    Nothing => pure False
isPreludeParamFunction _ = pure False

typeIsInVariableDomain : TcType -> TypeVariableDomain -> Bool
typeIsInVariableDomain _ AnyTypeDomain = True
typeIsInVariableDomain (TcPrimitiveType primitiveName) IntegerLiteralDomain =
  isJust (integerBitWidth primitiveName) || primitiveName == TypPrimBit
typeIsInVariableDomain (TcPrimitiveType primitiveName) FloatLiteralDomain =
  primitiveName `elem` [TypPrimF32, TypPrimF64, TypPrimAngle32, TypPrimAngle64]
typeIsInVariableDomain _ _ = False

supportKindListsAreEqualAsSets : List SupportKind -> List SupportKind -> Bool
supportKindListsAreEqualAsSets firstSupportKinds secondSupportKinds =
  all (`elem` secondSupportKinds) firstSupportKinds && all (`elem` firstSupportKinds) secondSupportKinds

resolvedTcTypeToDiagnosticLeafType : SortedMap Nat InferenceVariableState -> TcType -> Maybe LeafType
resolvedTcTypeToDiagnosticLeafType inferenceVariables tcType =
  case tcType of
    TcPrimitiveType primitiveName => Just (LeafPrimitiveType primitiveName)
    TcNamedType symbolId => Just (LeafNamedType symbolId)
    TcUnitType => Just LeafUnitType
    TcTupleType elementTypes => LeafTupleType <$> traverse recur elementTypes
    TcArrayType elementType arrayLength => (\elementLeafType => LeafArrayType elementLeafType arrayLength) <$> recur elementType
    TcSliceType elementType => LeafSliceType <$> recur elementType
    TcRangeType rangeShape elementType => LeafRangeType rangeShape <$> recur elementType
    TcReferenceType borrowKind referencedType => LeafReferenceType borrowKind <$> recur referencedType
    TcFunctionType functionEffect supportKinds parameterTypes resultType =>
      LeafFunctionType functionEffect supportKinds <$> traverse recur parameterTypes <*> recur resultType
    TcQuantumQualifiedType (KnownQuantumUsage quantumUsageQualifier) qualifiedType =>
      LeafQuantumQualifiedType quantumUsageQualifier <$> recur qualifiedType
    TcQuantumQualifiedType (UnknownQuantumUsage _) qualifiedType =>
      LeafQuantumQualifiedType QuantumUsageLinear <$> recur qualifiedType
    TcNeverType => Just LeafNeverType
    TcStringLiteralType => Just LeafStringLiteralType
    TcVariable rootId =>
      case lookup rootId inferenceVariables of
        Just (OpenTypeVariable IntegerLiteralDomain _) => Just (LeafPrimitiveType TypPrimI32)
        Just (OpenTypeVariable FloatLiteralDomain _) => Just (LeafPrimitiveType TypPrimF64)
        Just (OpenTypeVariable AnyTypeDomain _) => Nothing
        _ =>
          unreachable __FILE__
            {function = "resolvedTcTypeToDiagnosticLeafType"}
            {reason = "type variable " ++ show rootId ++ " is not an open root after resolution"}
  where
    recur : TcType -> Maybe LeafType
    recur componentType = resolvedTcTypeToDiagnosticLeafType inferenceVariables (assert_smaller tcType componentType)

reportTypeMismatch : SourceSpan -> (expected : TcType) -> (actual : TcType) -> StateT TypeCheckerState (Either CheckFailure) a
reportTypeMismatch sourceSpan expectedType actualType = do
  resolvedExpectedType <- liftInferenceOperation (resolveTcTypeThroughParentReferences expectedType)
  resolvedActualType <- liftInferenceOperation (resolveTcTypeThroughParentReferences actualType)
  checkerState <- get
  let inferenceVariables = checkerState.inferenceState.inferenceVariables
  case (resolvedTcTypeToDiagnosticLeafType inferenceVariables resolvedExpectedType,
        resolvedTcTypeToDiagnosticLeafType inferenceVariables resolvedActualType) of
    (Just expectedLeafType, Just actualLeafType) => liftTypeError (TypeMismatch expectedLeafType actualLeafType sourceSpan)
    _ => liftTypeError (CannotInferType sourceSpan)

unifyQuantumUsagesAndReturnWhetherTheyMatch : (expected : TcQuantumUsage) -> (actual : TcQuantumUsage) -> StateT TypeCheckerState (Either CheckFailure) Bool
unifyQuantumUsagesAndReturnWhetherTheyMatch expectedQuantumUsage actualQuantumUsage =
  case (expectedQuantumUsage, actualQuantumUsage) of
    (KnownQuantumUsage expectedQualifier, KnownQuantumUsage actualQualifier) =>
      pure (expectedQualifier == actualQualifier)
    (UnknownQuantumUsage expectedRootId, KnownQuantumUsage actualQualifier) => do
      liftInferenceOperation (recordInferenceVariableState expectedRootId (FixedQuantumUsage actualQualifier))
      pure True
    (KnownQuantumUsage expectedQualifier, UnknownQuantumUsage actualRootId) => do
      liftInferenceOperation (recordInferenceVariableState actualRootId (FixedQuantumUsage expectedQualifier))
      pure True
    (UnknownQuantumUsage expectedRootId, UnknownQuantumUsage actualRootId) => do
      liftInferenceOperation (mergeQuantumUsageVariables expectedRootId actualRootId)
      pure True

unifyAndReturnWhetherTypesMatch : SourceSpan -> (expected : TcType) -> (actual : TcType) -> StateT TypeCheckerState (Either CheckFailure) Bool
unifyAndReturnWhetherTypesMatch sourceSpan expectedType actualType = do
  resolvedExpectedType <- liftInferenceOperation (resolveTcTypeThroughParentReferences expectedType)
  resolvedActualType <- liftInferenceOperation (resolveTcTypeThroughParentReferences actualType)
  case (resolvedExpectedType, resolvedActualType) of
    (TcVariable expectedRootId, TcVariable actualRootId) =>
      mergeTypeVariablesUnlessLiteralDomainsClash expectedRootId actualRootId
    (TcVariable expectedRootId, _) => fixTypeVariableIfTypeIsInItsDomain expectedRootId resolvedActualType
    (_, TcVariable actualRootId) => fixTypeVariableIfTypeIsInItsDomain actualRootId resolvedExpectedType
    (TcPrimitiveType expectedPrimitive, TcPrimitiveType actualPrimitive) => pure (expectedPrimitive == actualPrimitive)
    (TcNamedType expectedSymbolId, TcNamedType actualSymbolId) => pure (expectedSymbolId == actualSymbolId)
    (TcUnitType, TcUnitType) => pure True
    (TcTupleType expectedElementTypes, TcTupleType actualElementTypes) =>
      unifyComponentLists (forget expectedElementTypes) (forget actualElementTypes)
    (TcArrayType expectedElementType expectedLength, TcArrayType actualElementType actualLength) =>
      if expectedLength == actualLength
        then unifyComponents expectedElementType actualElementType
        else pure False
    (TcSliceType expectedElementType, TcSliceType actualElementType) =>
      unifyComponents expectedElementType actualElementType
    (TcRangeType expectedRangeShape expectedElementType, TcRangeType actualRangeShape actualElementType) =>
      if expectedRangeShape == actualRangeShape
        then unifyComponents expectedElementType actualElementType
        else pure False
    (TcReferenceType expectedBorrowKind expectedReferencedType, TcReferenceType actualBorrowKind actualReferencedType) =>
      if expectedBorrowKind == actualBorrowKind
        then unifyComponents expectedReferencedType actualReferencedType
        else pure False
    (TcFunctionType expectedEffect expectedSupportKinds expectedParameterTypes expectedResultType,
     TcFunctionType actualEffect actualSupportKinds actualParameterTypes actualResultType) =>
      if expectedEffect == actualEffect && supportKindListsAreEqualAsSets expectedSupportKinds actualSupportKinds
        then do
          parameterTypesMatch <- unifyComponentLists expectedParameterTypes actualParameterTypes
          if parameterTypesMatch
            then unifyComponents expectedResultType actualResultType
            else pure False
        else pure False
    (TcQuantumQualifiedType expectedQuantumUsage expectedQualifiedType, TcQuantumQualifiedType actualQuantumUsage actualQualifiedType) => do
      quantumUsagesMatch <- unifyQuantumUsagesAndReturnWhetherTheyMatch expectedQuantumUsage actualQuantumUsage
      if quantumUsagesMatch
        then unifyComponents expectedQualifiedType actualQualifiedType
        else pure False
    (TcNeverType, TcNeverType) => pure True
    (TcStringLiteralType, TcStringLiteralType) => pure True
    _ => pure False
  where
    unifyComponents : (expectedComponent : TcType) -> (actualComponent : TcType) -> StateT TypeCheckerState (Either CheckFailure) Bool
    unifyComponents expectedComponent actualComponent =
      unifyAndReturnWhetherTypesMatch sourceSpan
        (assert_smaller expectedType expectedComponent)
        (assert_smaller actualType actualComponent)

    -- Lists of different lengths never match: the tuple arity or the parameter count differs.
    unifyComponentLists : (expectedComponents : List TcType) -> (actualComponents : List TcType) -> StateT TypeCheckerState (Either CheckFailure) Bool
    unifyComponentLists [] [] = pure True
    unifyComponentLists (expectedComponent :: remainingExpectedComponents) (actualComponent :: remainingActualComponents) = do
      componentsMatch <- unifyComponents expectedComponent actualComponent
      if componentsMatch
        then unifyComponentLists remainingExpectedComponents remainingActualComponents
        else pure False
    unifyComponentLists _ _ = pure False

    -- An {integer} and a {float} variable share no type. Checking it here, rather than
    -- letting mergeTypeVariables report it, keeps the report on the whole types.
    mergeTypeVariablesUnlessLiteralDomainsClash : (expectedRootId : Nat) -> (actualRootId : Nat) -> StateT TypeCheckerState (Either CheckFailure) Bool
    mergeTypeVariablesUnlessLiteralDomainsClash expectedRootId actualRootId = do
      (_, expectedRootState) <- liftInferenceOperation (findInferenceVariableRootAndShortenPath expectedRootId)
      (_, actualRootState) <- liftInferenceOperation (findInferenceVariableRootAndShortenPath actualRootId)
      case (expectedRootState, actualRootState) of
        (OpenTypeVariable IntegerLiteralDomain _, OpenTypeVariable FloatLiteralDomain _) => pure False
        (OpenTypeVariable FloatLiteralDomain _, OpenTypeVariable IntegerLiteralDomain _) => pure False
        _ => do
          liftInferenceOperation (mergeTypeVariables sourceSpan expectedRootId actualRootId)
          pure True

    -- The occurs check runs before the root is fixed, so no variable stands for an infinite type.
    fixTypeVariableIfTypeIsInItsDomain : (rootId : Nat) -> (candidateType : TcType) -> StateT TypeCheckerState (Either CheckFailure) Bool
    fixTypeVariableIfTypeIsInItsDomain rootId candidateType = do
      (_, rootState) <- liftInferenceOperation (findInferenceVariableRootAndShortenPath rootId)
      case rootState of
        OpenTypeVariable variableDomain _ =>
          if typeIsInVariableDomain candidateType variableDomain
            then do
              liftInferenceOperation (checkVariableDoesNotOccurInType sourceSpan rootId candidateType)
              liftInferenceOperation (recordInferenceVariableState rootId (FixedTypeVariable candidateType))
              pure True
            else pure False
        _ =>
          unreachable __FILE__
            {function = "unifyAndReturnWhetherTypesMatch"}
            {reason = "type variable " ++ show rootId ++ " is not an open root after resolution"}

export
unify : SourceSpan -> (expected : TcType) -> (actual : TcType) -> StateT TypeCheckerState (Either CheckFailure) ()
unify sourceSpan expectedType actualType = do
  typesMatch <- unifyAndReturnWhetherTypesMatch sourceSpan expectedType actualType
  unless typesMatch $ reportTypeMismatch sourceSpan expectedType actualType

isAssignableTo : SourceSpan -> (actual : TcType) -> (expected : TcType) -> StateT TypeCheckerState (Either CheckFailure) ()
isAssignableTo sourceSpan actualType expectedType = do
  let resolveAssignedValueType = resolveTcTypeThroughParentReferences actualType
  let resolveExpectedType = resolveTcTypeThroughParentReferences expectedType
  resolvedAssignedValueType <- liftInferenceOperation resolveAssignedValueType
  resolvedExpectedType <- liftInferenceOperation resolveExpectedType
  case (resolvedAssignedValueType, resolvedExpectedType) of
    (TcNeverType, _) => pure ()
    (TcFunctionType actualEffect actualSupportKinds actualParameterTypes actualResultType,
     TcFunctionType expectedEffect expectedSupportKinds expectedParameterTypes expectedResultType) => do
      let providesEveryRequiredSupportKind = all (`elem` actualSupportKinds) expectedSupportKinds
      if isEffectAtMost actualEffect expectedEffect && providesEveryRequiredSupportKind
        then do
          -- The effect and support kinds fit, so only the parameter and result types are left to compare
          parameterAndResultTypesMatch <-
            unifyAndReturnWhetherTypesMatch sourceSpan
              resolvedExpectedType
              (TcFunctionType expectedEffect expectedSupportKinds actualParameterTypes actualResultType)
          unless parameterAndResultTypesMatch $ reportTypeMismatch sourceSpan expectedType actualType
        else reportTypeMismatch sourceSpan expectedType actualType
    _ => unify sourceSpan expectedType actualType

joinTypesAndReturnNothingIfIncompatible : SourceSpan -> (firstAlternative : TcType) -> (secondAlternative : TcType) -> StateT TypeCheckerState (Either CheckFailure) (Maybe TcType)
joinTypesAndReturnNothingIfIncompatible sourceSpan firstAlternativeType secondAlternativeType = do
  resolvedFirstAlternativeType <- liftInferenceOperation (resolveTcTypeThroughParentReferences firstAlternativeType)
  resolvedSecondAlternativeType <- liftInferenceOperation (resolveTcTypeThroughParentReferences secondAlternativeType)
  case (resolvedFirstAlternativeType, resolvedSecondAlternativeType) of
    (TcNeverType, _) => pure (Just resolvedSecondAlternativeType)
    (_, TcNeverType) => pure (Just resolvedFirstAlternativeType)
    (TcTupleType (firstHeadType ::: firstTailTypes), TcTupleType (secondHeadType ::: secondTailTypes)) => do
      joinedHeadType <- joinComponents firstHeadType secondHeadType
      joinedTailTypes <- joinComponentLists firstTailTypes secondTailTypes
      pure (TcTupleType <$> ((:::) <$> joinedHeadType <*> joinedTailTypes))
    (TcArrayType firstElementType firstLength, TcArrayType secondElementType secondLength) =>
      if firstLength == secondLength
        then map (\joinedElementType => TcArrayType joinedElementType firstLength) <$> joinComponents firstElementType secondElementType
        else pure Nothing
    (TcFunctionType firstEffect firstSupportKinds firstParameterTypes firstResultType,
     TcFunctionType secondEffect secondSupportKinds secondParameterTypes secondResultType) => do
      -- Parameter and result types stay invariant: unify them by giving the second
      -- function the first one's effect and support kinds, which are joined separately.
      parameterAndResultTypesMatch <-
        unifyAndReturnWhetherTypesMatch sourceSpan
          resolvedFirstAlternativeType
          (TcFunctionType firstEffect firstSupportKinds secondParameterTypes secondResultType)
      let supportKindsOfBothFunctions = filter (`elem` secondSupportKinds) firstSupportKinds
      pure $ if parameterAndResultTypesMatch
        then Just (TcFunctionType (joinEffects firstEffect secondEffect) supportKindsOfBothFunctions firstParameterTypes firstResultType)
        else Nothing
    _ => do
      alternativesMatch <- unifyAndReturnWhetherTypesMatch sourceSpan resolvedFirstAlternativeType resolvedSecondAlternativeType
      pure $ if alternativesMatch then Just resolvedFirstAlternativeType else Nothing
  where
    joinComponents : (firstComponent : TcType) -> (secondComponent : TcType) -> StateT TypeCheckerState (Either CheckFailure) (Maybe TcType)
    joinComponents firstComponent secondComponent =
      joinTypesAndReturnNothingIfIncompatible sourceSpan
        (assert_smaller firstAlternativeType firstComponent)
        (assert_smaller secondAlternativeType secondComponent)

    -- Lists of different lengths never join: the tuple arity differs.
    joinComponentLists : (firstComponents : List TcType) -> (secondComponents : List TcType) -> StateT TypeCheckerState (Either CheckFailure) (Maybe (List TcType))
    joinComponentLists [] [] = pure (Just [])
    joinComponentLists (firstComponent :: remainingFirstComponents) (secondComponent :: remainingSecondComponents) = do
      joinedComponent <- joinComponents firstComponent secondComponent
      case joinedComponent of
        Nothing => pure Nothing
        Just joinedComponentType => map (joinedComponentType ::) <$> joinComponentLists remainingFirstComponents remainingSecondComponents
    joinComponentLists _ _ = pure Nothing

joinTypes : SourceSpan -> TcType -> TcType -> StateT TypeCheckerState (Either CheckFailure) TcType
joinTypes sourceSpan firstAlternativeType secondAlternativeType = do
  joinedType <- joinTypesAndReturnNothingIfIncompatible sourceSpan firstAlternativeType secondAlternativeType
  case joinedType of
    Just commonType => pure commonType
    Nothing => reportTypeMismatch sourceSpan firstAlternativeType secondAlternativeType

--------------------------------------------------------------------------------
-- Pass B: literals and names
--------------------------------------------------------------------------------

||| The primitive an expected type resolves to, which checking mode passes to a literal.
resolvedExpectedPrimitive : (expected : TcType) -> StateT TypeCheckerState (Either CheckFailure) (Maybe TypPrimName)
resolvedExpectedPrimitive expectedType = do
  resolvedExpectedType <- liftInferenceOperation (resolveTcTypeThroughParentReferences expectedType)
  pure $ case resolvedExpectedType of
    TcPrimitiveType primitiveName => Just primitiveName
    _ => Nothing

||| Types an integer literal, negated as a whole when it is the direct operand of a
||| unary minus; the AstInfo is that of the literal or of the negation. A suffixed
||| literal, or one whose expected primitive is known, is typed and range-checked at
||| once; against a non-integer expected primitive this is TypeMismatch expected i32.
||| Any other literal gets a fresh {integer} variable and is range-checked at writeback.
typeIntegerLiteral : (isNegated : Bool) -> AstInfo -> (rawLiteralText : String) -> (expectedPrimitive : Maybe TypPrimName) -> StateT TypeCheckerState (Either CheckFailure) TcType
typeIntegerLiteral isNegated literalInfo rawLiteralText expectedPrimitive =
  case (expectedPrimitive, integerLiteralSuffixType rawLiteralText) of
    (Nothing, Nothing) =>
      case integerLiteralValue rawLiteralText of
        Nothing => unreachable __FILE__ {function = "typeIntegerLiteral"} {reason = "the lexer accepted a malformed integer literal: " ++ rawLiteralText}
        Just literalMagnitude => do
          let literalValue = if isNegated then negate (cast literalMagnitude) else cast literalMagnitude
          literalVariable <- liftInferenceOperation (freshTypeVariable literalInfo.span IntegerLiteralDomain)
          recordIntegerLiteral literalInfo.span literalInfo.nodeId literalValue
          pure literalVariable
    _ => do
      let literalTypeResult : Either TypeError (TypPrimName, Integer)
          literalTypeResult =
            if isNegated
              then inferNegatedIntegerLiteral expectedPrimitive rawLiteralText literalInfo.span
              else inferIntegerLiteral expectedPrimitive rawLiteralText literalInfo.span
      case literalTypeResult of
        Left typeError => liftTypeError typeError
        Right (literalType, _) => pure (TcPrimitiveType literalType)

||| Types a float literal: its suffix type, else the expected float primitive of
||| checking mode, else a fresh {float} variable.
typeFloatLiteral : (literalSpan : SourceSpan) -> (rawLiteralText : String) -> (expectedPrimitive : Maybe TypPrimName) -> StateT TypeCheckerState (Either CheckFailure) TcType
typeFloatLiteral literalSpan rawLiteralText expectedPrimitive =
  case (floatLiteralSuffixType rawLiteralText, expectedPrimitive) of
    (Just suffixType, _) => pure (TcPrimitiveType suffixType)
    (Nothing, Just primitiveName) =>
      if typeIsInVariableDomain (TcPrimitiveType primitiveName) FloatLiteralDomain
        then pure (TcPrimitiveType primitiveName)
        else liftInferenceOperation (freshTypeVariable literalSpan FloatLiteralDomain)
    (Nothing, Nothing) => liftInferenceOperation (freshTypeVariable literalSpan FloatLiteralDomain)

||| A local of this body has the type its binding recorded; any other symbol has the
||| type pass A recorded. The prelude `phase` and `Param` have no value type: `phase`
||| is excluded, and `Param` is valid only as a direct callee.
inferNameType : (nameSpan : SourceSpan) -> SymbolId -> StateT TypeCheckerState (Either CheckFailure) TcType
inferNameType nameSpan symbolId = do
  checkerState <- get
  case lookup symbolId checkerState.typeTables.symbols of
    Nothing => unreachable __FILE__ {function = "inferNameType"} {reason = "the resolved name's symbol is not in the symbol table"}
    Just symbolInfo =>
      case symbolInfo.symbolKind of
        SymbolLocalBinding =>
          case lookup symbolId checkerState.inferenceState.binderTypes of
            Just binderType => pure binderType
            Nothing => unreachable __FILE__ {function = "inferNameType"} {reason = "the local " ++ symbolInfo.declaredName ++ " is used before its binding recorded a type"}
        _ =>
          case symbolInfo.symbolType of
            ResolvedType leafType => pure (leafTypeToTcType leafType)
            TypeNotYetResolved => blocked symbolId
            NoValueType =>
              case symbolInfo.origin of
                PreludeSymbol =>
                  if symbolInfo.declaredName == "phase"
                    then liftTypeError (UnsupportedFeature "phase" nameSpan)
                    else if symbolInfo.declaredName == "Param"
                      then liftTypeError (InvalidBuiltinContext "Param" nameSpan)
                      else notImplemented __FILE__ {function = "inferNameType"} {feature = "prelude symbol without a value type: " ++ symbolInfo.declaredName}
                _ => notImplemented __FILE__ {function = "inferNameType"} {feature = "modules used as values"}

--------------------------------------------------------------------------------
-- Pass B: expressions
--------------------------------------------------------------------------------

mutual
  ||| Infers an expression's type and records it for the expression's node.
  inferExpression : ResolvedExpr -> StateT TypeCheckerState (Either CheckFailure) TcType
  inferExpression (MkAstNode expressionInfo expressionMetadata expressionNode) = do
    expressionType <- inferExpressionNodeType expressionInfo expressionNode
    recordExpressionType expressionInfo.nodeId expressionType
    pure expressionType

  ||| The type of one expression node; inferExpression records it.
  inferExpressionNodeType : AstInfo -> ExpressionNode ResolvedAstPhase -> StateT TypeCheckerState (Either CheckFailure) TcType
  inferExpressionNodeType expressionInfo expressionNode =
    case expressionNode of
      ExprLiteral (MkAstNode literalInfo literalMetadata literalNode) =>
        case literalNode of
          LiteralIntegerRaw rawLiteralText => typeIntegerLiteral False expressionInfo rawLiteralText Nothing
          LiteralFloatRaw rawLiteralText => typeFloatLiteral expressionInfo.span rawLiteralText Nothing
          -- A direct Param("name") argument is typed in inferPreludeParamCall without
          -- reaching this point, so any string literal here is used in another context.
          LiteralStringRaw rawSpelling => liftTypeError (UnsupportedFeature "string literal" literalInfo.span)
          LiteralByteRaw rawSpelling => notImplemented __FILE__ {function = "inferExpression"} {feature = "byte literals"}
          LiteralByteStringRaw rawSpelling => notImplemented __FILE__ {function = "inferExpression"} {feature = "byte string literals"}
          LiteralBasisStringRaw rawSpelling => liftTypeError (UnsupportedFeature "basis-string value" literalInfo.span)
          LiteralBoolean value => pure (TcPrimitiveType TypPrimBool)
          LiteralUnit => pure TcUnitType
          LiteralQuantumState basisStateName => notImplemented __FILE__ {function = "inferExpression"} {feature = "quantum state literals"}
      ExprName (MkAstNode nameInfo nameMetadata resolvedName) => inferNameType expressionInfo.span resolvedName.nameNodeSymbolId
      ExprPath path => notImplemented __FILE__ {function = "inferExpression"} {feature = "expression paths"}
      ExprBuiltin builtin =>
        case builtin of
          BuiltinBarrier => ?inferExpressionBuiltinBarrierHole
          BuiltinCtrl => ?inferExpressionBuiltinCtrlHole
          BuiltinOn => ?inferExpressionBuiltinOnHole
          BuiltinApply => ?inferExpressionBuiltinApplyHole
          BuiltinBasis => notImplemented __FILE__ {function = "inferExpression"} {feature = "basis builtin function"}
          BuiltinClean => notImplemented __FILE__ {function = "inferExpression"} {feature = "clean builtin function"}
          BuiltinDiscard => ?inferExpressionBuiltinDiscardHole
          BuiltinIsolated => notImplemented __FILE__ {function = "inferExpression"} {feature = "isolated builtin function"}
          BuiltinLen => ?inferExpressionBuiltinLenHole
          BuiltinMeasr => ?inferExpressionBuiltinMeasrHole
          BuiltinProduct => notImplemented __FILE__ {function = "inferExpression"} {feature = "product builtin function"}
          BuiltinQAlloc => ?inferExpressionBuiltinQAllocHole
          BuiltinReset => ?inferExpressionBuiltinResetHole
          BuiltinRev => ?inferExpressionBuiltinRevHole
          BuiltinTensor => notImplemented __FILE__ {function = "inferExpression"} {feature = "tensor builtin function"}
          BuiltinSeparable => notImplemented __FILE__ {function = "inferExpression"} {feature = "separable builtin function"}
          BuiltinStabilized => notImplemented __FILE__ {function = "inferExpression"} {feature = "stabilized builtin function"}
          BuiltinUncompute => notImplemented __FILE__ {function = "inferExpression"} {feature = "uncompute builtin function"}
          BuiltinWeaken => notImplemented __FILE__ {function = "inferExpression"} {feature = "weaken builtin function"}
      ExprSelf selfReceiver => notImplemented __FILE__ {function = "inferExpression"} {feature = "self"}
      ExprParenthesized inner => unreachable __FILE__ {function = "inferExpression"} {reason = "parenthesized expressions should have been removed during the desugaring phase"}
      ExprTuple elements => ?inferExpressionTupleHole
      ExprArray elements => ?inferExpressionArrayHole
      ExprRepeatedArray element count => ?inferExpressionRepeatedArrayHole
      ExprStructLiteral path fields => notImplemented __FILE__ {function = "inferExpression"} {feature = "struct literals"}
      ExprCall callee arguments => do
        calleeIsPreludeParam <- isPreludeParamFunction callee
        if calleeIsPreludeParam
          then inferPreludeParamCall callee arguments
          else ?inferExpressionCallHole
      ExprMethodCall receiver name arguments => ?inferExpressionMethodCallHole
      ExprField object name => ?inferExpressionFieldHole
      ExprTupleIndex tuple indexText => ?inferExpressionTupleIndexHole
      ExprIndex object index => ?inferExpressionIndexHole
      -- A unary minus applied directly to a literal is typed as one negative literal,
      -- and the negation and the literal nodes get the same type.
      ExprUnary operatorNode operand =>
        case (operatorNode.nodeValue, operand) of
          (UnaryNegate, MkAstNode operandInfo _ (ExprLiteral (MkAstNode _ _ (LiteralIntegerRaw rawLiteralText)))) => do
            negatedLiteralType <- typeIntegerLiteral True expressionInfo rawLiteralText Nothing
            recordExpressionType operandInfo.nodeId negatedLiteralType
            pure negatedLiteralType
          (UnaryNegate, MkAstNode operandInfo _ (ExprLiteral (MkAstNode _ _ (LiteralFloatRaw rawLiteralText)))) => do
            negatedLiteralType <- typeFloatLiteral expressionInfo.span rawLiteralText Nothing
            recordExpressionType operandInfo.nodeId negatedLiteralType
            pure negatedLiteralType
          _ => ?inferExpressionUnaryHole
      ExprBinary operator left right => ?inferExpressionBinaryHole
      ExprRange start operator end => ?inferExpressionRangeHole
      ExprCast operand target => ?inferExpressionCastHole
      ExprBlock block => ?inferExpressionBlockHole
      ExprIf ifNode => ?inferExpressionIfHole
      ExprQIf ifNode => notImplemented __FILE__ {function = "inferExpression"} {feature = "qif"}
      ExprSIf ifNode => notImplemented __FILE__ {function = "inferExpression"} {feature = "sif"}
      ExprMatch matchNode => notImplemented __FILE__ {function = "inferExpression"} {feature = "match"}
      ExprQMatch matchNode => notImplemented __FILE__ {function = "inferExpression"} {feature = "qmatch"}
      ExprSMatch matchNode => notImplemented __FILE__ {function = "inferExpression"} {feature = "smatch"}
      ExprLoop body => ?inferExpressionLoopHole
      ExprWhile condition body => ?inferExpressionWhileHole
      ExprFor pattern iterator body => ?inferExpressionForHole
      ExprBreak value => ?inferExpressionBreakHole
      ExprContinue => ?inferExpressionContinueHole
      ExprReturn returnValue => do
        checkerState <- get
        case checkerState.enclosingFunctionReturnType of
          Nothing => unreachable __FILE__ {function = "inferExpression"} {reason = "post-parse validation rejects a return outside a function body"}
          Just returnLeafType => do
            let returnType = leafTypeToTcType returnLeafType
            case returnValue of
              Just value => checkNestedExpression returnType value
              Nothing => isAssignableTo expressionInfo.span TcUnitType returnType
            pure TcNeverType
      ExprCtrl control => ?inferExpressionCtrlHole
      ExprAdjoint adjoint => ?inferExpressionAdjointHole
    where
      inferNestedExpression : ResolvedExpr -> StateT TypeCheckerState (Either CheckFailure) TcType
      inferNestedExpression nestedExpression = inferExpression (assert_smaller expressionNode nestedExpression)

      checkNestedExpression : TcType -> ResolvedExpr -> StateT TypeCheckerState (Either CheckFailure) ()
      checkNestedExpression expectedType nestedExpression = checkExpression expectedType (assert_smaller expressionNode nestedExpression)

      -- Param("name") has the type param. The Param symbol has no value type, so its
      -- callee node is given the function type directly. Any argument other than a
      -- direct string literal is checked against the string literal type, which
      -- reports a nested string literal as unsupported and anything else as a mismatch.
      inferPreludeParamCall : (callee : ResolvedExpr) -> (callArguments : List ResolvedExpr) -> StateT TypeCheckerState (Either CheckFailure) TcType
      inferPreludeParamCall callee callArguments =
        case (callee, callArguments) of
          (MkAstNode calleeInfo _ (ExprName (MkAstNode _ _ paramName)), [argument]) => do
            case argument of
              MkAstNode argumentInfo _ (ExprLiteral (MkAstNode _ _ (LiteralStringRaw _))) =>
                recordExpressionType argumentInfo.nodeId TcStringLiteralType
              _ => checkNestedExpression TcStringLiteralType argument
            recordExpressionType calleeInfo.nodeId (TcFunctionType EffectClassical [] [TcStringLiteralType] (TcPrimitiveType TypPrimParam))
            recordCallResolution expressionInfo.nodeId (MkCallResolution (FunctionCall paramName.nameNodeSymbolId) [ByValue])
            pure (TcPrimitiveType TypPrimParam)
          (MkAstNode _ _ (ExprName _), _) => liftTypeError (WrongArgumentCount 1 (length callArguments) expressionInfo.span)
          _ => unreachable __FILE__ {function = "inferExpression"} {reason = "isPreludeParamFunction recognizes only a name as the Param callee"}

  ||| Checks an expression against an expected type and records the expression's own
  ||| type. A literal, possibly under a unary minus, takes the expected primitive when
  ||| it can; every other construct is inferred and then checked with isAssignableTo.
  checkExpression : (expected : TcType) -> ResolvedExpr -> StateT TypeCheckerState (Either CheckFailure) ()
  checkExpression expectedType resolvedExpression@(MkAstNode expressionInfo expressionMetadata expressionNode) =
    case expressionNode of
      ExprLiteral (MkAstNode _ _ (LiteralIntegerRaw rawLiteralText)) => do
        expectedPrimitive <- resolvedExpectedPrimitive expectedType
        literalType <- typeIntegerLiteral False expressionInfo rawLiteralText expectedPrimitive
        recordExpressionType expressionInfo.nodeId literalType
        isAssignableTo expressionInfo.span literalType expectedType
      ExprLiteral (MkAstNode _ _ (LiteralFloatRaw rawLiteralText)) => do
        expectedPrimitive <- resolvedExpectedPrimitive expectedType
        literalType <- typeFloatLiteral expressionInfo.span rawLiteralText expectedPrimitive
        recordExpressionType expressionInfo.nodeId literalType
        isAssignableTo expressionInfo.span literalType expectedType
      ExprUnary (MkAstNode _ _ UnaryNegate) (MkAstNode operandInfo _ (ExprLiteral (MkAstNode _ _ (LiteralIntegerRaw rawLiteralText)))) => do
        expectedPrimitive <- resolvedExpectedPrimitive expectedType
        negatedLiteralType <- typeIntegerLiteral True expressionInfo rawLiteralText expectedPrimitive
        recordExpressionType expressionInfo.nodeId negatedLiteralType
        recordExpressionType operandInfo.nodeId negatedLiteralType
        isAssignableTo expressionInfo.span negatedLiteralType expectedType
      ExprUnary (MkAstNode _ _ UnaryNegate) (MkAstNode operandInfo _ (ExprLiteral (MkAstNode _ _ (LiteralFloatRaw rawLiteralText)))) => do
        expectedPrimitive <- resolvedExpectedPrimitive expectedType
        negatedLiteralType <- typeFloatLiteral expressionInfo.span rawLiteralText expectedPrimitive
        recordExpressionType expressionInfo.nodeId negatedLiteralType
        recordExpressionType operandInfo.nodeId negatedLiteralType
        isAssignableTo expressionInfo.span negatedLiteralType expectedType
      _ => do
        inferredType <- inferExpression resolvedExpression
        isAssignableTo expressionInfo.span inferredType expectedType

--------------------------------------------------------------------------------
-- Pass B: statements and declarations
--------------------------------------------------------------------------------

||| Records a binding's type for its pattern node, and for its binder when it names one.
||| This step handles name, `mut` name and `_` patterns.
recordLetPatternType : Pattern ResolvedAstPhase -> TcType -> StateT TypeCheckerState (Either CheckFailure) ()
recordLetPatternType (MkAstNode patternInfo patternMetadata patternNode) bindingType =
  case patternNode of
    PatternWildcard => recordPatternType patternInfo.nodeId bindingType
    PatternName mutability (MkAstNode binderInfo binderMetadata binderName) => do
      recordPatternType patternInfo.nodeId bindingType
      recordBinderType binderName.nameNodeSymbolId bindingType
    PatternPath valuePath => ?recordLetPatternTypePathHole
    PatternLiteral literal => ?recordLetPatternTypeLiteralHole
    PatternParenthesized innerPattern => unreachable __FILE__ {function = "recordLetPatternType"} {reason = "parenthesized patterns should have been removed during the desugaring phase"}
    PatternTuple elementPatterns => ?recordLetPatternTypeTupleHole
    PatternArray elementPatterns => ?recordLetPatternTypeArrayHole
    PatternStruct structPath fieldPatterns => notImplemented __FILE__ {function = "recordLetPatternType"} {feature = "struct patterns"}
    PatternEnumTuple variantPath argumentPatterns => notImplemented __FILE__ {function = "recordLetPatternType"} {feature = "enum tuple patterns"}

||| Stage 1 supports only `linear` among the qualifiers left on a `let`: `affine` and
||| `scratch` are unsupported. A `linear` qualifier is checked at writeback against the
||| binding's final type.
checkStageOneLetQualifier : (patternNodeId : NodeId) -> AstNode ResolvedAstPhase QuantumStorageQualifier -> StateT TypeCheckerState (Either CheckFailure) ()
checkStageOneLetQualifier patternNodeId (MkAstNode qualifierInfo qualifierMetadata qualifier) =
  case qualifier of
    QualifierLinear => recordLinearQualifier qualifierInfo.span patternNodeId
    QualifierAffine => liftTypeError (UnsupportedFeature "affine" qualifierInfo.span)
    QualifierScratch => liftTypeError (UnsupportedFeature "scratch" qualifierInfo.span)

||| Stage 1 does not support the auto-uncompute marker `:=`.
checkStageOneInitializerMarker : LetInitializerNode ResolvedAstPhase -> StateT TypeCheckerState (Either CheckFailure) ()
checkStageOneInitializerMarker (MkLetInitializerNode (MkAstNode markerInfo markerMetadata marker) initializerValue) =
  case marker of
    InitializerEquals => pure ()
    InitializerAutoUncompute => liftTypeError (UnsupportedFeature ":=" markerInfo.span)

||| The qualifiers and the initializer marker are checked before the initializer. With an
||| annotation, the initializer is checked against it; without one, the initializer's type
||| is inferred. A binding without an initializer takes its annotation, or else a fresh
||| general variable that later uses may constrain.
checkLetStatement : LetBindingNode ResolvedAstPhase -> StateT TypeCheckerState (Either CheckFailure) ()
checkLetStatement (MkLetBindingNode letQualifiers letPattern letTypeAnnotation letInitializer) = do
  traverse_ (checkStageOneLetQualifier letPattern.astInfo.nodeId) letQualifiers
  traverse_ checkStageOneInitializerMarker letInitializer
  annotatedType <- for letTypeAnnotation $ \typeAnnotation => do
    checkWrittenTypeIsSizedAndSupported typeAnnotation
    leafTypeToTcType <$> writtenLeafTypeM evalConstExprNat typeAnnotation
  bindingType <-
    case (annotatedType, letInitializer) of
      (Just expectedType, Just initializer) => do
        checkExpression expectedType initializer.initializerValue
        pure expectedType
      (Nothing, Just initializer) => inferExpression initializer.initializerValue
      (Just expectedType, Nothing) => pure expectedType
      (Nothing, Nothing) => liftInferenceOperation (freshTypeVariable letPattern.astInfo.span AnyTypeDomain)
  recordLetPatternType letPattern bindingType
  liftInferenceOperation (moveOpenAnyTypeDomainVariableSpansToLetPattern letPattern.astInfo.span bindingType)

checkStatement : Statement ResolvedAstPhase -> StateT TypeCheckerState (Either CheckFailure) ()
checkStatement (MkAstNode statementAstInfo (MkProvenanceMetadata provenance) statementNode) = do
  case statementNode of
    StatementLet letBinding => checkLetStatement letBinding
    StatementAssignment (MkAssignmentNode assignmentTarget assignmentOperator assignmentValue) => ?checkStatementAssignmentHole
    StatementSemiExpression statementExpression => ignore (inferExpression statementExpression)
    StatementExpression statementExpression => ?checkStatementExpressionHole

checkBlock : Block ResolvedAstPhase ->  StateT TypeCheckerState (Either CheckFailure) ()
checkBlock (MkAstNode blockAstInfo (MkProvenanceMetadata provenance) (MkBlockNode blockInnerDocs blockStatements finalExpression)) = do
  traverse_ checkStatement blockStatements
  traverse_ (\finalExpressionNode => ignore (inferExpression finalExpressionNode)) finalExpression

--------------------------------------------------------------------------------
-- Pass B: writeback
--------------------------------------------------------------------------------

||| Writeback for the body or const initializer just checked, in this order: default
||| every open variable that has a default, and report a general variable still open
||| as CannotInferType at its report span; check the recorded `linear` qualifiers and
||| range-check the integer literals typed by a variable, now that their types are
||| final; commit expression, pattern and binder types, and classify the storage of
||| each binder; then reset the inference state and the enclosing return type.
writeBackInferenceResults : StateT TypeCheckerState (Either CheckFailure) ()
writeBackInferenceResults = do
  openGeneralVariableId <- liftInferenceOperation defaultOpenVariables
  checkerState <- get
  let inferenceState = checkerState.inferenceState
  case openGeneralVariableId of
    Nothing => pure ()
    Just variableId =>
      case lookup variableId inferenceState.anyTypeDomainVariableSpans of
        Just reportSpan => liftTypeError (CannotInferType reportSpan)
        Nothing => unreachable __FILE__ {function = "writeBackInferenceResults"} {reason = "general variable " ++ show variableId ++ " has no report span"}
  -- Both lists were built by prepending, so reversing them reports the first error in source order.
  traverse_ checkRecordedLinearQualifier (reverse inferenceState.linearQualifiers)
  traverse_ rangeCheckRecordedIntegerLiteral (reverse inferenceState.integerLiterals)
  expressionLeafTypes <- traverse convertEntryToLeafType (Data.SortedMap.toList inferenceState.expressionTypes)
  patternLeafTypes <- traverse convertEntryToLeafType (Data.SortedMap.toList inferenceState.patternTypes)
  binderLeafTypes <- traverse convertEntryToLeafType (Data.SortedMap.toList inferenceState.binderTypes)
  modify $ \currentState =>
    { typeTables.expressionTypes := insertFrom expressionLeafTypes currentState.typeTables.expressionTypes
    , typeTables.patternTypes := insertFrom patternLeafTypes currentState.typeTables.patternTypes
    } currentState
  for_ binderLeafTypes $ \(binderSymbolId, binderLeafType) => do
    recordSymbolType binderSymbolId binderLeafType
    recordLocalStorage binderSymbolId binderLeafType
  modify $ \currentState => { inferenceState := emptyInferenceState, enclosingFunctionReturnType := Nothing } currentState
  where
    convertEntryToLeafType : (key, TcType) -> StateT TypeCheckerState (Either CheckFailure) (key, LeafType)
    convertEntryToLeafType (entryKey, entryType) = (entryKey,) <$> liftInferenceOperation (tcTypeToLeafType entryType)

    -- In stage 1 every qbit is linear, so the qualifier only requires an owned qbit in the type.
    checkRecordedLinearQualifier : (SourceSpan, NodeId) -> StateT TypeCheckerState (Either CheckFailure) ()
    checkRecordedLinearQualifier (qualifierSpan, patternNodeId) = do
      checkerState <- get
      case lookup patternNodeId checkerState.inferenceState.patternTypes of
        Nothing => unreachable __FILE__ {function = "writeBackInferenceResults"} {reason = "a linear qualifier's pattern has no recorded type"}
        Just patternType => do
          patternLeafType <- liftInferenceOperation (tcTypeToLeafType patternType)
          unless (hasOwnedQbit patternLeafType) $
            liftTypeError (InvalidQuantumQualifier "linear" patternLeafType qualifierSpan)

    -- The literal's variable has the {integer} domain, so its final type is an integer primitive or bit.
    rangeCheckRecordedIntegerLiteral : (SourceSpan, NodeId, Integer) -> StateT TypeCheckerState (Either CheckFailure) ()
    rangeCheckRecordedIntegerLiteral (literalSpan, literalNodeId, literalValue) = do
      checkerState <- get
      case lookup literalNodeId checkerState.inferenceState.expressionTypes of
        Nothing => unreachable __FILE__ {function = "writeBackInferenceResults"} {reason = "a recorded integer literal has no expression type"}
        Just literalType => do
          resolvedLiteralType <- liftInferenceOperation (resolveTcTypeThroughParentReferences literalType)
          case resolvedLiteralType of
            TcPrimitiveType literalPrimitive =>
              case checkIntegerLiteralRange literalPrimitive literalValue literalSpan of
                Left typeError => liftTypeError typeError
                Right () => pure ()
            _ => unreachable __FILE__ {function = "writeBackInferenceResults"} {reason = "an integer literal's final type is not a primitive"}

--------------------------------------------------------------------------------
-- Pass B: function bodies and const initializers
--------------------------------------------------------------------------------

||| Checks a function's body from an empty inference state, with `return` checked against
||| the return type pass A recorded, then runs writeback. A function that is not a
||| `const fn` is then added to checkedBodies; for a `const fn`, membership will also
||| certify its const eligibility, which is not checked yet.
checkFunctionBody : FunctionDeclarationNode ResolvedAstPhase -> StateT TypeCheckerState (Either CheckFailure) ()
checkFunctionBody
    (MkFunctionDeclarationNode
      functionDocs
      functionAttributes
      functionVisibility
      functionConstness
      functionEffect
      functionName
      functionParameters
      returnType
      supportClause
      contractClauses
      functionBody
    ) = do
  let functionSymbolId = functionName.nodeValue.nameNodeSymbolId
  checkerState <- get
  case map (.symbolType) (lookup functionSymbolId checkerState.typeTables.symbols) of
    Just (ResolvedType (LeafFunctionType _ _ _ functionResultType)) => do
      modify $ \currentState => { enclosingFunctionReturnType := Just functionResultType, inferenceState := emptyInferenceState } currentState
      checkBlock functionBody
      writeBackInferenceResults
      when (isNothing functionConstness) $
        modify $ \currentState => { checkedBodies := insert functionSymbolId currentState.checkedBodies } currentState
    Just TypeNotYetResolved => blocked functionSymbolId
    _ => unreachable __FILE__ {function = "checkFunctionBody"} {reason = "pass A records a function type for every function"}

||| Checks a const item's initializer against its declared type from an empty inference
||| state, outside any function, then runs writeback. It records no value yet.
checkConstInitializer : ConstDeclarationNode ResolvedAstPhase ->  StateT TypeCheckerState (Either CheckFailure) ()
checkConstInitializer (MkConstDeclarationNode constDocs constVisibility constName constType constValue) = do
  let constSymbolId = constName.nodeValue.nameNodeSymbolId
  checkerState <- get
  case map (.symbolType) (lookup constSymbolId checkerState.typeTables.symbols) of
    Just (ResolvedType constLeafType) => do
      modify $ \currentState => { enclosingFunctionReturnType := Nothing, inferenceState := emptyInferenceState } currentState
      checkExpression (leafTypeToTcType constLeafType) constValue
      writeBackInferenceResults
    Just TypeNotYetResolved => blocked constSymbolId
    _ => unreachable __FILE__ {function = "checkConstInitializer"} {reason = "pass A records a type for every constant"}

export
checkBody : ResolvedItem -> StateT TypeCheckerState (Either CheckFailure) ()
checkBody (MkAstNode itemInfo metadata item) = do
  case item of
      ItemModule declaration => notImplemented __FILE__ {function = "checkBody"} {feature = "ItemModule"}
      ItemUse declaration => notImplemented __FILE__ {function = "checkBody"} {feature = "ItemUse"}
      ItemConst declaration => checkConstInitializer declaration
      ItemEnum declaration => notImplemented __FILE__ {function = "checkBody"} {feature = "ItemEnum"}
      ItemQEnum declaration => notImplemented __FILE__ {function = "checkBody"} {feature = "ItemQEnum"}
      ItemStruct declaration => notImplemented __FILE__ {function = "checkBody"} {feature = "ItemStruct"}
      ItemImpl declaration => notImplemented __FILE__ {function = "checkBody"} {feature = "ItemImpl"}
      ItemFunction declaration => checkFunctionBody declaration

