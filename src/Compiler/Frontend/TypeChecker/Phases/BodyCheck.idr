module Compiler.Frontend.TypeChecker.Phases.BodyCheck

import Compiler.Helper
import Data.List1
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
                Just (NonUsizeLengthSuffix suffixType) => typeError (IncorrectArrayLengthType (LeafPrimitiveType suffixType) astInfo.span)
                _ =>
                  case inferIntegerLiteral (Just TypPrimUsize) raw astInfo.span of
                    Left err => typeError err
                    Right (primitive, value) =>
                      case checkArrayLength (LeafPrimitiveType primitive) value astInfo.span of
                        Left err => typeError err
                        Right count => pure count
        _ => typeError ?hh
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
    ExprParenthesized inner => ?evalConstExprNatParenthesizedHole
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
              typeError (UnsizedValue leafType astInfo.span)
        TyReference borrowKind referencedType => walk True (assert_smaller typeNode referencedType)
        TyQualified (MkAstNode qualifierInfo _ quantumUsageQualifier) qualifiedType =>
          case quantumUsageQualifier of
            QuantumUsageAffine => typeError (UnsupportedFeature "affine" qualifierInfo.span)
            QuantumUsageLinear => walk unsizedAllowed (assert_smaller typeNode qualifiedType)
        TyFunction functionEffect functionParameters returnType => do
          traverse_ (\parameter => walk False (assert_smaller typeNode parameter.nodeValue.parameterType)) functionParameters
          traverse_ (\result => walk False (assert_smaller typeNode result)) returnType


||| True when the callee names the prelude function Param, not a user declaration that shadows it.
isPreludeParamFunction : ResolvedExpr -> StateT TypeCheckerState (Either CheckFailure) Bool
isPreludeParamFunction (MkAstNode calleeInfo calleeMetadata (ExprName (MkAstNode nameInfo nameMetadata calleeName))) = do
  checkerState <- get
  case lookup calleeName.nameNodeSymbolId checkerState.tables.symbols of
    Just symbolInfo =>
      case symbolInfo.origin of
        PreludeSymbol => pure (symbolInfo.declaredName == "Param")
        _ => pure False
    Nothing => pure False
isPreludeParamFunction _ = pure False

checkExpressionNode : ExpressionNode ResolvedAstPhase -> StateT TypeCheckerState (Either CheckFailure) ()
checkExpressionNode expression =
  case expression of
    ExprLiteral (MkAstNode literalAstInfo literalMetadata literalNode) => do
      case literalNode of
        LiteralIntegerRaw rawSpelling => pure () --?checkExpressionLiteralIntegerHole
        LiteralFloatRaw rawSpelling => pure () --?checkExpressionLiteralFloatHole
        -- Param("name") is accepted in the ExprCall case without visiting its argument,
        -- so any string literal reaching this point is used in another context.
        LiteralStringRaw rawSpelling => notImplemented __FILE__ {function = "checkExpressionNode"} {feature = "string literal used outside Param()"}
        LiteralByteRaw rawSpelling => pure () --?checkExpressionLiteralByteHole
        LiteralByteStringRaw rawSpelling => pure () --?checkExpressionLiteralByteStringHole
        LiteralBasisStringRaw rawSpelling => pure () --?checkExpressionLiteralBasisStringHole
        LiteralBoolean value => pure () --?checkExpressionLiteralBooleanHole
        LiteralUnit => pure () --?checkExpressionLiteralUnitHole
        LiteralQuantumState basisStateName => pure () --?checkExpressionLiteralQuantumStateHole
    ExprName name => pure () --?checkExpressionNameHole
    ExprPath path => pure () --?checkExpressionPathHole
    ExprBuiltin builtin => do
      case builtin of
        BuiltinBarrier => pure () --?checkExpressionBuiltinBarrierHole
        BuiltinCtrl => pure () --?checkExpressionBuiltinCtrlHole
        BuiltinOn => pure () --?checkExpressionBuiltinOnHole
        BuiltinApply => pure () --?checkExpressionBuiltinApplyHole
        BuiltinBasis => notImplemented __FILE__ {function = "checkExpressionNode"} {feature = "basis builtin function"}
        BuiltinClean => notImplemented __FILE__ {function = "checkExpressionNode"} {feature = "clean builtin function"}
        BuiltinDiscard => pure () --?checkExpressionBuiltinDiscardHole
        BuiltinIsolated => notImplemented __FILE__ {function = "checkExpressionNode"} {feature = "isolated builtin function"}
        BuiltinLen => pure () --?checkExpressionBuiltinLenHole
        BuiltinMeasr => pure () --?checkExpressionBuiltinMeasrHole
        BuiltinProduct => notImplemented __FILE__ {function = "checkExpressionNode"} {feature = "product builtin function"}
        BuiltinQAlloc => pure () --?checkExpressionBuiltinQAllocHole
        BuiltinReset => pure () --?checkExpressionBuiltinResetHole
        BuiltinRev => pure () --?checkExpressionBuiltinRevHole
        BuiltinTensor => notImplemented __FILE__ {function = "checkExpressionNode"} {feature = "tensor builtin function"}
        BuiltinSeparable => notImplemented __FILE__ {function = "checkExpressionNode"} {feature = "separable builtin function"}
        BuiltinStabilized => notImplemented __FILE__ {function = "checkExpressionNode"} {feature = "stabilized builtin function"}
        BuiltinUncompute => notImplemented __FILE__ {function = "checkExpressionNode"} {feature = "uncompute builtin function"}
        BuiltinWeaken => notImplemented __FILE__ {function = "checkExpressionNode"} {feature = "weaken builtin function"}

    ExprSelf selfReceiver => pure () --?checkExpressionSelfHole
    ExprParenthesized inner => pure () --?checkExpressionParenthesizedHole
    ExprTuple elements => pure () --?checkExpressionTupleHole
    ExprArray elements => pure () --?checkExpressionArrayHole
    ExprRepeatedArray element count => pure () --?checkExpressionRepeatedArrayHole
    ExprStructLiteral path fields => pure () --?checkExpressionStructLiteralHole
    ExprCall callee arguments => do
      calleeIsPreludeParam <- isPreludeParamFunction callee
      case (calleeIsPreludeParam, arguments) of
        (True, [MkAstNode argumentInfo argumentMetadata (ExprLiteral (MkAstNode literalAstInfo literalMetadata (LiteralStringRaw parameterName)))]) => pure ()
        _ => pure () --?checkExpressionCallHole
    ExprMethodCall receiver name arguments => pure () --?checkExpressionMethodCallHole
    ExprField object name => pure () --?checkExpressionFieldHole
    ExprTupleIndex tuple indexText => pure () --?checkExpressionTupleIndexHole
    ExprIndex object index => pure () --?checkExpressionIndexHole
    ExprUnary operator operand => pure () --?checkExpressionUnaryHole
    ExprBinary operator left right => pure () --?checkExpressionBinaryHole
    ExprRange start operator end => pure () --?checkExpressionRangeHole
    ExprCast operand target => pure () --?checkExpressionCastHole
    ExprBlock block => pure () --?checkExpressionBlockHole
    ExprIf ifNode => pure () --?checkExpressionIfHole
    ExprQIf ifNode => pure () --?checkExpressionQIfHole
    ExprSIf ifNode => pure () --?checkExpressionSIfHole
    ExprMatch matchNode => pure () --?checkExpressionMatchHole
    ExprQMatch matchNode => pure () --?checkExpressionQMatchHole
    ExprSMatch matchNode => pure () --?checkExpressionSMatchHole
    ExprLoop body => pure () --?checkExpressionLoopHole
    ExprWhile condition body => pure () --?checkExpressionWhileHole
    ExprFor pattern iterator body => pure () --?checkExpressionForHole
    ExprBreak value => pure () --?checkExpressionBreakHole
    ExprContinue => pure () --?checkExpressionContinueHole
    ExprReturn value => pure () --?checkExpressionReturnHole
    ExprCtrl control => pure () --?checkExpressionCtrlHole
    ExprAdjoint adjoint => pure () --?checkExpressionAdjointHole

checkExpression : ResolvedExpr -> StateT TypeCheckerState (Either CheckFailure) ()
checkExpression (MkAstNode expressionInfo (MkProvenanceMetadata provenance) expressionNode) = checkExpressionNode expressionNode

checkStatement : Statement ResolvedAstPhase -> StateT TypeCheckerState (Either CheckFailure) ()
checkStatement (MkAstNode statementAstInfo (MkProvenanceMetadata provenance) statementNode) = do
  case statementNode of
    StatementLet (MkLetBindingNode qualifiers pattern typeAnnotation initializer) => pure () --?statementlet
    StatementAssignment (MkAssignmentNode assignmentTarget assignmentOperator assignmentValue) => pure () --?statemnassignment
    StatementSemiExpression statementExpression => checkExpression statementExpression
    StatementExpression statementExpression => checkExpression statementExpression

checkFunctionBody : Block ResolvedAstPhase ->  StateT TypeCheckerState (Either CheckFailure) ()
checkFunctionBody (MkAstNode functionBodyAstInfo (MkProvenanceMetadata provenance) (MkBlockNode blockInnerDocs blockStatements finalExpression)) = do
      (traverse_ checkStatement blockStatements)
      (traverse_ checkExpression finalExpression)

checkFunctionDeclaration : FunctionDeclarationNode ResolvedAstPhase -> StateT TypeCheckerState (Either CheckFailure) ()
checkFunctionDeclaration
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
    ) = checkFunctionBody functionBody

checkConstDeclaration : ConstDeclarationNode ResolvedAstPhase ->  StateT TypeCheckerState (Either CheckFailure) ()
checkConstDeclaration (MkConstDeclarationNode constDocs constVisibility constName constType constValue) = checkExpression constValue

export
checkBody : ResolvedItem -> StateT TypeCheckerState (Either CheckFailure) ()
checkBody (MkAstNode itemInfo metadata item) = do
  case item of
      ItemModule declaration => notImplemented __FILE__ {function = "checkItem"} {feature = "ItemModule"}
      ItemUse declaration => notImplemented __FILE__ {function = "checkItem"} {feature = "ItemUse"}
      ItemConst declaration => checkConstDeclaration declaration
      ItemEnum declaration => notImplemented __FILE__ {function = "checkItem"} {feature = "ItemEnum"}
      ItemQEnum declaration => notImplemented __FILE__ {function = "checkItem"} {feature = "ItemQEnum"}
      ItemStruct declaration => notImplemented __FILE__ {function = "checkItem"} {feature = "ItemStruct"}
      ItemImpl declaration => notImplemented __FILE__ {function = "checkItem"} {feature = "ItemImpl"}
      ItemFunction declaration => checkFunctionDeclaration declaration

