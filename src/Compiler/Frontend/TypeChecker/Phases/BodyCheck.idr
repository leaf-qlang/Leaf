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

||| A slice type [T] has no length known at compile time, so it can't be a parameter, result or constant type on its own. 
||| A reference to a slice, &[T], is fine, a slice reference carries both a pointer to its first element and its length.
export
checkTypeIsSized : ResolvedTy -> StateT TypeCheckerState (Either CheckFailure) ()
checkTypeIsSized = walk False
  where
    walk : (unsizedAllowed : Bool) -> ResolvedTy -> StateT TypeCheckerState (Either CheckFailure) ()
    walk unsizedAllowed typeAstNode@(MkAstNode astInfo metadata typeNode) =
      case typeNode of
        TyPrimitive primitiveName => pure ()
        TyPath typePath => notImplemented __FILE__ {function = "checkTypeIsSized"} {feature = "structs, enums or qenums"}
        TyUnit => pure ()
        TyParenthesized innerType => unreachable __FILE__ {function = "checkTypeIsSized"} {reason = "parenthesized types should have been removed during the desugaring phase."}
        TyTuple elementTypes => traverse_ (\element => walk False (assert_smaller typeNode element)) elementTypes
        TyArray elementType sizeExpression => walk False (assert_smaller typeNode elementType)
        TySlice elementType =>
          if unsizedAllowed
            then walk False (assert_smaller typeNode elementType)
            else do
              leafType <- writtenLeafTypeM evalConstExprNat typeAstNode
              typeError (UnsizedValue leafType astInfo.span)
        TyReference borrowKind referencedType => walk True (assert_smaller typeNode referencedType)
        TyQualified quantumUsageQualifier qualifiedType => walk unsizedAllowed (assert_smaller typeNode qualifiedType)
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
        LiteralIntegerRaw rawSpelling => ?checkExpressionLiteralIntegerHole
        LiteralFloatRaw rawSpelling => ?checkExpressionLiteralFloatHole
        -- Param("name") is accepted in the ExprCall case without visiting its argument,
        -- so any string literal reaching this point is used in another context.
        LiteralStringRaw rawSpelling => notImplemented __FILE__ {function = "checkExpressionNode"} {feature = "string literal used outside Param()"}
        LiteralByteRaw rawSpelling => ?checkExpressionLiteralByteHole
        LiteralByteStringRaw rawSpelling => ?checkExpressionLiteralByteStringHole
        LiteralBasisStringRaw rawSpelling => ?checkExpressionLiteralBasisStringHole
        LiteralBoolean value => ?checkExpressionLiteralBooleanHole
        LiteralUnit => ?checkExpressionLiteralUnitHole
        LiteralQuantumState basisStateName => ?checkExpressionLiteralQuantumStateHole
    ExprName name => ?checkExpressionNameHole
    ExprPath path => ?checkExpressionPathHole
    ExprBuiltin builtin => do
      case builtin of
        BuiltinBarrier => ?checkExpressionBuiltinBarrierHole
        BuiltinCtrl => ?checkExpressionBuiltinCtrlHole
        BuiltinOn => ?checkExpressionBuiltinOnHole
        BuiltinApply => ?checkExpressionBuiltinApplyHole
        BuiltinBasis => notImplemented __FILE__ {function = "checkExpressionNode"} {feature = "basis builtin function"}
        BuiltinClean => notImplemented __FILE__ {function = "checkExpressionNode"} {feature = "clean builtin function"}
        BuiltinDiscard => ?checkExpressionBuiltinDiscardHole
        BuiltinIsolated => notImplemented __FILE__ {function = "checkExpressionNode"} {feature = "isolated builtin function"}
        BuiltinLen => ?checkExpressionBuiltinLenHole
        BuiltinMeasr => ?checkExpressionBuiltinMeasrHole
        BuiltinProduct => notImplemented __FILE__ {function = "checkExpressionNode"} {feature = "product builtin function"}
        BuiltinQAlloc => ?checkExpressionBuiltinQAllocHole
        BuiltinReset => ?checkExpressionBuiltinResetHole
        BuiltinRev => ?checkExpressionBuiltinRevHole
        BuiltinTensor => notImplemented __FILE__ {function = "checkExpressionNode"} {feature = "tensor builtin function"}
        BuiltinSeparable => notImplemented __FILE__ {function = "checkExpressionNode"} {feature = "separable builtin function"}
        BuiltinStabilized => notImplemented __FILE__ {function = "checkExpressionNode"} {feature = "stabilized builtin function"}
        BuiltinUncompute => notImplemented __FILE__ {function = "checkExpressionNode"} {feature = "uncompute builtin function"}
        BuiltinWeaken => notImplemented __FILE__ {function = "checkExpressionNode"} {feature = "weaken builtin function"}

    ExprSelf selfReceiver => ?checkExpressionSelfHole
    ExprParenthesized inner => ?checkExpressionParenthesizedHole
    ExprTuple elements => ?checkExpressionTupleHole
    ExprArray elements => ?checkExpressionArrayHole
    ExprRepeatedArray element count => ?checkExpressionRepeatedArrayHole
    ExprStructLiteral path fields => ?checkExpressionStructLiteralHole
    ExprCall callee arguments => do
      calleeIsPreludeParam <- isPreludeParamFunction callee
      case (calleeIsPreludeParam, arguments) of
        (True, [MkAstNode argumentInfo argumentMetadata (ExprLiteral (MkAstNode literalAstInfo literalMetadata (LiteralStringRaw parameterName)))]) => pure ()
        _ => ?checkExpressionCallHole
    ExprMethodCall receiver name arguments => ?checkExpressionMethodCallHole
    ExprField object name => ?checkExpressionFieldHole
    ExprTupleIndex tuple indexText => ?checkExpressionTupleIndexHole
    ExprIndex object index => ?checkExpressionIndexHole
    ExprUnary operator operand => ?checkExpressionUnaryHole
    ExprBinary operator left right => ?checkExpressionBinaryHole
    ExprRange start operator end => ?checkExpressionRangeHole
    ExprCast operand target => ?checkExpressionCastHole
    ExprBlock block => ?checkExpressionBlockHole
    ExprIf ifNode => ?checkExpressionIfHole
    ExprQIf ifNode => ?checkExpressionQIfHole
    ExprSIf ifNode => ?checkExpressionSIfHole
    ExprMatch matchNode => ?checkExpressionMatchHole
    ExprQMatch matchNode => ?checkExpressionQMatchHole
    ExprSMatch matchNode => ?checkExpressionSMatchHole
    ExprLoop body => ?checkExpressionLoopHole
    ExprWhile condition body => ?checkExpressionWhileHole
    ExprFor pattern iterator body => ?checkExpressionForHole
    ExprBreak value => ?checkExpressionBreakHole
    ExprContinue => ?checkExpressionContinueHole
    ExprReturn value => ?checkExpressionReturnHole
    ExprCtrl control => ?checkExpressionCtrlHole
    ExprAdjoint adjoint => ?checkExpressionAdjointHole

checkExpression : ResolvedExpr -> StateT TypeCheckerState (Either CheckFailure) ()
checkExpression (MkAstNode expressionInfo (MkProvenanceMetadata provenance) expressionNode) = checkExpressionNode expressionNode

checkStatement : Statement ResolvedAstPhase -> StateT TypeCheckerState (Either CheckFailure) ()
checkStatement (MkAstNode statementAstInfo (MkProvenanceMetadata provenance) statementNode) = do
  case statementNode of
    StatementLet (MkLetBindingNode qualifiers pattern typeAnnotation initializer) => ?statementlet
    StatementAssignment (MkAssignmentNode assignmentTarget assignmentOperator assignmentValue) => ?statemnassignment
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

