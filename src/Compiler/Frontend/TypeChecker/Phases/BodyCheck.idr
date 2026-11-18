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


checkExpressionNode : ExpressionNode ResolvedAstPhase -> StateT TypeCheckerState (Either CheckFailure) ()
checkExpressionNode expression =
  case expression of
    ExprLiteral literal => ?checkExpressionLiteralHole
    ExprName name => ?checkExpressionNameHole
    ExprPath path => ?checkExpressionPathHole
    ExprBuiltin builtin => ?checkExpressionBuiltinHole
    ExprSelf selfReceiver => ?checkExpressionSelfHole
    ExprParenthesized inner => ?checkExpressionParenthesizedHole
    ExprTuple elements => ?checkExpressionTupleHole
    ExprArray elements => ?checkExpressionArrayHole
    ExprRepeatedArray element count => ?checkExpressionRepeatedArrayHole
    ExprStructLiteral path fields => ?checkExpressionStructLiteralHole
    ExprCall callee arguments => ?checkExpressionCallHole
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
checkExpression (MkAstNode expressionInfo (MkProvenanceMetadata provenance) expressionNode) = pure ()

checkBlock : Block ResolvedAstPhase ->  StateT TypeCheckerState (Either CheckFailure) ()
checkBlock (MkAstNode functionBodyAstInfo (MkProvenanceMetadata provenance) (MkBlockNode blockInnerDocs blockStatements finalExpression)) = pure ()

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
    ) = checkBlock functionBody

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

