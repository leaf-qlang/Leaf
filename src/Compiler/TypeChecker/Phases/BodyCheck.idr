module Compiler.TypeChecker.Phases.BodyCheck

import Data.List1
import Data.SortedMap
import Data.SortedSet

import Control.Monad.State
import Compiler.ScopeAndNameResolution.Data
import Compiler.TypeChecker.Data
import Compiler.TypeChecker.Helper
import Compiler.TypeChecker.Numeric
import Compiler.TypeChecker.State
import Compiler.TypeChecker.Type
import Frontend.ASTData
import Frontend.ASTPhases
import Frontend.Syntax.Attribute
import Frontend.Syntax.AST
import Frontend.Syntax.Contract
import Frontend.Syntax.Common
import Frontend.Syntax.Doc
import Frontend.Syntax.Literal
import Frontend.Syntax.Name
import Frontend.Syntax.Operator
import Frontend.Syntax.Pattern
import Frontend.Syntax.Type
import Frontend.Token

%default total

export
evalConstExprNat : Expr ResolvedAstPhase -> StateT TypeCheckerState (Either CheckFailure) Nat
evalConstExprNat (MkAstNode astInfo _ (ExprLiteral (MkAstNode _ _ (LiteralIntegerRaw raw)))) =
  case integerLiteralValue raw of
    Nothing => unreachable {function = "evalConstExprNat"} {reason = "the lexer accepted a malformed integer literal: " ++ raw}
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
-- only literal expression are implemented for now in order to unblock Phase A
evalConstExprNat _ = notImplemented {function = "evalConstExprNat"} {feature = "array lengths other than a literal (needs ConstEval/ConstRules)"}

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
        TyPath typePath => notImplemented {function = "checkTypeIsSized"} {feature = "structs, enums or qenums"}
        TyUnit => pure ()
        TyParenthesized innerType => assert_total (idris_crash "Parenthesized types should have been removed during the desugaring phase.")
        TyTuple elementTypes => traverse_ (\element => walk False (assert_smaller typeNode element)) elementTypes
        TyArray elementType sizeExpression => walk False (assert_smaller typeNode elementType)
        TySlice elementType =>
          if unsizedAllowed
            then walk False (assert_smaller typeNode elementType)
            else do
              leafType <- writtenLeafTypeM evalConstExprNat typeAstNode
              typeError (UnsizedValue leafType astInfo.span)
        TyReference borrowKind referencedType => walk True (assert_smaller typeNode referencedType)
        TyQualified multiplicityQualifier qualifiedType => walk unsizedAllowed (assert_smaller typeNode qualifiedType)
        TyFunction functionEffect functionParameters returnType => do
          traverse_ (\parameter => walk False (assert_smaller typeNode parameter.nodeValue.parameterType)) functionParameters
          traverse_ (\result => walk False (assert_smaller typeNode result)) returnType

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
    ) = pure ()

checkConstDeclaration : ConstDeclarationNode ResolvedAstPhase ->  StateT TypeCheckerState (Either CheckFailure) ()
checkConstDeclaration (MkConstDeclarationNode constDocs constVisibility constName constType constValue) = pure ()

export
checkBody : ResolvedItem -> StateT TypeCheckerState (Either CheckFailure) ()
checkBody (MkAstNode itemInfo metadata item) = do
  case item of
      ItemModule declaration => notImplemented {function = "checkItem"} {feature = "ItemModule"}
      ItemUse declaration => notImplemented {function = "checkItem"} {feature = "ItemUse"}
      ItemConst declaration => checkConstDeclaration declaration
      ItemEnum declaration => notImplemented {function = "checkItem"} {feature = "ItemEnum"}
      ItemQEnum declaration => notImplemented {function = "checkItem"} {feature = "ItemQEnum"}
      ItemStruct declaration => notImplemented {function = "checkItem"} {feature = "ItemStruct"}
      ItemImpl declaration => notImplemented {function = "checkItem"} {feature = "ItemImpl"}
      ItemFunction declaration => checkFunctionDeclaration declaration

