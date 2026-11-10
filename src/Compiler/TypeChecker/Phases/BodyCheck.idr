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

||| Reports, at the offending node's own span, the two written-type errors of
||| §4.1 item 4: a `qstate` anywhere in the type (`UnsupportedFeature "qstate"`,
||| §1.5 item 8) and a slice in an owned position -- entered through
||| parentheses, tuples, arrays and slices, but not behind a reference or
||| inside a function type -- (`UnsizedValue`, §5.6). Walks the written type
||| rather than the `LeafType`, because only the written nodes carry spans.
||| Shared by pass A (parameter, result and constant types) and pass B (`let`
||| annotations).
export
checkWrittenType : ResolvedTy -> StateT TypeCheckerState (Either CheckFailure) ()
checkWrittenType writtenType = ?checkWrittenTypeH


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

