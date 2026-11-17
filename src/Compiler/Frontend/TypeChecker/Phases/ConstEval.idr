module Compiler.Frontend.TypeChecker.Phases.ConstEval

import Control.Monad.State

import Compiler.Frontend.TypeChecker.Data
import Compiler.Frontend.TypeChecker.Helper
import Compiler.Frontend.TypeChecker.Numeric
import Compiler.Frontend.TypeChecker.State
import Compiler.Frontend.TypeChecker.Type
import Compiler.Frontend.ASTData
import Compiler.Frontend.ASTPhases
import Compiler.Frontend.Syntax.AST
import Compiler.Frontend.Syntax.Literal
import Compiler.Frontend.Token

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
