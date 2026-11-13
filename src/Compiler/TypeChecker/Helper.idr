module Compiler.TypeChecker.Helper

import Compiler.TypeChecker.Data
import Compiler.TypeChecker.Type
import Data.List
import Data.List1
import Data.Maybe
import Frontend.ASTData
import Frontend.ASTPhases
import Frontend.Syntax.AST
import Frontend.Syntax.Common
import Frontend.Syntax.Literal
import Frontend.Syntax.Name
import Frontend.Syntax.Operator
import Frontend.Syntax.Type
import Frontend.Token

%default total

||| Crash on a language feature that typechecking does not support yet.
export
notImplemented : (function : String) -> (feature : String) -> a
notImplemented function feature =
  assert_total $ idris_crash $
    "Typechecking, " ++ function ++ ": not yet implemented: " ++ feature ++ "."

||| Crash on a violated internal invariant: a compiler bug, not invalid Leaf source.
export
unreachable : (function : String) -> (reason : String) -> a
unreachable function reason =
  assert_total $ idris_crash $
    "Typechecking, " ++ function ++ ": internal error: " ++ reason ++ "."

pathTargetSymbolId : {astPhase : AstPhase} -> Path astPhase -> SymbolId
pathTargetSymbolId {astPhase = SurfaceAstPhase} _ = unreachable {function = "pathTargetSymbolId"} {reason = "paths are not yet resolved"}
pathTargetSymbolId {astPhase = CanonicalAstPhase} _ = unreachable {function = "pathTargetSymbolId"} {reason = "paths are not yet resolved"}
pathTargetSymbolId {astPhase = ResolvedAstPhase} path = path.nodeValue.resolvedPathTargetSymbolId
pathTargetSymbolId {astPhase = TypedAstPhase} path = path.nodeValue.resolvedPathTargetSymbolId

export
writtenLeafTypeM :  {astPhase : AstPhase} -> Monad m => (resolveLength : Expr astPhase -> m Nat) -> Ty astPhase (Expr astPhase) -> m LeafType
writtenLeafTypeM resolveLength typeAstNode@(MkAstNode _ _ typeNode) =
  case typeNode of
    TyPrimitive primitiveName => pure (LeafPrimitiveType primitiveName)
    TyPath typePath           => pure (LeafNamedType (pathTargetSymbolId typePath))
    TyUnit                    => pure LeafUnitType
    TyParenthesized innerType => recur innerType
    TyTuple elementTypes      => LeafTupleType <$> traverse recur elementTypes
    TyArray elementType sizeExpression => LeafArrayType <$> recur elementType <*> resolveLength sizeExpression
    TySlice elementType => LeafSliceType <$> recur elementType
    TyReference borrowKind referencedType => quantumMultiplicityFreeReference borrowKind.nodeValue <$> recur referencedType
    TyQualified multiplicityQualifier qualifiedType => LeafQualifiedType multiplicityQualifier.nodeValue <$> recur qualifiedType
    TyFunction functionEffect functionParameters returnType =>
      LeafFunctionType (maybe EffectGeneral (.nodeValue) functionEffect) []
        <$> traverse (\parameter => recur parameter.nodeValue.parameterType) functionParameters
        <*> maybe (pure LeafUnitType) recur returnType
  where
    recur : Ty astPhase (Expr astPhase) -> m LeafType
    recur nestedType = writtenLeafTypeM resolveLength (assert_smaller typeAstNode nestedType)

export
toInferredType : {astPhase : AstPhase} -> Ty astPhase (Expr astPhase) -> InferredType
toInferredType = maybe TypeNotYetResolved ResolvedType . writtenLeafTypeM literalArrayLength
  where
    literalArrayLength : Expr astPhase -> Maybe Nat
    literalArrayLength (MkAstNode _ _ (ExprLiteral (MkAstNode _ _ (LiteralIntegerRaw raw)))) =
      case (integerLiteralValue raw, arrayLengthProblem raw) of
        (Just length, Nothing) => if length <= usizeMaximum then Just length else Nothing
        (Just _, Just _) => unreachable {function = "toInferredType"} {reason = "post-parse validation rejects this array length: " ++ raw}
        (Nothing, _) => unreachable {function = "toInferredType"} {reason = "the lexer accepted a malformed integer literal: " ++ raw}
    literalArrayLength _ = Nothing

