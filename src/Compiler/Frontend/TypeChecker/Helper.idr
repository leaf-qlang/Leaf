module Compiler.Frontend.TypeChecker.Helper

import Compiler.Helper
import Compiler.Frontend.TypeChecker.Data
import Compiler.Frontend.TypeChecker.Type
import Data.List
import Data.List1
import Data.Maybe
import Compiler.Frontend.ASTData
import Compiler.Frontend.ASTPhases
import Compiler.Frontend.Syntax.AST
import Compiler.Frontend.Syntax.Common
import Compiler.Frontend.Syntax.Literal
import Compiler.Frontend.Syntax.Name
import Compiler.Frontend.Syntax.Operator
import Compiler.Frontend.Syntax.Type
import Compiler.Frontend.Token

%default total

pathReferencedSymbolId : {astPhase : AstPhase} -> Path astPhase -> SymbolId
pathReferencedSymbolId {astPhase = SurfaceAstPhase} _ = unreachable __FILE__ {function = "pathReferencedSymbolId"} {reason = "paths are not yet resolved"}
pathReferencedSymbolId {astPhase = CanonicalAstPhase} _ = unreachable __FILE__ {function = "pathReferencedSymbolId"} {reason = "paths are not yet resolved"}
pathReferencedSymbolId {astPhase = ResolvedAstPhase} resolvedPath = resolvedPath.nodeValue.referencedSymbolId
pathReferencedSymbolId {astPhase = TypedAstPhase} typedPath = typedPath.nodeValue.referencedSymbolId

export
writtenLeafTypeM :  {astPhase : AstPhase} -> Monad m => (resolveLength : Expr astPhase -> m Nat) -> Ty astPhase (Expr astPhase) -> m LeafType
writtenLeafTypeM resolveLength typeAstNode@(MkAstNode _ _ typeNode) =
  case typeNode of
    TyPrimitive primitiveName => pure (LeafPrimitiveType primitiveName)
    TyPath typePath           => pure (LeafNamedType (pathReferencedSymbolId typePath))
    TyUnit                    => pure LeafUnitType
    TyParenthesized innerType => recur innerType
    TyTuple elementTypes      => LeafTupleType <$> traverse recur elementTypes
    TyArray elementType sizeExpression => LeafArrayType <$> recur elementType <*> resolveLength sizeExpression
    TySlice elementType => LeafSliceType <$> recur elementType
    TyReference borrowKind referencedType => quantumUsageFreeReference borrowKind.nodeValue <$> recur referencedType
    TyQualified quantumUsageQualifier qualifiedType => LeafQuantumQualifiedType quantumUsageQualifier.nodeValue <$> recur qualifiedType
    TyFunction functionEffect functionParameters returnType =>
      LeafFunctionType (maybe EffectGeneral (.nodeValue) functionEffect) []
        <$> traverse (\functionTypeParameter => recur functionTypeParameter.nodeValue.parameterType) functionParameters
        <*> maybe (pure LeafUnitType) recur returnType
  where
    recur : Ty astPhase (Expr astPhase) -> m LeafType
    recur nestedType = writtenLeafTypeM resolveLength (assert_smaller typeAstNode nestedType)

export
toInferredType : {astPhase : AstPhase} -> Ty astPhase (Expr astPhase) -> InferredType
toInferredType = maybe TypeNotYetResolved ResolvedType . writtenLeafTypeM literalArrayLength
  where
    literalArrayLength : Expr astPhase -> Maybe Nat
    literalArrayLength (MkAstNode _ _ (ExprLiteral (MkAstNode _ _ (LiteralIntegerRaw rawLiteralText)))) =
      case (integerLiteralValue rawLiteralText, arrayLengthProblem rawLiteralText) of
        (Just arrayLength, Nothing) => if arrayLength <= usizeMaximum then Just arrayLength else Nothing
        (Just _, Just _) => unreachable __FILE__ {function = "toInferredType"} {reason = "post-parse validation rejects this array length: " ++ rawLiteralText}
        (Nothing, _) => unreachable __FILE__ {function = "toInferredType"} {reason = "the lexer accepted a malformed integer literal: " ++ rawLiteralText}
    literalArrayLength _ = Nothing

