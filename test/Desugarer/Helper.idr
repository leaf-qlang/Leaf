module Desugarer.Helper

import Text.Bounds

import Compiler.Frontend.Desugarer.Desugar
import Compiler.Frontend.ASTData
import Compiler.Frontend.ASTPhases
import Compiler.Frontend.Lexer.Error
import Compiler.Frontend.Lexer.Lexer
import Compiler.Frontend.Parser.Error
import Compiler.Frontend.Parser.Parser
import Compiler.Frontend.Source
import Compiler.Frontend.Syntax.AST
import Compiler.Frontend.Syntax.Common
import Compiler.Frontend.Syntax.Type
import Compiler.Frontend.Utils.ASTPrettyPrinter
import Compiler.Frontend.Token

%default total

export
lexParseThenDesugar : String -> String -> Maybe CanonicalSourceFile
lexParseThenDesugar fileName inputProgram =
  case lexFile inputProgram of
    Left _ => Nothing
    Right tokens => case parseFile fileName tokens of
      Left _ => Nothing
      Right surfaceSourceFile => Just (desugarSurfaceSyntax surfaceSourceFile)

export
desugarAndPrettyPrint : String -> Maybe String
desugarAndPrettyPrint inputProgram =
  map showSourceFileStrict (lexParseThenDesugar "test-fixture.rs" inputProgram)

||| Start and end (line, column) of each quantum usage qualifier at an owned
||| position of the first function's first `let` annotation, after desugaring.
export
firstLetTypeQualifierSpans : String -> Maybe (List ((Nat, Nat), (Nat, Nat)))
firstLetTypeQualifierSpans inputProgram = do
  MkAstNode _ _ (MkSourceFileNode _ sourceFileItems) <- lexParseThenDesugar "test-fixture.rs" inputProgram
  MkAstNode _ _ (ItemFunction functionDeclaration) :: _ <- Just sourceFileItems
    | _ => Nothing
  let MkAstNode _ _ (MkBlockNode _ bodyStatements _) = functionDeclaration.functionBody
  MkAstNode _ _ (StatementLet (MkLetBindingNode _ _ (Just typeAnnotation) _)) :: _ <- Just bodyStatements
    | _ => Nothing
  Just (map (spanCoordinates . (.astInfo.span)) (mapMaybe positionQualifier (ownedPositions typeAnnotation)))
  where
    spanCoordinates : SourceSpan -> ((Nat, Nat), (Nat, Nat))
    spanCoordinates qualifierSpan = ((qualifierSpan.start.line, qualifierSpan.start.column), (qualifierSpan.end.line, qualifierSpan.end.column))
