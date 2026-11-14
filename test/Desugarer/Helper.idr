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

||| Start and end (line, column) of each multiplicity qualifier at an owned
||| position of the first function's first `let` annotation, after desugaring.
export
firstLetTypeQualifierSpans : String -> Maybe (List ((Nat, Nat), (Nat, Nat)))
firstLetTypeQualifierSpans inputProgram = do
  MkAstNode _ _ (MkSourceFileNode _ items) <- lexParseThenDesugar "test-fixture.rs" inputProgram
  MkAstNode _ _ (ItemFunction declaration) :: _ <- Just items
    | _ => Nothing
  let MkAstNode _ _ (MkBlockNode _ statements _) = declaration.functionBody
  MkAstNode _ _ (StatementLet (MkLetBindingNode _ _ (Just annotation) _)) :: _ <- Just statements
    | _ => Nothing
  Just (map (bounds . (.astInfo.span)) (mapMaybe positionQualifier (ownedPositions annotation)))
  where
    bounds : SourceSpan -> ((Nat, Nat), (Nat, Nat))
    bounds span = ((span.start.line, span.start.column), (span.end.line, span.end.column))
