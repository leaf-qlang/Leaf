module ScopeAndNameResolution.Helper

import Compiler.Frontend.Desugarer.Desugar
import Compiler.Frontend.ScopeAndNameResolver.Data
import Compiler.Frontend.ScopeAndNameResolver.Resolve
import Compiler.Frontend.ScopeAndNameResolver.Validate
import Compiler.Frontend.ASTData
import Compiler.Frontend.ASTPhases
import Compiler.Frontend.Lexer.Error
import Compiler.Frontend.Lexer.Lexer
import Compiler.Frontend.Parser.Error
import Compiler.Frontend.Parser.Parser
import Compiler.Frontend.Validator.PostParseValidation
import Compiler.Frontend.Source
import Compiler.Frontend.Syntax.AST
import Compiler.Frontend.Token
import Text.Bounds

import Data.List
import Data.SnocList
import Data.SortedMap

%default total

public export
data FixtureError
  = LexingFailure String
  | ParsingFailure String
  | ValidationFailure (List String)
  | ResolutionFailure ResolutionError
  | InvariantFailure (List String)

public export
Show FixtureError where
  show (LexingFailure message) = "Lexing: " ++ message
  show (ParsingFailure message) = "Parsing: " ++ message
  show (ValidationFailure messages) = "Validation: " ++ show messages
  show (ResolutionFailure resolutionError) = "Resolution: " ++ show resolutionError
  show (InvariantFailure messages) = "Resolution invariants: " ++ show messages

export
canonicalSource : String -> Either FixtureError (SourceFile CanonicalAstPhase)
canonicalSource sourceText = do
  tokens <- case lexFile sourceText of
    Left lexerError => Left (LexingFailure (renderLexerError lexerError))
    Right tokens => Right tokens
  surfaceSourceFile <- case parseFile "resolution-test.lf" tokens of
    Left parseError => Left (ParsingFailure (showParseError parseError))
    Right surfaceSourceFile => Right surfaceSourceFile
  case validateSourceFile surfaceSourceFile of
    [] => Right ()
    validationErrors => Left (ValidationFailure (map interpolate validationErrors))
  Right (desugarSurfaceSyntax surfaceSourceFile)

-- Every successful fixture, including manually adjusted canonical ASTs, must
-- pass table validation. Failures retain the phase and original diagnostic.
export
resolveCanonicalSource : SourceFile CanonicalAstPhase -> Either FixtureError ResolvedModule
resolveCanonicalSource canonicalSourceFile = do
  resolvedModule <- case resolveCanonicalSyntax canonicalSourceFile of
    Left resolutionError => Left (ResolutionFailure resolutionError)
    Right resolvedModule => Right resolvedModule
  case validateResolvedModule resolvedModule of
    [] => Right resolvedModule
    invariantErrors => Left (InvariantFailure (map show invariantErrors))

export
resolveSource : String -> Either FixtureError ResolvedModule
resolveSource sourceText = canonicalSource sourceText >>= resolveCanonicalSource

export
resolvedSource : String -> Maybe ResolvedModule
resolvedSource sourceText = case resolveSource sourceText of
  Left _ => Nothing
  Right resolvedModule => Just resolvedModule

export
checkSource : String -> (ResolvedModule -> Maybe a) -> Either String a
checkSource sourceText inspect = case resolveSource sourceText of
  Left fixtureError => Left (show fixtureError)
  Right resolvedModule => case inspect resolvedModule of
    Nothing => Left ("Unexpected resolved AST or missing table entry for: " ++ sourceText)
    Just inspectedValue => Right inspectedValue

export
expectUnresolvedName : String -> Either String String
expectUnresolvedName sourceText = case resolveSource sourceText of
  Left (ResolutionFailure (UnresolvedName unresolvedName _)) => Right unresolvedName
  Left otherFailure => Left (show otherFailure)
  Right _ => Left "Expected UnresolvedName, but resolution succeeded"

export
kindText : SymbolKind -> String
kindText SymbolLocalBinding = "local"
kindText SymbolFunctionParameter = "parameter"
kindText SymbolFunction = "function"
kindText SymbolConstant = "constant"
kindText _ = "other"

export
spanKey : SourceSpan -> (String, Nat, Nat, Nat, Nat)
spanKey sourceSpan = (sourceSpan.file, sourceSpan.start.line, sourceSpan.start.column, sourceSpan.end.line, sourceSpan.end.column)

export
allReferences : ResolvedModule -> List SymbolReference
allReferences resolvedModule =
  sortBy (\firstReference, secondReference => compare (spanKey firstReference.occurrence.span) (spanKey secondReference.occurrence.span)) $
    concatMap (\(_, bucketReferences) => bucketReferences <>> []) (SortedMap.toList resolvedModule.tables.references)

export
valueReferences : ResolvedModule -> List SymbolReference
valueReferences resolvedModule = filter isValue (allReferences resolvedModule)
  where
    isValue : SymbolReference -> Bool
    isValue reference = case reference.role of
      ValueReference => True
      _ => False
