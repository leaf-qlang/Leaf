module Parser.Helper

import Data.String
import Text.Bounds

import Compiler.Frontend.ASTPhases
import Compiler.Frontend.Lexer.Error
import Compiler.Frontend.Lexer.Lexer
import Compiler.Frontend.Parser.Error
import Compiler.Frontend.Parser.Parser
import Compiler.Frontend.Source
import Compiler.Frontend.Syntax.AST
import Compiler.Frontend.Token
import Compiler.Frontend.Utils.ASTDebugPrinter
import Compiler.Frontend.Utils.ASTPrettyPrinter
import TestFramework
import public Parser.DebugDump
import public Parser.FixtureSource

%default total

--------------------------------------------------------------------------------
-- Parsing fixtures
--
-- Every helper that takes source returns `Left` with the reason when the
-- source does not get as far as the helper needs, so a failing test reports
-- why instead of a bare `Nothing`.
--------------------------------------------------------------------------------

lexBounded : String -> Either String (List (Bounded Token))
lexBounded sourceText = case lexFile sourceText of
  Left lexerError => Left "lexer error: \{lexerError.val}"
  Right tokens => Right tokens

||| The fixture's tokens, without their bounds.
export
lexFixture : String -> Either String (List Token)
lexFixture = map (map val) . lexBounded

||| The parser's verdict, once the fixture lexes.
parseFixture : String -> Either String (Either (Located ParseError) SurfaceSourceFile)
parseFixture = map (parseFile fixtureFile) . lexBounded

export
lexThenParse : String -> Either String SurfaceSourceFile
lexThenParse sourceText = parseFixture sourceText >>= either (Left . showParseError) Right

export
parseAndPrettyPrintStrict : String -> Either String String
parseAndPrettyPrintStrict = map showSourceFileStrict . lexThenParse

export
parseAndPrettyPrintLax : String -> Either String String
parseAndPrettyPrintLax = map showSourceFileLax . lexThenParse

||| A source already in the printer's spacing, which strict style prints back
||| exactly as written.
export
printsUnchangedStrict : String -> Diagnostic (Either String String)
printsUnchangedStrict sourceText = parseAndPrettyPrintStrict sourceText `shouldBe` Right sourceText

||| A source already in the printer's spacing, which lax style prints back
||| exactly as written.
export
printsUnchangedLax : String -> Diagnostic (Either String String)
printsUnchangedLax sourceText = parseAndPrettyPrintLax sourceText `shouldBe` Right sourceText

||| The message the user is shown, which carries the file and the error's start,
||| paired with the span's end, which no message shows.
export
parseErrorDetails : String -> Either String (String, (Nat, Nat))
parseErrorDetails sourceText = parseFixture sourceText >>= either (Right . details) parsed
  where
    details : Located ParseError -> (String, (Nat, Nat))
    details locatedError = (showParseError locatedError, (locatedError.span.end.line, locatedError.span.end.column))

    parsed : SurfaceSourceFile -> Either String (String, (Nat, Nat))
    parsed sourceFile = Left "parsed without error as: \{showSourceFileStrict sourceFile}"

||| What `parseErrorDetails` gives for an error that starts at `start`, ends at
||| `end` and carries `message`.
export
parseErrorAt : (start : (Nat, Nat)) -> (end : (Nat, Nat)) -> (message : String) -> Either String (String, (Nat, Nat))
parseErrorAt (line, column) end message =
  Right ("Parse error at: \{fixtureFile}:\{show line}:\{show column}, with message: \{message}", end)

||| One test per source in which the name `z` stands where the parser expected
||| something else: the source, the column of `z` on its first line, and what
||| the message says was expected there.
export
misplacedNameTests : String -> List (String, Nat, String) -> List TestResult
misplacedNameTests testGroupName = testEach testGroupName parseErrorDetails . map expectation
  where
    expectation : (String, Nat, String) -> (String, Either String (String, (Nat, Nat)))
    expectation (sourceText, column, expectedDescription) =
      (sourceText, parseErrorAt (1, column) (1, S column) "expected \{expectedDescription}, but got identifier \"z\"")

--------------------------------------------------------------------------------
-- Printing in both styles
--------------------------------------------------------------------------------

export
inBothStyles : (PrettyStyle -> a) -> List a
inBothStyles render = map render [PrettyLax, PrettyStrict]

export
sameInBothStyles : (PrettyStyle -> a) -> a -> Diagnostic (List a)
sameInBothStyles render expected = inBothStyles render `shouldBe` [expected, expected]

--------------------------------------------------------------------------------
-- Dumping parsed fixtures
--------------------------------------------------------------------------------

||| Covering because the debug traversal is itself declared covering.
export
covering
debugAstOf : String -> Either String String
debugAstOf = map showAstDebug . lexThenParse

||| Surface IDs in structural pre-order, including names, tokens and literals.
export
covering
parseAndListNodeIds : String -> Either String (List Nat)
parseAndListNodeIds sourceText = debugAstOf sourceText >>= withIds
  where
    withIds : String -> Either String (List Nat)
    withIds dump = maybe (Left "a node heading has no ID in:\n\{dump}") Right (debugNodeSurfaceIds dump)
