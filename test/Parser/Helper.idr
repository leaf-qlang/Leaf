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
import Expect
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
lexBounded source = case lexFile source of
  Left located => Left "lexer error: \{located.val}"
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
lexThenParse source = parseFixture source >>= either (Left . showParseError) Right

export
parseAndPrettyPrintStrict : String -> Either String String
parseAndPrettyPrintStrict = map showSourceFileStrict . lexThenParse

export
parseAndPrettyPrintLax : String -> Either String String
parseAndPrettyPrintLax = map showSourceFileLax . lexThenParse

||| A source already in the printer's spacing, which strict style prints back
||| exactly as written.
export
printsUnchangedStrict : String -> Expectation (Either String String)
printsUnchangedStrict source = parseAndPrettyPrintStrict source `shouldBe` Right source

||| A source already in the printer's spacing, which lax style prints back
||| exactly as written.
export
printsUnchangedLax : String -> Expectation (Either String String)
printsUnchangedLax source = parseAndPrettyPrintLax source `shouldBe` Right source

||| The message the user is shown, which carries the file and the error's start,
||| paired with the span's end, which no message shows.
export
parseErrorDetails : String -> Either String (String, (Nat, Nat))
parseErrorDetails source = parseFixture source >>= either (Right . details) parsed
  where
    details : Located ParseError -> (String, (Nat, Nat))
    details located = (showParseError located, (located.span.end.line, located.span.end.column))

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
misplacedNameTests name = testEach name parseErrorDetails . map expectation
  where
    expectation : (String, Nat, String) -> (String, Either String (String, (Nat, Nat)))
    expectation (source, column, expected) =
      (source, parseErrorAt (1, column) (1, S column) "expected \{expected}, but got identifier \"z\"")

--------------------------------------------------------------------------------
-- Printing in both styles
--------------------------------------------------------------------------------

export
inBothStyles : (PrettyStyle -> a) -> List a
inBothStyles render = map render [PrettyLax, PrettyStrict]

export
sameInBothStyles : (PrettyStyle -> a) -> a -> Expectation (List a)
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
parseAndListNodeIds source = debugAstOf source >>= withIds
  where
    withIds : String -> Either String (List Nat)
    withIds dump = maybe (Left "a node heading has no ID in:\n\{dump}") Right (debugNodeSurfaceIds dump)
