module Parser.TopModuleParseTest

import TestFramework
import Parser.Helper

%default total

||| Top-level items the parser rejects as not yet supported: the keyword that
||| starts each one, the rest of it, and the message, which spans the keyword.
unsupportedItems : List (String, String, String)
unsupportedItems =
  [ ("mod", " my_library;", "Modules are not yet supported.")
  , ("use", " my_library::helper;", "Use statements are not yet supported.")
  , ("enum", " Result {}", "Enums are not yet supported.")
  , ("qenum", " QResult {}", "Qenums are not yet supported.")
  , ("struct", " Point {}", "Structs are not yet supported.")
  , ("impl", " Point {}", "Impl blocks and structs are not yet supported.")
  ]

unsupportedItemTests : List TestResult
unsupportedItemTests = concatMap rejectionTest unsupportedItems
  where
    rejectionTest : (String, String, String) -> List TestResult
    rejectionTest (keyword, followingText, message) =
      test "\{keyword}\{followingText} is rejected: \{message}" $
        parseErrorDetails "\{keyword}\{followingText}" `shouldBe` parseErrorAt (1, 1) (1, 1 + length keyword) message

||| Declaration prefixes after which an unsupported item keeps its own message,
||| with the column at which the item's keyword starts.
itemPrefixes : List (String, Nat)
itemPrefixes = [("pub ", 5), ("general ", 9), ("const general ", 15)]

unsupportedAfterPrefixTests : List TestResult
unsupportedAfterPrefixTests = testEach "an unsupported item after a prefix keeps its message" parseErrorDetails $ do
  (itemPrefix, column) <- itemPrefixes
  (keyword, followingText, message) <- unsupportedItems
  pure (itemPrefix ++ keyword ++ followingText, parseErrorAt (1, column) (1, column + length keyword) message)

export
runTopModuleParseTests : IO Bool
runTopModuleParseTests = runTests $ Test.do

  test "empty input parses as an empty output" $
    printsUnchangedStrict ""

  test "input containing only ordinary comments parses as an empty output" $
    parseAndPrettyPrintStrict "// nothing here\n/* still nothing */" `shouldBe` Right ""

  unsupportedItemTests

  test "a constant declaration parses" $
    printsUnchangedStrict "const N: i64 = 4;"

  test "a constant may be public" $
    printsUnchangedStrict "pub const MAX_USERS: i16 = 100;"

  test "constant declarations accept array types with expression lengths" $
    printsUnchangedLax "const A: [i32; 2 + 2] = [1, 2, 3, 4];"

  test "constant declarations report a missing constant name" $
    parseErrorDetails "const struct Point {}" `shouldBe`
      parseErrorAt (1, 7) (1, 13) "expected 'constant name', but got keyword struct"

  test "constant declarations require a colon after the name" $
    parseErrorDetails "const N i64 = 4;" `shouldBe`
      parseErrorAt (1, 9) (1, 12) "Expected `:` after constant name, found instead: `i64`."

  test "constant declarations require an equals sign after the type" $
    parseErrorDetails "const N: i64 4;" `shouldBe`
      parseErrorAt (1, 14) (1, 15) "Expected `=` in const declaration, found instead: `4`."

  test "constant declarations require a semicolon after the value" $
    parseErrorDetails "const N: i64 = 4 }" `shouldBe`
      parseErrorAt (1, 18) (1, 19) "Expected `;` after const declaration, found instead: `}`."

  unsupportedAfterPrefixTests

  testEach "node identifiers account for each declaration prefix modifier" parseAndListNodeIds
    [ ("fn f() {}", Right [0, 1, 2, 3])
    , ("pub fn f() {}", Right [0, 1, 2, 3, 4])
    , ("const fn f() {}", Right [0, 1, 2, 3, 4])
    , ("pub const fn f() {}", Right [0, 1, 2, 3, 4, 5])
    , ("pub const unitary fn f() {}", Right [0, 1, 2, 3, 4, 5, 6])
    , ("#[qasm_gate]\nfn f() {}", Right [0, 1, 2, 3, 4, 5])
    ]

  test "outer doc comments are not yet supported" $
    parseErrorDetails "/// docs\n" `shouldBe`
      parseErrorAt (1, 1) (1, 9) "Outer doc comments are not yet supported."

  test "inner doc comments are not yet supported" $
    parseErrorDetails "//! module docs" `shouldBe`
      parseErrorAt (1, 1) (1, 16) "Inner doc comments are not yet supported."

  test "unexpected top-level tokens report the token" $
    parseErrorDetails "let i = 1;" `shouldBe`
      parseErrorAt (1, 1) (1, 4) ("Unexpected token: `let` at module level. Only function and " ++
                                  "constant declarations are currently supported.")

  test "unexpected non-keyword top-level tokens report the token" $
    parseErrorDetails "foo" `shouldBe`
      parseErrorAt (1, 1) (1, 4) ("Unexpected token: `foo` at module level. Only function and " ++
                                  "constant declarations are currently supported.")