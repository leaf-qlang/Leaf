module Parser.TopModuleParseTest

import Expect
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
unsupportedItemTests = concatMap rejected unsupportedItems
  where
    rejected : (String, String, String) -> List TestResult
    rejected (keyword, rest, message) =
      test "\{keyword}\{rest} is rejected: \{message}" $
        parseErrorDetails "\{keyword}\{rest}" `shouldBe` parseErrorAt (1, 1) (1, 1 + length keyword) message

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

  test "struct declarations after pub visibility are not yet supported" $
    parseErrorDetails "pub struct Point {}" `shouldBe`
      parseErrorAt (1, 5) (1, 11) "Structs are not yet supported."

  test "impl blocks after a function effect are not yet supported" $
    parseErrorDetails "general impl Point {}" `shouldBe`
      parseErrorAt (1, 9) (1, 13) "Impl blocks and structs are not yet supported."

  test "impl blocks after const and a function effect are not yet supported" $
    parseErrorDetails "const general impl Point {}" `shouldBe`
      parseErrorAt (1, 15) (1, 19) "Impl blocks and structs are not yet supported."

  test "unsupported top-level items after a function effect preserve their error" $
    parseErrorDetails "general mod my_library;" `shouldBe`
      parseErrorAt (1, 9) (1, 12) "Modules are not yet supported."

  test "unsupported top-level items after const and a function effect preserve their error" $
    parseErrorDetails "const general mod my_library;" `shouldBe`
      parseErrorAt (1, 15) (1, 18) "Modules are not yet supported."

  test "non-keyword items after const and a function effect report the effect" $
    parseErrorDetails "const general foo" `shouldBe`
      parseErrorAt (1, 15) (1, 18) "Expected `fn` after `general` effect modifier, found instead: `foo`."

  test "node identifiers account for each declaration prefix modifier" $
    map parseAndListNodeIds
      [ "fn f() {}"
      , "pub fn f() {}"
      , "const fn f() {}"
      , "pub const fn f() {}"
      , "pub const unitary fn f() {}"
      , "#[qasm_gate]\nfn f() {}"
      ] `shouldBe`
      [ Right [0, 1, 2, 3]
      , Right [0, 1, 2, 3, 4]
      , Right [0, 1, 2, 3, 4]
      , Right [0, 1, 2, 3, 4, 5]
      , Right [0, 1, 2, 3, 4, 5, 6]
      , Right [0, 1, 2, 3, 4, 5]
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