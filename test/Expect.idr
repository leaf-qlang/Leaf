||| Unit tests that report what went wrong. A failing test prints the value it
||| expected and the value it got, and a suite returns whether it passed
||| instead of exiting, so the runner can go on to the remaining suites.
|||
||| The API mirrors the `Test.Simple` library it replaces: write `runTests $ Test.do` followed by one
||| test per line, as in ``test "name" $ actual `shouldBe` expected``.
module Expect

import Data.Maybe

%default total

||| The value a test computed, paired with the value it should equal.
public export
record Expectation a where
  constructor MkExpectation
  actual : a
  expected : a

export infixl 9 `shouldBe`

export
shouldBe : a -> a -> Expectation a
shouldBe = MkExpectation

||| A named test, with the report to print if it failed.
export
record TestResult where
  constructor MkTestResult
  name : String
  failure : Maybe String

export
test : Eq a => Show a => String -> Expectation a -> List TestResult
test name (MkExpectation actual expected) =
  [MkTestResult name (if actual == expected then Nothing else Just report)]
  where
    report : String
    report = "    expected: \{show expected}\n    actual:   \{show actual}"

||| One test per case: `run` applied to each input should give the value paired
||| with it. Each test is named after `name` and its input.
|||
||| Independent cases get a test each, through this or a table of their own, so
||| a failure names the case. One test holds several values only when they are
||| asserted together, as a contrast or as parts of one source.
export
testEach : Eq b => Show b => String -> (String -> b) -> List (String, b) -> List TestResult
testEach name run = concatMap check
  where
    check : (String, b) -> List TestResult
    check (input, expected) = test "\{name}: \{input}" (run input `shouldBe` expected)

namespace Test
  export
  (>>) : List TestResult -> List TestResult -> List TestResult
  (>>) = (++)

colored : (colorCode : String) -> String -> String
colored colorCode text = "\ESC[\{colorCode}m\{text}\ESC[0m"

printResult : TestResult -> IO ()
printResult (MkTestResult name Nothing) = putStrLn (colored "32" "success: \{name}")
printResult (MkTestResult name (Just report)) = do
  putStrLn (colored "31" "failure: \{name}")
  putStrLn report

||| Runs the tests in order and reports each one. True if they all passed.
export
runTests : List TestResult -> IO Bool
runTests results = do
  traverse_ printResult results
  let passed = length (filter (isNothing . failure) results)
  putStrLn "Done \{show passed}/\{show (length results)}"
  pure (passed == length results)
