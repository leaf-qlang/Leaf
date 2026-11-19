||| Unit tests that report what went wrong. A failing test prints the value it
||| expected and the value it got, and a suite returns whether it passed
||| instead of exiting, so the runner can go on to the remaining suites.
module TestFramework

import Data.Maybe

%default total

public export
record Diagnostic a where
  constructor MkDiagnostic
  actual : a
  expected : a

export infixl 9 `shouldBe`

export
shouldBe : a -> a -> Diagnostic a
shouldBe = MkDiagnostic

export
record TestResult where
  constructor MkTestResult
  testName : String
  testFailure : Maybe String

export
test : Eq a => Show a => String -> Diagnostic a -> List TestResult
test name (MkDiagnostic actual expected) =
  [
    MkTestResult name (if actual == expected then Nothing else Just report)
  ]
  where
    report : String
    report = "    expected: \{show expected}\n    actual:   \{show actual}"

||| One test per case: `run` applied to each input should give the value paired
||| with it. Each test is named after `name` and its input.
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

||| Wraps the text in an ANSI color escape code, then resets the color.
export
coloredText : (colorCode : String) -> (text : String) -> String
coloredText colorCode text = "\ESC[\{colorCode}m\{text}\ESC[0m"

printResult : TestResult -> IO ()
printResult (MkTestResult name Nothing) = putStrLn (coloredText {colorCode = "32"} {text = "success: \{name}"})
printResult (MkTestResult name (Just report)) = do
  putStrLn (coloredText {colorCode = "31"} {text = "failure: \{name}"})
  putStrLn report

export
runTests : List TestResult -> IO Bool
runTests results = do
  traverse_ printResult results
  let passed = length (filter (isNothing . testFailure) results)
  putStrLn "Done \{show passed}/\{show (length results)}"
  -- True if all tests pass
  pure (passed == length results)
