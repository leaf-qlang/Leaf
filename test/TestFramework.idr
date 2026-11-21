||| Unit tests that report what went wrong. A failing test prints the value it
||| expected and the value it got, and a suite returns whether it passed
||| instead of exiting, so the runner can go on to the remaining suites.
module TestFramework

import Data.Maybe

%default total

public export
record Diagnostic a where
  constructor MkDiagnostic
  actualValue : a
  expectedValue : a

export infixl 9 `shouldBe`

export
shouldBe : a -> a -> Diagnostic a
shouldBe = MkDiagnostic

export
record TestResult where
  constructor MkTestResult
  testName : String
  failureReport : Maybe String

export
test : Eq a => Show a => String -> Diagnostic a -> List TestResult
test testName (MkDiagnostic actualValue expectedValue) =
  [
    MkTestResult testName (if actualValue == expectedValue then Nothing else Just mismatchReport)
  ]
  where
    mismatchReport = "    expected: \{show expectedValue}\n    actual:   \{show actualValue}"

||| One test per case: `computeActualValue` applied to each input should give
||| the value paired with it. Each test is named after `testGroupName` and its input.
export
testEach : Eq b => Show b => String -> (String -> b) -> List (String, b) -> List TestResult
testEach testGroupName computeActualValue = concatMap testOneCase
  where
    testOneCase : (String, b) -> List TestResult
    testOneCase (caseInput, expectedValue) =
      test "\{testGroupName}: \{caseInput}" (computeActualValue caseInput `shouldBe` expectedValue)

namespace Test
  export
  (>>) : List TestResult -> List TestResult -> List TestResult
  (>>) = (++)

||| Wraps the text in an ANSI color escape code, then resets the color.
export
coloredText : (colorCode : String) -> (text : String) -> String
coloredText colorCode text = "\ESC[\{colorCode}m\{text}\ESC[0m"

printTestResult : TestResult -> IO ()
printTestResult (MkTestResult testName Nothing) = putStrLn (coloredText {colorCode = "32"} {text = "success: \{testName}"})
printTestResult (MkTestResult testName (Just failureReport)) = do
  putStrLn (coloredText {colorCode = "31"} {text = "failure: \{testName}"})
  putStrLn failureReport

export
runTests : List TestResult -> IO Bool
runTests testResults = do
  traverse_ printTestResult testResults
  let passedTestCount = length (filter (isNothing . failureReport) testResults)
  putStrLn "Done \{show passedTestCount}/\{show (length testResults)}"
  -- True if all tests pass
  pure (passedTestCount == length testResults)
