module Run

import Data.String
import System

import CompileCodeExamples
import CompileCodeExamplesTest
import Desugarer.DesugaringTest
import Lexer.LexerTest
import Parser.ASTDebugPrinterTest
import Parser.ASTPrettyPrinterTest
import Parser.ExpressionParseTest
import Parser.FunctionParseTest
import Parser.PostParseValidationTest
import Parser.TopModuleParseTest
import ScopeAndNameResolution.PreludeTest
import ScopeAndNameResolution.ResolveTest
import ScopeAndNameResolution.ValidationTest
import TypeChecker.NumericTest
import TypeChecker.TypeTranslationTest

||| Each suite's module name and runner, in the order they run. A runner
||| reports whether all its tests passed. The `TypeChecker.Phases` suites and
||| `TypeChecker.TypeCheckTest` are left out until the type checker has no
||| holes left: they stop at the first one they reach.
suites : List (String, IO Bool)
suites =
  [ ("Lexer.LexerTest", runLexerTests)
  , ("Parser.ExpressionParseTest", runExpressionParseTests)
  , ("Parser.ASTDebugPrinterTest", runASTDebugPrinterTests)
  , ("Parser.ASTPrettyPrinterTest", runASTPrettyPrinterTests)
  , ("Parser.FunctionParseTest", runFunctionParseTests)
  , ("Parser.TopModuleParseTest", runTopModuleParseTests)
  , ("Parser.PostParseValidationTest", runPostParseValidationTests)
  , ("Desugarer.DesugaringTest", runDesugaringTests)
  , ("ScopeAndNameResolution.ResolveTest", runSymbolAndScopeResolutionTests)
  , ("ScopeAndNameResolution.PreludeTest", runPreludeFunctionsResolutionTests)
  , ("ScopeAndNameResolution.ValidationTest", runResolutionValidationTests)
  , ("TypeChecker.NumericTest", runNumericTests)
  , ("TypeChecker.TypeTranslationTest", runTypeTranslationTests)
  , ("CompileCodeExamplesTest", runCompileCodeExamplesTests)
  ]

||| Runs every suite, even after one fails, and then compiles the examples.
main : IO ()
main = do
  results <- for suites $ \(name, run) => do
    putStrLn "== \{name} =="
    passed <- run
    pure (name, passed)
  Right () <- discoverAndCompileExamples
    | Left err => do
        putStrLn err
        exitFailure
  case map fst (filter (not . snd) results) of
    [] => putStrLn "All tests completed."
    failed => do
      putStrLn "Failing suites: \{joinBy ", " failed}"
      exitFailure
