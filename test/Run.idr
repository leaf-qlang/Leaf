module Run

import Data.String
import System

import Backend.OpenQasm3SerializerTest
import DSL.IntrinsicProofsTest
import DSL.TypeLevelReductionTest
import Examples.CompileCodeExamples
import Examples.CompileCodeExamplesTest
import Desugarer.DesugaringTest
import TestFramework
import Lexer.LexerTest
import Parser.ExpressionParseTest
import Parser.FunctionParseTest
import Parser.TopModuleParseTest
import ScopeAndNameResolution.PreludeTest
import ScopeAndNameResolution.ResolveTest
import ScopeAndNameResolution.ValidationTest
import TypeChecker.NumericTest
import TypeChecker.TypeTranslationTest
import Utils.ASTDebugPrinterTest
import Utils.ASTPrettyPrinterTest
import Validator.PostParseValidationTest

suites : List (String, IO Bool)
suites =
  [ ("Lexer.LexerTest", runLexerTests)
  , ("Backend.OpenQasm3SerializerTest", runSerializerTests)
  , ("Parser.ExpressionParseTest", runExpressionParseTests)
  , ("Utils.ASTDebugPrinterTest", runASTDebugPrinterTests)
  , ("Utils.ASTPrettyPrinterTest", runASTPrettyPrinterTests)
  , ("Parser.FunctionParseTest", runFunctionParseTests)
  , ("Parser.TopModuleParseTest", runTopModuleParseTests)
  , ("Validator.PostParseValidationTest", runPostParseValidationTests)
  , ("Desugarer.DesugaringTest", runDesugaringTests)
  , ("ScopeAndNameResolution.ResolveTest", runSymbolAndScopeResolutionTests)
  , ("ScopeAndNameResolution.PreludeTest", runPreludeFunctionsResolutionTests)
  , ("ScopeAndNameResolution.ValidationTest", runResolutionValidationTests)
  , ("TypeChecker.NumericTest", runNumericTests)
  , ("TypeChecker.TypeTranslationTest", runTypeTranslationTests)
  , ("Examples.CompileCodeExamplesTest", runCompileCodeExamplesTests)
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
    [] => putStrLn (coloredText {colorCode = "94"} {text = "All tests completed."})  -- light blue
    failed => do
      putStrLn (coloredText {colorCode = "38;5;169"} {text = "Failing suites: \{joinBy ", " failed}"})  -- pink
      exitFailure
