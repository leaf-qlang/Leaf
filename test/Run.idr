module Run

import Data.String
import System

import Backend.OpenQasm3SerializerTest
import DSL.CircuitBuilderReductionTest
import DSL.CircuitInverseReductionTest
import DSL.IntrinsicProofsTest
import DSL.RadiansArithmeticTest
import DSL.RadiansConstructionTest
import DSL.TypeLevelReductionTest
import DSL.Wrap4PiTest
import Examples.CompileCodeExamples
import Examples.CompileCodeExamplesTest
import Desugarer.DesugaringTest
import TestFramework
import Lexer.LexerTest
import Lexer.UnicodeNormalizationTest
import Parser.ExpressionParseTest
import Parser.FunctionParseTest
import Parser.TopModuleParseTest
import ScopeAndNameResolution.PreludeTest
import ScopeAndNameResolution.ResolveTest
import ScopeAndNameResolution.ValidationTest
import TypeChecker.InferenceVariableTest
import TypeChecker.NumericTest
import TypeChecker.Phases.BodyCheckTest
import TypeChecker.Phases.SignatureCheckTest
import TypeChecker.TypeTranslationTest
import Utils.ASTDebugPrinterTest
import Utils.ASTPrettyPrinterTest
import Validator.PostParseValidationTest

suites : List (String, IO Bool)
suites =
  [ ("Lexer.LexerTest", runLexerTests)
  , ("Lexer.UnicodeNormalizationTest", runUnicodeNormalizationTests)
  , ("Backend.OpenQasm3SerializerTest", runSerializerTests)
  , ("DSL.Wrap4PiTest", runWrap4PiTests)
  , ("DSL.RadiansArithmeticTest", runRadiansArithmeticTests)
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
--  , ("TypeChecker.InferenceVariableTest", runInferenceVariableTests)
  , ("TypeChecker.TypeTranslationTest", runTypeTranslationTests)
  , ("TypeChecker.Phases.SignatureCheckTest", runSignatureCheckTests)
--  , ("TypeChecker.Phases.BodyCheckTest", runBodyCheckTests)
  , ("Examples.CompileCodeExamplesTest", runCompileCodeExamplesTests)
  ]

||| Runs every suite, even after one fails, and then compiles the examples.
main : IO ()
main = do
  suiteResults <- for suites $ \(suiteName, runSuite) => do
    putStrLn "== \{suiteName} =="
    suitePassed <- runSuite
    pure (suiteName, suitePassed)
  Right () <- discoverAndCompileExamples
    | Left errorMessage => do
        putStrLn errorMessage
        exitFailure
  case map fst (filter (not . snd) suiteResults) of
    [] => putStrLn (coloredText {colorCode = "94"} {text = "All tests completed."})  -- light blue
    failedSuiteNames => do
      putStrLn (coloredText {colorCode = "38;5;169"} {text = "Failing suites: \{joinBy ", " failedSuiteNames}"})  -- pink
      exitFailure
