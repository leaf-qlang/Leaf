module Run

import System

import CompileCodeExamples
import CompileCodeExamplesTest
import Desugarer.DesugaringTest
import Lexer.LexerTest
import Parser.ValidationTests
import Parser.ExpressionParseTest
import Parser.FunctionParseTest
import Parser.TopModuleParseTest
import ScopeAndNameResolution.ValidationTest
import ScopeAndNameResolution.ResolveTest
import ScopeAndNameResolution.PreludeTest
import TypeChecker.NumericTest
import TypeChecker.TypeTranslationTest

main : IO ()
main = do
  putStrLn "== Lexer.LexerTest =="
  runLexerTests
  putStrLn "== Parser.ExpressionParseTest =="
  runExpressionParseTests
  putStrLn "== Parser.FunctionParseTest =="
  runFunctionParseTests
  putStrLn "== Parser.TopModuleParseTest =="
  runTopModuleParseTests
  putStrLn "== Parser.ValidationTests =="
  runPostParseValidationTests
  putStrLn "== Desugarer.DesugaringTest =="
  runDesugaringTests
  putStrLn "== ScopeAndNameResolution.ResolveTest =="
  runSymbolAndScopeResolutionTests
  putStrLn "== ScopeAndNameResolution.PreludeTest =="
  runPreludeFunctionsResolutionTests
  putStrLn "== ScopeAndNameResolution.ValidationTest =="
  runResolutionValidationTests
  putStrLn "== TypeChecker.NumericTest =="
  runNumericTests
  putStrLn "== TypeChecker.TypeTranslationTest =="
  runTypeTranslationTests
  putStrLn "== CompileCodeExamplesTest =="
  runCompileCodeExamplesTests
  Right () <- discoverAndCompileExamples
    | Left err => do
        putStrLn err
        exitFailure
  putStrLn "All tests completed."
