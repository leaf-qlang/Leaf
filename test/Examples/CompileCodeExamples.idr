module Examples.CompileCodeExamples

import Data.String
import System.Directory
import System.File

import Compiler.Frontend.ScopeAndNameResolver.Data
import Main

compileLeafFile : String -> IO (Either String ())
compileLeafFile programFile = do
  readResult <- readFile programFile
  case readResult of
    Left fileError => pure $ Left $ "Failed to read \{programFile}: " ++ show fileError
    Right sourceText => pure $ map (const ()) (compileSource programFile sourceText)

compileLeafFiles : String -> List String -> IO (Either String ())
compileLeafFiles examplesDirectory [] = do
  putStrLn "Finished compiling all code examples."
  pure $ Right ()
compileLeafFiles examplesDirectory (fileName :: fileNames) = do
  compilationResult <- compileLeafFile $ examplesDirectory ++ "/" ++ fileName
  case compilationResult of
    Left errorMessage => pure $ Left errorMessage
    Right () => 
      do
        putStrLn $ "Successfully compiled: " ++ fileName
        compileLeafFiles examplesDirectory fileNames

export
discoverAndCompileExamples : IO (Either String ())
discoverAndCompileExamples = do
  let examplesDirectory = "examples"
  Right directoryEntries <- listDir examplesDirectory
    | Left errorMessage => pure $ Left $ "Failed to list \{examplesDirectory}: " ++ show errorMessage
  -- Example 8 demonstrates quantum conditionals, which the parser rejects
  -- explicitly until that language feature is implemented.
  let codeExampleFiles =
        filter
          (\fileName =>
            isSuffixOf ".rs" fileName &&
            fileName /= "08_deutsch_jozsa_using_quantum_conditional.rs")
          directoryEntries
  compileLeafFiles examplesDirectory (sort codeExampleFiles)
