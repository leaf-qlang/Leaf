module Compiler.Helper

%default total

||| Crash on a language feature that the compiler does not support yet.
export
notImplemented : (sourceFile : String) -> (function : String) -> (feature : String) -> a
notImplemented sourceFile function feature =
  assert_total $ idris_crash $
    sourceFile ++ ", " ++ function ++ ": not yet implemented: " ++ feature ++ "."

||| Crash on a violated internal invariant: a compiler bug, not invalid Leaf source.
export
unreachable : (sourceFile : String) -> (function : String) -> (reason : String) -> a
unreachable sourceFile function reason =
  assert_total $ idris_crash $
    sourceFile ++ ", " ++ function ++ ": internal error: " ++ reason ++ "."
