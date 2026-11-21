module Examples.CompileCodeExamplesTest

import TestFramework

import Compiler.Frontend.ScopeAndNameResolver.Data
import Main

%default total

-- Runs the same pipeline as the leaf executable, discarding the resolved module.
compileFixture : String -> Either String ()
compileFixture sourceText = map (const ()) (compileSource "test-fixture.rs" sourceText)

isFailure : Either String () -> Bool
isFailure (Left _)  = True
isFailure (Right _) = False

export
runCompileCodeExamplesTests : IO Bool
runCompileCodeExamplesTests = runTests $ Test.do

  test "the source compilation pipeline accepts a valid program" $
    compileFixture "fn f() {}" `shouldBe` Right ()

  test "the source compilation pipeline desugars and resolves local and prelude names" $
    compileFixture "fn f() { let mut x = 1; x += 2; sin(x) }" `shouldBe` Right ()

  test "the source compilation pipeline reports unresolved names" $
    compileFixture "fn f() { missing; }" `shouldBe`
      Left "Could not find a matching declaration for this name: 'missing' in 'test-fixture.rs:1:10'."

  test "the source compilation pipeline resolves quantum gate calls" $
    compileFixture "fn f() { let q = qalloc(); H(&q); X(&q); U1(0.25, &q); measr(q) }" `shouldBe` Right ()

  test "the source compilation pipeline reports both duplicate declaration positions" $
    compileFixture "fn f() {}\nfn f() {}" `shouldBe`
      Left "A duplicate declaration for name: 'f' declared in 'test-fixture.rs:2:4' was found; the previous declaration is in 'test-fixture.rs:1:4'."

  test "the source compilation pipeline reports mutable bindings that shadow constants" $
    compileFixture "const N: i32 = 1;\nfn f() { let mut N = 2; }" `shouldBe`
      Left "The mutable binding for name: 'N' in 'test-fixture.rs:2:18' cannot shadow the constant declared in 'test-fixture.rs:1:7'."

  test "the source compilation pipeline accepts repeated constant patterns" $
    compileFixture "const U: () = (); fn f(U: (), U: ()) { let (U, U) = ((), ()); for U in [()] {} }"
      `shouldBe` Right ()

  test "the source compilation pipeline reports locals used in constant expressions" $
    compileFixture "fn f(n: i32) {\n  [0; n];\n}" `shouldBe`
      Left "The local: 'n' used in 'test-fixture.rs:2:7' is not a constant and cannot be used in an array length, in a repeat count from an array declaration or in the qubits register size argument for qalloc; it is declared in 'test-fixture.rs:1:6'."

  -- The lexer never sees the filename, so the pipeline prefixes it.
  test "the source compilation pipeline reports lexer failures" $
    compileFixture "@" `shouldBe`
      Left "test-fixture.rs: Lexer error at 1:1: Unsupported character U+0040 `@`"

  test "the source compilation pipeline reports parser failures" $
    isFailure (compileFixture "fn f( {}") `shouldBe` True

  test "the source compilation pipeline reports every validation failure" $
    compileFixture "fn f() {break; continue;}" `shouldBe`
      Left
        ( "Validation errors:\n" ++
          "test-fixture.rs:1:9: `break` found outside of a loop\n" ++
          "test-fixture.rs:1:16: `continue` found outside of a loop"
        )
