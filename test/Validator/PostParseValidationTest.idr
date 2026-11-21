module Validator.PostParseValidationTest

import TestFramework

import Compiler.Frontend.ASTPhases
import Compiler.Frontend.Validator.PostParseValidation
import Compiler.Frontend.Syntax.AST
import Parser.Helper

%default total

validationMessages : String -> Either String (List String)
validationMessages = map (map interpolate . validateSourceFile) . lexThenParse

||| A validation message reported at a line and column of the fixture.
messageAt : (Nat, Nat) -> String -> String
messageAt (line, column) message = "\{fixtureFile}:\{show line}:\{show column}: \{message}"

mutQbitReferenceAt : (Nat, Nat) -> String
mutQbitReferenceAt position =
  messageAt position ("`mut` should never be written on a qbit reference; " ++
                      "qbit references are mutable by default")

||| A qualifier in a let's type annotation that the let already states.
repeatedQualifierAt : (Nat, Nat) -> (written : String) -> (onLet : String) -> String
repeatedQualifierAt position written onLet =
  messageAt position (("`\{written}` cannot be written in the type annotation because the `let` " ++
                       "already has the `\{onLet}` qualifier; " ++
                       "write the quantum usage qualifier in one place only"))

behindReferenceAt : (Nat, Nat) -> (qualifier : String) -> String
behindReferenceAt position qualifier =
  messageAt position ("`\{qualifier}` cannot be written behind a reference; " ++
                      "a reference borrows its referent without owning it")

||| An array length whose integer suffix is not `usize`.
nonUsizeLengthAt : (Nat, Nat) -> (suffix : String) -> String
nonUsizeLengthAt position suffix =
  messageAt position ("an array length must have type `usize`, but the suffix gives it type " ++
                      "`\{suffix}`; write a `usize` suffix, or none")

export
runPostParseValidationTests : IO Bool
runPostParseValidationTests = runTests $ Test.do

  test "unknown attributes are rejected after parsing" $
    validationMessages "#[unknown]\nfn f() {}" `shouldBe`
      Right [messageAt (1, 1) "unknown attribute `unknown` (supported: qasm_gate, qasm_def)"]

  test "mutable qbit references are rejected after parsing" $
    validationMessages "fn f(q: &mut qbit) {}" `shouldBe` Right [mutQbitReferenceAt (1, 9)]

  test "a quantum usage qualifier repeated in a let type annotation is rejected" $
    validationMessages "fn f() {let linear q: linear qbit = qalloc();}" `shouldBe`
      Right [repeatedQualifierAt (1, 23) "linear" "linear"]

  test "a conflicting quantum usage qualifier nested in a let type annotation is rejected" $
    validationMessages "fn f() {let linear (a, b): (affine qbit, qbit) = (qalloc(), qalloc());}" `shouldBe`
      Right [repeatedQualifierAt (1, 29) "affine" "linear"]

  test "a quantum usage qualifier written in one place only is accepted" $
    validationMessages ("fn f() {let linear a: qbit = qalloc(); let b: affine qbit = qalloc(); " ++
                        "let scratch c: affine qbit = qalloc();}") `shouldBe`
      Right []

  test "quantum usage qualifiers inside a function type in a let annotation are not repeats" $
    validationMessages ("fn f(g: fn(q: affine qbit) -> qbit) {let linear h: fn(q: affine qbit) " ++
                        "-> linear qbit = g;}") `shouldBe`
      Right []

  test "a quantum usage qualifier behind a reference in a let annotation is not reported as a repeat" $
    validationMessages "fn f(q: qbit) {let affine x: (qbit, &[linear qbit; 1]) = (qalloc(), &q);}" `shouldBe`
      Right [behindReferenceAt (1, 39) "linear"]

  test "a quantum usage qualifier in a referenced slice is rejected" $
    validationMessages "fn f(qs: &[linear qbit]) {}" `shouldBe`
      Right [behindReferenceAt (1, 12) "linear"]

  test "a quantum usage qualifier deep in a referenced tuple is rejected" $
    validationMessages "fn f(p: &(i32, [affine qbit; 2])) {}" `shouldBe`
      Right [behindReferenceAt (1, 17) "affine"]

  test "a quantum usage qualifier behind nested references is rejected once" $
    validationMessages "fn f(v: &[&[affine qbit]]) {}" `shouldBe`
      Right [behindReferenceAt (1, 13) "affine"]

  test "a quantum usage qualifier behind a mutable qbit reference is rejected with the mut" $
    validationMessages "fn f(qs: &mut [affine qbit]) {}" `shouldBe`
      Right
        [ mutQbitReferenceAt (1, 10)
        , behindReferenceAt (1, 16) "affine"
        ]

  test "quantum usage qualifiers in a referenced function type are allowed" $
    validationMessages "fn f(g: &fn(q: affine qbit) -> linear qbit) {}" `shouldBe` Right []

  test "a quantum usage qualifier on a qbit array element repeated in a let is rejected" $
    validationMessages "fn f() {let affine qs: [linear qbit; 2] = qalloc(2);}" `shouldBe`
      Right [repeatedQualifierAt (1, 25) "linear" "affine"]

  test "a signed suffix on a parenthesized array type length is rejected" $
    validationMessages "fn f(qs: [qbit; (3i8)]) {}" `shouldBe` Right [nonUsizeLengthAt (1, 18) "i8"]

  test "a signed suffix on a doubly parenthesized repeated array length is rejected" $
    validationMessages "fn f() {let xs = [0; ((3i8))];}" `shouldBe`
      Right [nonUsizeLengthAt (1, 24) "i8"]

  test "a u8 array length is rejected regardless of its value" $
    validationMessages "fn f(qs: [qbit; 256u8]) {}" `shouldBe` Right [nonUsizeLengthAt (1, 17) "u8"]

  test "usize and missing array length suffixes are accepted" $
    validationMessages ("fn f(qs: [qbit; 3usize], rs: [qbit; 0x2_usize], ss: " ++
                        "[qbit; 4], ts: [qbit; 3usize]) {let xs = [0; 4usize]; let ys = " ++
                        "[0; 0x5_usize];}") `shouldBe`
      Right []

  test "usize maximum is a valid count before object layout is checked" $
    validationMessages ("fn f(qs: [(); 18446744073709551615usize], rs: " ++
                        "[qbit; (0xff_usize)]) {let xs = [0; 65535usize]; let ys = " ++
                        "[(); 18446744073709551615usize];}") `shouldBe`
      Right []

  test "an array type length too large for usize is rejected" $
    validationMessages "fn f(qs: [qbit; 18446744073709551616usize]) {}" `shouldBe`
      Right [messageAt (1, 17) ("the array length `18446744073709551616usize` does not fit in " ++
                                "`usize`, whose largest value is 18446744073709551615")]

  testEach "every fixed-width integer suffix is rejected on an array length"
    (\suffix => validationMessages "fn f(xs: [(); 1\{suffix}]) {}")
    (map (\suffix => (suffix, Right [nonUsizeLengthAt (1, 15) suffix]))
      ["i8", "i16", "i32", "i64", "i128", "u8", "u16", "u32", "u64", "u128"])

  testEach "a non-usize suffix on a repeat count is rejected"
    (\count => validationMessages "fn f() {let xs = [0; \{count}];}")
    [ ("0x2_i128", Right [nonUsizeLengthAt (1, 22) "i128"])
    , ("0x1_0000_u16", Right [nonUsizeLengthAt (1, 22) "u16"])
    , ("3u64", Right [nonUsizeLengthAt (1, 22) "u64"])
    ]

  test "an explicit cast to usize in a length is left for typing" $
    validationMessages "fn f(xs: [i32; 3u64 as usize]) {let ys = [0; 3u8 as usize];}" `shouldBe`
      Right []

  test "break outside a loop is rejected after parsing" $
    validationMessages "fn f() {break;}" `shouldBe`
      Right [messageAt (1, 9) "`break` found outside of a loop"]

  test "continue outside a loop is rejected after parsing" $
    validationMessages "fn f() {continue;}" `shouldBe`
      Right [messageAt (1, 9) "`continue` found outside of a loop"]

  test "return in a constant initializer is rejected after parsing" $
    validationMessages "const N: i64 = return 4;" `shouldBe`
      Right [messageAt (1, 16) "`return` found outside of a function body"]

  test "a repeated attribute name is rejected after parsing" $
    validationMessages "#[qasm_gate]\n#[qasm_gate]\nfn f() {}" `shouldBe`
      Right [messageAt (2, 1) "attribute `qasm_gate` is already applied to this item"]

  test "two distinct known attributes together are rejected after parsing" $
    validationMessages "#[qasm_gate]\n#[qasm_def]\nfn f() {}" `shouldBe`
      Right [messageAt (2, 1) ("attribute `qasm_def` conflicts with another attribute already " ++
                               "applied to this item (qasm_gate and qasm_def are mutually " ++
                               "exclusive)")]

  -- Repeated names, constant patterns included, are reported by name resolution.
  testEach "repeated names pass post-parse validation" validationMessages $ map (\sourceText => (sourceText, Right []))
    [ "fn f(x: i32, x: i32) {}"
    , "fn f() {let (x, x) = pair;}"
    , "fn f() {let ((x, y), (z, x)) = value;}"
    , "fn f() {let (x, [y, x]) = value;}"
    , "const U: () = (); fn f(U: (), U: ()) {let (U, U) = ((), ());}"
    , "const U: () = (); fn f() {for U in [()] {} for U in [()] {}}" ]

  test "repeated parameter names do not skip type validation" $
    validationMessages "fn f(x: &mut qbit, x: &mut qbit) {}" `shouldBe`
      Right [mutQbitReferenceAt (1, 9), mutQbitReferenceAt (1, 23)]

  test "a control basis matching the number of controls is accepted" $
    validationMessages "fn f() {ctrl(q0, q1).on(bs\"10\").apply(H)(q2);}" `shouldBe` Right []

  test "a missing control basis is accepted" $
    validationMessages "fn f() {ctrl(q0, q1).apply(H)(q2); ctrl(q0) {H(q1);}}" `shouldBe` Right []

  test "a control basis shorter than the callable controls is rejected" $
    validationMessages "fn f() {ctrl(q0, q1).on(bs\"1\").apply(H)(q2);}" `shouldBe`
      Right [messageAt (1, 25) ("control basis contains 1 states, but the control expression " ++
                                "has 2 control qbits")]

  test "a control basis longer than the block controls is rejected" $
    validationMessages "fn f() {ctrl(q0).on(bs\"10\") {H(q1);}}" `shouldBe`
      Right [messageAt (1, 21) ("control basis contains 2 states, but the control expression " ++
                                "has 1 control qbits")]

  test "valid contextual forms pass post-parse validation" $
    validationMessages ("#[qasm_gate]\nfn f(x: &mut i32) {loop {break;} while ready {continue;} " ++
                        "return}") `shouldBe`
      Right []
