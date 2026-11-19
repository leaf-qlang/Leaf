module Parser.FunctionParseTest

import TestFramework
import Parser.Helper

%default total

--------------------------------------------------------------------------------
-- Messages
--------------------------------------------------------------------------------

fnAfterEffect : (found : String) -> String
fnAfterEffect found = "Expected `fn` after `general` effect modifier, found instead: `\{found}`."

scratchInType : String
scratchInType =
  "The `scratch` qualifier is only allowed on `let` bindings, not in types: write `let scratch q: qbit = ...`."

behindReference : (qualifier : String) -> String
behindReference qualifier =
  "The `\{qualifier}` qualifier cannot be written behind a reference: " ++
  "a reference borrows its referent without owning it, so remove the qualifier."

qualifiedArray : (qualifier : String) -> String
qualifiedArray qualifier =
  "The `\{qualifier}` qualifier cannot qualify an array or slice: " ++
  "qualify the qbits of an array instead, e.g. `[\{qualifier} qbit; 2]`."

qualifiedTuple : (qualifier : String) -> String
qualifiedTuple qualifier =
  "The `\{qualifier}` qualifier cannot qualify a parenthesized type or tuple: qualify each qbit " ++
  "inside it instead, e.g. `\{qualifier} qbit` or `(\{qualifier} qbit, \{qualifier} qbit)`."

--------------------------------------------------------------------------------
-- Fixtures
--------------------------------------------------------------------------------

||| Each parameter or type list whose element may be followed only by a
||| separator or by the list's closing token.
misplacedNames : List (String, Nat, String)
misplacedNames =
  [ ("fn f(a: i32 z: i32) {}", 13, "',' or ')'")
  , ("fn f(g: fn(a: i32 z: i32)) {}", 19, "',' or ')'")
  , ("fn f(g: fn(a z)) {}", 14, "':'")
  , ("fn f(p: (i32 z)) {}", 14, "',' or ')'")
  , ("fn f(p: (i32, i32 z)) {}", 19, "',' or ')'")
  , ("fn f(a: [i32 z]) {}", 14, "']' or ';'")
  ]

export
runFunctionParseTests : IO Bool
runFunctionParseTests = runTests $ Test.do

  -- Declarations and their modifiers

  test "an empty function parses" $
    printsUnchangedStrict "fn empty() { }"

  test "a function may be public" $
    printsUnchangedStrict "pub fn empty() { }"

  test "a function may declare a unit result" $
    printsUnchangedStrict "fn empty() -> () { }"

  test "a function may be unitary" $
    printsUnchangedStrict "unitary fn empty() -> () { }"

  test "a function may be uncompsafe" $
    printsUnchangedStrict "uncompsafe fn empty() { }"

  test "a function may be const and classical" $
    printsUnchangedLax "const classical fn multBy2(i: i32) -> i32 { 2 * i }"

  test "a const classical function may be public" $
    printsUnchangedLax "pub const classical fn multBy2(i: i32) -> i32 { 2 * i }"

  test "a public const function needs no effect" $
    printsUnchangedLax "pub const fn square(x: i64) -> i64 { x * x }"

  test "a unitary function may be public" $
    printsUnchangedStrict "pub unitary fn empty() -> () { }"

  -- Function bodies

  test "a function body may hold a statement" $
    printsUnchangedStrict "fn simple() { let i: i32 = 1; }"

  test "a function body may end in a value" $
    printsUnchangedStrict "fn simple_expression() -> i64 { 1 }"

  test "a function body must start with a brace" $
    parseErrorDetails "fn empty(); }" `shouldBe`
      parseErrorAt (1, 11) (1, 12) "Expected a braced block starting with `{`, found instead: `;`."

  test "a statement that is not last must end in a semicolon" $
    parseErrorDetails "fn simple() { let i: i32 = 1; 2 let j = 3;" `shouldBe`
      parseErrorAt (1, 33) (1, 36) "Expected `;` or `}`, found instead: `let`."

  -- Declaration errors

  test "a raw integer literal in place of a function name is described by kind" $
    parseErrorDetails "fn 5() {}" `shouldBe`
      parseErrorAt (1, 4) (1, 5) "expected 'function name', but got raw integer literal `5`"

  test "pub must be followed by a function or constant" $
    parseErrorDetails "pub let i = 1;" `shouldBe`
      parseErrorAt (1, 5) (1, 8) ("Expected function or constant declaration after `pub` " ++
                                  "visibility modifier, found instead: `let`.")

  testEach "a function effect must be followed by fn" parseErrorDetails
    [ ("general foo", parseErrorAt (1, 9) (1, 12) (fnAfterEffect "foo"))
    , ("pub general let i = 1;", parseErrorAt (1, 13) (1, 16) (fnAfterEffect "let"))
    , ("const general foo", parseErrorAt (1, 15) (1, 18) (fnAfterEffect "foo"))
    , ("const general let i = 1;", parseErrorAt (1, 15) (1, 18) (fnAfterEffect "let"))
    ]

  -- Attributes

  test "a function may have an attribute without arguments" $
    parseAndPrettyPrintStrict "#[qasm_gate]\nfn empty() -> () {}" `shouldBe`
      Right "#[qasm_gate]\nfn empty() -> () { }"

  test "a function may have an attribute with a string argument" $
    parseAndPrettyPrintStrict ("#[qasm_def(\"qasm_subroutine_name\")]\npub general fn empty() " ++
                               "-> () {}") `shouldBe`
      Right "#[qasm_def(\"qasm_subroutine_name\")]\npub general fn empty() -> () { }"

  test "a function may have two attributes" $
    parseAndPrettyPrintStrict ("#[qasm_gate]\n#[qasm_def(\"qasm_subroutine_name\")]\npub " ++
                               "general fn empty() -> () {}") `shouldBe`
      Right "#[qasm_gate]\n#[qasm_def(\"qasm_subroutine_name\")]\npub general fn empty() -> () { }"

  test "an attribute must be followed by a function declaration" $
    parseErrorDetails "#[qasm_gate]\nlet i = 1;" `shouldBe`
      parseErrorAt (2, 1) (2, 4) "Expected function declaration after attribute, found instead: `let`."

  test "attributes on const declarations are not yet supported" $
    parseErrorDetails "#[qasm_gate]\nconst N: i64 = 4;" `shouldBe`
      parseErrorAt (1, 1) (1, 2) "Attributes on const declarations are not yet supported."

  test "an attribute without its closing bracket is malformed" $
    parseErrorDetails "#[qasm_gate \nfn empty() -> () {}" `shouldBe`
      parseErrorAt (1, 1) (1, 2) "Malformed attribute."

  test "an attribute with extra content is malformed" $
    parseErrorDetails "#[qasm_gate bogus_name] \nfn empty() -> () {}" `shouldBe`
      parseErrorAt (1, 1) (1, 2) "Malformed attribute."

  test "an attribute with an argument but no closing bracket is malformed" $
    parseErrorDetails "#[qasm_def(\"qasm_subroutine_name\") \nfn empty() -> () {}" `shouldBe`
      parseErrorAt (1, 1) (1, 2) "Malformed attribute."

  test "an attribute with an argument and extra content is malformed" $
    parseErrorDetails "#[qasm_def(\"qasm_subroutine_name\") bogus_name] \nfn empty() -> () {}" `shouldBe`
      parseErrorAt (1, 1) (1, 2) "Malformed attribute."

  -- Parameters

  test "function parameters are normalized to `name: type`" $
    parseAndPrettyPrintStrict "fn add(i : i32, point : (i32, i32)) {}" `shouldBe`
      Right "fn add(i: i32, point: (i32, i32)) { }"

  test "function parameters accept a trailing comma" $
    parseAndPrettyPrintStrict "fn add(i: i32, point: (i32, i32),) {}" `shouldBe`
      Right "fn add(i: i32, point: (i32, i32)) { }"

  test "function parameters reject a missing middle parameter" $
    parseErrorDetails "fn add(i: i32,, point: i32) {}" `shouldBe`
      parseErrorAt (1, 15) (1, 16) "expected 'parameter name', but got symbol ,"

  misplacedNameTests "what may follow a parameter or a type is reported" misplacedNames

  test "a function parameter may be mutable" $
    printsUnchangedStrict "fn increment(mut x: i32) -> i32 { x += 1; x }"

  test "node identifiers follow source order through parameter types" $
    parseAndListNodeIds "fn f(c: a::b::c, r: &mut P) {}" `shouldBe`
      Right [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]

  test "function parameter outer doc comments are not yet supported" $
    parseErrorDetails "fn f(\n/// docs\nx: i32) {}" `shouldBe`
      parseErrorAt (2, 1) (2, 9) "Documentation comments on function parameters are not yet supported."

  -- Types

  test "parameter types may be names or paths" $
    printsUnchangedStrict "fn use_types(person: Person, config: my_module::Config) { }"

  test "path types may have more than two segments" $
    printsUnchangedStrict "fn use_types(value: root::inner::Leaf) { }"

  test "reference and slice types parse" $
    printsUnchangedStrict ("fn borrow(q: &qbit, person: &Person, mutable: &mut Person, values: " ++
                           "&[i32], output: &mut [i32]) { }")

  test "reference types require an inner type" $
    parseErrorDetails "fn f(x: &) {}" `shouldBe`
      parseErrorAt (1, 10) (1, 11) "expected 'a type declaration', but got symbol )"

  test "a builtin in place of a type is described by kind" $
    parseErrorDetails "fn f(x: measr) {}" `shouldBe`
      parseErrorAt (1, 9) (1, 14) "expected 'a type declaration', but got builtin measr"

  test "array parameter types accept expression lengths" $
    printsUnchangedLax "fn f(a: [i32; 2 + 2]) { }"

  test "function types may be parameter types" $
    printsUnchangedStrict ("general fn phase_kickback(oracle: unitary fn(qs: [qbit; " ++
                           "4], target: qbit) -> ([qbit; 4], qbit)) { }")

  test "a function type needs no effect or result" $
    printsUnchangedStrict "fn callback(f: fn(value: i32)) { }"

  test "a function type requires a parameter list" $
    parseErrorDetails "fn f(g: fn i32) {}" `shouldBe`
      parseErrorAt (1, 12) (1, 15) "expected '`(` after `fn`', but got primitive type i32"

  test "an effect in a type must be followed by fn" $
    parseErrorDetails "fn f(g: unitary i32) {}" `shouldBe`
      parseErrorAt (1, 17) (1, 20) "expected '`fn` after `unitary`', but got primitive type i32"

  test "a qstate parameter type is rejected by the parser" $
    parseErrorDetails "fn f(s: qstate) {}" `shouldBe`
      parseErrorAt (1, 9) (1, 15) "The `qstate` type is not yet supported."

  test "qstate nested in an array type is rejected by the parser" $
    parseErrorDetails "fn f(s: [qstate; 2]) {}" `shouldBe`
      parseErrorAt (1, 10) (1, 16) "The `qstate` type is not yet supported."

  test "a qstate local type is rejected by the parser" $
    parseErrorDetails "fn f() { let s: qstate; }" `shouldBe`
      parseErrorAt (1, 17) (1, 23) "The `qstate` type is not yet supported."

  -- Quantum qualifiers

  test "qbit types may be qualified" $
    printsUnchangedStrict "fn qualified(q: affine qbit, pair: (linear qbit, affine qbit)) { }"

  test "conflicting quantum usage qualifiers in a type are rejected" $
    parseErrorDetails "fn bad(q: linear affine qbit) {}" `shouldBe`
      parseErrorAt (1, 18) (1, 24) "Cannot combine `linear` and `affine` storage qualifiers."

  test "duplicate quantum usage qualifiers in a type are rejected" $
    parseErrorDetails "fn bad(q: affine affine qbit) {}" `shouldBe`
      parseErrorAt (1, 18) (1, 24) "Duplicate `affine` storage qualifier."

  test "scratch qualifier in a type is rejected" $
    parseErrorDetails "fn bad(q: scratch qbit) {}" `shouldBe`
      parseErrorAt (1, 11) (1, 18) scratchInType

  test "scratch qualifier after a quantum usage qualifier in a type is rejected" $
    parseErrorDetails "fn bad(q: linear scratch qbit) {}" `shouldBe`
      parseErrorAt (1, 18) (1, 25) scratchInType

  test "scratch qualifier in a nested type is rejected" $
    parseErrorDetails "fn bad(f: fn(value: qbit) -> (scratch qbit, qbit)) {}" `shouldBe`
      parseErrorAt (1, 31) (1, 38) scratchInType

  test "a qualifier followed by a non-type keyword is rejected" $
    parseErrorDetails "fn bad(q: linear if) {}" `shouldBe`
      parseErrorAt (1, 18) (1, 20) "The `linear` qualifier can only qualify `qbit`, not keyword if."

  test "qualified qbits may appear inside nested type forms" $
    printsUnchangedStrict "fn nested(q: fn(value: affine qbit) -> (linear qbit, [affine qbit])) { }"

  test "array elements may be qualified qbits" $
    printsUnchangedStrict "fn f(qs: [affine qbit; 2], rs: [[linear qbit; 2]; 3]) { }"

  test "a qualified array type is rejected" $
    parseErrorDetails "fn bad(qs: linear [qbit; 2]) {}" `shouldBe`
      parseErrorAt (1, 19) (1, 20) (qualifiedArray "linear")

  test "a qualified array type in a let annotation is rejected" $
    parseErrorDetails "fn f() { let qs: affine [qbit; 2] = qalloc(2); }" `shouldBe`
      parseErrorAt (1, 25) (1, 26) (qualifiedArray "affine")

  test "a qualifier directly behind a reference is rejected" $
    parseErrorDetails "fn bad(q: &affine qbit) {}" `shouldBe`
      parseErrorAt (1, 12) (1, 18) (behindReference "affine")

  test "a qualifier directly behind a mutable reference is rejected" $
    parseErrorDetails "fn bad(q: &mut linear qbit) {}" `shouldBe`
      parseErrorAt (1, 16) (1, 22) (behindReference "linear")

  test "a qualified slice behind a reference is rejected as behind a reference" $
    parseErrorDetails "fn bad(qs: &linear [qbit]) {}" `shouldBe`
      parseErrorAt (1, 13) (1, 19) (behindReference "linear")

  test "scratch directly behind a reference is rejected as scratch in a type" $
    parseErrorDetails "fn bad(q: &scratch qbit) {}" `shouldBe`
      parseErrorAt (1, 12) (1, 19) scratchInType

  test "a qualifier nested behind a reference is left to post-parse validation" $
    printsUnchangedStrict "fn f(qs: &[linear qbit]) { }"

  test "a qualified tuple type is rejected" $
    parseErrorDetails "fn bad(p: affine (qbit, qbit)) {}" `shouldBe`
      parseErrorAt (1, 18) (1, 19) (qualifiedTuple "affine")

  test "a qualified parenthesized qbit is rejected" $
    parseErrorDetails "fn bad(q: linear (qbit)) {}" `shouldBe`
      parseErrorAt (1, 18) (1, 19) (qualifiedTuple "linear")

  test "a qualified function type is rejected" $
    parseErrorDetails "fn bad(f: linear fn(q: qbit)) {}" `shouldBe`
      parseErrorAt (1, 18) (1, 20) "The `linear` qualifier can only qualify `qbit`, not keyword fn."

  -- Not yet supported

  test "function supports clauses are not yet supported" $
    parseErrorDetails "fn f() supports adjoint {}" `shouldBe`
      parseErrorAt (1, 8) (1, 16) "Function `supports` clauses are not yet supported."

  test "requires contract clauses are not yet supported" $
    parseErrorDetails "fn f() requires clean(q) {}" `shouldBe`
      parseErrorAt (1, 8) (1, 16) "Quantum contracts `requires` and/or `ensures` are not yet supported."

  test "ensures contract clauses are not yet supported" $
    parseErrorDetails "fn f() ensures basis(q, X) {}" `shouldBe`
      parseErrorAt (1, 8) (1, 15) "Quantum contracts `requires` and/or `ensures` are not yet supported."