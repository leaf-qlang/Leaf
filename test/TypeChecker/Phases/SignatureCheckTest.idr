module TypeChecker.Phases.SignatureCheckTest

import Expect

import Compiler.Frontend.TypeChecker.Data
import Compiler.Frontend.TypeChecker.Type
import Compiler.Frontend.Syntax.Common
import TypeChecker.Helper

%default total

--------------------------------------------------------------------------------
-- Pass A: signatures
--------------------------------------------------------------------------------
-- Pass A records the type of every function and constant without entering
-- bodies (plan §4). Signatures and bodies are checked in rounds (§2.3): a
-- signature can need a constant's value, a constant's value needs its checked
-- initializer, and a constant initializer can call a const fn whose body must
-- be checked first. Every test runs only phases A and B on a program that
-- passes the frontend; the expected result is acceptance or the first error
-- reported, compared through `show`. A signature diagnostic points at the
-- function's name, its effect keyword or the offending type or length.
--------------------------------------------------------------------------------

-- Function signatures
functionSignatureTests : List TestResult
functionSignatureTests = Test.do
  test "a function with primitive parameters and result type-checks" $
    signaturesAndBodiesOutcome "fn add(x: i32, y: i32) -> i32 { x + y }" `shouldBe` accepted

  test "an omitted return type is unit" $
    signaturesAndBodiesOutcome "fn f() {} fn g() { let u: () = f(); }" `shouldBe` accepted

  test "a call has the callee's declared result type" $
    signaturesAndBodiesOutcome "fn f(x: i32) -> i32 { x } fn g() -> i32 { f(1) }" `shouldBe` accepted

  test "a call's argument is checked against the declared parameter type" $
    signaturesAndBodiesOutcome "fn f(x: i32) -> i32 { x } fn g() -> i32 { f(true) }"
      `shouldBe` rejectedWith (TypeMismatch i32 bool (spanAt 1 45))

  test "a call's declared result type must fit its use" $
    signaturesAndBodiesOutcome "fn f() -> bool { true } fn g() -> i32 { f() }"
      `shouldBe` rejectedWith (TypeMismatch i32 bool (spanAt 1 41))

  test "parameters may be shared and mutable references to values and slices" $
    signaturesAndBodiesOutcome "fn f(a: &i32, b: &mut i32, c: &[i32], d: &mut [i32]) {}" `shouldBe` accepted

  test "a parameter may be a qubit reference or a qubit slice" $
    signaturesAndBodiesOutcome "fn f(q: &qbit, qs: &[qbit]) {}" `shouldBe` accepted

  test "qubit parameters and results may carry quantum usage qualifiers" $
    signaturesAndBodiesOutcome "fn f(q: affine qbit, p: (linear qbit, affine qbit)) -> (affine qbit, (linear qbit, affine qbit)) { (q, p) }"
      `shouldBe` accepted

  test "a mut parameter has its declared type" $
    signaturesAndBodiesOutcome "fn f(mut x: i32) -> i32 { x += 1; x }" `shouldBe` accepted

  test "a function-typed parameter records its effect, parameters and result" $
    signaturesAndBodiesOutcome "general fn phase_kickback(qs: [qbit; 4], oracle: unitary fn(qs: [qbit; 4], target: qbit) -> ([qbit; 4], qbit)) -> [qbit; 4] { let ancilla = qalloc(); let (qs, ancilla) = oracle(qs, ancilla); discard(ancilla); qs }"
      `shouldBe` accepted

  test "a function type without an effect or result is general and returns unit" $
    signaturesAndBodiesOutcome "fn run(g: fn(value: i32)) { g(1); }" `shouldBe` accepted

  test "a declared function is a value of its function type" $
    signaturesAndBodiesOutcome "classical fn inc(x: i32) -> i32 { x + 1 } fn run(g: classical fn(x: i32) -> i32) -> i32 { g(1) } fn main() -> i32 { run(inc) }"
      `shouldBe` accepted

  test "parameter names do not take part in function type equality" $
    signaturesAndBodiesOutcome "classical fn inc(y: i32) -> i32 { y + 1 } fn run(g: classical fn(x: i32) -> i32) -> i32 { g(1) } fn main() -> i32 { run(inc) }"
      `shouldBe` accepted

  test "pub items type-check like private ones" $
    signaturesAndBodiesOutcome "pub const N: u32 = 2; pub fn f(a: [i32; N as usize]) -> [i32; N as usize] { a }" `shouldBe` accepted

  test "an owned slice parameter is unsized" $
    signaturesAndBodiesOutcome "fn f(xs: [i32]) {}"
      `shouldBe` rejectedWith (UnsizedValue (slice i32) (spanAt 1 10))

  test "an owned slice result is unsized" $
    signaturesAndBodiesOutcome "fn f() -> [i32] {}"
      `shouldBe` rejectedWith (UnsizedValue (slice i32) (spanAt 1 11))

-- Forward references and recursion
forwardReferenceTests : List TestResult
forwardReferenceTests = Test.do
  test "a function may call a function declared later" $
    signaturesAndBodiesOutcome "fn f() -> i32 { g() } fn g() -> i32 { 1 }" `shouldBe` accepted

  test "a recursive function needs only its own signature" $
    signaturesAndBodiesOutcome "classical fn fact(n: u32) -> u32 { if n == 0 { 1 } else { n * fact(n - 1) } }"
      `shouldBe` accepted

  test "mutually recursive functions are not a declaration cycle" $
    signaturesAndBodiesOutcome "fn even(n: u32) -> bool { if n == 0 { true } else { odd(n - 1) } } fn odd(n: u32) -> bool { if n == 0 { false } else { even(n - 1) } }"
      `shouldBe` accepted

  test "a function may read a constant declared later" $
    signaturesAndBodiesOutcome "fn f() -> i32 { FIVE } const FIVE: i32 = 5;" `shouldBe` accepted

  test "a signature length may use a constant declared later" $
    signaturesAndBodiesOutcome "fn f(a: [i32; N as usize]) -> i32 { a[0] } const N: u32 = 4;" `shouldBe` accepted

  test "a signature length may call a const fn declared later" $
    signaturesAndBodiesOutcome "fn f(a: [i32; square(2) as usize]) {} const fn square(x: u32) -> u32 { x * x }"
      `shouldBe` accepted

  test "a signature length that needs several rounds is evaluated" $
    signaturesAndBodiesOutcome "fn f(a: [i32; LEN as usize]) {} const LEN: u32 = double(HALF); const HALF: u32 = 2; const fn double(x: u32) -> u32 { x * 2 } fn g() { let a: [i32; 4] = [0; 4]; f(a); }"
      `shouldBe` accepted

  test "a recursive const fn may size a signature" $
    signaturesAndBodiesOutcome "const fn fact(n: u32) -> u32 { if n == 0 { 1 } else { n * fact(n - 1) } } fn f(a: [i32; fact(3) as usize]) {} fn g() { let a: [i32; 6] = [0; 6]; f(a); }"
      `shouldBe` accepted

-- Retry boundaries and independently checked lengths.
-- Each fixture makes a demand whose producer occurs later in source order.
signatureRetryTests : List TestResult
signatureRetryTests = Test.do
  test "mutually recursive const functions can produce a finite signature length" $
    signaturesAndBodiesOutcome "fn f(a: [i32; even(4) as usize]) {} const fn even(n: u32) -> u32 { if n == 0 { 1 } else { odd(n - 1) } } const fn odd(n: u32) -> u32 { if n == 0 { 0 } else { even(n - 1) } } fn g() { f([0; 1]); }"
      `shouldBe` accepted

  test "nested function types evaluate both parameter and return array lengths" $
    signaturesAndBodiesOutcome "fn run(g: fn(a: [i32; N as usize]) -> [i32; N as usize], a: [i32; N as usize]) -> [i32; N as usize] { g(a) } const N: u32 = 2; fn identity(a: [i32; 2]) -> [i32; 2] { a } fn f() { let a: [i32; 2] = run(identity, [1, 2]); }"
      `shouldBe` accepted

  test "the same dependent length can occur in several parameter and result types" $
    signaturesAndBodiesOutcome "fn f(a: [i32; size() as usize], b: [bool; size() as usize]) -> ([i32; size() as usize], [bool; size() as usize]) { (a, b) } const fn size() -> u32 { COUNT } const COUNT: u32 = 2; fn g() { let pair: ([i32; 2], [bool; 2]) = f([1, 2], [true, false]); }"
      `shouldBe` accepted

  test "a blocked body retries with its return context and earlier local inference intact" $
    signaturesAndBodiesOutcome "fn f() -> i16 { let result = 7; let a: [i32; N as usize] = [0; N as usize]; result } const N: u32 = size(); const fn size() -> u32 { 2 }"
      `shouldBe` accepted

  test "an isolated length does not default unrelated local inference variables" $
    signaturesAndBodiesOutcome "fn f() -> i8 { let result = 7; let a: [u32; { let result = 2; result }] = [0; 2]; result }"
      `shouldBe` accepted

  test "several blocked constants and signatures settle without a false cycle" $
    signaturesAndBodiesOutcome "fn f(a: [i32; FIRST as usize]) -> [i32; SECOND as usize] { a } const FIRST: u32 = next(); const SECOND: u32 = LAST; const fn next() -> u32 { SECOND } const LAST: u32 = 3; fn g() { let a: [i32; 3] = f([0; 3]); }"
      `shouldBe` accepted

-- Array lengths in signatures
signatureLengthTests : List TestResult
signatureLengthTests = Test.do
  test "a literal length in a signature type-checks" $
    signaturesAndBodiesOutcome "fn f(qs: [qbit; 2]) -> [qbit; 2] { qs }" `shouldBe` accepted

  test "a constant-expression length is evaluated" $
    signaturesAndBodiesOutcome "fn f(a: [i32; 2 + 2]) {} fn g() { let a: [i32; 4] = [0; 4]; f(a); }" `shouldBe` accepted

  test "an explicit usize cast lets a u64 constant size an array" $
    signaturesAndBodiesOutcome "const N: u64 = 4; fn f(a: [i32; N as usize]) {} fn g() { let a: [i32; 4] = [0; 4]; f(a); }"
      `shouldBe` accepted

  test "a signed constant cannot size an array" $
    signaturesAndBodiesOutcome "const N: i32 = 4; fn f(a: [i32; N]) {}"
      `shouldBe` rejectedWith (IncorrectArrayLengthType i32 (spanAt 1 33))

  test "a bool constant cannot size an array" $
    signaturesAndBodiesOutcome "const FLAG: bool = true; fn f(a: [i32; FLAG]) {}"
      `shouldBe` rejectedWith (IncorrectArrayLengthType bool (spanAt 1 40))

  test "a u128 length is rejected even when its value is known" $
    signaturesAndBodiesOutcome "const N: u128 = 18446744073709551616; fn f(a: [i32; N]) {}"
      `shouldBe` rejectedWith (IncorrectArrayLengthType u128 (spanAt 1 53))

  test "a non-const call cannot size a signature" $
    signaturesAndBodiesOutcome "fn g() -> u32 { 3 } fn f(a: [i32; g() as usize]) {}"
      `shouldBe` rejectedWith (NotAConstantExpression (spanAt 1 35))

  test "an argument's array length must equal the parameter's" $
    signaturesAndBodiesOutcome "fn f(a: [i32; 3]) {} fn g() { f([1, 2]); }"
      `shouldBe` rejectedWith (TypeMismatch (array i32 3) (array i32 2) (spanAt 1 33))

  test "a returned array's length must equal the declared result's" $
    signaturesAndBodiesOutcome "fn f() -> [i32; 2] { [1, 2, 3] }"
      `shouldBe` rejectedWith (TypeMismatch (array i32 2) (array i32 3) (spanAt 1 22))

-- Constant items
constantItemTests : List TestResult
constantItemTests = Test.do
  test "a constant has its written type" $
    signaturesAndBodiesOutcome "const FIVE: i32 = 5; fn f() -> i32 { FIVE }" `shouldBe` accepted

  test "a constant's written type is used where it is read" $
    signaturesAndBodiesOutcome "const FLAG: bool = true; fn f() -> i32 { FLAG }"
      `shouldBe` rejectedWith (TypeMismatch i32 bool (spanAt 1 42))

  test "an array constant has its written type" $
    signaturesAndBodiesOutcome "const A: [i32; 3] = [1, 2, 3]; fn f() -> i32 { A[0] }" `shouldBe` accepted

  test "a tuple constant has its written type" $
    signaturesAndBodiesOutcome "const T: (u32, bool) = (3, true); fn f() -> bool { T.1 }" `shouldBe` accepted

-- Parameter names that resolve to constants
constantParameterTests : List TestResult
constantParameterTests = Test.do
  test "a parameter named like a unit constant is an irrefutable pattern" $
    signaturesAndBodiesOutcome "const UNIT: () = (); fn f(UNIT: ()) {} fn g() { f(()); }" `shouldBe` accepted

  test "a constant-name parameter keeps the constant's own type" $
    signaturesAndBodiesOutcome "const UNIT: () = (); fn f(UNIT: ()) {} fn g() -> () { UNIT }" `shouldBe` accepted

  test "a parameter named like a non-unit constant is a refutable pattern" $
    signaturesAndBodiesOutcome "const ZERO: i32 = 0; fn f(ZERO: i32) {}"
      `shouldBe` rejectedWith (RefutableBindingPattern (spanAt 1 27))

  test "a constant-name parameter must have the constant's type" $
    signaturesAndBodiesOutcome "const UNIT: () = (); fn f(UNIT: i32) {}"
      `shouldBe` rejectedWith (TypeMismatch i32 unit (spanAt 1 27))

-- Const functions are classical
constFunctionTests : List TestResult
constFunctionTests = Test.do
  test "a const fn may be written classical" $
    signaturesAndBodiesOutcome "const classical fn square(x: i32) -> i32 { x * x } classical fn f() -> i32 { square(3) }"
      `shouldBe` accepted

  test "a const fn cannot be written unitary" $
    signaturesAndBodiesOutcome "const unitary fn f() {}"
      `shouldBe` rejectedWith (EffectViolation EffectClassical EffectUnitary (spanAt 1 7))

  test "a const fn cannot be written general" $
    signaturesAndBodiesOutcome "const general fn f() {}"
      `shouldBe` rejectedWith (EffectViolation EffectClassical EffectGeneral (spanAt 1 7))

  test "a const fn that is never called cannot call a non-const function" $
    signaturesAndBodiesOutcome "fn g() -> u32 { 3 } const fn f() -> u32 { g() }"
      `shouldBe` rejectedWith (NotAConstantExpression (spanAt 1 43))

-- Declaration cycles: the error names the symbols on the cycle and
-- points at the name of the first item that is still waiting
declarationCycleTests : List TestResult
declarationCycleTests = Test.do
  test "a constant defined by itself is a cycle" $
    signaturesAndBodiesOutcome "const A: i32 = A;"
      `shouldBe` rejectedWith (CyclicDeclaration ["A"] (spanAt 1 7))

  test "two constants defined by each other are a cycle" $
    signaturesAndBodiesOutcome "const A: i32 = B; const B: i32 = A;"
      `shouldBe` rejectedWith (CyclicDeclaration ["B", "A"] (spanAt 1 7))

  test "a signature length and a const fn call that need each other are a cycle" $
    signaturesAndBodiesOutcome "const fn f(a: [i32; N as usize]) -> u32 { 3 } const N: u32 = f([0; 3]);"
      `shouldBe` rejectedWith (CyclicDeclaration ["N", "f"] (spanAt 1 10))

  test "an item waiting on a cycle is not listed in it" $
    signaturesAndBodiesOutcome "const N: u32 = M; const M: u32 = N; fn f(a: [i32; N as usize]) {}"
      `shouldBe` rejectedWith (CyclicDeclaration ["N", "M"] (spanAt 1 40))

  test "a three-constant dependency cycle reports every cycle member once" $
    signaturesAndBodiesOutcome "const A: u32 = B; const B: u32 = C; const C: u32 = A;"
      `shouldBe` rejectedWith (CyclicDeclaration ["B", "C", "A"] (spanAt 1 7))

  test "a constant evaluated through a const fn that reads it is a cycle" $
    signaturesAndBodiesOutcome "const fn f() -> u32 { N } const N: u32 = f();"
      `shouldBe` rejectedWith (CyclicDeclaration ["N"] (spanAt 1 33))

-- Only evaluated constant reads create value dependencies.
-- The references still have to be resolved and type-checked in every branch.
lazyDependencyTests : List TestResult
lazyDependencyTests = Test.do
  test "a constant reference in an unselected else branch does not create a cycle" $
    signaturesAndBodiesOutcome "const A: u32 = if true { 1 } else { B }; const B: u32 = A; fn f() { let a: [i32; B as usize] = [0; 1]; }"
      `shouldBe` accepted

  test "a constant reference in an unselected then branch does not create a cycle" $
    signaturesAndBodiesOutcome "const A: u32 = if false { B } else { 2 }; const B: u32 = A; fn f() { let a: [i32; B as usize] = [0; 2]; }"
      `shouldBe` accepted

  test "short-circuiting and avoids a cyclic constant value dependency" $
    signaturesAndBodiesOutcome "const A: bool = false && B; const B: bool = A; const N: u32 = if (B) { 0 } else { 1 }; fn f() { let a: [i32; N as usize] = [0; 1]; }"
      `shouldBe` accepted

  test "short-circuiting or avoids a cyclic constant value dependency" $
    signaturesAndBodiesOutcome "const A: bool = true || B; const B: bool = A; const N: u32 = if (B) { 1 } else { 0 }; fn f() { let a: [i32; N as usize] = [0; 1]; }"
      `shouldBe` accepted

  test "an unselected const function branch does not wait on its caller's constant" $
    signaturesAndBodiesOutcome "const fn size() -> u32 { if true { 2 } else { N } } const N: u32 = size(); fn f() { let a: [i32; N as usize] = [0; 2]; }"
      `shouldBe` accepted

  test "a constant reference in the selected branch is a cycle" $
    signaturesAndBodiesOutcome "const A: u32 = if false { 1 } else { B }; const B: u32 = A;"
      `shouldBe` rejectedWith (CyclicDeclaration ["B", "A"] (spanAt 1 7))

-- Prelude functions used as values
preludeValueTests : List TestResult
preludeValueTests = Test.do
  test "a gate can be passed where a unitary function type is expected" $
    signaturesAndBodiesOutcome "fn run(g: unitary fn(q: qbit) -> qbit, q: qbit) -> qbit { g(q) } fn main() -> qbit { let q = qalloc(); run(H, q) }"
      `shouldBe` accepted

  test "a basis-permuting gate satisfies an uncompsafe function type" $
    signaturesAndBodiesOutcome "fn run(g: uncompsafe fn(q: qbit) -> qbit, q: qbit) -> qbit { g(q) } fn main() -> qbit { run(X, qalloc()) }"
      `shouldBe` accepted

  test "a non-permuting gate does not satisfy an uncompsafe function type" $
    signaturesAndBodiesOutcome "fn run(g: uncompsafe fn(q: qbit) -> qbit, q: qbit) -> qbit { g(q) } fn main() -> qbit { run(H, qalloc()) }"
      `shouldBe` rejectedWith (TypeMismatch (fnType EffectUncompsafe [linearQbit] linearQbit) (LeafFunctionType EffectUnitary [SupportAdjoint, SupportCtrl] [linearQbit] linearQbit) (spanAt 1 93))

  test "a rotation gate value takes an angle64 and a qubit" $
    signaturesAndBodiesOutcome "fn run(g: unitary fn(theta: angle64, q: qbit) -> qbit, q: qbit) -> qbit { g(0.5, q) } fn main() -> qbit { run(RX, qalloc()) }"
      `shouldBe` accepted

  test "a user function may shadow a prelude gate" $
    signaturesAndBodiesOutcome "fn H(x: i32) -> i32 { x } fn main() -> i32 { H(1) }" `shouldBe` accepted

  test "a user function may shadow a prelude math function" $
    signaturesAndBodiesOutcome "fn sin(x: bool) -> bool { x } fn main() -> bool { sin(true) }" `shouldBe` accepted

  test "a constant may shadow a prelude gate name" $
    signaturesAndBodiesOutcome "const I: i32 = 1; fn main() -> i32 { I + 1 }" `shouldBe` accepted

  test "a rotation gate value specializes to an angle32 function type" $
    signaturesAndBodiesOutcome "fn run(g: unitary fn(theta: angle32, q: qbit) -> qbit, q: qbit) -> qbit { g(0.5, q) } fn main() -> qbit { run(RX, qalloc()) }"
      `shouldBe` accepted

  test "a two-qubit gate value has a tuple-returning function type" $
    signaturesAndBodiesOutcome "fn run(g: unitary fn(a: qbit, b: qbit) -> (qbit, qbit), a: qbit, b: qbit) -> (qbit, qbit) { g(a, b) } fn main() -> (qbit, qbit) { run(CX, qalloc(), qalloc()) }"
      `shouldBe` accepted

  test "a math function value has its f64 signature" $
    signaturesAndBodiesOutcome "fn run(g: fn(x: f64) -> f64) -> f64 { g(1.0) } fn main() -> f64 { run(sin) }"
      `shouldBe` accepted

-- Length typing precedes value conversion; usize is distinct from every uN.
usizeSignatureTests : List TestResult
usizeSignatureTests = Test.do
  test "a u8 constant cannot size a signature without a cast" $
    signaturesAndBodiesOutcome "const N: u8 = 3; fn f(a: [i32; N]) {}"
      `shouldBe` rejectedWith (IncorrectArrayLengthType u8 (spanAt 1 32))

  test "a u32 constant cannot size a signature without a cast" $
    signaturesAndBodiesOutcome "const N: u32 = 3; fn f(a: [i32; N]) {}"
      `shouldBe` rejectedWith (IncorrectArrayLengthType u32 (spanAt 1 33))

  test "a u64 constant cannot size a signature without a cast" $
    signaturesAndBodiesOutcome "const N: u64 = 3; fn f(a: [i32; N]) {}"
      `shouldBe` rejectedWith (IncorrectArrayLengthType u64 (spanAt 1 33))

  test "a u128 constant cannot size a signature without a cast" $
    signaturesAndBodiesOutcome "const N: u128 = 3; fn f(a: [i32; N]) {}"
      `shouldBe` rejectedWith (IncorrectArrayLengthType u128 (spanAt 1 34))

  test "even a zero-valued u64 length has the wrong type" $
    signaturesAndBodiesOutcome "const N: u64 = 0; fn f(a: [i32; N]) {}"
      `shouldBe` rejectedWith (IncorrectArrayLengthType u64 (spanAt 1 33))

  test "a usize-returning const function can size a signature directly" $
    signaturesAndBodiesOutcome "const fn size() -> usize { 3 } fn f(a: [i32; size()]) -> [i32; 3] { a }"
      `shouldBe` accepted

  test "a fixed u64 return type is not inferred as usize in a length" $
    signaturesAndBodiesOutcome "const fn size() -> u64 { 3 } fn f(a: [i32; size()]) {}"
      `shouldBe` rejectedWith (IncorrectArrayLengthType u64 (spanAt 1 44))

  test "a u128 length cast truncates to the 64-bit usize target" $
    signaturesAndBodiesOutcome "const N: u128 = 18446744073709551617; fn f(a: [i32; N as usize]) -> [i32; 1] { a }"
      `shouldBe` accepted

export
runSignatureCheckTests : IO Bool
runSignatureCheckTests =
  runTests $ concat
    [ functionSignatureTests
    , forwardReferenceTests
    , signatureRetryTests
    , signatureLengthTests
    , constantItemTests
    , constantParameterTests
    , constFunctionTests
    , declarationCycleTests
    , lazyDependencyTests
    , preludeValueTests
    , usizeSignatureTests
    ]
