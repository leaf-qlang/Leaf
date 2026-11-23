module TypeChecker.TypeCheckTest

import System.File
import TestFramework

import Compiler.Frontend.TypeChecker.Data
import TypeChecker.Helper

%default total

--------------------------------------------------------------------------------
-- Type checker integration tests
--------------------------------------------------------------------------------
-- Whole programs through every phase: the examples in
-- `examples/`, read at run time, and the in-scope sections of the language
-- specification, each placed in the smallest context that declares what it
-- uses. Example 08 is excluded: the parser rejects its qmatch. Spec snippets
-- that the parser or post-parse validation rejects are left to those phases.
--------------------------------------------------------------------------------

||| Spec §5: every primitive type except qstate.
primitiveTypesProgram : String
primitiveTypesProgram = """
  fn primitive_types(
      b: bit, q: qbit, a32: angle32, a64: angle64, p: param,
      i1: i8, i2: i16, i3: i32, i4: i64, i5: i128,
      u1: u8, u2: u16, u3: u32, u4: u64, u5: u128, u6: usize,
      f1: f32, f2: f64, flag: bool, unit: ()
  ) {
      discard(q);
  }
  """

||| Spec §6: primitive types, literals, mutation, references and casts.
basicTypesProgram : String
basicTypesProgram = """
  fn basic_types() {
      let f: f32 = 1.234567;
      let d: f64 = -1.2345678901234567;
      let d = -1000.0;
      let i: i8 = -1;
      let i: i16 = -1;
      let i: i32 = 1;
      let i: i64 = 1;
      let i: i128 = -1;
      let i = -7;
      let u: u8 = 1;
      let u: u16 = 1;
      let u: u32 = 1;
      let u: u64 = 1;
      let u: u128 = 1;
      let u: usize = 1;
      let unit: () = ();
      let unit = ();
      let theta: param = Param("theta");
      let mut x: i32 = 0;
      x = 5;
      let mut x: [i32; 2] = [0, 0];
      x[0] = 10;
      let mut t: (i32, f64) = (0, 0.0);
      t.0 = 3;
      let x = 10;
      let r: &i32 = &x;
      let mut x = 10;
      let r: &mut i32 = &mut x;
  }
  const FIVE: i32 = 5;
  fn qubit_declarations() {
      let q: qbit = qalloc();
      discard(q);
      let q: linear qbit = qalloc();
      discard(q);
      let linear q: qbit = qalloc();
      discard(q);
      let q = qalloc();
      discard(q);
  }
  fn casts() {
      let x: i8 = 34;
      let x = 34 as i8;
      let x: i16 = 34;
      let x = 34 as i16;
      let x: i32 = 34;
      let x = 34 as i32;
      let x: i64 = 34;
      let x = 34 as i64;
      let x: i128 = 34;
      let x = 34 as i128;
      let x: u8 = 34;
      let x = 34 as u8;
      let x: u16 = 34;
      let x = 34 as u16;
      let x: u32 = 34;
      let x = 34 as u32;
      let x: u64 = 34;
      let x = 34 as u64;
      let x: u128 = 34;
      let x = 34 as u128;
      let x: usize = 34;
      let x = 34 as usize;
      let x: f32 = 34.0;
      let x = 34 as f32;
      let x: f64 = 34.0;
      let x = 34 as f64;
      let x: angle32 = 34.0;
      let x = 34 as angle32;
      let x: angle64 = 34.0;
      let x = 34 as angle64;
      let b: bit = 1;
      let x = b as i32;
  }
  """

||| Spec §9: slices, mutable slices, qubit slices and array-to-slice coercion.
slicesProgram : String
slicesProgram = """
  classical fn sum(xs: &[i32]) -> i32 {
      let mut total = 0;
      for i in 0..len(xs) {
          total += xs[i];
      }
      total
  }
  classical fn zero_out(xs: &mut [i32]) {
      for i in 0..len(xs) {
          xs[i] = 0;
      }
  }
  unitary fn apply_hadamard_layer(qs: &[qbit]) {
      if len(qs) == 0 {
          return;
      }
      H(&qs[0]);
      apply_hadamard_layer(&qs[1..]);
  }
  fn slices() -> i32 {
      let a: [i32; 5] = [10, 20, 30, 40, 50];
      let s: &[i32] = &a[..];
      let s: &[i32] = &a[1..4];
      let s: &[i32] = &a[1..=3];
      let s: &[i32] = &a[2..];
      let s: &[i32] = &a[..3];
      let s: &[i32] = &a[..=3];
      let s = &a[1..4];
      let n = len(s);
      let x = s[0];
      let mid: &[i32] = &s[1..n - 1];
      let mut m: [i32; 5] = [10, 20, 30, 40, 50];
      let w: &mut [i32] = &mut m[1..4];
      w[0] = 99;
      let r: &[i32] = &m[..];
      zero_out(&mut m);
      let qs: [qbit; 4] = qalloc(4);
      let qv: &[qbit] = &qs[..];
      H(&qv[0]);
      CX(&qv[1], &qv[2]);
      apply_hadamard_layer(&qs);
      discard(qs);
      sum(&a) + x
  }
  """

||| Spec §9: `&mut` is never written on qubits.
mutableQubitSliceProgram : String
mutableQubitSliceProgram = """
  fn f() {
      let qs: [qbit; 4] = qalloc(4);
      let bad = &mut qs[..];
      discard(qs);
  }
  """

||| Spec §9: a shared slice cannot be written through.
sharedSliceWriteProgram : String
sharedSliceWriteProgram = """
  fn f() {
      let mut m: [i32; 5] = [10, 20, 30, 40, 50];
      let r: &[i32] = &m[..];
      r[0] = 0;
  }
  """

||| Spec §10: a qubit consumed by measr cannot be used after the measurement.
measuredQubitProgram : String
measuredQubitProgram = """
  fn f() -> bit {
      let q = qalloc();
      let b = measr(q);
      H(&q);
      b
  }
  """

||| Spec §13 and §14: owned and borrowed gate calls and angle arguments.
gatesProgram : String
gatesProgram = """
  fn gates() -> (qbit, qbit) {
      let q = qalloc();
      let q: qbit = H(q);
      let linear q: qbit = H(q);
      let q: linear qbit = H(q);
      let q = H(q);
      H(&q);
      let q: qbit = U3(1.0, 2.0, 3.0, q);
      let q = U3(1.0, 2.0, 3.0, q);
      U3(1.0, 2.0, 3.0, &q);
      let q0 = qalloc();
      let q1 = qalloc();
      let (q0, q1): (qbit, qbit) = CX(q0, q1);
      let (q0, q1) = CX(q0, q1);
      CX(&q0, &q1);
      let q: qbit = U1(0.25, q);
      let angle: angle64 = 3.141592653589793;
      let q: qbit = U1(angle, q);
      let angle: angle64 = turns(0.25);
      let q: qbit = U1(angle, q);
      let theta = Param("theta");
      let q: qbit = U1(theta, q);
      let q: qbit = U1(turns(0.25), q);
      discard(q);
      (q0, q1)
  }
  """

||| Spec §15: ctrl applied to a user function as a callable.
controlledCallableProgram : String
controlledCallableProgram = """
  unitary fn f(a: &qbit, b: &qbit) {
      CX(a, b);
  }
  fn controlled_callable() {
      let q0 = qalloc();
      let q1 = qalloc();
      let q2 = qalloc();
      let q3 = qalloc();
      ctrl(&q0, &q1).apply(f)(&q2, &q3);
      discard(q0, q1, q2, q3);
  }
  """

||| Spec §17 to §19: arithmetic, boolean and bitwise operators. The spec reuses `a`
||| for bits and integers; here bits and integers have their own names.
operatorsProgram : String
operatorsProgram = """
  fn operators(a: bool, b: bool, p: bit, q: bit, y: u32) {
      let add = 5 + 3;
      let sub = 10 - 4;
      let mul = 6 * 2;
      let div = 12 / 3;
      let rem = 10 % 3;
      let mut x = 10;
      x += 5;
      x -= 2;
      x *= 2;
      x /= 3;
      x %= 4;
      let c = !a;
      let d = a && b;
      let e = a || b;
      let and_bit: bit = p & q;
      let or_bit: bit = p | q;
      let xor_bit: bit = p ^ q;
      let mut z: u32 = 12;
      z &= y;
      z |= y;
      z ^= y;
      let l = z << 2;
      let r = z >> 1;
      z <<= 1;
      z >>= 1;
  }
  """

||| Spec §20 and §36: if and else with bool and bit conditions.
conditionalsProgram : String
conditionalsProgram = """
  fn f1() -> i32 {
      -1
  }
  fn f2() -> i32 {
      0
  }
  fn f3() -> i32 {
      1
  }
  fn fun(q: &qbit) {
      X(q);
  }
  fn conditionals(x: i32, b: bit) -> i32 {
      let q = qalloc();
      if 7 > 5 {
          H(&q);
      } else {
          X(&q);
      }
      if b { fun(&q); }
      if b == 1 { fun(&q); }
      let sign = if x < 0 {
          f1()
      } else if x == 0 {
          f2()
      } else {
          f3()
      };
      discard(q);
      let boolflag = true;
      let y: i32 = if boolflag { 1 } else { 2 };
      if x < 0 {
          -1
      } else if x == 0 {
          0
      } else {
          1
      }
  }
  """

||| Spec §27 to §35: blocks, loops, ranges, for loops and tuples.
blocksAndLoopsProgram : String
blocksAndLoopsProgram = """
  fn blocks_and_loops(xs: [i32; 3]) -> i32 {
      let x = {
          let a = 1;
          let b = 2;
          a + b
      };
      let unit = {
          let a = 1;
      };
      let mut count = 0;
      loop {
          if count == 3 {
              break;
          }
          count += 1;
      }
      let mut count = 0;
      let result = loop {
          if count == 3 {
              break count;
          }
          count += 1;
      };
      while count <= 5 {
          count += 1;
      }
      for i in 1..6 {
          count += 1;
      }
      for i in rev(1..6) {
          count -= 1;
      }
      for i in 0..len(xs) {
          count += xs[i];
      }
      let t: (i32, f64, bool) = (1, 3.14, true);
      let t = (1, 3.14, true);
      let x0 = t.0;
      let y0 = t.1;
      let z0 = t.2;
      let (a, b, c) = (1, 2, 3);
      let (p, _, r) = (1, 2, 3);
      x + result + count
  }
  fn ranges(a: i32, b: i32, n: u32) {
      let r1 = a..b;
      let r2 = a..=b;
      let r3 = 1..;
      let r4 = ..5;
      let r5 = ..=5;
      let r6 = rev(0..n);
  }
  fn tuple_qubits() -> (qbit, qbit, qbit) {
      let q0 = qalloc();
      let q1 = qalloc();
      let q2 = qalloc();
      let qbits = CNOT(q0, q1);
      let q0 = qbits.0;
      let q1 = qbits.1;
      let (q0, q1, q2) = (H(q0), H(q1), H(q2));
      (q0, q1, q2)
  }
  """

||| Spec §31: rev needs a range with both endpoints.
reversedOpenRangeProgram : String
reversedOpenRangeProgram = """
  fn reversed() {
      for i in rev(..6) {
      }
  }
  """

||| Spec §46 to §50 and §52: functions, const fns, returns and local scopes.
functionsProgram : String
functionsProgram = """
  fn function_name() {
  }
  const fn square(x: i32) -> i32 {
      x * x
  }
  fn add(x: i32, y: i32) -> i32 {
      x + y
  }
  fn f(x: f32) -> f32 {
      let y = 2.0;
      x + y
  }
  fn g() -> f64 {
      let x = 2.0;
      return x;
  }
  fn my_function() {
      let i = 10;
  }
  fn increment(mut x: i32) -> i32 {
      x += 1;
      x
  }
  fn local_block() {
      {
          let mut x = 0;
          x = x + 1;
      }
  }
  """

||| Spec §53: the effect qualifiers, except the contract-bearing coisometry.
effectsProgram : String
effectsProgram = """
  classical fn f(x: i32) -> i32 {
      x + 1
  }
  uncompsafe fn g(q: qbit) -> qbit {
      let q = X(q);
      q
  }
  unitary fn h(q: qbit) -> qbit {
      let q = X(q);
      let q = H(q);
      q
  }
  isometry fn grow(qs: [qbit; 2]) -> [qbit; 4] {
      let q1 = X(qs[0]);
      let q2 = H(qs[1]);
      let q3 = qalloc();
      let q4 = qalloc();
      let q3 = X(q3);
      let (q3, q4) = CX(q3, q4);
      [q1, q2, q3, q4]
  }
  general fn sample(q: qbit) -> bit {
      measr(q)
  }
  """

||| Spec §54 and §55: integer and floating-point literals.
literalsProgram : String
literalsProgram = """
  fn integer_literals() {
      let x = 1000;
      let x = 1_000;
      let x = 1_000_000;
      let h = 0xff;
      let h = 0xFF;
      let h = 0xff_u8;
      let o = 0o77;
      let o = 0o70_i16;
      let b = 0b1010;
      let b = 0b1111_0000;
      let b = 0b1111_1111_1001_0000i64;
      let z = 10u32;
      let z = 10_u32;
      let z = 10usize;
      let z = 10_usize;
      let z = 123i32;
      let z = 123_i32;
  }
  fn float_literals() {
      let x = 1.0;
      let x = 0.1;
      let x = 1.0e-3;
      let x = 12E+99;
      let x = 12E+99_f64;
      let f = 1.0f64;
      let f = 1.0_f64;
      let f = 0.1f32;
      let f = 5f32;
  }
  """

||| Spec §66: a qubit reference argument.
referenceArgumentsProgram : String
referenceArgumentsProgram = """
  fn apply_gate(q: &qbit)
  {
    H(q);
  }
  fn main() -> bit {
    let q = qalloc();
    apply_gate(&q);
    let b = measr(q);
    b
  }
  """

||| Spec §67: a function and a constant item. The constant `I` shadows the
||| prelude gate of the same name.
itemsProgram : String
itemsProgram = """
  fn main() {
  }
  const I: i32 = 1;
  fn uses_constant() -> i32 {
      I
  }
  """

||| Spec §68: qasm_gate and qasm_def, with distinct function names.
attributesProgram : String
attributesProgram = """
  #[qasm_gate]
  unitary fn myfun1(q: qbit) -> qbit {
    let q = X(q);
    let q = H(q);
    q
  }
  #[qasm_gate("qasm_subroutine_name")]
  unitary fn myfun2(q: qbit) -> qbit {
    let q = X(q);
    let q = H(q);
    q
  }
  #[qasm_def]
  general fn myfun3(q: qbit) -> bit {
    let q = X(q);
    let q = H(q);
    measr(q)
  }
  #[qasm_def("qasm_subroutine_name")]
  general fn myfun4(q: qbit) -> bit {
    let q = X(q);
    let q = H(q);
    measr(q)
  }
  """

||| Spec §69: classical, circuit-generating and classically controlled recursion.
recursionProgram : String
recursionProgram = """
  classical fn fact(n: u32) -> u32 {
      if n == 0 { 1 } else { n * fact(n - 1) }
  }
  unitary fn apply_hadamard_layer(qs: &[qbit]) {
      if len(qs) == 0 {
          return;
      }
      H(&qs[0]);
      apply_hadamard_layer(&qs[1..]);
  }
  general fn sample_until_zero() -> qbit {
      let q = qalloc();
      H(&q);
      let b = measr(&q);
      if b == 0 {
          return q;
      } else {
          discard(q);
          sample_until_zero()
      }
  }
  """

-- Language specification sections
specificationTests : List TestResult
specificationTests = Test.do
  test "spec §5 every primitive type except qstate type-checks" $
    typeCheckOutcome primitiveTypesProgram `shouldBe` accepted

  test "spec §6 basic types, mutation, references and casts type-check" $
    typeCheckOutcome basicTypesProgram `shouldBe` accepted

  test "spec §9 slices and array-to-slice coercion type-check" $
    typeCheckOutcome slicesProgram `shouldBe` accepted

  test "spec §9 rejects &mut on qubits" $
    typeCheckOutcome mutableQubitSliceProgram
      `shouldBe` rejectedWith (InvalidQbitReference (spanAt 3 15))

  test "spec §9 rejects writes through a shared slice" $
    typeCheckOutcome sharedSliceWriteProgram
      `shouldBe` rejectedWith (AssignmentThroughSharedReference (spanAt 4 5))

  test "spec §10 rejects a qubit used after measr consumed it" $
    typeCheckOutcome measuredQubitProgram
      `shouldBe` rejectedWith (UseAfterMove "q" (spanAt 4 7))

  test "spec §13 and §14 gate calls type-check" $
    typeCheckOutcome gatesProgram `shouldBe` accepted

  test "spec §15 rejects ctrl applied to a user function without ctrl support" $
    typeCheckOutcome controlledCallableProgram
      `shouldBe` rejectedWith (MissingCapability "ctrl" (spanAt 9 26))

  test "spec §17 to §19 operators type-check" $
    typeCheckOutcome operatorsProgram `shouldBe` accepted

  test "spec §20 and §36 conditionals type-check" $
    typeCheckOutcome conditionalsProgram `shouldBe` accepted

  test "spec §27 to §35 blocks, loops, ranges and tuples type-check" $
    typeCheckOutcome blocksAndLoopsProgram `shouldBe` accepted

  test "spec §31 rejects rev of a range without a start" $
    typeCheckOutcome reversedOpenRangeProgram
      `shouldBe` rejectedWith (MissingRangeEndpoint "rev" (spanAt 2 14))

  test "spec §46 to §52 functions type-check" $
    typeCheckOutcome functionsProgram `shouldBe` accepted

  test "spec §53 effect qualifiers type-check" $
    typeCheckOutcome effectsProgram `shouldBe` accepted

  test "spec §54 and §55 integer and floating-point literals type-check" $
    typeCheckOutcome literalsProgram `shouldBe` accepted

  test "spec §66 qubit reference arguments type-check" $
    typeCheckOutcome referenceArgumentsProgram `shouldBe` accepted

  test "spec §67 a function and a constant shadowing the gate I type-check" $
    typeCheckOutcome itemsProgram `shouldBe` accepted

  test "spec §68 attributes type-check" $
    typeCheckOutcome attributesProgram `shouldBe` accepted

  test "spec §69 recursion type-checks" $
    typeCheckOutcome recursionProgram `shouldBe` accepted

||| Every example the parser accepts, each with its test name.
examples : List (String, String)
examples =
  [ ("01_coin_flip.rs", "example 01, a coin flip, type-checks")
  , ("02_phase_kickback.rs", "example 02, phase kickback, type-checks")
  , ("03_deutsch.rs", "example 03, Deutsch's algorithm, type-checks")
  , ("04_deutsch_jozsa.rs", "example 04, Deutsch-Jozsa, type-checks")
  , ("05_deutsch_jozsa_compact_syntax.rs", "example 05, compact Deutsch-Jozsa with indexed qubits, type-checks")
  , ("06_deutsch_jozsa_even_more_compact_syntax.rs", "example 06, Deutsch-Jozsa with borrowed iteration, type-checks")
  , ("07_deutsch_jozsa_emphasizing_phase_kickback.rs", "example 07, Deutsch-Jozsa with an oracle argument, type-checks")
  , ("09_bernstein_vazirani.rs", "example 09, Bernstein-Vazirani, type-checks")
  , ("10_simons.rs", "example 10, Simon's algorithm, type-checks")
  , ("11_grover.rs", "example 11, Grover's search, type-checks")
  ]

-- The examples are read from `examples/`, relative to where the tests run.
covering
exampleOutcome : (String, String) -> IO (String, Either String ())
exampleOutcome (fileName, testName) = do
  Right exampleSource <- readFile ("examples/" ++ fileName)
    | Left fileError => pure (testName, Left ("Failed to read examples/" ++ fileName ++ ": " ++ show fileError))
  pure (testName, typeCheckOutcome exampleSource)

exampleTests : List (String, Either String ()) -> List TestResult
exampleTests = concatMap (\(testName, outcome) => test testName (outcome `shouldBe` accepted))

export covering
runTypeCheckTests : IO Bool
runTypeCheckTests = do
  outcomes <- traverse exampleOutcome examples
  runTests (exampleTests outcomes ++ specificationTests)
