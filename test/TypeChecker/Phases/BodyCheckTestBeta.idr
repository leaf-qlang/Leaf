module TypeChecker.Phases.BodyCheckTestBeta

import TestFramework

import Compiler.Frontend.TypeChecker.Data
import Compiler.Frontend.TypeChecker.Type
import Compiler.Frontend.Syntax.Common
import TypeChecker.Helper

%default total

--------------------------------------------------------------------------------
-- Pass B: bodies and inference, stage 2
--------------------------------------------------------------------------------
-- The BodyCheckTest tests of the constructs that stage 2 adds (plan part
-- A.6): `affine` and `weaken`, `adjoint`, control blocks, `scratch`, `:=`,
-- `uncompute` and clean ancilla disposal. No runner includes these groups
-- yet; each stage 2 step (plan steps 18 to 21) adds its group to
-- runBodyCheckTests.
--------------------------------------------------------------------------------

-- Stage 2, plan step 18: `affine` qualifiers and `weaken`. Left out of
-- runBodyCheckTests until step 18 re-enables this group.
export
affineStageTwoTests : List TestResult
affineStageTwoTests = Test.do
  test "function parameter quantum usage qualifiers must match exactly" $
    signaturesAndBodiesOutcome "fn keep(q: affine qbit) -> affine qbit { q } fn run(g: fn(q: qbit) -> qbit, q: qbit) -> qbit { g(q) } fn f() -> qbit { run(keep, qalloc()) }"
      `shouldBe` rejectedWith (TypeMismatch (fnType EffectGeneral [linearQbit] linearQbit) (fnType EffectGeneral [affineQbit] affineQbit) (spanAt 1 124))

  test "a branch join keeps qubit quantum usage qualifiers invariant" $
    signaturesAndBodiesOutcome "fn f(c: bool, a: qbit, b: affine qbit) { let q = if c { a } else { b }; discard(q); }"
      `shouldBe` rejectedWith (TypeMismatch linearQbit affineQbit (spanAt 1 68))

  test "let and type qualifiers give qubits their quantum usage" $
    signaturesAndBodiesOutcome "fn f() { let linear a: qbit = qalloc(); let b: linear qbit = qalloc(); let affine c: qbit = qalloc(); let d: affine qbit = qalloc(); let e: [affine qbit; 2] = qalloc(2); let p: (affine qbit, affine qbit) = (qalloc(), qalloc()); discard(a); discard(b); }"
      `shouldBe` accepted

  test "an affine let fixes an inferred qubit's quantum usage" $
    signaturesAndBodiesOutcome "fn f() { let affine q = qalloc(); }" `shouldBe` accepted

  test "a gate preserves its argument's quantum usage" $
    signaturesAndBodiesOutcome "fn f() { let affine q: qbit = qalloc(); let affine r = H(q); }" `shouldBe` accepted

  test "an affine let cannot hold a linear qubit" $
    signaturesAndBodiesOutcome "fn f() { let q: qbit = qalloc(); let affine r = H(q); discard(r); }"
      `shouldBe` rejectedWith (QuantumUsageMismatch QuantumUsageAffine QuantumUsageLinear (spanAt 1 38))

  test "weaken makes qubits affine" $
    signaturesAndBodiesOutcome "fn f() { let linear q: qbit = qalloc(); let affine q = weaken(q); let linear qs: [qbit; 3] = qalloc(3); let affine qs = weaken(qs); }"
      `shouldBe` accepted

  test "weaken's result is affine without a qualifier" $
    signaturesAndBodiesOutcome "fn f() { let q = qalloc(); let r = weaken(q); }" `shouldBe` accepted

  test "weaken's result is not linear" $
    signaturesAndBodiesOutcome "fn f() { let q = qalloc(); let r: qbit = weaken(q); discard(r); }"
      `shouldBe` rejectedWith (TypeMismatch linearQbit affineQbit (spanAt 1 42))

  test "weaken of several qubits returns affine qubits" $
    signaturesAndBodiesOutcome "fn f() { let q1 = qalloc(); let q2 = qalloc(); let q3 = qalloc(); let affine (a, b, c): (qbit, qbit, qbit) = weaken(q1, q2, q3); }"
      `shouldBe` accepted

  test "an affine qualifier needs a qubit" $
    signaturesAndBodiesOutcome "fn f() { let affine n = 5; }"
      `shouldBe` rejectedWith (InvalidQuantumQualifier "affine" i32 (spanAt 1 14))

  test "an affine let over a tuple qualifies only its qubit positions" $
    signaturesAndBodiesOutcome "fn f() -> i32 { let affine (q, n) = (qalloc(), 1); n }" `shouldBe` accepted

  test "weaken takes owned qubits only" $
    signaturesAndBodiesOutcome "fn f(q: &qbit) { let r = weaken(q); }"
      `shouldBe` rejectedWith (TypeMismatch linearQbit qbitRef (spanAt 1 33))

  test "an owned gate on an affine qubit returns an affine qubit" $
    signaturesAndBodiesOutcome "fn f(q: affine qbit) -> affine qbit { H(q) }" `shouldBe` accepted

  test "an owned gate on an affine qubit does not return a linear qubit" $
    signaturesAndBodiesOutcome "fn f(q: affine qbit) -> qbit { H(q) }"
      `shouldBe` rejectedWith (TypeMismatch linearQbit affineQbit (spanAt 1 32))

  test "a two-qubit gate returns each argument's quantum usage" $
    signaturesAndBodiesOutcome "fn f(a: affine qbit, b: qbit) -> (affine qbit, qbit) { CX(a, b) }" `shouldBe` accepted

  test "reset preserves an affine argument's quantum usage" $
    signaturesAndBodiesOutcome "fn f(q: affine qbit) -> affine qbit { reset(q) }" `shouldBe` accepted

-- Stage 2, plan step 19: `adjoint(f)` and `adjoint { … }`. Left out of
-- runBodyCheckTests until step 19 re-enables this group.
export
adjointStageTwoTests : List TestResult
adjointStageTwoTests = Test.do
  test "a controlled adjoint gate type-checks" $
    signaturesAndBodiesOutcome "fn f(c: &qbit, q: &qbit) { ctrl(c).apply(adjoint(S))(q); }" `shouldBe` accepted

  test "the adjoint of a gate keeps the gate's owned and borrowed forms" $
    signaturesAndBodiesOutcome "fn f(q1: qbit, q2: qbit) -> (qbit, qbit) { let q1 = adjoint(H)(q1); adjoint(H)(&q1); adjoint(CT)(&q1, &q2); (q1, q2) }"
      `shouldBe` accepted

  test "the adjoint of a rotation still takes its angle" $
    signaturesAndBodiesOutcome "fn f(q: &qbit) { adjoint(RX)(1.0, q); }" `shouldBe` accepted

  test "the adjoint of a rotation needs its angle" $
    signaturesAndBodiesOutcome "fn f(q: &qbit) { adjoint(RX)(q); }"
      `shouldBe` rejectedWith (WrongArgumentCount 2 1 (spanAt 1 18))

  test "an adjoint alias keeps the gate's borrowed form" $
    signaturesAndBodiesOutcome "fn f(q: &qbit) { let h = adjoint(H); h(q); }" `shouldBe` accepted

  test "an adjoint block has unit type" $
    signaturesAndBodiesOutcome "fn f(q1: &qbit, q2: &qbit) { let u: () = adjoint { H(q1); CT(q1, q2) }; }"
      `shouldBe` accepted

  test "the adjoint of an owned two-qubit gate returns both qubits" $
    signaturesAndBodiesOutcome "fn f(a: qbit, b: qbit) -> (qbit, qbit) { adjoint(CX)(a, b) }" `shouldBe` accepted

  test "an adjoint rotation alias independently accepts f32 and f64 calls" $
    signaturesAndBodiesOutcome "fn f(q: &qbit) { let rotate = adjoint(RX); rotate(0.5f32, q); rotate(0.5f64, q); }"
      `shouldBe` accepted

-- Stage 2, plan step 20: control blocks `ctrl(…) { … }`. Left out of
-- runBodyCheckTests until step 20 re-enables this group.
export
controlBlockStageTwoTests : List TestResult
controlBlockStageTwoTests = Test.do
  test "a control block over borrowed controls has unit type" $
    signaturesAndBodiesOutcome "fn f(q0: &qbit, q1: &qbit, q2: &qbit) { ctrl(q0, q1) { H(q2); } let u: () = ctrl(q0, q1).on(bs\"10\") { H(q2); }; }"
      `shouldBe` accepted

  test "a control block requires borrowed controls" $
    signaturesAndBodiesOutcome "fn f(q0: qbit, q2: &qbit) -> qbit { ctrl(q0) { H(q2); } q0 }"
      `shouldBe` rejectedWith (TypeMismatch qbitRef linearQbit (spanAt 1 42))

-- Stage 2, plan step 21: `scratch`, `:=`, `uncompute` and clean ancilla disposal. Left out of
-- runBodyCheckTests until step 21 re-enables this group.
export
uncomputationStageTwoTests : List TestResult
uncomputationStageTwoTests = Test.do
  test "scratch qualifiers apply to qubit bindings" $
    signaturesAndBodiesOutcome "fn f() { let scratch q: qbit = qalloc(); let scratch qs: [qbit; 2] = qalloc(2); let scratch affine r: qbit = qalloc(); }"
      `shouldBe` accepted

  test "a scratch qualifier needs a qubit" $
    signaturesAndBodiesOutcome "fn f() { let scratch n: i32 = 5; }"
      `shouldBe` rejectedWith (InvalidQuantumQualifier "scratch" i32 (spanAt 1 14))

  test ":= needs a qubit-valued initializer" $
    signaturesAndBodiesOutcome "fn f() { let x: i32 := 5; }"
      `shouldBe` rejectedWith (InvalidQuantumQualifier ":=" i32 (spanAt 1 21))

  test "uncompute consumes and returns or borrows its qubits" $
    signaturesAndBodiesOutcome "fn f() { let a = X(qalloc()); uncompute(&a); discard(a); let b = X(qalloc()); let b = uncompute(b); discard(b); }"
      `shouldBe` accepted
