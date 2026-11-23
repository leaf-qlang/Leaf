module TypeChecker.TypeCheckTestBeta

import TestFramework

import Compiler.Frontend.TypeChecker.Data
import TypeChecker.Helper

%default total

--------------------------------------------------------------------------------
-- Type checker integration tests, constructs not yet supported
--------------------------------------------------------------------------------
-- The TypeCheckTest tests of constructs that the type checker does not
-- support yet: `affine` and `weaken`, `adjoint`, control blocks, `scratch`,
-- `:=`, `uncompute` and clean ancilla disposal. No runner includes these
-- groups yet; each group is added to runTypeCheckTests once the type checker
-- supports its constructs.
--------------------------------------------------------------------------------

||| Spec §7 and §8: arrays, lengths and len.
arraysProgram : String
arraysProgram = """
  const N: usize = 4;
  fn arrays() {
      let bs: [bool; 4] = [true, false, true, false];
      let is: [i32; 3] = [1, 2, 3];
      let us: [u64; 2] = [10, 20];
      let fs: [f64; 3] = [1.0, 2.0, 3.0];
      let bits: [bit; 3] = [1, 0, 1];
      let angles: [angle64; 2] = [3.14, 1.57];
      let units: [(); 5] = [(), (), (), (), ()];
      let params: [param; 2] = [Param("theta"), Param("phi")];
      let qbits: [qbit; 2] = qalloc(2);
      discard(qbits);
      let linear qbits: [qbit; 2] = qalloc(2);
      discard(qbits);
      let affine qbits: [qbit; 2] = qalloc(2);
      let a: [i32; 4];
      let b: [i32; 2 + 2];
      let c: [i32; N];
      let d: [i32; 4usize];
      let bools = [true, false, true, false];
      let ints = [1, 2, 3];
      let zeros = [0; 3];
      let fs = [1.0, 2.0, 3.0];
      let qbits = qalloc(2);
      discard(qbits);
      let units = [(), (), (), (), ()];
  }
  fn member_access() -> usize {
      let a = [1, 2, 3];
      let first = a[0];
      let n = len(a);
      n
  }
  """

||| Spec §16: adjoint of gates and adjoint blocks.
adjointsProgram : String
adjointsProgram = """
  unitary fn f(a: &qbit, b: &qbit, c: &qbit) {
      CCX(a, b, c);
  }
  fn adjoints() {
      let q1 = qalloc();
      let q2 = qalloc();
      let q3 = qalloc();
      adjoint {
          f(&q1, &q2, &q3);
      }
      adjoint {
          H(&q1);
          CT(&q1, &q2)
      }
      adjoint(CT)(&q1, &q2);
      adjoint(H)(&q1);
      discard(q1, q2, q3);
  }
  """

||| Spec §16: adjoint applied to a user function as a callable.
adjointCallableProgram : String
adjointCallableProgram = """
  unitary fn f(a: &qbit, b: &qbit, c: &qbit) {
      CCX(a, b, c);
  }
  fn adjoint_callable() {
      let f_adjoint = adjoint(f);
  }
  """

||| Spec §15: ctrl over gates, as a callable and as a block, with and without a selector.
controlledGatesProgram : String
controlledGatesProgram = """
  fn controlled_gates() {
      let q0 = qalloc();
      let q1 = qalloc();
      let q2 = qalloc();
      let (q0, q1, q2): (qbit, qbit, qbit) = ctrl(q0, q1).apply(H)(q2);
      let (q0, q1, q2) = ctrl(q0, q1).apply(H)(q2);
      ctrl(&q0, &q1).apply(H)(&q2);
      ctrl(&q0, &q1) {
          H(&q2);
      }
      let (q0, q1, q2) = ctrl(q0, q1).on(bs"10").apply(H)(q2);
      ctrl(&q0, &q1).on(bs"10").apply(H)(&q2);
      ctrl(&q0, &q1).on(bs"10") {
          H(&q2);
      }
      discard(q0, q1, q2);
  }
  """

||| Spec §15: control blocks over a user function. The spec's `f` takes owned qubits in
||| the callable form and references in the block form; here it takes references.
controlledBlocksProgram : String
controlledBlocksProgram = """
  unitary fn f(a: &qbit, b: &qbit) {
      CX(a, b);
  }
  fn controlled_blocks() {
      let q0 = qalloc();
      let q1 = qalloc();
      let q2 = qalloc();
      let q3 = qalloc();
      ctrl(&q0, &q1) {
          f(&q2, &q3);
      }
      ctrl(&q0, &q1).on(bs"++") {
          f(&q2, &q3);
      }
      discard(q0, q1, q2, q3);
  }
  """

||| Spec §10 and §12: allocation, measurement and qubit qualifiers.
qubitsProgram : String
qubitsProgram = """
  fn allocation_and_measurement() -> bit {
      let q: qbit = qalloc();
      let q2: linear qbit = qalloc();
      let linear q3: qbit = qalloc();
      let qs: [qbit; 1] = qalloc(1);
      let rs: [qbit; 3] = qalloc(3);
      let b: bit = measr(q);
      let b: bit = 0;
      let bs: [bit; 3] = measr(rs);
      let q = qalloc();
      let qs3 = qalloc(3);
      let b = measr(&q);
      let b = measr(q);
      discard(q2);
      discard(q3);
      discard(qs);
      discard(qs3);
      b
  }
  fn qualifiers() {
      let linear q: qbit = qalloc();
      let linear qs: [qbit; 2] = qalloc(2);
      let q2: linear qbit = qalloc();
      let qs2: [linear qbit; 2] = qalloc(2);
      let affine a: qbit = qalloc();
      let affine aqs: [qbit; 2] = qalloc(2);
      let a2: affine qbit = qalloc();
      let aqs2: [affine qbit; 2] = qalloc(2);
      let p: (affine qbit, affine qbit) = (qalloc(), qalloc());
      let r: &qbit = &q;
      let v: &[qbit] = &qs[..];
      discard(q);
      discard(qs);
      discard(q2);
      discard(qs2);
  }
  fn scratch_qubits() {
      let scratch q: qbit = qalloc();
      let scratch qs: [qbit; 2] = qalloc(2);
      let scratch linear q1: qbit = qalloc();
      let scratch q2: linear qbit = qalloc();
      let linear scratch qs3: [qbit; 2] = qalloc(2);
      let scratch affine q4: qbit = qalloc();
      let affine scratch q5: qbit = qalloc();
      let scratch q6: affine qbit = qalloc();
  }
  fn applyHadamard(q: linear qbit) -> linear qbit {
      H(q)
  }
  """

||| Spec §38 to §44: reset, discard, uncompute, weaken, measr and barrier.
builtinsProgram : String
builtinsProgram = """
  fn resets() {
      let q: qbit = qalloc();
      let q = reset(q);
      reset(&q);
      let qs: [qbit; 3] = qalloc(3);
      let qs = reset(qs);
      reset(&qs);
      let q1 = qalloc();
      let q2 = qalloc();
      let q3 = qalloc();
      let (q1, q2, q3): (qbit, qbit, qbit) = reset(q1, q2, q3);
      let (q1, q2, q3) = reset(q1, q2, q3);
      discard(q);
      discard(qs);
      discard(q1, q2, q3);
  }
  fn discards() {
      let q: qbit = qalloc();
      discard(q);
      let q1: qbit = qalloc();
      let q2: qbit = qalloc();
      discard(q1, q2);
      let qs: [qbit; 3] = qalloc(3);
      discard(qs);
  }
  fn uncomputation() {
      let q: qbit = X(qalloc());
      let q = uncompute(q);
      let r: qbit = X(qalloc());
      uncompute(&r);
      let qs: [qbit; 3] = qalloc(3);
      X(&qs[0]);
      let qs = uncompute(qs);
      discard(q);
      discard(r);
      discard(qs);
  }
  fn weakening() {
      let linear q: qbit = qalloc();
      let affine q = weaken(q);
      let linear qs: [qbit; 3] = qalloc(3);
      let affine qs = weaken(qs);
      let q1 = qalloc();
      let q2 = qalloc();
      let q3 = qalloc();
      let affine (q1, q2, q3): (qbit, qbit, qbit) = weaken(q1, q2, q3);
  }
  fn measurements() -> [bit; 3] {
      let q: qbit = qalloc();
      let b: bit = measr(&q);
      let b: bit = measr(q);
      let q1 = qalloc();
      let q2 = qalloc();
      let q3 = qalloc();
      let (b1, b2, b3): (bit, bit, bit) = measr(q1, q2, q3);
      let qs: [qbit; 3] = qalloc(3);
      let bs: [bit; 3] = measr(&qs);
      let [b0, b1, b2]: [bit; 3] = measr(qs);
      [b0, b1, b2]
  }
  fn barriers() {
      barrier();
      let q0 = qalloc();
      let q1 = qalloc();
      let q2 = qalloc();
      let (q0, q1, q2) = barrier(q0, q1, q2);
      barrier(&q0, &q1);
      let qs = qalloc(2);
      let qs = barrier(qs);
      barrier(&qs);
      discard(q0, q1, q2);
      discard(qs);
  }
  """

||| Spec §61, with the `prepare_minus` it calls. The scratch ancilla's history
||| includes H and an opaque oracle, so its cleanup cannot be proved;
||| which check reports it first is not fixed.
phaseKickbackProgram : String
phaseKickbackProgram = """
  unitary fn prepare_minus(q: qbit) -> qbit {
      let q = X(q);
      H(q)
  }
  general fn phase_kickback(
      qs: [qbit; 4],
      oracle: unitary fn(qs: [qbit; 4], target: qbit) -> ([qbit; 4], qbit)
  ) -> [qbit; 4] {
      let scratch ancilla = qalloc();
      let ancilla = prepare_minus(ancilla);
      let (qs, ancilla) = oracle(qs, ancilla);
      qs
  }
  """

-- `affine` qualifiers and `weaken`. Left out of
-- runTypeCheckTests until the type checker supports these constructs.
export
affineBetaReleaseTests : List TestResult
affineBetaReleaseTests = Test.do
  test "spec §7 and §8 arrays and len type-check" $
    typeCheckOutcome arraysProgram `shouldBe` accepted

-- `adjoint(f)` and `adjoint { … }`. Left out of
-- runTypeCheckTests until the type checker supports these constructs.
export
adjointBetaReleaseTests : List TestResult
adjointBetaReleaseTests = Test.do
  test "spec §16 adjoints of gates and adjoint blocks type-check" $
    typeCheckOutcome adjointsProgram `shouldBe` accepted

  test "spec §16 rejects adjoint applied to a user function without adjoint support" $
    typeCheckOutcome adjointCallableProgram
      `shouldBe` rejectedWith (MissingCapability "adjoint" (spanAt 5 29))

-- Control blocks `ctrl(…) { … }`. Left out of
-- runTypeCheckTests until the type checker supports these constructs.
export
controlBlockBetaReleaseTests : List TestResult
controlBlockBetaReleaseTests = Test.do
  test "spec §15 controlled gates type-check" $
    typeCheckOutcome controlledGatesProgram `shouldBe` accepted

  test "spec §15 control blocks over a user function type-check" $
    typeCheckOutcome controlledBlocksProgram `shouldBe` accepted

-- `scratch`, `:=`, `uncompute` and clean ancilla disposal. Left out of
-- runTypeCheckTests until the type checker supports these constructs.
export
uncomputationBetaReleaseTests : List TestResult
uncomputationBetaReleaseTests = Test.do
  test "spec §10 and §12 qubit allocation, measurement and qualifiers type-check" $
    typeCheckOutcome qubitsProgram `shouldBe` accepted

  test "spec §38 to §44 qubit builtins type-check" $
    typeCheckOutcome builtinsProgram `shouldBe` accepted

  test "spec §61 rejects a scratch ancilla whose cleanup crosses an opaque oracle" $
    rejected (typeCheckOutcome phaseKickbackProgram)
      `shouldBe` True
