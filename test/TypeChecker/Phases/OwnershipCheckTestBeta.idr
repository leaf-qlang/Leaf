module TypeChecker.Phases.OwnershipCheckTestBeta

import TestFramework

import Compiler.Frontend.TypeChecker.Data
import Compiler.Frontend.Syntax.Common
import TypeChecker.Helper

%default total

--------------------------------------------------------------------------------
-- Pass C, part 2: ownership, initialization and cleanup, constructs not yet supported
--------------------------------------------------------------------------------
-- The OwnershipCheckTest tests of constructs that the type checker does not
-- support yet: `affine` and `weaken`, `adjoint`, control blocks, `scratch`,
-- `:=`, `uncompute` and clean ancilla disposal. No runner includes these
-- groups yet; each group is added to runOwnershipCheckTests once the type checker
-- supports its constructs.
--------------------------------------------------------------------------------

-- `affine` qualifiers and `weaken`. Left out of
-- runOwnershipCheckTests until the type checker supports these constructs.
export
affineBetaReleaseTests : List TestResult
affineBetaReleaseTests = Test.do
  test "an affine qubit may be dropped" $
    typeCheckOutcome "fn f() { let affine q = qalloc(); H(&q); }" `shouldBe` accepted

  test "an affine parameter may be dropped" $
    typeCheckOutcome "fn f(q: affine qbit) {}" `shouldBe` accepted

  test "a dropped affine qubit needs a discard the effect allows" $
    typeCheckOutcome "unitary fn f(q: &qbit) { let affine a = qalloc(); CX(q, &a); }"
      `shouldBe` rejectedWith (EffectViolation EffectUnitary EffectGeneral (spanAt 1 37))

-- `adjoint(f)` and `adjoint { … }`. Left out of
-- runOwnershipCheckTests until the type checker supports these constructs.
export
adjointBetaReleaseTests : List TestResult
adjointBetaReleaseTests = Test.do
  test "an adjoint block of gates can be transformed" $
    typeCheckOutcome "fn f(q1: &qbit, q2: &qbit) { adjoint { H(q1); CT(q1, q2); } }" `shouldBe` accepted

  test "an adjoint block cannot overwrite classical state" $
    typeCheckOutcome "fn f(q: &qbit) { let mut n = 0; adjoint { n = 1; H(q); } }"
      `shouldBe` rejectedWith (UnprovableTransformation "adjoint" (spanAt 1 33))

  test "an adjoint block cannot call a function that writes classical state" $
    typeCheckOutcome "unitary fn g(q: &qbit, xs: &mut [i32]) { xs[0] = 1; H(q); } fn f(q: &qbit) { let mut xs = [0]; adjoint { g(q, &mut xs); } }"
      `shouldBe` rejectedWith (UnprovableTransformation "adjoint" (spanAt 1 96))

  test "an adjoint block may update a local declared inside it" $
    typeCheckOutcome "fn f(q: &qbit) { adjoint { let mut n = 0; n += 1; if n == 1 { H(q); } } }"
      `shouldBe` accepted

  test "an opaque unitary callee does not prove an adjoint block transformable" $
    typeCheckOutcome "fn f(g: unitary fn(q: &qbit), q: &qbit) { adjoint { g(q); } }"
      `shouldBe` rejectedWith (UnprovableTransformation "adjoint" (spanAt 1 43))

  test "a known gate alias supplies transformation evidence inside an adjoint block" $
    typeCheckOutcome "fn f(q: &qbit) { let gate = H; adjoint { gate(q); } }" `shouldBe` accepted

-- Control blocks `ctrl(…) { … }`. Left out of
-- runOwnershipCheckTests until the type checker supports these constructs.
export
controlBlockBetaReleaseTests : List TestResult
controlBlockBetaReleaseTests = Test.do
  test "a control block cannot overwrite classical state" $
    typeCheckOutcome "fn f(c: &qbit, t: &qbit) { let mut n = 0; ctrl(c) { n = 1; X(t); } }"
      `shouldBe` rejectedWith (UnprovableTransformation "ctrl" (spanAt 1 43))

  test "a control block may read classical state" $
    typeCheckOutcome "fn f(c: &qbit, q: &qbit, n: i32) { ctrl(c) { if n > 0 { X(q); } } }" `shouldBe` accepted

  test "an opaque unitary callee does not prove a control block transformable" $
    typeCheckOutcome "fn f(g: unitary fn(q: &qbit), c: &qbit, q: &qbit) { ctrl(c) { g(q); } }"
      `shouldBe` rejectedWith (UnprovableTransformation "ctrl" (spanAt 1 53))

  test "a known gate alias supplies transformation evidence inside a control block" $
    typeCheckOutcome "fn f(c: &qbit, q: &qbit) { let gate = X; ctrl(c) { gate(q); } }" `shouldBe` accepted

-- `scratch`, `:=`, `uncompute` and clean ancilla disposal. Left out of
-- runOwnershipCheckTests until the type checker supports these constructs.
export
uncomputationBetaReleaseTests : List TestResult
uncomputationBetaReleaseTests = Test.do
  test "a scratch qubit computed reversibly is reclaimed at scope exit" $
    typeCheckOutcome "fn f(q: &qbit) { let scratch a = qalloc(); CX(q, &a); }" `shouldBe` accepted

  test "a scratch qubit is reclaimed on every iteration of a loop" $
    typeCheckOutcome "fn f(q: &qbit) { for i in 0..3 { let scratch a = qalloc(); CX(q, &a); } }"
      `shouldBe` accepted

  test "a scratch qubit is reclaimed when a break leaves its loop body" $
    typeCheckOutcome "fn f(q: &qbit) { for i in 0..3 { let scratch a = qalloc(); CX(q, &a); if i == 1 { break; } } }"
      `shouldBe` accepted

  test "a scratch qubit is reclaimed on an early return" $
    typeCheckOutcome "fn f(q: &qbit, c: bool) { let scratch a = qalloc(); CX(q, &a); if c { return; } }"
      `shouldBe` accepted

  test "a scratch qubit cannot be reclaimed after a gate that is not reversible classically" $
    typeCheckOutcome "fn f() { let scratch a = qalloc(); H(&a); }"
      `shouldBe` rejectedWith (UnprovableCleanup (spanAt 1 22))

  test "a scratch qubit cannot be reclaimed after its dependency changed" $
    typeCheckOutcome "fn f(q: &qbit) { let scratch a = qalloc(); CX(q, &a); H(q); }"
      `shouldBe` rejectedWith (UnprovableCleanup (spanAt 1 30))

  test "a scratch qubit cannot be reclaimed after a measurement" $
    typeCheckOutcome "fn f() -> bit { let scratch a = qalloc(); X(&a); measr(&a) }"
      `shouldBe` rejectedWith (UnprovableCleanup (spanAt 1 29))

  test "a scratch qubit cannot be returned" $
    typeCheckOutcome "fn f() -> qbit { let scratch a = qalloc(); a }"
      `shouldBe` rejectedWith (UnprovableCleanup (spanAt 1 30))

  test "a := qubit is uncomputed when the function returns" $
    typeCheckOutcome "fn f(t: &qbit) { let a: qbit := X(qalloc()); CX(&a, t); }" `shouldBe` accepted

  test "a := qubit outlives its inner block until the function returns" $
    typeCheckOutcome "fn f(t: &qbit) { { let a: qbit := X(qalloc()); CX(&a, t); } X(t); }" `shouldBe` accepted

  test "uncompute reverses a reversible computation" $
    typeCheckOutcome "fn f() { let q = X(qalloc()); let q = uncompute(q); discard(q); }" `shouldBe` accepted

  test "uncompute cannot reverse a computation that is not reversible classically" $
    typeCheckOutcome "fn f() { let q = H(qalloc()); let q = uncompute(q); discard(q); }"
      `shouldBe` rejectedWith (UnprovableCleanup (spanAt 1 39))

  test "a := qubit is uncomputed on an early return" $
    typeCheckOutcome "fn f(t: &qbit, c: bool) { let a: qbit := X(qalloc()); CX(&a, t); if c { return; } X(t); }"
      `shouldBe` accepted

  test "a := qubit cannot be returned" $
    typeCheckOutcome "fn f() -> qbit { let a: qbit := X(qalloc()); a }"
      `shouldBe` rejectedWith (UnprovableCleanup (spanAt 1 22))

  test "uncompute cannot reverse after its dependency changed" $
    typeCheckOutcome "fn f(c: &qbit) { let a = qalloc(); CX(c, &a); X(c); let a = uncompute(a); discard(a); }"
      `shouldBe` rejectedWith (UnprovableCleanup (spanAt 1 61))

  test "a scratch qubit cannot be reclaimed after its dependency is moved away" $
    typeCheckOutcome "fn f(q: qbit) { let scratch a = qalloc(); CX(&q, &a); discard(q); }"
      `shouldBe` rejectedWith (UnprovableCleanup (spanAt 1 29))

  test "shadowing a scratch qubit through a gate keeps its cleanup" $
    typeCheckOutcome "fn f(q: &qbit) { let scratch a = qalloc(); CX(q, &a); let a = X(a); CX(q, &a); }"
      `shouldBe` accepted

  test "a scratch array's cleanup skips an element discarded early" $
    typeCheckOutcome "fn f(q: &qbit) { let scratch qs = qalloc(2); CX(q, &qs[0]); discard(qs[1]); }"
      `shouldBe` accepted

  test "a scratch qubit is reclaimed when continue exits its scope" $
    typeCheckOutcome "fn f(q: &qbit) { for i in 0..3 { let scratch a = qalloc(); CX(q, &a); continue; } }" `shouldBe` accepted

  test "moving a scratch resource to a different name preserves its cleanup" $
    typeCheckOutcome "fn f(q: &qbit) { let scratch a = qalloc(); let b = a; CX(q, &b); }" `shouldBe` accepted

  test "destructuring a scratch array preserves cleanup for each resource" $
    typeCheckOutcome "fn f(q: &qbit) { let scratch qs = qalloc(2); let [a, b] = qs; CX(q, &a); CX(q, &b); }" `shouldBe` accepted
