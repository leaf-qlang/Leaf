module TypeChecker.Phases.EffectsCheckTestBeta

import TestFramework

import Compiler.Frontend.TypeChecker.Data
import Compiler.Frontend.Syntax.Common
import TypeChecker.Helper

%default total

--------------------------------------------------------------------------------
-- Pass E: effects, capabilities and attributes, stage 2
--------------------------------------------------------------------------------
-- The EffectsCheckTest tests of the constructs that stage 2 adds (plan part
-- A.6): `affine` and `weaken`, `adjoint`, control blocks, `scratch`, `:=`,
-- `uncompute` and clean ancilla disposal. No runner includes these groups
-- yet; each stage 2 step (plan steps 18 to 21) adds its group to
-- runEffectsCheckTests.
--------------------------------------------------------------------------------

-- Stage 2, plan step 18: `affine` qualifiers and `weaken`. Left out of
-- runEffectsCheckTests until step 18 re-enables this group.
export
affineStageTwoTests : List TestResult
affineStageTwoTests = Test.do
  test "weaken and barrier are classical operations" $
    typeCheckOutcome "uncompsafe fn f(q: qbit) -> affine qbit { barrier(&q); weaken(q) }" `shouldBe` accepted

-- Stage 2, plan step 19: `adjoint(f)` and `adjoint { … }`. Left out of
-- runEffectsCheckTests until step 19 re-enables this group.
export
adjointStageTwoTests : List TestResult
adjointStageTwoTests = Test.do
  test "the adjoint of a gate is permitted in unitary code" $
    typeCheckOutcome "unitary fn f(q: &qbit) { adjoint(H)(q); adjoint(S)(q); }" `shouldBe` accepted

  test "the adjoint of a user function needs adjoint support" $
    typeCheckOutcome "unitary fn g(q: &qbit) { H(q); } unitary fn f(q: &qbit) { adjoint(g)(q); }"
      `shouldBe` rejectedWith (MissingCapability "adjoint" (spanAt 1 67))

  test "an adjoint block may call a unitary user function" $
    typeCheckOutcome "unitary fn g(q: &qbit) { H(q); } unitary fn f(q: &qbit) { adjoint { g(q); } }"
      `shouldBe` accepted

  test "an adjoint block admits only unitary operations" $
    typeCheckOutcome "general fn f(q: &qbit) { adjoint { let b = measr(q); } }"
      `shouldBe` rejectedWith (EffectViolation EffectUnitary EffectGeneral (spanAt 1 44))

  test "an adjoint block does not lift an enclosing classical ceiling" $
    typeCheckOutcome "classical fn f() { adjoint { let q = qalloc(); } }"
      `shouldBe` rejectedWith (EffectViolation EffectClassical EffectUncompsafe (spanAt 1 38))

  test "the adjoint of a function-typed parameter needs adjoint support" $
    typeCheckOutcome "unitary fn f(g: unitary fn(q: &qbit), q: &qbit) { adjoint(g)(q); }"
      `shouldBe` rejectedWith (MissingCapability "adjoint" (spanAt 1 59))

  test "the adjoint of a gate alias is permitted" $
    typeCheckOutcome "fn f(q: &qbit) { let s = S; adjoint(s)(q); }" `shouldBe` accepted

  test "the adjoint of a gate's adjoint is permitted" $
    typeCheckOutcome "fn f(q: &qbit) { adjoint(adjoint(T))(q); }" `shouldBe` accepted

  test "a callable join intersects capabilities instead of retaining adjoint" $
    typeCheckOutcome "unitary fn plain(q: qbit) -> qbit { H(q) } fn f(flag: bool, q: qbit) -> qbit { let g = if flag { H } else { plain }; adjoint(g)(q) }"
      `shouldBe` rejectedWith (MissingCapability "adjoint" (spanAt 1 126))

  test "a break cannot leave an adjoint block" $
    typeCheckOutcome "fn f(q: &qbit) { for i in 0..3 { adjoint { H(q); break; } } }"
      `shouldBe` rejectedWith (JumpOutOfQuantumBlock "break" (spanAt 1 50))

  test "a loop inside an adjoint block stays inside it" $
    typeCheckOutcome "fn f(q: &qbit) { adjoint { for i in 0..3 { H(q); } } }" `shouldBe` accepted

  test "an adjoint block preserves the enclosing uncompsafe ceiling" $
    typeCheckOutcome "uncompsafe fn f(q: &qbit) { adjoint { H(q); } }"
      `shouldBe` rejectedWith (EffectViolation EffectUncompsafe EffectUnitary (spanAt 1 39))

  test "the adjoint of a basis permutation remains uncompsafe" $
    typeCheckOutcome "uncompsafe fn f(q: &qbit) { adjoint(X)(q); }" `shouldBe` accepted

  test "a return cannot leave an adjoint block" $
    typeCheckOutcome "fn f(q: &qbit) { adjoint { H(q); return; } }"
      `shouldBe` rejectedWith (JumpOutOfQuantumBlock "return" (spanAt 1 34))

-- Stage 2, plan step 20: control blocks `ctrl(…) { … }`. Left out of
-- runEffectsCheckTests until step 20 re-enables this group.
export
controlBlockStageTwoTests : List TestResult
controlBlockStageTwoTests = Test.do
  test "a control block may call a unitary user function" $
    typeCheckOutcome "unitary fn g(q: &qbit) { H(q); } unitary fn f(c: &qbit, q: &qbit) { ctrl(c) { g(q); } }"
      `shouldBe` accepted

  test "a control block on - is a unitary operation" $
    typeCheckOutcome "uncompsafe fn f(c: &qbit, t: &qbit) { ctrl(c).on(bs\"-\") { X(t); } }"
      `shouldBe` rejectedWith (EffectViolation EffectUncompsafe EffectUnitary (spanAt 1 39))

  test "a control block nested in an adjoint block over gates is permitted" $
    typeCheckOutcome "unitary fn f(c: &qbit, q: &qbit) { adjoint { ctrl(c) { H(q); } } }" `shouldBe` accepted

  test "a control block over X keeps an uncompsafe function uncompsafe" $
    typeCheckOutcome "uncompsafe fn f(c: &qbit, t: &qbit) { ctrl(c) { X(t); } }" `shouldBe` accepted

  test "a return cannot leave a control block" $
    typeCheckOutcome "fn f(c: &qbit, t: &qbit) { ctrl(c) { X(t); return; } }"
      `shouldBe` rejectedWith (JumpOutOfQuantumBlock "return" (spanAt 1 44))

  test "a continue cannot leave a control block" $
    typeCheckOutcome "fn f(c: &qbit, t: &qbit) { for i in 0..3 { ctrl(c) { X(t); continue; } } }"
      `shouldBe` rejectedWith (JumpOutOfQuantumBlock "continue" (spanAt 1 60))

  test "a control block preserves the enclosing uncompsafe ceiling" $
    typeCheckOutcome "uncompsafe fn f(c: &qbit, q: &qbit) { ctrl(c) { H(q); } }"
      `shouldBe` rejectedWith (EffectViolation EffectUncompsafe EffectUnitary (spanAt 1 49))

  test "an imaginary negative-basis selector raises a control block to unitary" $
    typeCheckOutcome "uncompsafe fn f(c: &qbit, q: &qbit) { ctrl(c).on(bs\"I\") { X(q); } }"
      `shouldBe` rejectedWith (EffectViolation EffectUncompsafe EffectUnitary (spanAt 1 39))

  test "a break targeting a loop inside a control block is allowed" $
    typeCheckOutcome "fn f(c: &qbit, q: &qbit) { ctrl(c) { loop { X(q); break; } } }" `shouldBe` accepted

-- Stage 2, plan step 21: `scratch`, `:=`, `uncompute` and clean ancilla disposal. Left out of
-- runEffectsCheckTests until step 21 re-enables this group.
export
uncomputationStageTwoTests : List TestResult
uncomputationStageTwoTests = Test.do
  test "qalloc is permitted in a unitary function" $
    typeCheckOutcome "unitary fn f(q: &qbit) { let scratch a = qalloc(); CX(q, &a); }" `shouldBe` accepted

  test "a unitary function may discard a fresh ancilla" $
    typeCheckOutcome "unitary fn f(q: &qbit) { let a = qalloc(); discard(a); }" `shouldBe` accepted

  test "a unitary function may uncompute and discard an ancilla" $
    typeCheckOutcome "unitary fn f(c: &qbit) { let a = qalloc(); CX(c, &a); let a = uncompute(a); discard(a); }"
      `shouldBe` accepted

  test "a := initializer admits only uncompsafe operations" $
    typeCheckOutcome "general fn f() { let q: qbit := H(qalloc()); }"
      `shouldBe` rejectedWith (EffectViolation EffectUncompsafe EffectUnitary (spanAt 1 33))

  test ":= accepts an uncompsafe qubit initializer" $
    typeCheckOutcome "uncompsafe fn flip(q: qbit) -> qbit { X(q) } fn f() { let q: qbit := flip(qalloc()); }"
      `shouldBe` accepted

  test "a := initializer preserves the enclosing classical ceiling" $
    typeCheckOutcome "classical fn f() { let q: qbit := qalloc(); }"
      `shouldBe` rejectedWith (EffectViolation EffectClassical EffectUncompsafe (spanAt 1 35))
