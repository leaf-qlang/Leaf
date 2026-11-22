module TypeChecker.Phases.OwnershipEventsTestBeta

import TestFramework

import Compiler.Frontend.TypeChecker.Data
import TypeChecker.Helper

%default total

--------------------------------------------------------------------------------
-- Pass C, part 1: ownership events, stage 2
--------------------------------------------------------------------------------
-- The OwnershipEventsTest tests of the constructs that stage 2 adds (plan part
-- A.6): `affine` and `weaken`, `adjoint`, control blocks, `scratch`, `:=`,
-- `uncompute` and clean ancilla disposal. No runner includes these groups
-- yet; each stage 2 step (plan steps 18 to 21) adds its group to
-- runOwnershipEventsTests.
--------------------------------------------------------------------------------

-- Stage 2, plan step 18: `affine` qualifiers and `weaken`. Left out of
-- runOwnershipEventsTests until step 18 re-enables this group.
export
affineStageTwoTests : List TestResult
affineStageTwoTests = Test.do
  test "an affine temporary may be dropped" $
    typeCheckOutcome "fn f(q: affine qbit) { H(q); }" `shouldBe` accepted

  test "weaken moves the original linear resource" $
    typeCheckOutcome "fn f(q: qbit) { let affine r = weaken(q); discard(q); }"
      `shouldBe` rejectedWith (UseAfterMove "q" (spanAt 1 51))

  test "a zero repeat count permits an affine operand to be dropped" $
    typeCheckOutcome "fn f() { let qs = [weaken(qalloc()); 0]; }" `shouldBe` accepted

  test "breaking from owned iteration may discard remaining affine elements" $
    typeCheckOutcome "fn f() { for q in weaken(qalloc(2)) { discard(q); break; } }" `shouldBe` accepted

  test "returning from owned iteration may discard remaining affine elements" $
    typeCheckOutcome "fn f() { for q in weaken(qalloc(2)) { discard(q); return; } }" `shouldBe` accepted

  test "repeating an affine qubit more than once is rejected" $
    rejected (typeCheckOutcome "fn f() { let qs = [weaken(qalloc()); 2]; }")
      `shouldBe` True

-- Stage 2, plan step 20: control blocks `ctrl(…) { … }`. Left out of
-- runOwnershipEventsTests until step 20 re-enables this group.
export
controlBlockStageTwoTests : List TestResult
controlBlockStageTwoTests = Test.do
  test "a borrowed control conflicts with a write to it inside its block" $
    typeCheckOutcome "fn f(c: &qbit) { ctrl(c) { X(c); } }"
      `shouldBe` rejectedWith (OverlappingBorrow (spanAt 1 30))
