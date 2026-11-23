module TypeChecker.Phases.OwnershipEventsTestBeta

import TestFramework

import Compiler.Frontend.TypeChecker.Data
import TypeChecker.Helper

%default total

--------------------------------------------------------------------------------
-- Pass C, part 1: ownership events, constructs not yet supported
--------------------------------------------------------------------------------
-- The OwnershipEventsTest tests of constructs that the type checker does not
-- support yet: `affine` and `weaken`, `adjoint`, control blocks, `scratch`,
-- `:=`, `uncompute` and clean ancilla disposal. No runner includes these
-- groups yet; each group is added to runOwnershipEventsTests once the type checker
-- supports its constructs.
--------------------------------------------------------------------------------

-- `affine` qualifiers and `weaken`. Left out of
-- runOwnershipEventsTests until the type checker supports these constructs.
export
affineBetaReleaseTests : List TestResult
affineBetaReleaseTests = Test.do
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

-- Control blocks `ctrl(…) { … }`. Left out of
-- runOwnershipEventsTests until the type checker supports these constructs.
export
controlBlockBetaReleaseTests : List TestResult
controlBlockBetaReleaseTests = Test.do
  test "a borrowed control conflicts with a write to it inside its block" $
    typeCheckOutcome "fn f(c: &qbit) { ctrl(c) { X(c); } }"
      `shouldBe` rejectedWith (OverlappingBorrow (spanAt 1 30))
