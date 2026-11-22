module TypeChecker.Phases.SignatureCheckTestBeta

import TestFramework

import TypeChecker.Helper

%default total

--------------------------------------------------------------------------------
-- Pass A: signatures, stage 2
--------------------------------------------------------------------------------
-- The SignatureCheckTest tests of the constructs that stage 2 adds (plan part
-- A.6): `affine` and `weaken`, `adjoint`, control blocks, `scratch`, `:=`,
-- `uncompute` and clean ancilla disposal. No runner includes these groups
-- yet; each stage 2 step (plan steps 18 to 21) adds its group to
-- runSignatureCheckTests.
--------------------------------------------------------------------------------

-- Stage 2, plan step 18: `affine` qualifiers and `weaken`. Left out of
-- runSignatureCheckTests until step 18 re-enables this group.
export
affineStageTwoTests : List TestResult
affineStageTwoTests = Test.do
  test "qubit parameters and results may carry quantum usage qualifiers" $
    signaturesAndBodiesOutcome "fn f(q: affine qbit, p: (linear qbit, affine qbit)) -> (affine qbit, (linear qbit, affine qbit)) { (q, p) }"
      `shouldBe` accepted
