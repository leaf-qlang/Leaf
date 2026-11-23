module TypeChecker.Phases.SignatureCheckTestBeta

import TestFramework

import TypeChecker.Helper

%default total

--------------------------------------------------------------------------------
-- Pass A: signatures, constructs not yet supported
--------------------------------------------------------------------------------
-- The SignatureCheckTest tests of constructs that the type checker does not
-- support yet: `affine` and `weaken`, `adjoint`, control blocks, `scratch`,
-- `:=`, `uncompute` and clean ancilla disposal. No runner includes these
-- groups yet; each group is added to runSignatureCheckTests once the type checker
-- supports its constructs.
--------------------------------------------------------------------------------

-- `affine` qualifiers and `weaken`. Left out of
-- runSignatureCheckTests until the type checker supports these constructs.
export
affineBetaReleaseTests : List TestResult
affineBetaReleaseTests = Test.do
  test "qubit parameters and results may carry quantum usage qualifiers" $
    signaturesAndBodiesOutcome "fn f(q: affine qbit, p: (linear qbit, affine qbit)) -> (affine qbit, (linear qbit, affine qbit)) { (q, p) }"
      `shouldBe` accepted
