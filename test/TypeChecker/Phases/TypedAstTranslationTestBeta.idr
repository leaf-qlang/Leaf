module TypeChecker.Phases.TypedAstTranslationTestBeta

import TestFramework

import TypeChecker.Helper

%default total

--------------------------------------------------------------------------------
-- Phase T: the typed AST, constructs not yet supported
--------------------------------------------------------------------------------
-- The TypedAstTranslationTest tests of constructs that the type checker does not
-- support yet: `affine` and `weaken`, `adjoint`, control blocks, `scratch`,
-- `:=`, `uncompute` and clean ancilla disposal. No runner includes these
-- groups yet; each group is added to runTypedAstTranslationTests once the type checker
-- supports its constructs.
--------------------------------------------------------------------------------

-- `affine` qualifiers and `weaken`. Left out of
-- runTypedAstTranslationTests until the type checker supports these constructs.
export
affineBetaReleaseTests : List TestResult
affineBetaReleaseTests = Test.do
  test "a let quantum usage keeps its place in the annotation" $
    printedTypedAst "fn f() -> bit { let affine q: qbit = qalloc(); H(&q); measr(q) }"
      `shouldBe` Right "general fn f() -> bit { let q: affine qbit = qalloc(); H((&q)); return measr(q); }"

-- Control blocks `ctrl(…) { … }`. Left out of
-- runTypedAstTranslationTests until the type checker supports these constructs.
export
controlBlockBetaReleaseTests : List TestResult
controlBlockBetaReleaseTests = Test.do
  test "ctrl and adjoint forms are translated" $
    printedTypedAst "fn f(c: &qbit, t: &qbit) { ctrl(c) { X(t); } adjoint { H(t); } ctrl(c).on(bs\"0\").apply(X)(t); adjoint(H)(t); }"
      `shouldBe` Right "general fn f(c: &qbit, t: &qbit) -> () { ctrl(c).on(bs\"1\") { X(t); } adjoint { H(t); } ctrl(c).on(bs\"0\").apply(X)(t); adjoint(H)(t); return (); }"

-- `scratch`, `:=`, `uncompute` and clean ancilla disposal. Left out of
-- runTypedAstTranslationTests until the type checker supports these constructs.
export
uncomputationBetaReleaseTests : List TestResult
uncomputationBetaReleaseTests = Test.do
  test "scratch and := markers are translated" $
    printedTypedAst "uncompsafe fn flip(q: qbit) -> qbit { X(q) } fn f(t: &qbit) { let b: qbit := flip(qalloc()); CX(&b, t); let scratch a = qalloc(); CX(t, &a); }"
      `shouldBe` Right "uncompsafe fn flip(q: linear qbit) -> linear qbit { return X(q); }\ngeneral fn f(t: &qbit) -> () { let b: linear qbit := flip(qalloc()); CX((&b), t); let scratch a = qalloc(); CX(t, (&a)); return (); }"
