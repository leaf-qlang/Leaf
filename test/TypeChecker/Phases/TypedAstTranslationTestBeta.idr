module TypeChecker.Phases.TypedAstTranslationTestBeta

import TestFramework

import TypeChecker.Helper

%default total

--------------------------------------------------------------------------------
-- Phase T: the typed AST, stage 2
--------------------------------------------------------------------------------
-- The TypedAstTranslationTest tests of the constructs that stage 2 adds (plan part
-- A.6): `affine` and `weaken`, `adjoint`, control blocks, `scratch`, `:=`,
-- `uncompute` and clean ancilla disposal. No runner includes these groups
-- yet; each stage 2 step (plan steps 18 to 21) adds its group to
-- runTypedAstTranslationTests.
--------------------------------------------------------------------------------

-- Stage 2, plan step 18: `affine` qualifiers and `weaken`. Left out of
-- runTypedAstTranslationTests until step 18 re-enables this group.
export
affineStageTwoTests : List TestResult
affineStageTwoTests = Test.do
  test "a let quantum usage keeps its place in the annotation" $
    printedTypedAst "fn f() -> bit { let affine q: qbit = qalloc(); H(&q); measr(q) }"
      `shouldBe` Right "general fn f() -> bit { let q: affine qbit = qalloc(); H((&q)); return measr(q); }"

-- Stage 2, plan step 20: control blocks `ctrl(…) { … }`. Left out of
-- runTypedAstTranslationTests until step 20 re-enables this group.
export
controlBlockStageTwoTests : List TestResult
controlBlockStageTwoTests = Test.do
  test "ctrl and adjoint forms are translated" $
    printedTypedAst "fn f(c: &qbit, t: &qbit) { ctrl(c) { X(t); } adjoint { H(t); } ctrl(c).on(bs\"0\").apply(X)(t); adjoint(H)(t); }"
      `shouldBe` Right "general fn f(c: &qbit, t: &qbit) -> () { ctrl(c).on(bs\"1\") { X(t); } adjoint { H(t); } ctrl(c).on(bs\"0\").apply(X)(t); adjoint(H)(t); return (); }"

-- Stage 2, plan step 21: `scratch`, `:=`, `uncompute` and clean ancilla disposal. Left out of
-- runTypedAstTranslationTests until step 21 re-enables this group.
export
uncomputationStageTwoTests : List TestResult
uncomputationStageTwoTests = Test.do
  test "scratch and := markers are translated" $
    printedTypedAst "uncompsafe fn flip(q: qbit) -> qbit { X(q) } fn f(t: &qbit) { let b: qbit := flip(qalloc()); CX(&b, t); let scratch a = qalloc(); CX(t, &a); }"
      `shouldBe` Right "uncompsafe fn flip(q: linear qbit) -> linear qbit { return X(q); }\ngeneral fn f(t: &qbit) -> () { let b: linear qbit := flip(qalloc()); CX((&b), t); let scratch a = qalloc(); CX(t, (&a)); return (); }"
