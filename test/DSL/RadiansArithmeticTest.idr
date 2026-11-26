module DSL.RadiansArithmeticTest

import DSL.Core
import TestFramework

%default total

-- These equations must reduce in a client module, including the bounds checks
-- used to construct their results. No imports beyond DSL.Core are needed for
-- the arithmetic or its proofs.
literalAdditionReduces : MkRadians 0.25 + MkRadians 0.5 = MkRadians 0.75
literalAdditionReduces = Refl

literalSubtractionReduces : MkRadians 0.75 - MkRadians 0.5 = MkRadians 0.25
literalSubtractionReduces = Refl

literalNegationReduces : DSL.Core.negate (MkRadians 0.25) = MkRadians (-0.25)
literalNegationReduces = Refl

literalAdditionWrapsAcrossBothBounds :
  ( MkRadians 4.0 + MkRadians 4.0 = MkRadians (8.0 - DSL.AngleConstants.fourPi)
  , MkRadians (-4.0) + MkRadians (-4.0) = MkRadians (DSL.AngleConstants.fourPi - 8.0)
  )
literalAdditionWrapsAcrossBothBounds = (Refl, Refl)

literalSubtractionWrapsAcrossBothBounds :
  ( MkRadians 4.0 - MkRadians (-4.0) = MkRadians (8.0 - DSL.AngleConstants.fourPi)
  , MkRadians (-4.0) - MkRadians 4.0 = MkRadians (DSL.AngleConstants.fourPi - 8.0)
  )
literalSubtractionWrapsAcrossBothBounds = (Refl, Refl)

literalAdditionWrapsUpperEndpoint :
  DSL.Core.pi + DSL.Core.pi = MkRadians (Prelude.negate DSL.AngleConstants.twoPi)
literalAdditionWrapsUpperEndpoint = Refl

literalNegationWrapsUpperEndpoint :
  DSL.Core.negate (MkRadians (Prelude.negate DSL.AngleConstants.twoPi))
    = MkRadians (Prelude.negate DSL.AngleConstants.twoPi)
literalNegationWrapsUpperEndpoint = Refl

-- The stored form of -2π, the included lower endpoint of [-2π, 2π).
minusTwoPi : Radians
minusTwoPi = MkRadians (Prelude.negate twoPi)

zeroRadians : Radians
zeroRadians = MkRadians 0.0

-- The angles one unit in the last place (ulp) inside the two endpoints. Near
-- 2π one ulp is 2^-50, about 8.88e-16.
justAboveMinusTwoPi : Radians
justAboveMinusTwoPi = MkRadians (Prelude.negate 6.283185307179585)

justBelowTwoPi : Radians
justBelowTwoPi = MkRadians 6.283185307179585

-- Two ulps near 2π, 2^-49.
twoUlpsNearTwoPi : Double
twoUlpsNearTwoPi = 1.7763568394002505e-15

export
runRadiansArithmeticTests : IO Bool
runRadiansArithmeticTests = runTests $ Test.do

  test "pi plus pi is stored as minus two pi" $
    (DSL.Core.pi + DSL.Core.pi) `shouldBe` minusTwoPi

  test "the negation of minus two pi is stored as minus two pi" $
    (DSL.Core.negate minusTwoPi) `shouldBe` minusTwoPi

  test "the sum of the two minus two pi endpoints is zero" $
    (minusTwoPi + minusTwoPi) `shouldBe` zeroRadians

  test "minus two pi plus its negation is zero, like minus two pi minus itself" $
    let twoPiSum = DSL.Core.pi + DSL.Core.pi
    in (twoPiSum + DSL.Core.negate twoPiSum, twoPiSum - twoPiSum) `shouldBe` (zeroRadians, zeroRadians)

  test "minus two pi plus pi is minus pi" $
    (minusTwoPi + DSL.Core.pi) `shouldBe` MkRadians (Prelude.negate onePi)

  -- Near the endpoints, a sum that wraps loses exactly one stored period.

  test "minus two pi plus the angle one ulp above it is zero, since the sum rounds to minus four pi" $
    (minusTwoPi + justAboveMinusTwoPi) `shouldBe` zeroRadians

  test "twice the angle one ulp above minus two pi wraps to exactly two ulps" $
    (justAboveMinusTwoPi + justAboveMinusTwoPi) `shouldBe` MkRadians twoUlpsNearTwoPi

  test "twice the angle one ulp below two pi wraps to exactly minus two ulps" $
    (justBelowTwoPi + justBelowTwoPi) `shouldBe` MkRadians (Prelude.negate twoUlpsNearTwoPi)

  test "an angle one ulp inside either endpoint plus its negation is zero" $
    ( justAboveMinusTwoPi + DSL.Core.negate justAboveMinusTwoPi
    , justBelowTwoPi + DSL.Core.negate justBelowTwoPi
    ) `shouldBe` (zeroRadians, zeroRadians)
