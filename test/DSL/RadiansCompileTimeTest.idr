module DSL.RadiansCompileTimeTest

-- Compile-time checks for Radians. MkRadians accepts only literal angles in
-- [-2π, 2π), and radiansFromDouble and Radians arithmetic evaluate while a
-- module type checks. A broken check stops the test package from compiling;
-- nothing runs at test time.
--
-- The module imports DSL.Core alone, so it also checks that DSL.Core by itself
-- is enough to build Radians values and to prove facts about them.

import DSL.Core

%default total

-- Accepts a literal angle inside [-2π, 2π).
quarterRadian : Radians
quarterRadian = MkRadians 0.25

-- Rejects a literal angle outside [-2π, 2π).
failing "Can't find an implementation for So False"
  sevenRadians : Radians
  sevenRadians = MkRadians 7.0

-- The compiler must evaluate radiansFromDouble to accept each Refl below.
-- This checks that proofs written in modules that import DSL.Core can 
-- still compute radiansFromDouble's results.

-- Keeps an angle inside [-2π, 2π) unchanged.
fromDoubleKeepsAngleInsideRange : radiansFromDouble 0.25 = Just (MkRadians 0.25)
fromDoubleKeepsAngleInsideRange = Refl

-- Reduces an angle outside [-2π, 2π) by one period of 4π.
fromDoubleReducesAngleOutsideRange : radiansFromDouble 7.0 = Just (MkRadians (-5.566370614359173))
fromDoubleReducesAngleOutsideRange = Refl

-- Reduces the excluded upper endpoint 2π to the included lower endpoint -2π.
fromDoubleReducesUpperEndpoint : radiansFromDouble DSL.AngleConstants.twoPi = Just (MkRadians (Prelude.negate DSL.AngleConstants.twoPi))
fromDoubleReducesUpperEndpoint = Refl

-- Gives no angle for NaN.
fromDoubleRejectsNaN : radiansFromDouble (0.0 / 0.0) = Nothing
fromDoubleRejectsNaN = Refl

-- The compiler must evaluate Radians arithmetic, including its bounds checks
-- and reduceByOnePeriodIntoSignedTwoPiRange, to accept each Refl below.

literalAdditionReduces : MkRadians 0.25 + MkRadians 0.5 = MkRadians 0.75
literalAdditionReduces = Refl

literalSubtractionReduces : MkRadians 0.75 - MkRadians 0.5 = MkRadians 0.25
literalSubtractionReduces = Refl

literalNegationReduces : DSL.Core.negate (MkRadians 0.25) = MkRadians (-0.25)
literalNegationReduces = Refl

literalAdditionReducesAcrossBothBounds :
  ( MkRadians 4.0 + MkRadians 4.0 = MkRadians (8.0 - DSL.AngleConstants.fourPi)
  , MkRadians (-4.0) + MkRadians (-4.0) = MkRadians (DSL.AngleConstants.fourPi - 8.0)
  )
literalAdditionReducesAcrossBothBounds = (Refl, Refl)

literalSubtractionReducesAcrossBothBounds :
  ( MkRadians 4.0 - MkRadians (-4.0) = MkRadians (8.0 - DSL.AngleConstants.fourPi)
  , MkRadians (-4.0) - MkRadians 4.0 = MkRadians (DSL.AngleConstants.fourPi - 8.0)
  )
literalSubtractionReducesAcrossBothBounds = (Refl, Refl)

literalAdditionReducesUpperEndpoint : DSL.Core.pi + DSL.Core.pi = MkRadians (Prelude.negate DSL.AngleConstants.twoPi)
literalAdditionReducesUpperEndpoint = Refl

literalNegationReducesUpperEndpoint : DSL.Core.negate (MkRadians (Prelude.negate DSL.AngleConstants.twoPi)) = MkRadians (Prelude.negate DSL.AngleConstants.twoPi)
literalNegationReducesUpperEndpoint = Refl
