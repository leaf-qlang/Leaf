module DSL.RadiansConstructionTest

-- This module imports DSL.Core alone, so it checks that DSL.Core by itself is
-- enough to build a Radians value from a literal angle.
import DSL.Core

%default total

-- Accepts a literal angle inside [-2π, 2π).
quarterRadian : Radians
quarterRadian = MkRadians 0.25

-- Rejects a literal angle outside [-2π, 2π).
failing "Can't find an implementation for So False"
  sevenRadians : Radians
  sevenRadians = MkRadians 7.0

-- radiansFromDouble reduces in a client proof, so these equations hold by Refl.

-- Keeps an angle inside [-2π, 2π) unchanged.
fromDoubleKeepsAngleInsideRange : radiansFromDouble 0.25 = Just (MkRadians 0.25)
fromDoubleKeepsAngleInsideRange = Refl

-- Reduces an angle outside [-2π, 2π) by one period of 4π.
fromDoubleReducesAngleOutsideRange : radiansFromDouble 7.0 = Just (MkRadians (-5.566370614359173))
fromDoubleReducesAngleOutsideRange = Refl

-- Wraps the excluded upper endpoint 2π to the included lower endpoint -2π.
fromDoubleWrapsUpperEndpoint :
  radiansFromDouble DSL.AngleConstants.twoPi = Just (MkRadians (Prelude.negate DSL.AngleConstants.twoPi))
fromDoubleWrapsUpperEndpoint = Refl

-- Gives no angle for NaN.
fromDoubleRejectsNaN : radiansFromDouble (0.0 / 0.0) = Nothing
fromDoubleRejectsNaN = Refl
