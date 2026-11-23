module DSL.Wrap2Pi

import DSL.AngleConstants

%default total

-- Cody–Waite split of 4π into a high part with few significant bits and a low
-- part holding the rest: 4π ≈ fourPiHigh + fourPiLow. fourPiHigh = 201/16 has
-- 8 significant bits, so periodCount * fourPiHigh is exact while
-- |periodCount| < 2^45 (|angle| below about 2^48), and subtracting it loses no
-- precision. The remaining error comes from rounding periodCount * fourPiLow,
-- so it grows with |angle|: about 1e-15 near [-2π, 2π) and 4e-13 near 1e7.
fourPiHigh : Double
fourPiHigh = 12.5625

fourPiLow : Double
fourPiLow = 3.8706143591729538506e-3

-- Rotation angles are taken modulo 4π, the period of the rotation gates, and
-- each angle is represented by its unique value in [-2π, 2π).
export
reduceModuloFourPiIntoSignedTwoPiRange : Double -> Double
reduceModuloFourPiIntoSignedTwoPiRange angle =
  let nearestPeriodCount = floor (angle / fourPi + 0.5)
      remainder = (angle - nearestPeriodCount * fourPiHigh) - nearestPeriodCount * fourPiLow
  in -- Rounding can leave the remainder just outside [-2π, 2π); one period
     -- brings it back. Both corrections are exact because fourPi = 2 * twoPi.
     if remainder >= twoPi then remainder - fourPi
     else if remainder < negate twoPi then remainder + fourPi
     else remainder
