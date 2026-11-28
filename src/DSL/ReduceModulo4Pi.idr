module DSL.ReduceModulo4Pi

import DSL.AngleConstants

%default total

-- Standard trick for reducing doubles without losing precision (Cody–Waite).
-- 4π is split into three parts whose sum is closer to the true 4π than a single
-- Double. Removing k periods as three separate subtractions, largest part first,
-- avoids multiplying the rounding error of a single-Double 4π by k. The high and
-- middle parts are short enough that multiplying them by k gives an exact
-- result, with no rounding, as long as the angle is below the 2^35 cutoff used
-- below. Only the product with the tiny low part can round, and that error is
-- negligible.

public export
fourPiHigh : Double
fourPiHigh = 12.566368103027344

public export
fourPiMiddle : Double
fourPiMiddle = 2.511331331334077e-6

public export
fourPiLow : Double
fourPiLow = 4.978697737517291e-13

-- Rotation angles are taken modulo 4π, the period of the rotation gates, and
-- each angle is represented by its unique value in [-2π, 2π).
public export
reduceIntoSignedTwoPiRange : Double -> Double
reduceIntoSignedTwoPiRange angle =
  let magnitude = abs angle
      remainder =
        if magnitude <= twoPi then angle
        else if magnitude < 34359738368.0 then -- 2^35, so |periodCount| < 2^32
          let nearestPeriodCount = floor (angle / fourPi + 0.5)
          in ((angle - nearestPeriodCount * fourPiHigh) - nearestPeriodCount * fourPiMiddle)
               - nearestPeriodCount * fourPiLow
        else
          -- tan has period π. Applying atan to the result gives a quarter-angle
          -- between -π/2 and π/2. Scaling back by four gives a period of 4π.
          -- For large inputs, accuracy depends on the platform's math library.
          4.0 * atan (tan (angle / 4.0))
  in -- A result outside [-twoPi, twoPi) needs one final adjustment.
     -- In particular, twoPi reduces to -twoPi.
     if remainder >= twoPi then remainder - fourPi
     else if remainder < negate twoPi then remainder + fourPi
     else remainder
