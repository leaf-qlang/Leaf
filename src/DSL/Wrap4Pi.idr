module DSL.Wrap4Pi

import DSL.AngleConstants

%default total

-- These three parts approximate 4π. Subtracting their multiples separately
-- preserves precision when removing many periods. The high and middle parts
-- each use 21 significant bits, so their products with the period count are
-- exact below the cutoff used here. The low-part product can still round.
fourPiHigh : Double
fourPiHigh = 12.566368103027344

fourPiMiddle : Double
fourPiMiddle = 2.511331331334077e-6

fourPiLow : Double
fourPiLow = 4.978697737517291e-13

-- Rotation angles are taken modulo 4π, the period of the rotation gates, and
-- each angle is represented by its unique value in [-2π, 2π).
export
reduceModuloFourPiIntoSignedTwoPiRange : Double -> Double
reduceModuloFourPiIntoSignedTwoPiRange angle =
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
     -- In particular, twoPi wraps to -twoPi.
     if remainder >= twoPi then remainder - fourPi
     else if remainder < negate twoPi then remainder + fourPi
     else remainder
