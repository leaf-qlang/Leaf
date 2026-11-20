module DSL.Wrap2Pi

%default total

-- This code is using the Cody–Waite split of 2π

twoPi : Double
twoPi = 2 * Prelude.pi

twoPiHi : Double
twoPiHi = 6.28125

twoPiLo : Double
twoPiLo = 1.9353071795864769253e-3

truncD : Double -> Double
truncD x = if x < 0 then ceiling x else floor x

export
wrap : Double -> Double
wrap x =
  let n = truncD (x / twoPi)
      r = (x - n * twoPiHi) - n * twoPiLo
  in if r > twoPi then r - twoPi
     else if r <= negate twoPi then r + twoPi
     else r
