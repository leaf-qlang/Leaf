module DSL.Core

import public Data.So

import public DSL.AngleConstants
import public DSL.Wrap4Pi

%default total

public export
inBounds : Double -> Bool
inBounds angle = negate twoPi <= angle && angle < twoPi

public export
data Radians : Type where
  MkRadians : (angle : Double) -> {auto 0 prf : So (inBounds angle)} -> Radians

-- Matching on the bounds check directly, rather than through Data.So.choose,
-- keeps radiansFromDouble reducible in client proofs. The check fails only for
-- NaN and ±Infinity.
public export
radiansFromDouble : Double -> Maybe Radians
radiansFromDouble angle
    with (inBounds (reduceModuloFourPiIntoSignedTwoPiRange angle)) proof 0 boundsCheck
  radiansFromDouble angle | True =
    Just (MkRadians (reduceModuloFourPiIntoSignedTwoPiRange angle) {prf = rewrite boundsCheck in Oh})
  radiansFromDouble angle | False = Nothing

-- Arithmetic on angles in [-2π, 2π) produces values in [-4π, 4π] after rounding.
-- Wrap these results by removing at most one period. The period is the stored
-- fourPi, so the wrap is exact, -2π + -2π is 0, and a + negate a equals a - a.
-- Caveat: arithmetic is modulo the stored fourPi, not the exact 4π used by
-- radiansFromDouble, so each wrap is off by about 4.9e-16 from the exact angle.
public export
wrapByOnePeriodIntoSignedTwoPiRange : Double -> Double
wrapByOnePeriodIntoSignedTwoPiRange angle =
  if angle >= twoPi then angle - fourPi
  else if angle < negate twoPi then angle + fourPi
  else angle

-- Direct Boolean matches keep the bounds checks reducible in client proofs;
-- Data.So.choose is opaque outside its module. Radians inputs are bounded, so
-- the failed checks are unreachable.
public export
(+) : Radians -> Radians -> Radians
(MkRadians leftAngle) + (MkRadians rightAngle)
    with (inBounds (wrapByOnePeriodIntoSignedTwoPiRange (leftAngle + rightAngle))) proof 0 boundsCheck
  (MkRadians leftAngle) + (MkRadians rightAngle) | True =
    MkRadians (wrapByOnePeriodIntoSignedTwoPiRange (leftAngle + rightAngle)) {prf = rewrite boundsCheck in Oh}
  (MkRadians leftAngle) + (MkRadians rightAngle) | False = assert_total $ idris_crash
    "DSL/Core.idr, (+): internal error: angle sum did not wrap into [-2π, 2π)."

public export
(-) : Radians -> Radians -> Radians
(MkRadians leftAngle) - (MkRadians rightAngle)
    with (inBounds (wrapByOnePeriodIntoSignedTwoPiRange (leftAngle - rightAngle))) proof 0 boundsCheck
  (MkRadians leftAngle) - (MkRadians rightAngle) | True =
    MkRadians (wrapByOnePeriodIntoSignedTwoPiRange (leftAngle - rightAngle)) {prf = rewrite boundsCheck in Oh}
  (MkRadians leftAngle) - (MkRadians rightAngle) | False = assert_total $ idris_crash
    "DSL/Core.idr, (-): internal error: angle difference did not wrap into [-2π, 2π)."

public export
negate : Radians -> Radians
negate (MkRadians angle)
    with (inBounds (wrapByOnePeriodIntoSignedTwoPiRange (Prelude.negate angle))) proof 0 boundsCheck
  negate (MkRadians angle) | True =
    MkRadians (wrapByOnePeriodIntoSignedTwoPiRange (Prelude.negate angle)) {prf = rewrite boundsCheck in Oh}
  negate (MkRadians angle) | False = assert_total $ idris_crash
    "DSL/Core.idr, negate: internal error: negated angle did not wrap into [-2π, 2π)."

public export
Eq Radians where
  (MkRadians x) == (MkRadians y) = x == y

public export
Show Radians where
  show (MkRadians angle) = show angle

public export
data QState
  = Zero
  | One
  | Plus
  | Minus
  | PlusI
  | MinusI

public export
data Bit = Bit0 | Bit1

public export
pi : Radians
pi = MkRadians onePi
