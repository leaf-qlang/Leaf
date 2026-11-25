module DSL.Core

import Data.So

import public DSL.AngleConstants
import DSL.Wrap4Pi

%default total

public export
inBounds : Double -> Bool
inBounds angle = negate twoPi <= angle && angle < twoPi

public export
data Radians : Type where
  MkRadians : (angle : Double) -> {auto 0 prf : So (inBounds angle)} -> Radians

public export
radiansFromDouble : Double -> Maybe Radians
radiansFromDouble angle =
  let reducedAngle = reduceModuloFourPiIntoSignedTwoPiRange angle in
  case choose (inBounds reducedAngle) of
    Left prf => Just (MkRadians reducedAngle {prf = prf})
    Right _  => Nothing  -- the result is Nothing only for NaN and ±Infinity.

mkRadiansReducedModuloFourPi : Double -> Radians
mkRadiansReducedModuloFourPi angle =
  case radiansFromDouble angle of
    Just radians => radians
    -- Unreachable: callers only pass sums, differences or negations of angles
    -- already in [-2π, 2π), which are finite.
    Nothing => assert_total $ idris_crash $
      "DSL/Core.idr, mkRadiansReducedModuloFourPi: internal error: angle "
        ++ show angle ++ " did not reduce into [-2π, 2π)."

public export
(+) : Radians -> Radians -> Radians
(MkRadians x) + (MkRadians y) = mkRadiansReducedModuloFourPi (x + y)

public export
(-) : Radians -> Radians -> Radians
(MkRadians x) - (MkRadians y) = mkRadiansReducedModuloFourPi (x - y)

public export
negate : Radians -> Radians
negate (MkRadians angle) = mkRadiansReducedModuloFourPi (negate angle)

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
