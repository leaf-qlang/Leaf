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

-- Reduce modulo 4π into [-2π, 2π), then turn the Boolean range check into the
-- proof MkRadians needs.
mkRadiansReducedModuloFourPi : Double -> Radians
mkRadiansReducedModuloFourPi angle =
  let reducedAngle = reduceModuloFourPiIntoSignedTwoPiRange angle in
  case choose (inBounds reducedAngle) of
    Left prf => MkRadians reducedAngle {prf = prf}  -- prf : So (inBounds reducedAngle), from choose
    -- Reached only for NaN and ±Infinity: every finite angle reduces into range.
    -- inBounds 0.0 reduces to True, so Oh : So True fits.
    Right _  => MkRadians 0.0 {prf = Oh}

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
pi = MkRadians Prelude.pi
