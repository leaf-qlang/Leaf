module DSL.Core

import Data.So

import DSL.Wrap2Pi

%default total

public export
inBounds : Double -> Bool
inBounds x = - 2 * Prelude.pi < x && x <= 2 * Prelude.pi

public export
data Radians : Type where
  MkRadians : (x : Double) -> {auto 0 prf : So (inBounds x)} -> Radians

-- Reduce, then turn the Boolean check into the proof
mkWrapped : Double -> Radians
mkWrapped x = let r = wrap x in
  case choose (inBounds r) of
    Left prf => MkRadians r {prf = prf}   -- prf : So (inBounds r), from choose
    Right _  => MkRadians 0.0 {prf = Oh}  -- inBounds 0.0 reduces to True, so Oh : So True fits

public export
(+) : Radians -> Radians -> Radians
(MkRadians x) + (MkRadians y) = mkWrapped (x + y)

public export
(-) : Radians -> Radians -> Radians
(MkRadians x) - (MkRadians y) = mkWrapped (x - y)

public export
negate : Radians -> Radians
negate (MkRadians x) = mkWrapped (negate x)

public export
Show Radians where
  show (MkRadians x) = show x

public export
data QState
  = Zero
  | One
  | Plus
  | Minus
  | PlusI
  | MinusI

public export
data BState = ZERO | ONE

public export
pi : Radians
pi = MkRadians Prelude.pi
