module DSL.Gates

import Data.Fin
import Data.Vect
import Data.Vect.Quantifiers
import DSL.Core
import public DSL.Control

%default total

public export
prependControlWiresToInnerWires : {k : Nat} -> Vect k (Fin n) -> (m ** Vect m (Fin n)) -> (m ** Vect m (Fin n))
prependControlWiresToInnerWires {k} controlWires (innerWireCount ** innerWires) = (k + innerWireCount ** controlWires ++ innerWires)

-- The constructor checks disjointness against the inner gate's complete wire list.
mutual
  public export
  data UnitaryGate : Nat -> Type where
    -- 1-qbit (Clifford + T and friends)
    Id    : (q : Fin n) -> UnitaryGate n
    X     : (q : Fin n) -> UnitaryGate n
    Y     : (q : Fin n) -> UnitaryGate n
    Z     : (q : Fin n) -> UnitaryGate n
    H     : (q : Fin n) -> UnitaryGate n
    S     : (q : Fin n) -> UnitaryGate n
    SDG   : (q : Fin n) -> UnitaryGate n
    T     : (q : Fin n) -> UnitaryGate n
    TDG   : (q : Fin n) -> UnitaryGate n
    SX    : (q : Fin n) -> UnitaryGate n
    SXDG  : (q : Fin n) -> UnitaryGate n

    -- Parametric 1-qbit rotations
    RX    : Radians -> (q : Fin n) -> UnitaryGate n
    RY    : Radians -> (q : Fin n) -> UnitaryGate n
    RZ    : Radians -> (q : Fin n) -> UnitaryGate n

    -- OpenQASM 2 primitives / U-family
    U     : Radians -> Radians -> Radians -> (q : Fin n) -> UnitaryGate n      -- U(θ, φ, λ)
    U1    : Radians -> (q : Fin n) -> UnitaryGate n                            -- U1(λ)   == U(0, 0, λ)
    U2    : Radians -> Radians -> (q : Fin n) -> UnitaryGate n                 -- U2(φ,λ) == gphase(-(φ+λ+π/2)/2) U(π/2, φ, λ), as in OpenQASM 3
    U3    : Radians -> Radians -> Radians -> (q : Fin n) -> UnitaryGate n      -- U3(θ,φ,λ) == gphase(-(φ+λ+θ)/2) U(θ, φ, λ), as in OpenQASM 3

    -- 2-qbit (with a proof that control ≠ target)
    CX    : (c,t : Fin n) -> {auto 0 neq : Not (c = t)} -> UnitaryGate n
    CY    : (c,t : Fin n) -> {auto 0 neq : Not (c = t)} -> UnitaryGate n
    CZ    : (c,t : Fin n) -> {auto 0 neq : Not (c = t)} -> UnitaryGate n
    CH    : (c,t : Fin n) -> {auto 0 neq : Not (c = t)} -> UnitaryGate n
    CS    : (c,t : Fin n) -> {auto 0 neq : Not (c = t)} -> UnitaryGate n
    CSDG  : (c,t : Fin n) -> {auto 0 neq : Not (c = t)} -> UnitaryGate n
    CT    : (c,t : Fin n) -> {auto 0 neq : Not (c = t)} -> UnitaryGate n
    CTDG  : (c,t : Fin n) -> {auto 0 neq : Not (c = t)} -> UnitaryGate n
    CSX   : (c,t : Fin n) -> {auto 0 neq : Not (c = t)} -> UnitaryGate n
    CSXDG : (c,t : Fin n) -> {auto 0 neq : Not (c = t)} -> UnitaryGate n

    CRX   : Radians -> (c,t : Fin n) -> {auto 0 neq : Not (c = t)} -> UnitaryGate n
    CRY   : Radians -> (c,t : Fin n) -> {auto 0 neq : Not (c = t)} -> UnitaryGate n
    CRZ   : Radians -> (c,t : Fin n) -> {auto 0 neq : Not (c = t)} -> UnitaryGate n
    CU1   : Radians -> (c,t : Fin n) -> {auto 0 neq : Not (c = t)} -> UnitaryGate n
    CU2   : Radians -> Radians -> (c,t : Fin n) -> {auto 0 neq : Not (c = t)} -> UnitaryGate n
    CU3   : Radians -> Radians -> Radians -> (c,t : Fin n) -> {auto 0 neq : Not (c = t)} -> UnitaryGate n

    SWAP  : (a,b : Fin n) -> {auto 0 neq : Not (a = b)} -> UnitaryGate n
    RXX   : Radians -> (a,b : Fin n) -> {auto 0 neq : Not (a = b)} -> UnitaryGate n
    RYY   : Radians -> (a,b : Fin n) -> {auto 0 neq : Not (a = b)} -> UnitaryGate n
    RZZ   : Radians -> (a,b : Fin n) -> {auto 0 neq : Not (a = b)} -> UnitaryGate n
    RZX   : Radians -> (a,b : Fin n) -> {auto 0 neq : Not (a = b)} -> UnitaryGate n

    -- 3-qbit (all distinct)
    CCX   : (c1,c2,t : Fin n)
          -> {auto 0 d12 : Not (c1 = c2)}
          -> {auto 0 d1t : Not (c1 = t)}
          -> {auto 0 d2t : Not (c2 = t)}
          -> UnitaryGate n
    CSWAP : (c,a,b : Fin n)
          -> {auto 0 ab  : Not (a = b)}
          -> {auto 0 ca  : Not (c = a)}
          -> {auto 0 cb  : Not (c = b)}
          -> UnitaryGate n

    -- Generic controlled wrapper
    Controlled :
      {k : Nat} ->
      (cs : Vect k (Fin n)) ->           -- control wires
      (bs : Vect k QState) ->            -- control wires polarities: 0, 1, +, -, +i, -i
      (inner : UnitaryGate n) ->         -- original gate
      {auto 0 distinct : AllDistinct cs} ->
      {auto 0 disjoint : Disjoint cs (snd (wiresUnitary inner))} ->
      UnitaryGate n

  public export
  wiresUnitary : UnitaryGate n -> (m ** Vect m (Fin n))
  wiresUnitary (Id q)                    = (1 ** [q])
  wiresUnitary (X q)                     = (1 ** [q])
  wiresUnitary (Y q)                     = (1 ** [q])
  wiresUnitary (Z q)                     = (1 ** [q])
  wiresUnitary (H q)                     = (1 ** [q])
  wiresUnitary (S q)                     = (1 ** [q])
  wiresUnitary (SDG q)                   = (1 ** [q])
  wiresUnitary (T q)                     = (1 ** [q])
  wiresUnitary (TDG q)                   = (1 ** [q])
  wiresUnitary (SX q)                    = (1 ** [q])
  wiresUnitary (SXDG q)                  = (1 ** [q])
  wiresUnitary (RX _ q)                  = (1 ** [q])
  wiresUnitary (RY _ q)                  = (1 ** [q])
  wiresUnitary (RZ _ q)                  = (1 ** [q])
  wiresUnitary (U _ _ _ q)               = (1 ** [q])
  wiresUnitary (U1 _ q)                  = (1 ** [q])
  wiresUnitary (U2 _ _ q)                = (1 ** [q])
  wiresUnitary (U3 _ _ _ q)              = (1 ** [q])
  wiresUnitary (CX c t)                  = (2 ** [c, t])
  wiresUnitary (CY c t)                  = (2 ** [c, t])
  wiresUnitary (CZ c t)                  = (2 ** [c, t])
  wiresUnitary (CH c t)                  = (2 ** [c, t])
  wiresUnitary (CS c t)                  = (2 ** [c, t])
  wiresUnitary (CSDG c t)                = (2 ** [c, t])
  wiresUnitary (CT c t)                  = (2 ** [c, t])
  wiresUnitary (CTDG c t)                = (2 ** [c, t])
  wiresUnitary (CSX c t)                 = (2 ** [c, t])
  wiresUnitary (CSXDG c t)               = (2 ** [c, t])
  wiresUnitary (CRX _ c t)               = (2 ** [c, t])
  wiresUnitary (CRY _ c t)               = (2 ** [c, t])
  wiresUnitary (CRZ _ c t)               = (2 ** [c, t])
  wiresUnitary (CU1 _ c t)               = (2 ** [c, t])
  wiresUnitary (CU2 _ _ c t)             = (2 ** [c, t])
  wiresUnitary (CU3 _ _ _ c t)           = (2 ** [c, t])
  wiresUnitary (SWAP a b)                = (2 ** [a, b])
  wiresUnitary (RXX _ a b)               = (2 ** [a, b])
  wiresUnitary (RYY _ a b)               = (2 ** [a, b])
  wiresUnitary (RZZ _ a b)               = (2 ** [a, b])
  wiresUnitary (RZX _ a b)               = (2 ** [a, b])
  wiresUnitary (CCX c1 c2 t)             = (3 ** [c1, c2, t])
  wiresUnitary (CSWAP c a b)             = (3 ** [c, a, b])
  wiresUnitary (Controlled controlWires _ inner) =
    prependControlWiresToInnerWires controlWires (wiresUnitary inner)

public export
data Gate : Nat -> Type where
  UGate   : UnitaryGate n -> Gate n
  Measure : (q : Fin n) -> Gate n
  Reset   : (q : Fin n) -> Gate n
