module DSL.GateHelpers

import Data.Fin
import Data.Vect
import DSL.Gates
import DSL.Circuit
import public DSL.Control
import DSL.Core

%default total

public export
emptyCircuit : {n : Nat} -> Circuit n n
emptyCircuit = Identity


-- 1-qbit Clifford + T gates
public export
x : {n : Nat} -> (q : Fin n) -> Circuit n n -> Circuit n n
x q circ = Sequence circ (SingleGate (UGate (X q)))

public export
y : {n : Nat} -> (q : Fin n) -> Circuit n n -> Circuit n n
y q circ = Sequence circ (SingleGate (UGate (Y q)))

public export
z : {n : Nat} -> (q : Fin n) -> Circuit n n -> Circuit n n
z q circ = Sequence circ (SingleGate (UGate (Z q)))

public export
hadamard : {n : Nat} -> (q : Fin n) -> Circuit n n -> Circuit n n
hadamard q circ = Sequence circ (SingleGate (UGate (H q)))

public export
s : {n : Nat} -> (q : Fin n) -> Circuit n n -> Circuit n n
s q circ = Sequence circ (SingleGate (UGate (S q)))

public export
t : {n : Nat} -> (q : Fin n) -> Circuit n n -> Circuit n n
t q circ = Sequence circ (SingleGate (UGate (T q)))

public export
sDag : {n : Nat} -> (q : Fin n) -> Circuit n n -> Circuit n n
sDag q circ = Sequence circ (SingleGate (UGate (SDG q)))

public export
tDag : {n : Nat} -> (q : Fin n) -> Circuit n n -> Circuit n n
tDag q circ = Sequence circ (SingleGate (UGate (TDG q)))

public export
sx : {n : Nat} -> (q : Fin n) -> Circuit n n -> Circuit n n
sx q circ = Sequence circ (SingleGate (UGate (SX q)))

public export
sxDag : {n : Nat} -> (q : Fin n) -> Circuit n n -> Circuit n n
sxDag q circ = Sequence circ (SingleGate (UGate (SXDG q)))


-- Rotation gates
public export
rotX : {n : Nat} -> Radians -> (q : Fin n) -> Circuit n n -> Circuit n n
rotX angle q circ = Sequence circ (SingleGate (UGate (RX angle q)))

public export
rotY : {n : Nat} -> Radians -> (q : Fin n) -> Circuit n n -> Circuit n n
rotY angle q circ = Sequence circ (SingleGate (UGate (RY angle q)))

public export
rotZ : {n : Nat} -> Radians -> (q : Fin n) -> Circuit n n -> Circuit n n
rotZ angle q circ = Sequence circ (SingleGate (UGate (RZ angle q)))


-- U-family gates
public export
u : {n : Nat} -> Radians -> Radians -> Radians -> (q : Fin n) -> Circuit n n -> Circuit n n
u theta phi lambda q circ =
  Sequence circ (SingleGate (UGate (U theta phi lambda q)))

public export
u1 : {n : Nat} -> Radians -> (q : Fin n) -> Circuit n n -> Circuit n n
u1 lambda q circ =
  Sequence circ (SingleGate (UGate (U1 lambda q)))

public export
u2 : {n : Nat} -> Radians -> Radians -> (q : Fin n) -> Circuit n n -> Circuit n n
u2 phi lambda q circ =
  Sequence circ (SingleGate (UGate (U2 phi lambda q)))

public export
u3 : {n : Nat} -> Radians -> Radians -> Radians -> (q : Fin n) -> Circuit n n -> Circuit n n
u3 theta phi lambda q circ =
  Sequence circ (SingleGate (UGate (U3 theta phi lambda q)))


-- Additional operations
public export
measure : {n : Nat} -> (q : Fin n) -> Circuit n n -> Circuit n n
measure q circ = Sequence circ (SingleGate (Measure q))

public export
reset : {n : Nat} -> (q : Fin n) -> Circuit n n -> Circuit n n
reset q circ = Sequence circ (SingleGate (Reset q))


-- Two-qbit gates
public export
cnot : {n : Nat} -> (c, t : Fin n) -> {auto 0 neq : Not (c = t)} -> Circuit n n -> Circuit n n
cnot c t circ = Sequence circ (SingleGate (UGate (CNOT c t)))

public export
ctrlY : {n : Nat} -> (c, t : Fin n) -> {auto 0 neq : Not (c = t)} -> Circuit n n -> Circuit n n
ctrlY c t circ = Sequence circ (SingleGate (UGate (CY c t)))

public export
ctrlZ : {n : Nat} -> (c, t : Fin n) -> {auto 0 neq : Not (c = t)} -> Circuit n n -> Circuit n n
ctrlZ c t circ = Sequence circ (SingleGate (UGate (CZ c t)))

public export
swap : {n : Nat} -> (a, b : Fin n) -> {auto 0 neq : Not (a = b)} -> Circuit n n -> Circuit n n
swap a b circ = Sequence circ (SingleGate (UGate (SWAP a b)))

public export
ctrlH : {n : Nat} -> (c, t : Fin n) -> {auto 0 neq : Not (c = t)} -> Circuit n n -> Circuit n n
ctrlH c t circ = Sequence circ (SingleGate (UGate (CH c t)))

public export
ctrlS : {n : Nat} -> (c, t : Fin n) -> {auto 0 neq : Not (c = t)} -> Circuit n n -> Circuit n n
ctrlS c t circ = Sequence circ (SingleGate (UGate (CS c t)))

public export
ctrlSDag : {n : Nat} -> (c, t : Fin n) -> {auto 0 neq : Not (c = t)} -> Circuit n n -> Circuit n n
ctrlSDag c t circ = Sequence circ (SingleGate (UGate (CSDG c t)))

public export
ctrlT : {n : Nat} -> (c, t : Fin n) -> {auto 0 neq : Not (c = t)} -> Circuit n n -> Circuit n n
ctrlT c t circ = Sequence circ (SingleGate (UGate (CT c t)))

public export
ctrlTDag : {n : Nat} -> (c, t : Fin n) -> {auto 0 neq : Not (c = t)} -> Circuit n n -> Circuit n n
ctrlTDag c t circ = Sequence circ (SingleGate (UGate (CTDG c t)))

public export
ctrlSX : {n : Nat} -> (c, t : Fin n) -> {auto 0 neq : Not (c = t)} -> Circuit n n -> Circuit n n
ctrlSX c t circ = Sequence circ (SingleGate (UGate (CSX c t)))

public export
ctrlSXDag : {n : Nat} -> (c, t : Fin n) -> {auto 0 neq : Not (c = t)} -> Circuit n n -> Circuit n n
ctrlSXDag c t circ = Sequence circ (SingleGate (UGate (CSXDG c t)))


-- ctrl rotation gates
public export
ctrlRX : {n : Nat} -> Radians -> (c, t : Fin n) -> {auto 0 neq : Not (c = t)} -> Circuit n n -> Circuit n n
ctrlRX angle c t circ = Sequence circ (SingleGate (UGate (CRX angle c t)))

public export
ctrlRY : {n : Nat} -> Radians -> (c, t : Fin n) -> {auto 0 neq : Not (c = t)} -> Circuit n n -> Circuit n n
ctrlRY angle c t circ = Sequence circ (SingleGate (UGate (CRY angle c t)))

public export
ctrlRZ : {n : Nat} -> Radians -> (c, t : Fin n) -> {auto 0 neq : Not (c = t)} -> Circuit n n -> Circuit n n
ctrlRZ angle c t circ = Sequence circ (SingleGate (UGate (CRZ angle c t)))

-- ctrl U gates
public export
ctrlU1 : {n : Nat} -> Radians -> (c, t : Fin n) -> {auto 0 neq : Not (c = t)} -> Circuit n n -> Circuit n n
ctrlU1 lambda c t circ = Sequence circ (SingleGate (UGate (CU1 lambda c t)))

public export
ctrlU2 : {n : Nat} -> Radians -> Radians -> (c, t : Fin n) -> {auto 0 neq : Not (c = t)} -> Circuit n n -> Circuit n n
ctrlU2 phi lambda c t circ = Sequence circ (SingleGate (UGate (CU2 phi lambda c t)))

public export
ctrlU3 : {n : Nat} -> Radians -> Radians -> Radians -> (c, t : Fin n) -> {auto 0 neq : Not (c = t)} -> Circuit n n -> Circuit n n
ctrlU3 theta phi lambda c t circ = Sequence circ (SingleGate (UGate (CU3 theta phi lambda c t)))

-- Two-qbit interaction gates
public export
rxx : {n : Nat} -> Radians -> (a, b : Fin n) -> {auto 0 neq : Not (a = b)} -> Circuit n n -> Circuit n n
rxx angle a b circ = Sequence circ (SingleGate (UGate (RXX angle a b)))

public export
ryy : {n : Nat} -> Radians -> (a, b : Fin n) -> {auto 0 neq : Not (a = b)} -> Circuit n n -> Circuit n n
ryy angle a b circ = Sequence circ (SingleGate (UGate (RYY angle a b)))

public export
rzz : {n : Nat} -> Radians -> (a, b : Fin n) -> {auto 0 neq : Not (a = b)} -> Circuit n n -> Circuit n n
rzz angle a b circ = Sequence circ (SingleGate (UGate (RZZ angle a b)))

public export
rzx : {n : Nat} -> Radians -> (a, b : Fin n) -> {auto 0 neq : Not (a = b)} -> Circuit n n -> Circuit n n
rzx angle a b circ = Sequence circ (SingleGate (UGate (RZX angle a b)))

-- Three-qbit gates
public export
toffoli : {n : Nat} -> (c1, c2, t : Fin n) 
        -> {auto 0 d12 : Not (c1 = c2)}
        -> {auto 0 d1t : Not (c1 = t)}
        -> {auto 0 d2t : Not (c2 = t)}
        -> Circuit n n -> Circuit n n
toffoli c1 c2 t circ = Sequence circ (SingleGate (UGate (CCX c1 c2 t)))

public export
fredkin : {n : Nat} -> (c, a, b : Fin n) 
        -> {auto 0 cab : Not (a = b)}
        -> {auto 0 ca  : Not (c = a)}
        -> {auto 0 cb  : Not (c = b)}
        -> Circuit n n -> Circuit n n
fredkin c a b circ = Sequence circ (SingleGate (UGate (CSWAP c a b)))

-- Generic multi-controlled gate construction
public export
ctrl :
  {n : Nat} ->
  {k : Nat} ->
  (cs : Vect k (Fin n)) ->           -- control wires
  (bs : Vect k QState) ->              -- required polarities (True = |1>, False = |0>)
  (inner : UnitaryGate n) ->         -- gate to be controlled
  {auto 0 distinct : AllDistinct cs} ->
  {auto 0 disjoint : Disjoint cs (snd (wiresUnitary inner))} ->
  Circuit n n ->
  Circuit n n
ctrl cs bs inner {distinct} {disjoint} circ =
  let uCtrl : UnitaryGate n
      uCtrl = mkControlled cs bs inner
        {distinct = distinct}
        {disjoint = disjoint}
  in Sequence circ (SingleGate (UGate uCtrl))

