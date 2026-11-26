module DSL.CircuitBuilder

import public Control.Monad.State
import Data.Fin
import Data.Vect
import public DSL.Circuit
import public DSL.Control
import DSL.Core
import DSL.Gates
-- Client proofs must be able to unfold the helpers used by build and the gates.
import public DSL.GateHelpers

%default total

public export
Builder : Nat -> Type -> Type
Builder n = Control.Monad.State.State (Circuit n n)

public export
build : {0 n : Nat} -> Builder n () -> Circuit n n
build = execState EmptyCircuit

public export
append : Circuit n n -> Builder n ()
append circuit = modify (\current => Sequence current circuit)

public export
identity : {0 n : Nat} -> (q : Fin n) -> Builder n ()
identity q = modify (GateHelpers.identity q)

public export
x : {0 n : Nat} -> (q : Fin n) -> Builder n ()
x q = modify (GateHelpers.x q)

public export
y : {0 n : Nat} -> (q : Fin n) -> Builder n ()
y q = modify (GateHelpers.y q)

public export
z : {0 n : Nat} -> (q : Fin n) -> Builder n ()
z q = modify (GateHelpers.z q)

public export
hadamard : {0 n : Nat} -> (q : Fin n) -> Builder n ()
hadamard q = modify (GateHelpers.hadamard q)

public export
s : {0 n : Nat} -> (q : Fin n) -> Builder n ()
s q = modify (GateHelpers.s q)

public export
t : {0 n : Nat} -> (q : Fin n) -> Builder n ()
t q = modify (GateHelpers.t q)

public export
sDag : {0 n : Nat} -> (q : Fin n) -> Builder n ()
sDag q = modify (GateHelpers.sDag q)

public export
tDag : {0 n : Nat} -> (q : Fin n) -> Builder n ()
tDag q = modify (GateHelpers.tDag q)

public export
sx : {0 n : Nat} -> (q : Fin n) -> Builder n ()
sx q = modify (GateHelpers.sx q)

public export
sxDag : {0 n : Nat} -> (q : Fin n) -> Builder n ()
sxDag q = modify (GateHelpers.sxDag q)

public export
rotX : {0 n : Nat} -> Radians -> (q : Fin n) -> Builder n ()
rotX angle q = modify (GateHelpers.rotX angle q)

public export
rotY : {0 n : Nat} -> Radians -> (q : Fin n) -> Builder n ()
rotY angle q = modify (GateHelpers.rotY angle q)

public export
rotZ : {0 n : Nat} -> Radians -> (q : Fin n) -> Builder n ()
rotZ angle q = modify (GateHelpers.rotZ angle q)

public export
u : {0 n : Nat} -> Radians -> Radians -> Radians -> (q : Fin n) -> Builder n ()
u theta phi lambda q = modify (GateHelpers.u theta phi lambda q)

public export
u1 : {0 n : Nat} -> Radians -> (q : Fin n) -> Builder n ()
u1 lambda q = modify (GateHelpers.u1 lambda q)

public export
u2 : {0 n : Nat} -> Radians -> Radians -> (q : Fin n) -> Builder n ()
u2 phi lambda q = modify (GateHelpers.u2 phi lambda q)

public export
u3 : {0 n : Nat} -> Radians -> Radians -> Radians -> (q : Fin n) -> Builder n ()
u3 theta phi lambda q = modify (GateHelpers.u3 theta phi lambda q)

public export
measure : {0 n : Nat} -> (q : Fin n) -> Builder n ()
measure q = modify (GateHelpers.measure q)

public export
reset : {0 n : Nat} -> (q : Fin n) -> Builder n ()
reset q = modify (GateHelpers.reset q)

public export
cnot : {0 n : Nat} -> (c, t : Fin n) -> {auto 0 neq : Not (c = t)} -> Builder n ()
cnot c t = modify (GateHelpers.cnot c t)

public export
ctrlY : {0 n : Nat} -> (c, t : Fin n) -> {auto 0 neq : Not (c = t)} -> Builder n ()
ctrlY c t = modify (GateHelpers.ctrlY c t)

public export
ctrlZ : {0 n : Nat} -> (c, t : Fin n) -> {auto 0 neq : Not (c = t)} -> Builder n ()
ctrlZ c t = modify (GateHelpers.ctrlZ c t)

public export
swap : {0 n : Nat} -> (a, b : Fin n) -> {auto 0 neq : Not (a = b)} -> Builder n ()
swap a b = modify (GateHelpers.swap a b)

public export
ctrlH : {0 n : Nat} -> (c, t : Fin n) -> {auto 0 neq : Not (c = t)} -> Builder n ()
ctrlH c t = modify (GateHelpers.ctrlH c t)

public export
ctrlS : {0 n : Nat} -> (c, t : Fin n) -> {auto 0 neq : Not (c = t)} -> Builder n ()
ctrlS c t = modify (GateHelpers.ctrlS c t)

public export
ctrlSDag : {0 n : Nat} -> (c, t : Fin n) -> {auto 0 neq : Not (c = t)} -> Builder n ()
ctrlSDag c t = modify (GateHelpers.ctrlSDag c t)

public export
ctrlT : {0 n : Nat} -> (c, t : Fin n) -> {auto 0 neq : Not (c = t)} -> Builder n ()
ctrlT c t = modify (GateHelpers.ctrlT c t)

public export
ctrlTDag : {0 n : Nat} -> (c, t : Fin n) -> {auto 0 neq : Not (c = t)} -> Builder n ()
ctrlTDag c t = modify (GateHelpers.ctrlTDag c t)

public export
ctrlSX : {0 n : Nat} -> (c, t : Fin n) -> {auto 0 neq : Not (c = t)} -> Builder n ()
ctrlSX c t = modify (GateHelpers.ctrlSX c t)

public export
ctrlSXDag : {0 n : Nat} -> (c, t : Fin n) -> {auto 0 neq : Not (c = t)} -> Builder n ()
ctrlSXDag c t = modify (GateHelpers.ctrlSXDag c t)

public export
ctrlRX : {0 n : Nat} -> Radians -> (c, t : Fin n) -> {auto 0 neq : Not (c = t)} -> Builder n ()
ctrlRX angle c t = modify (GateHelpers.ctrlRX angle c t)

public export
ctrlRY : {0 n : Nat} -> Radians -> (c, t : Fin n) -> {auto 0 neq : Not (c = t)} -> Builder n ()
ctrlRY angle c t = modify (GateHelpers.ctrlRY angle c t)

public export
ctrlRZ : {0 n : Nat} -> Radians -> (c, t : Fin n) -> {auto 0 neq : Not (c = t)} -> Builder n ()
ctrlRZ angle c t = modify (GateHelpers.ctrlRZ angle c t)

public export
ctrlU1 : {0 n : Nat} -> Radians -> (c, t : Fin n) -> {auto 0 neq : Not (c = t)} -> Builder n ()
ctrlU1 lambda c t = modify (GateHelpers.ctrlU1 lambda c t)

public export
ctrlU2 : {0 n : Nat} -> Radians -> Radians -> (c, t : Fin n) -> {auto 0 neq : Not (c = t)} -> Builder n ()
ctrlU2 phi lambda c t = modify (GateHelpers.ctrlU2 phi lambda c t)

public export
ctrlU3 : {0 n : Nat} -> Radians -> Radians -> Radians -> (c, t : Fin n) -> {auto 0 neq : Not (c = t)} -> Builder n ()
ctrlU3 theta phi lambda c t = modify (GateHelpers.ctrlU3 theta phi lambda c t)

public export
rxx : {0 n : Nat} -> Radians -> (a, b : Fin n) -> {auto 0 neq : Not (a = b)} -> Builder n ()
rxx angle a b = modify (GateHelpers.rxx angle a b)

public export
ryy : {0 n : Nat} -> Radians -> (a, b : Fin n) -> {auto 0 neq : Not (a = b)} -> Builder n ()
ryy angle a b = modify (GateHelpers.ryy angle a b)

public export
rzz : {0 n : Nat} -> Radians -> (a, b : Fin n) -> {auto 0 neq : Not (a = b)} -> Builder n ()
rzz angle a b = modify (GateHelpers.rzz angle a b)

public export
rzx : {0 n : Nat} -> Radians -> (a, b : Fin n) -> {auto 0 neq : Not (a = b)} -> Builder n ()
rzx angle a b = modify (GateHelpers.rzx angle a b)

public export
toffoli : {0 n : Nat} -> (c1, c2, t : Fin n)
        -> {auto 0 d12 : Not (c1 = c2)}
        -> {auto 0 d1t : Not (c1 = t)}
        -> {auto 0 d2t : Not (c2 = t)}
        -> Builder n ()
toffoli c1 c2 t = modify (GateHelpers.toffoli c1 c2 t)

public export
fredkin : {0 n : Nat} -> (c, a, b : Fin n)
        -> {auto 0 cab : Not (a = b)}
        -> {auto 0 ca  : Not (c = a)}
        -> {auto 0 cb  : Not (c = b)}
        -> Builder n ()
fredkin c a b = modify (GateHelpers.fredkin c a b)

public export
ctrl : {0 n : Nat} ->
  {k : Nat} ->
  (cs : Vect k (Fin n)) ->           -- control wires
  (bs : Vect k QState) ->            -- required qubits states
  (inner : UnitaryGate n) ->         -- gate to be controlled
  {auto 0 distinct : AllDistinct cs} ->
  {auto 0 disjoint : Disjoint cs (snd (wiresUnitary inner))} ->
  Builder n ()
ctrl cs bs inner {distinct} {disjoint} =
  modify (GateHelpers.ctrl cs bs inner {distinct = distinct} {disjoint = disjoint})
