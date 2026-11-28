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
Builder : ClassicalContext -> Nat -> Type -> Type
Builder ctx n = Control.Monad.State.State (Circuit ctx n n UnitType)

public export
build : {0 ctx : ClassicalContext} -> {0 n : Nat} -> Builder ctx n () -> Circuit ctx n n UnitType
build = execState EmptyCircuit

public export
append : Circuit ctx n n UnitType -> Builder ctx n ()
append circuit = modify (\current => Sequence current circuit)

public export
identity : {0 ctx : ClassicalContext} -> {0 n : Nat} -> (q : Fin n) -> Builder ctx n ()
identity q = modify (GateHelpers.identity q)

public export
x : {0 ctx : ClassicalContext} -> {0 n : Nat} -> (q : Fin n) -> Builder ctx n ()
x q = modify (GateHelpers.x q)

public export
y : {0 ctx : ClassicalContext} -> {0 n : Nat} -> (q : Fin n) -> Builder ctx n ()
y q = modify (GateHelpers.y q)

public export
z : {0 ctx : ClassicalContext} -> {0 n : Nat} -> (q : Fin n) -> Builder ctx n ()
z q = modify (GateHelpers.z q)

public export
hadamard : {0 ctx : ClassicalContext} -> {0 n : Nat} -> (q : Fin n) -> Builder ctx n ()
hadamard q = modify (GateHelpers.hadamard q)

public export
s : {0 ctx : ClassicalContext} -> {0 n : Nat} -> (q : Fin n) -> Builder ctx n ()
s q = modify (GateHelpers.s q)

public export
t : {0 ctx : ClassicalContext} -> {0 n : Nat} -> (q : Fin n) -> Builder ctx n ()
t q = modify (GateHelpers.t q)

public export
sDag : {0 ctx : ClassicalContext} -> {0 n : Nat} -> (q : Fin n) -> Builder ctx n ()
sDag q = modify (GateHelpers.sDag q)

public export
tDag : {0 ctx : ClassicalContext} -> {0 n : Nat} -> (q : Fin n) -> Builder ctx n ()
tDag q = modify (GateHelpers.tDag q)

public export
sx : {0 ctx : ClassicalContext} -> {0 n : Nat} -> (q : Fin n) -> Builder ctx n ()
sx q = modify (GateHelpers.sx q)

public export
sxDag : {0 ctx : ClassicalContext} -> {0 n : Nat} -> (q : Fin n) -> Builder ctx n ()
sxDag q = modify (GateHelpers.sxDag q)

public export
rotX : {0 ctx : ClassicalContext} -> {0 n : Nat} -> Radians -> (q : Fin n) -> Builder ctx n ()
rotX angle q = modify (GateHelpers.rotX angle q)

public export
rotY : {0 ctx : ClassicalContext} -> {0 n : Nat} -> Radians -> (q : Fin n) -> Builder ctx n ()
rotY angle q = modify (GateHelpers.rotY angle q)

public export
rotZ : {0 ctx : ClassicalContext} -> {0 n : Nat} -> Radians -> (q : Fin n) -> Builder ctx n ()
rotZ angle q = modify (GateHelpers.rotZ angle q)

public export
u : {0 ctx : ClassicalContext} -> {0 n : Nat} -> Radians -> Radians -> Radians -> (q : Fin n) -> Builder ctx n ()
u theta phi lambda q = modify (GateHelpers.u theta phi lambda q)

public export
u1 : {0 ctx : ClassicalContext} -> {0 n : Nat} -> Radians -> (q : Fin n) -> Builder ctx n ()
u1 lambda q = modify (GateHelpers.u1 lambda q)

public export
u2 : {0 ctx : ClassicalContext} -> {0 n : Nat} -> Radians -> Radians -> (q : Fin n) -> Builder ctx n ()
u2 phi lambda q = modify (GateHelpers.u2 phi lambda q)

public export
u3 : {0 ctx : ClassicalContext} -> {0 n : Nat} -> Radians -> Radians -> Radians -> (q : Fin n) -> Builder ctx n ()
u3 theta phi lambda q = modify (GateHelpers.u3 theta phi lambda q)

public export
measure : {0 n : Nat} -> (q : Fin n) -> Builder n ()
measure q = modify (GateHelpers.measure q)

public export
reset : {0 ctx : ClassicalContext} -> {0 n : Nat} -> (q : Fin n) -> Builder ctx n ()
reset q = modify (GateHelpers.reset q)

public export
cnot : {0 ctx : ClassicalContext} -> {0 n : Nat} -> (c, t : Fin n) -> {auto 0 neq : Not (c = t)} -> Builder ctx n ()
cnot c t = modify (GateHelpers.cnot c t)

public export
ctrlY : {0 ctx : ClassicalContext} -> {0 n : Nat} -> (c, t : Fin n) -> {auto 0 neq : Not (c = t)} -> Builder ctx n ()
ctrlY c t = modify (GateHelpers.ctrlY c t)

public export
ctrlZ : {0 ctx : ClassicalContext} -> {0 n : Nat} -> (c, t : Fin n) -> {auto 0 neq : Not (c = t)} -> Builder ctx n ()
ctrlZ c t = modify (GateHelpers.ctrlZ c t)

public export
swap : {0 ctx : ClassicalContext} -> {0 n : Nat} -> (a, b : Fin n) -> {auto 0 neq : Not (a = b)} -> Builder ctx n ()
swap a b = modify (GateHelpers.swap a b)

public export
ctrlH : {0 ctx : ClassicalContext} -> {0 n : Nat} -> (c, t : Fin n) -> {auto 0 neq : Not (c = t)} -> Builder ctx n ()
ctrlH c t = modify (GateHelpers.ctrlH c t)

public export
ctrlS : {0 ctx : ClassicalContext} -> {0 n : Nat} -> (c, t : Fin n) -> {auto 0 neq : Not (c = t)} -> Builder ctx n ()
ctrlS c t = modify (GateHelpers.ctrlS c t)

public export
ctrlSDag : {0 ctx : ClassicalContext} -> {0 n : Nat} -> (c, t : Fin n) -> {auto 0 neq : Not (c = t)} -> Builder ctx n ()
ctrlSDag c t = modify (GateHelpers.ctrlSDag c t)

public export
ctrlT : {0 ctx : ClassicalContext} -> {0 n : Nat} -> (c, t : Fin n) -> {auto 0 neq : Not (c = t)} -> Builder ctx n ()
ctrlT c t = modify (GateHelpers.ctrlT c t)

public export
ctrlTDag : {0 ctx : ClassicalContext} -> {0 n : Nat} -> (c, t : Fin n) -> {auto 0 neq : Not (c = t)} -> Builder ctx n ()
ctrlTDag c t = modify (GateHelpers.ctrlTDag c t)

public export
ctrlSX : {0 ctx : ClassicalContext} -> {0 n : Nat} -> (c, t : Fin n) -> {auto 0 neq : Not (c = t)} -> Builder ctx n ()
ctrlSX c t = modify (GateHelpers.ctrlSX c t)

public export
ctrlSXDag : {0 ctx : ClassicalContext} -> {0 n : Nat} -> (c, t : Fin n) -> {auto 0 neq : Not (c = t)} -> Builder ctx n ()
ctrlSXDag c t = modify (GateHelpers.ctrlSXDag c t)

public export
ctrlRX : {0 ctx : ClassicalContext} -> {0 n : Nat} -> Radians -> (c, t : Fin n) -> {auto 0 neq : Not (c = t)} -> Builder ctx n ()
ctrlRX angle c t = modify (GateHelpers.ctrlRX angle c t)

public export
ctrlRY : {0 ctx : ClassicalContext} -> {0 n : Nat} -> Radians -> (c, t : Fin n) -> {auto 0 neq : Not (c = t)} -> Builder ctx n ()
ctrlRY angle c t = modify (GateHelpers.ctrlRY angle c t)

public export
ctrlRZ : {0 ctx : ClassicalContext} -> {0 n : Nat} -> Radians -> (c, t : Fin n) -> {auto 0 neq : Not (c = t)} -> Builder ctx n ()
ctrlRZ angle c t = modify (GateHelpers.ctrlRZ angle c t)

public export
ctrlU1 : {0 ctx : ClassicalContext} -> {0 n : Nat} -> Radians -> (c, t : Fin n) -> {auto 0 neq : Not (c = t)} -> Builder ctx n ()
ctrlU1 lambda c t = modify (GateHelpers.ctrlU1 lambda c t)

public export
ctrlU2 : {0 ctx : ClassicalContext} -> {0 n : Nat} -> Radians -> Radians -> (c, t : Fin n) -> {auto 0 neq : Not (c = t)} -> Builder ctx n ()
ctrlU2 phi lambda c t = modify (GateHelpers.ctrlU2 phi lambda c t)

public export
ctrlU3 : {0 ctx : ClassicalContext} -> {0 n : Nat} -> Radians -> Radians -> Radians -> (c, t : Fin n) -> {auto 0 neq : Not (c = t)} -> Builder ctx n ()
ctrlU3 theta phi lambda c t = modify (GateHelpers.ctrlU3 theta phi lambda c t)

public export
rxx : {0 ctx : ClassicalContext} -> {0 n : Nat} -> Radians -> (a, b : Fin n) -> {auto 0 neq : Not (a = b)} -> Builder ctx n ()
rxx angle a b = modify (GateHelpers.rxx angle a b)

public export
ryy : {0 ctx : ClassicalContext} -> {0 n : Nat} -> Radians -> (a, b : Fin n) -> {auto 0 neq : Not (a = b)} -> Builder ctx n ()
ryy angle a b = modify (GateHelpers.ryy angle a b)

public export
rzz : {0 ctx : ClassicalContext} -> {0 n : Nat} -> Radians -> (a, b : Fin n) -> {auto 0 neq : Not (a = b)} -> Builder ctx n ()
rzz angle a b = modify (GateHelpers.rzz angle a b)

public export
rzx : {0 ctx : ClassicalContext} -> {0 n : Nat} -> Radians -> (a, b : Fin n) -> {auto 0 neq : Not (a = b)} -> Builder ctx n ()
rzx angle a b = modify (GateHelpers.rzx angle a b)

public export
toffoli : {0 ctx : ClassicalContext} -> {0 n : Nat} -> (c1, c2, t : Fin n)
        -> {auto 0 d12 : Not (c1 = c2)}
        -> {auto 0 d1t : Not (c1 = t)}
        -> {auto 0 d2t : Not (c2 = t)}
        -> Builder ctx n ()
toffoli c1 c2 t = modify (GateHelpers.toffoli c1 c2 t)

public export
fredkin : {0 ctx : ClassicalContext} -> {0 n : Nat} -> (c, a, b : Fin n)
        -> {auto 0 cab : Not (a = b)}
        -> {auto 0 ca  : Not (c = a)}
        -> {auto 0 cb  : Not (c = b)}
        -> Builder ctx n ()
fredkin c a b = modify (GateHelpers.fredkin c a b)

public export
ctrl : {0 ctx : ClassicalContext} ->
       {0 n : Nat} ->
       {k : Nat} ->
       (cs : Vect k (Fin n)) ->           -- control wires
       (bs : Vect k QState) ->            -- required qubits states
       (inner : UnitaryGate n) ->         -- gate to be controlled
       {auto 0 distinct : AllDistinct cs} ->
       {auto 0 disjoint : Disjoint cs (snd (wiresUnitary inner))} ->
       Builder ctx n ()
ctrl cs bs inner {distinct} {disjoint} =
  modify (GateHelpers.ctrl cs bs inner {distinct = distinct} {disjoint = disjoint})
