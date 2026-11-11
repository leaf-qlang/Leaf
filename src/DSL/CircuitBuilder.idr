module DSL.CircuitBuilder

import public Control.Monad.State
import Data.Fin
import Data.Vect
import public DSL.Circuit
import DSL.Control
import DSL.Core
import DSL.Gates
import DSL.GateHelpers as Helpers

%default total

public export
Builder : Nat -> Type -> Type
Builder n = Control.Monad.State.State (Circuit n n)

public export
build : {n : Nat} -> Builder n () -> Circuit n n
build = execState Helpers.emptyCircuit

public export
append : Circuit n n -> Builder n ()
append circuit = modify (\current => Seq current circuit)

public export
x : {n : Nat} -> (q : Fin n) -> Builder n ()
x q = modify (Helpers.x q)

public export
y : {n : Nat} -> (q : Fin n) -> Builder n ()
y q = modify (Helpers.y q)

public export
z : {n : Nat} -> (q : Fin n) -> Builder n ()
z q = modify (Helpers.z q)

public export
hadamard : {n : Nat} -> (q : Fin n) -> Builder n ()
hadamard q = modify (Helpers.hadamard q)

public export
s : {n : Nat} -> (q : Fin n) -> Builder n ()
s q = modify (Helpers.s q)

public export
t : {n : Nat} -> (q : Fin n) -> Builder n ()
t q = modify (Helpers.t q)

public export
sDag : {n : Nat} -> (q : Fin n) -> Builder n ()
sDag q = modify (Helpers.sDag q)

public export
tDag : {n : Nat} -> (q : Fin n) -> Builder n ()
tDag q = modify (Helpers.tDag q)

public export
sx : {n : Nat} -> (q : Fin n) -> Builder n ()
sx q = modify (Helpers.sx q)

public export
sxDag : {n : Nat} -> (q : Fin n) -> Builder n ()
sxDag q = modify (Helpers.sxDag q)

public export
rotX : {n : Nat} -> Radians -> (q : Fin n) -> Builder n ()
rotX angle q = modify (Helpers.rotX angle q)

public export
rotY : {n : Nat} -> Radians -> (q : Fin n) -> Builder n ()
rotY angle q = modify (Helpers.rotY angle q)

public export
rotZ : {n : Nat} -> Radians -> (q : Fin n) -> Builder n ()
rotZ angle q = modify (Helpers.rotZ angle q)

public export
u : {n : Nat} -> Radians -> Radians -> Radians -> (q : Fin n) -> Builder n ()
u theta phi lambda q = modify (Helpers.u theta phi lambda q)

public export
u1 : {n : Nat} -> Radians -> (q : Fin n) -> Builder n ()
u1 lambda q = modify (Helpers.u1 lambda q)

public export
u2 : {n : Nat} -> Radians -> Radians -> (q : Fin n) -> Builder n ()
u2 phi lambda q = modify (Helpers.u2 phi lambda q)

public export
u3 : {n : Nat} -> Radians -> Radians -> Radians -> (q : Fin n) -> Builder n ()
u3 theta phi lambda q = modify (Helpers.u3 theta phi lambda q)

public export
measure : {n : Nat} -> (q : Fin n) -> Builder n ()
measure q = modify (Helpers.measure q)

public export
reset : {n : Nat} -> (q : Fin n) -> Builder n ()
reset q = modify (Helpers.reset q)

public export
cnot : {n : Nat} -> (c, t : Fin n) -> {auto 0 neq : Not (c = t)} -> Builder n ()
cnot c t = modify (Helpers.cnot c t)

public export
ctrlY : {n : Nat} -> (c, t : Fin n) -> {auto 0 neq : Not (c = t)} -> Builder n ()
ctrlY c t = modify (Helpers.ctrlY c t)

public export
ctrlZ : {n : Nat} -> (c, t : Fin n) -> {auto 0 neq : Not (c = t)} -> Builder n ()
ctrlZ c t = modify (Helpers.ctrlZ c t)

public export
swap : {n : Nat} -> (a, b : Fin n) -> {auto 0 neq : Not (a = b)} -> Builder n ()
swap a b = modify (Helpers.swap a b)

public export
ctrlH : {n : Nat} -> (c, t : Fin n) -> {auto 0 neq : Not (c = t)} -> Builder n ()
ctrlH c t = modify (Helpers.ctrlH c t)

public export
ctrlS : {n : Nat} -> (c, t : Fin n) -> {auto 0 neq : Not (c = t)} -> Builder n ()
ctrlS c t = modify (Helpers.ctrlS c t)

public export
ctrlSDag : {n : Nat} -> (c, t : Fin n) -> {auto 0 neq : Not (c = t)} -> Builder n ()
ctrlSDag c t = modify (Helpers.ctrlSDag c t)

public export
ctrlT : {n : Nat} -> (c, t : Fin n) -> {auto 0 neq : Not (c = t)} -> Builder n ()
ctrlT c t = modify (Helpers.ctrlT c t)

public export
ctrlTDag : {n : Nat} -> (c, t : Fin n) -> {auto 0 neq : Not (c = t)} -> Builder n ()
ctrlTDag c t = modify (Helpers.ctrlTDag c t)

public export
ctrlSX : {n : Nat} -> (c, t : Fin n) -> {auto 0 neq : Not (c = t)} -> Builder n ()
ctrlSX c t = modify (Helpers.ctrlSX c t)

public export
ctrlSXDag : {n : Nat} -> (c, t : Fin n) -> {auto 0 neq : Not (c = t)} -> Builder n ()
ctrlSXDag c t = modify (Helpers.ctrlSXDag c t)

public export
ctrlRX : {n : Nat} -> Radians -> (c, t : Fin n) -> {auto 0 neq : Not (c = t)} -> Builder n ()
ctrlRX angle c t = modify (Helpers.ctrlRX angle c t)

public export
ctrlRY : {n : Nat} -> Radians -> (c, t : Fin n) -> {auto 0 neq : Not (c = t)} -> Builder n ()
ctrlRY angle c t = modify (Helpers.ctrlRY angle c t)

public export
ctrlRZ : {n : Nat} -> Radians -> (c, t : Fin n) -> {auto 0 neq : Not (c = t)} -> Builder n ()
ctrlRZ angle c t = modify (Helpers.ctrlRZ angle c t)

public export
ctrlU1 : {n : Nat} -> Radians -> (c, t : Fin n) -> {auto 0 neq : Not (c = t)} -> Builder n ()
ctrlU1 lambda c t = modify (Helpers.ctrlU1 lambda c t)

public export
ctrlU2 : {n : Nat} -> Radians -> Radians -> (c, t : Fin n) -> {auto 0 neq : Not (c = t)} -> Builder n ()
ctrlU2 phi lambda c t = modify (Helpers.ctrlU2 phi lambda c t)

public export
ctrlU3 : {n : Nat} -> Radians -> Radians -> Radians -> (c, t : Fin n) -> {auto 0 neq : Not (c = t)} -> Builder n ()
ctrlU3 theta phi lambda c t = modify (Helpers.ctrlU3 theta phi lambda c t)

public export
rxx : {n : Nat} -> Radians -> (a, b : Fin n) -> {auto 0 neq : Not (a = b)} -> Builder n ()
rxx angle a b = modify (Helpers.rxx angle a b)

public export
ryy : {n : Nat} -> Radians -> (a, b : Fin n) -> {auto 0 neq : Not (a = b)} -> Builder n ()
ryy angle a b = modify (Helpers.ryy angle a b)

public export
rzz : {n : Nat} -> Radians -> (a, b : Fin n) -> {auto 0 neq : Not (a = b)} -> Builder n ()
rzz angle a b = modify (Helpers.rzz angle a b)

public export
rzx : {n : Nat} -> Radians -> (a, b : Fin n) -> {auto 0 neq : Not (a = b)} -> Builder n ()
rzx angle a b = modify (Helpers.rzx angle a b)

public export
toffoli : {n : Nat} -> (c1, c2, t : Fin n)
        -> {auto 0 d12 : Not (c1 = c2)}
        -> {auto 0 d1t : Not (c1 = t)}
        -> {auto 0 d2t : Not (c2 = t)}
        -> Builder n ()
toffoli c1 c2 t = modify (Helpers.toffoli c1 c2 t)

public export
fredkin : {n : Nat} -> (c, a, b : Fin n)
        -> {auto 0 cab : Not (a = b)}
        -> {auto 0 ca  : Not (c = a)}
        -> {auto 0 cb  : Not (c = b)}
        -> Builder n ()
fredkin c a b = modify (Helpers.fredkin c a b)

public export
ctrl : {n : Nat} ->
  {k : Nat} ->
  (cs : Vect k (Fin n)) ->           -- control wires
  (bs : Vect k Bool) ->              -- required polarities (True = |1>, False = |0>)
  (inner : UnitaryGate n) ->         -- gate to be controlled
  (distinct : AllDistinct cs) ->
  (disjoint : Disjoint cs (snd (targetsUnitary inner))) ->
  Builder n ()
ctrl cs bs inner distinct disjoint = modify (Helpers.ctrl cs bs inner distinct disjoint)
