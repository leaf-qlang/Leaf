module DSL.Helper

import Data.Fin
import Data.Vect
import DSL.Circuit
import DSL.Core
import DSL.Gates

%default total

-- Explicit proofs isolate the invalid obligation in pairwise rejection tests.
-- Automatic construction uses the production hint in DSL.Control.
public export
zeroNotSuccessor : {n : Nat} -> {q : Fin n} -> Not (FZ = FS q)
zeroNotSuccessor Refl impossible

public export
successorNotZero : {n : Nat} -> {q : Fin n} -> Not (FS q = FZ)
successorNotZero Refl impossible

-- Export fixture definitions so proof search can reduce their wire lists.
-- Keep them outside failing blocks so an invalid fixture cannot satisfy a
-- rejection test intended to check an outer construction.
public export
testAngle : Radians
testAngle = MkRadians 0.25

public export
singleWireGate : UnitaryGate 1
singleWireGate = X 0

public export
innerControlledRotation : UnitaryGate 3
innerControlledRotation = Controlled [1] [One] (RZ testAngle 2)

public export
innerCnot : UnitaryGate 2
innerCnot = CX 0 1

public export
innerSwap : UnitaryGate 2
innerSwap = SWAP 0 1

public export
innerToffoli : UnitaryGate 3
innerToffoli = CCX 0 1 2

public export
innerFredkin : UnitaryGate 3
innerFredkin = CSWAP 0 1 2

public export
oneWireCircuit : Circuit 1 1
oneWireCircuit = GateApplication (UGate singleWireGate)

public export
twoWireCircuit : Circuit 2 2
twoWireCircuit = GateApplication (UGate innerCnot)

public export
initializeOneWire : Circuit 1 2
initializeOneWire = Init [Zero]
