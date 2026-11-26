module DSL.IntrinsicProofsTest

import Data.Fin
import Data.Vect
import DSL.Circuit
import DSL.CircuitBuilder
import DSL.Control
import DSL.Core
import DSL.GateHelpers
import DSL.Gates
import DSL.Helper

%default total

-- Each rejection test is followed by an accepted construction that differs only
-- in the invalid part. The accepted constructions guard against unrelated
-- proof-search failures in the rejection tests. Shared proofs and fixtures live
-- in DSL.Helper.

-- Wire bounds apply to unitary gates, nonunitary gates and control vectors.

-- Rejects a gate on wire 0 of a register with no wires.
failing "Can't find an implementation for So"
  unitaryGateInEmptyRegister : UnitaryGate 0
  unitaryGateInEmptyRegister = X 0

-- Accepts a gate on wire 0 once the register has one wire.
unitaryGateInSingleWireRegister : UnitaryGate 1
unitaryGateInSingleWireRegister = X 0

-- Rejects a wire index equal to the register width (off-by-one bound).
failing "Can't find an implementation for So"
  wireAtRegisterBound : UnitaryGate 2
  wireAtRegisterBound = X 2

-- Rejects a wire index strictly greater than the register width.
failing "Can't find an implementation for So"
  wireBeyondRegisterBound : UnitaryGate 2
  wireBeyondRegisterBound = X 3

-- Accepts the same wire index once it is the last wire of a wider register.
lastWireInRegister : UnitaryGate 3
lastWireInRegister = X 2

-- Rejects a measurement on a wire outside the register.
failing "Can't find an implementation for So"
  measurementWireOutOfBounds : Gate 2
  measurementWireOutOfBounds = Measure 2

-- Accepts a measurement on the last wire inside the register.
measurementOnLastWire : Gate 2
measurementOnLastWire = Measure 1

-- Rejects a reset on a wire outside the register.
failing "Can't find an implementation for So"
  resetWireOutOfBounds : Gate 2
  resetWireOutOfBounds = Reset 2

-- Accepts a reset on the last wire inside the register.
resetOnLastWire : Gate 2
resetOnLastWire = Reset 1

-- Rejects a discard on a wire outside the register.
failing "Can't find an implementation for So"
  discardWireOutOfBounds : Circuit 2 1
  discardWireOutOfBounds = DiscardQubit 2

-- Accepts a discard on the last wire inside the register.
discardOnLastWire : Circuit 2 1
discardOnLastWire = DiscardQubit 1

-- Rejects a control wire outside the register even when the target is valid.
failing "Can't find an implementation for So"
  controlWireOutOfBounds : UnitaryGate 2
  controlWireOutOfBounds = Controlled [2] [One] (X 1)

-- Accepts a control on the last wire inside the register.
controlOnLastWire : UnitaryGate 2
controlOnLastWire = Controlled [1] [One] (X 0)

-- Rejects a numeric literal equal to the Fin bound.
failing "Can't find an implementation for LTE"
  literalAtRegisterBound : Fin 2
  literalAtRegisterBound = natToFinLT 2

-- Accepts the same literal once it is below the Fin bound.
literalWithinBounds : Fin 3
literalWithinBounds = natToFinLT 2

-- Rejects any numeric literal for the uninhabited type Fin 0.
failing "Can't find an implementation for LTE"
  literalInEmptyRegister : Fin 0
  literalInEmptyRegister = natToFinLT 0

-- Accepts literal 0 for Fin 1, its only inhabitant.
literalInSingleWireRegister : Fin 1
literalInSingleWireRegister = natToFinLT 0

-- Proof constructors must not manufacture evidence for repeated wires.

-- Rejects a proof that a wire is absent from a list containing only itself.
failing "Can't find an implementation for Void"
  wireAbsentFromItself : NotElem (the (Fin 1) 0) [0]
  wireAbsentFromItself = NotThere NotHere

-- Accepts a proof that a wire is absent from a list holding a different wire.
wireAbsentFromSingleOtherWire : NotElem (the (Fin 2) 0) [1]
wireAbsentFromSingleOtherWire = NotThere NotHere

-- Rejects a proof that a wire is absent when it occurs later in the list.
failing "Can't find an implementation for Void"
  wireAbsentFromTailContainingIt : NotElem (the (Fin 2) 0) [1, 0]
  wireAbsentFromTailContainingIt = NotThere (NotThere NotHere)

-- Accepts the same proof shape when no element of the list equals the wire.
wireAbsentFromOtherWires : NotElem (the (Fin 3) 0) [1, 2]
wireAbsentFromOtherWires = NotThere (NotThere NotHere)

-- Rejects a distinctness proof for a vector that repeats a wire.
failing "Can't find an implementation for NotElem"
  repeatedWiresAreDistinct : AllDistinct (the (Vect 2 (Fin 1)) [0, 0])
  repeatedWiresAreDistinct = ADCons %search (ADCons NotHere ADNil)

-- Accepts the same distinctness proof shape for two different wires.
differentWiresAreDistinct : AllDistinct (the (Vect 2 (Fin 2)) [0, 1])
differentWiresAreDistinct = ADCons %search (ADCons NotHere ADNil)

-- Rejects a disjointness proof for two vectors sharing a wire.
failing "Can't find an implementation for NotElem"
  overlappingWiresAreDisjoint : Disjoint (the (Vect 2 (Fin 3)) [0, 1]) [1, 2]
  overlappingWiresAreDisjoint = [%search, %search]

-- Accepts a disjointness proof for two vectors with no wire in common.
separateWiresAreDisjoint : Disjoint (the (Vect 2 (Fin 3)) [0, 1]) [2]
separateWiresAreDisjoint = [%search, %search]

-- Every two-wire primitive requires distinct operands.

-- Rejects CX with the same wire as control and target.
failing "Can't find an implementation for Void"
  cxWithRepeatedWire : UnitaryGate 1
  cxWithRepeatedWire = CX 0 0

-- Accepts CX on two distinct wires.
cxWithDistinctWires : UnitaryGate 2
cxWithDistinctWires = CX 0 1

-- Rejects CY with the same wire as control and target.
failing "Can't find an implementation for Void"
  cyWithRepeatedWire : UnitaryGate 1
  cyWithRepeatedWire = CY 0 0

-- Accepts CY on two distinct wires.
cyWithDistinctWires : UnitaryGate 2
cyWithDistinctWires = CY 0 1

-- Rejects CZ with the same wire as control and target.
failing "Can't find an implementation for Void"
  czWithRepeatedWire : UnitaryGate 1
  czWithRepeatedWire = CZ 0 0

-- Accepts CZ on two distinct wires.
czWithDistinctWires : UnitaryGate 2
czWithDistinctWires = CZ 0 1

-- Rejects CH with the same wire as control and target.
failing "Can't find an implementation for Void"
  chWithRepeatedWire : UnitaryGate 1
  chWithRepeatedWire = CH 0 0

-- Accepts CH on two distinct wires.
chWithDistinctWires : UnitaryGate 2
chWithDistinctWires = CH 0 1

-- Rejects CS with the same wire as control and target.
failing "Can't find an implementation for Void"
  csWithRepeatedWire : UnitaryGate 1
  csWithRepeatedWire = CS 0 0

-- Accepts CS on two distinct wires.
csWithDistinctWires : UnitaryGate 2
csWithDistinctWires = CS 0 1

-- Rejects CSDG with the same wire as control and target.
failing "Can't find an implementation for Void"
  csdgWithRepeatedWire : UnitaryGate 1
  csdgWithRepeatedWire = CSDG 0 0

-- Accepts CSDG on two distinct wires.
csdgWithDistinctWires : UnitaryGate 2
csdgWithDistinctWires = CSDG 0 1

-- Rejects CT with the same wire as control and target.
failing "Can't find an implementation for Void"
  ctWithRepeatedWire : UnitaryGate 1
  ctWithRepeatedWire = CT 0 0

-- Accepts CT on two distinct wires.
ctWithDistinctWires : UnitaryGate 2
ctWithDistinctWires = CT 0 1

-- Rejects CTDG with the same wire as control and target.
failing "Can't find an implementation for Void"
  ctdgWithRepeatedWire : UnitaryGate 1
  ctdgWithRepeatedWire = CTDG 0 0

-- Accepts CTDG on two distinct wires.
ctdgWithDistinctWires : UnitaryGate 2
ctdgWithDistinctWires = CTDG 0 1

-- Rejects CSX with the same wire as control and target.
failing "Can't find an implementation for Void"
  csxWithRepeatedWire : UnitaryGate 1
  csxWithRepeatedWire = CSX 0 0

-- Accepts CSX on two distinct wires.
csxWithDistinctWires : UnitaryGate 2
csxWithDistinctWires = CSX 0 1

-- Rejects CSXDG with the same wire as control and target.
failing "Can't find an implementation for Void"
  csxdgWithRepeatedWire : UnitaryGate 1
  csxdgWithRepeatedWire = CSXDG 0 0

-- Accepts CSXDG on two distinct wires.
csxdgWithDistinctWires : UnitaryGate 2
csxdgWithDistinctWires = CSXDG 0 1

-- Rejects CRX with the same wire as control and target.
failing "Can't find an implementation for Void"
  crxWithRepeatedWire : UnitaryGate 1
  crxWithRepeatedWire = CRX testAngle 0 0

-- Accepts CRX on two distinct wires.
crxWithDistinctWires : UnitaryGate 2
crxWithDistinctWires = CRX testAngle 0 1

-- Rejects CRY with the same wire as control and target.
failing "Can't find an implementation for Void"
  cryWithRepeatedWire : UnitaryGate 1
  cryWithRepeatedWire = CRY testAngle 0 0

-- Accepts CRY on two distinct wires.
cryWithDistinctWires : UnitaryGate 2
cryWithDistinctWires = CRY testAngle 0 1

-- Rejects CRZ with the same wire as control and target.
failing "Can't find an implementation for Void"
  crzWithRepeatedWire : UnitaryGate 1
  crzWithRepeatedWire = CRZ testAngle 0 0

-- Accepts CRZ on two distinct wires.
crzWithDistinctWires : UnitaryGate 2
crzWithDistinctWires = CRZ testAngle 0 1

-- Rejects CU1 with the same wire as control and target.
failing "Can't find an implementation for Void"
  cu1WithRepeatedWire : UnitaryGate 1
  cu1WithRepeatedWire = CU1 testAngle 0 0

-- Accepts CU1 on two distinct wires.
cu1WithDistinctWires : UnitaryGate 2
cu1WithDistinctWires = CU1 testAngle 0 1

-- Rejects CU2 with the same wire as control and target.
failing "Can't find an implementation for Void"
  cu2WithRepeatedWire : UnitaryGate 1
  cu2WithRepeatedWire = CU2 testAngle testAngle 0 0

-- Accepts CU2 on two distinct wires.
cu2WithDistinctWires : UnitaryGate 2
cu2WithDistinctWires = CU2 testAngle testAngle 0 1

-- Rejects CU3 with the same wire as control and target.
failing "Can't find an implementation for Void"
  cu3WithRepeatedWire : UnitaryGate 1
  cu3WithRepeatedWire = CU3 testAngle testAngle testAngle 0 0

-- Accepts CU3 on two distinct wires.
cu3WithDistinctWires : UnitaryGate 2
cu3WithDistinctWires = CU3 testAngle testAngle testAngle 0 1

-- Rejects SWAP of a wire with itself.
failing "Can't find an implementation for Void"
  swapWithRepeatedWire : UnitaryGate 1
  swapWithRepeatedWire = SWAP 0 0

-- Accepts SWAP of two distinct wires.
swapWithDistinctWires : UnitaryGate 2
swapWithDistinctWires = SWAP 0 1

-- Rejects RXX acting twice on the same wire.
failing "Can't find an implementation for Void"
  rxxWithRepeatedWire : UnitaryGate 1
  rxxWithRepeatedWire = RXX testAngle 0 0

-- Accepts RXX on two distinct wires.
rxxWithDistinctWires : UnitaryGate 2
rxxWithDistinctWires = RXX testAngle 0 1

-- Rejects RYY acting twice on the same wire.
failing "Can't find an implementation for Void"
  ryyWithRepeatedWire : UnitaryGate 1
  ryyWithRepeatedWire = RYY testAngle 0 0

-- Accepts RYY on two distinct wires.
ryyWithDistinctWires : UnitaryGate 2
ryyWithDistinctWires = RYY testAngle 0 1

-- Rejects RZZ acting twice on the same wire.
failing "Can't find an implementation for Void"
  rzzWithRepeatedWire : UnitaryGate 1
  rzzWithRepeatedWire = RZZ testAngle 0 0

-- Accepts RZZ on two distinct wires.
rzzWithDistinctWires : UnitaryGate 2
rzzWithDistinctWires = RZZ testAngle 0 1

-- Rejects RZX acting twice on the same wire.
failing "Can't find an implementation for Void"
  rzxWithRepeatedWire : UnitaryGate 1
  rzxWithRepeatedWire = RZX testAngle 0 0

-- Accepts RZX on two distinct wires.
rzxWithDistinctWires : UnitaryGate 2
rzxWithDistinctWires = RZX testAngle 0 1

-- The accepted calls must infer every inequality using the production proof
-- hint. Nonzero operands and permutations catch hints that prematurely choose FZ.

-- Rejects CX on a repeated wire that is not wire 0.
failing "Can't find an implementation for Void"
  cxWithRepeatedNonzeroWire : UnitaryGate 3
  cxWithRepeatedNonzeroWire = CX 1 1

-- Accepts CX on distinct nonzero wires in both operand orders.
cxWithDistinctNonzeroWires : List (UnitaryGate 3)
cxWithDistinctNonzeroWires = [CX 1 2, CX 2 1]

-- Rejects SWAP of a nonzero wire with itself.
failing "Can't find an implementation for Void"
  swapWithRepeatedNonzeroWire : UnitaryGate 3
  swapWithRepeatedNonzeroWire = SWAP 2 2

-- Accepts SWAP of distinct high-index wires in both operand orders.
swapWithDistinctNonzeroWires : List (UnitaryGate 5)
swapWithDistinctNonzeroWires = [SWAP 3 4, SWAP 4 3]

-- Accepts the builder versions of cnot and swap on nonzero and reversed wires.
nonzeroTwoWireBuilderCalls : Circuit 4 4
nonzeroTwoWireBuilderCalls = build $ do
  DSL.CircuitBuilder.cnot 1 2
  DSL.CircuitBuilder.cnot 3 1
  DSL.CircuitBuilder.swap 2 3

-- Isolate each pairwise inequality of the three-wire primitives. The remaining
-- pairs have explicit proofs, leaving only one obligation for search.

-- Rejects a Toffoli gate whose two controls are the same wire.
failing "Can't find an implementation for Void"
  toffoliWithRepeatedControls : UnitaryGate 2
  toffoliWithRepeatedControls = CCX 0 0 1
    {d1t = zeroNotSuccessor} {d2t = zeroNotSuccessor}

-- Accepts a Toffoli gate whose controls differ, with only that inequality
-- left to proof search.
toffoliWithDistinctControls : UnitaryGate 3
toffoliWithDistinctControls = CCX 1 2 0
  {d1t = successorNotZero} {d2t = successorNotZero}

-- Rejects a Toffoli gate whose first control is also the target.
failing "Can't find an implementation for Void"
  toffoliFirstControlIsTarget : UnitaryGate 2
  toffoliFirstControlIsTarget = CCX 0 1 0
    {d12 = zeroNotSuccessor} {d2t = successorNotZero}

-- Accepts a Toffoli gate whose first control differs from the target, with
-- only that inequality left to proof search.
toffoliFirstControlDiffersFromTarget : UnitaryGate 3
toffoliFirstControlDiffersFromTarget = CCX 1 0 2
  {d12 = successorNotZero} {d2t = zeroNotSuccessor}

-- Rejects a Toffoli gate whose second control is also the target.
failing "Can't find an implementation for Void"
  toffoliSecondControlIsTarget : UnitaryGate 2
  toffoliSecondControlIsTarget = CCX 0 1 1
    {d12 = zeroNotSuccessor} {d1t = zeroNotSuccessor}

-- Accepts a Toffoli gate whose second control differs from the target, with
-- only that inequality left to proof search.
toffoliSecondControlDiffersFromTarget : UnitaryGate 3
toffoliSecondControlDiffersFromTarget = CCX 0 1 2
  {d12 = zeroNotSuccessor} {d1t = zeroNotSuccessor}

-- Accepts Toffoli gates in every wire order, with all three inequalities
-- inferred automatically.
toffoliWirePermutations : List (UnitaryGate 3)
toffoliWirePermutations =
  [CCX 0 1 2, CCX 0 2 1, CCX 1 0 2, CCX 1 2 0, CCX 2 0 1, CCX 2 1 0]

-- Accepts the circuit helper toffoli with its inequalities inferred.
automaticToffoliCircuitHelper : Circuit 3 3
automaticToffoliCircuitHelper = DSL.GateHelpers.toffoli 0 1 2 EmptyCircuit

-- Accepts the builder toffoli with its inequalities inferred.
automaticToffoliBuilder : Builder 3 ()
automaticToffoliBuilder = DSL.CircuitBuilder.toffoli 0 1 2

-- Rejects a Fredkin gate that swaps a wire with itself.
failing "Can't find an implementation for Void"
  fredkinWithRepeatedTargets : UnitaryGate 2
  fredkinWithRepeatedTargets = CSWAP 0 1 1
    {ca = zeroNotSuccessor} {cb = zeroNotSuccessor}

-- Accepts a Fredkin gate with distinct swap targets, with only that
-- inequality left to proof search.
fredkinWithDistinctTargets : UnitaryGate 3
fredkinWithDistinctTargets = CSWAP 0 1 2
  {ca = zeroNotSuccessor} {cb = zeroNotSuccessor}

-- Rejects a Fredkin gate whose control is also its first swap target.
failing "Can't find an implementation for Void"
  fredkinControlIsFirstTarget : UnitaryGate 2
  fredkinControlIsFirstTarget = CSWAP 0 0 1
    {ab = zeroNotSuccessor} {cb = zeroNotSuccessor}

-- Accepts a Fredkin gate whose control differs from its first swap target,
-- with only that inequality left to proof search.
fredkinControlDiffersFromFirstTarget : UnitaryGate 3
fredkinControlDiffersFromFirstTarget = CSWAP 1 2 0
  {ab = successorNotZero} {cb = successorNotZero}

-- Rejects a Fredkin gate whose control is also its second swap target.
failing "Can't find an implementation for Void"
  fredkinControlIsSecondTarget : UnitaryGate 2
  fredkinControlIsSecondTarget = CSWAP 0 1 0
    {ab = successorNotZero} {ca = zeroNotSuccessor}

-- Accepts a Fredkin gate whose control differs from its second swap target,
-- with only that inequality left to proof search.
fredkinControlDiffersFromSecondTarget : UnitaryGate 3
fredkinControlDiffersFromSecondTarget = CSWAP 1 0 2
  {ab = zeroNotSuccessor} {ca = successorNotZero}

-- Accepts Fredkin gates in every wire order, with all three inequalities
-- inferred automatically.
fredkinWirePermutations : List (UnitaryGate 3)
fredkinWirePermutations =
  [CSWAP 0 1 2, CSWAP 0 2 1, CSWAP 1 0 2, CSWAP 1 2 0, CSWAP 2 0 1, CSWAP 2 1 0]

-- Accepts the circuit helper fredkin with its inequalities inferred.
automaticFredkinCircuitHelper : Circuit 3 3
automaticFredkinCircuitHelper = DSL.GateHelpers.fredkin 2 1 0 EmptyCircuit

-- Accepts the builder fredkin with its inequalities inferred.
automaticFredkinBuilder : Builder 3 ()
automaticFredkinBuilder = DSL.CircuitBuilder.fredkin 2 1 0

-- Generic controls must be unique and disjoint from every inner wire.

-- Rejects a control placed on the wire of the gate it controls.
failing "Can't find an implementation for All ("
  controlOverlapsTarget : UnitaryGate 1
  controlOverlapsTarget = Controlled [0] [One] (X 0)

-- Accepts a control on a wire separate from the controlled gate.
controlDisjointFromTarget : UnitaryGate 2
controlDisjointFromTarget = Controlled [0] [One] (X 1)

-- Rejects the same control wire listed twice in a row.
failing "Can't find an implementation for AllDistinct"
  duplicateControls : UnitaryGate 2
  duplicateControls = Controlled [0, 0] [One, Zero] (X 1)

-- Accepts two different control wires.
distinctControls : UnitaryGate 3
distinctControls = Controlled [0, 1] [One, Zero] (X 2)

-- Rejects a control wire repeated with another control in between.
failing "Can't find an implementation for AllDistinct"
  nonAdjacentDuplicateControls : UnitaryGate 3
  nonAdjacentDuplicateControls = Controlled [0, 1, 0] [One, Zero, Plus] (X 2)

-- Accepts three different control wires.
nonAdjacentDistinctControls : UnitaryGate 4
nonAdjacentDistinctControls = Controlled [0, 1, 2] [One, Zero, Plus] (X 3)

-- Rejects a later control, not just the first, that overlaps the target.
failing "Can't find an implementation for All ("
  secondControlOverlapsTarget : UnitaryGate 3
  secondControlOverlapsTarget = Controlled [0, 2] [One, Zero] (X 2)

-- Accepts the same controls once the target uses a different wire.
secondControlDisjointFromTarget : UnitaryGate 3
secondControlDisjointFromTarget = Controlled [0, 2] [One, Zero] (X 1)

-- Rejects an outer control on the control wire of an inner CX.
failing "Can't find an implementation for All ("
  controlOverlapsPrimitiveControl : UnitaryGate 2
  controlOverlapsPrimitiveControl = Controlled [0] [One] innerCnot

-- Rejects an outer control on the target wire of an inner CX.
failing "Can't find an implementation for All ("
  controlOverlapsPrimitiveTarget : UnitaryGate 2
  controlOverlapsPrimitiveTarget = Controlled [1] [One] innerCnot

-- Accepts an outer control on a wire unused by the inner CX.
controlAfterPrimitiveWires : UnitaryGate 3
controlAfterPrimitiveWires = Controlled [2] [One] (CX 0 1)

-- Rejects a control on the first wire of an inner SWAP.
failing "Can't find an implementation for All ("
  controlOverlapsFirstSwapWire : UnitaryGate 2
  controlOverlapsFirstSwapWire = Controlled [0] [One] innerSwap

-- Rejects a control on the second wire of an inner SWAP.
failing "Can't find an implementation for All ("
  controlOverlapsSecondSwapWire : UnitaryGate 2
  controlOverlapsSecondSwapWire = Controlled [1] [One] innerSwap

-- Accepts a control on a wire unused by the inner SWAP.
controlAfterSwapWires : UnitaryGate 3
controlAfterSwapWires = Controlled [2] [One] (SWAP 0 1)

-- Rejects a control on the first control wire of an inner Toffoli.
failing "Can't find an implementation for All ("
  controlOverlapsFirstToffoliControl : UnitaryGate 3
  controlOverlapsFirstToffoliControl = Controlled [0] [One] innerToffoli

-- Rejects a control on the second control wire of an inner Toffoli.
failing "Can't find an implementation for All ("
  controlOverlapsSecondToffoliControl : UnitaryGate 3
  controlOverlapsSecondToffoliControl = Controlled [1] [One] innerToffoli

-- Rejects a control on the target wire of an inner Toffoli.
failing "Can't find an implementation for All ("
  controlOverlapsToffoliTarget : UnitaryGate 3
  controlOverlapsToffoliTarget = Controlled [2] [One] innerToffoli

-- Accepts a control on a wire unused by the inner Toffoli.
controlAfterToffoliWires : UnitaryGate 4
controlAfterToffoliWires = Controlled [3] [One] (CCX 0 1 2)

-- Rejects a control on the control wire of an inner Fredkin.
failing "Can't find an implementation for All ("
  controlOverlapsFredkinControl : UnitaryGate 3
  controlOverlapsFredkinControl = Controlled [0] [One] innerFredkin

-- Rejects a control on the first swap target of an inner Fredkin.
failing "Can't find an implementation for All ("
  controlOverlapsFirstFredkinTarget : UnitaryGate 3
  controlOverlapsFirstFredkinTarget = Controlled [1] [One] innerFredkin

-- Rejects a control on the second swap target of an inner Fredkin.
failing "Can't find an implementation for All ("
  controlOverlapsSecondFredkinTarget : UnitaryGate 3
  controlOverlapsSecondFredkinTarget = Controlled [2] [One] innerFredkin

-- Accepts a control on a wire unused by the inner Fredkin.
controlAfterFredkinWires : UnitaryGate 4
controlAfterFredkinWires = Controlled [3] [One] (CSWAP 0 1 2)

-- Rejects an outer control on the control wire of a nested Controlled gate.
failing "Can't find an implementation for All ("
  controlOverlapsNestedControl : UnitaryGate 3
  controlOverlapsNestedControl = Controlled [1] [Zero] innerControlledRotation

-- Rejects an outer control on the target wire of a nested Controlled gate.
failing "Can't find an implementation for All ("
  controlOverlapsNestedTarget : UnitaryGate 3
  controlOverlapsNestedTarget = Controlled [2] [One] innerControlledRotation

-- Accepts an outer control on a wire unused by the nested Controlled gate.
nestedControlledRotation : UnitaryGate 3
nestedControlledRotation = Controlled [0] [Zero] innerControlledRotation

-- Control states and controls have the same length; all gates use the same
-- register width, and only unitary gates can be placed under quantum control.
-- Nonunitary gates have no accepted counterpart under quantum control.

-- Rejects fewer control states than control wires.
failing "Mismatch between"
  controlsWithTooFewStates : UnitaryGate 3
  controlsWithTooFewStates = Controlled {k = 2} [0, 1] [One] (X 2)

-- Rejects more control states than control wires.
failing "Mismatch between"
  controlsWithTooManyStates : UnitaryGate 3
  controlsWithTooManyStates = Controlled {k = 2} [0, 1] [One, Zero, Plus] (X 2)

-- Accepts one control state per control wire, using non-computational bases.
mixedBasisControls : UnitaryGate 3
mixedBasisControls = Controlled [0, 1] [Plus, MinusI] (X 2)

-- Rejects a control state given without any control wire.
failing "Mismatch between"
  emptyControlsWithState : UnitaryGate 1
  emptyControlsWithState = Controlled {k = 0} [] [One] singleWireGate

-- Accepts an empty control list with an empty state list.
emptyControls : UnitaryGate 1
emptyControls = Controlled [] [] singleWireGate

-- Rejects an inner gate whose register width differs from the outer gate's.
failing "Mismatch between"
  controlledGateWithDifferentRegisterWidth : UnitaryGate 2
  controlledGateWithDifferentRegisterWidth = Controlled [] [] innerControlledRotation

-- Accepts the same inner gate when both register widths agree.
controlledGateWithSameRegisterWidth : UnitaryGate 3
controlledGateWithSameRegisterWidth = Controlled [] [] innerControlledRotation

-- Rejects a measurement under quantum control.
failing "Mismatch between"
  controlledMeasurement : UnitaryGate 1
  controlledMeasurement = Controlled [] [] (Measure 0)

-- Rejects a reset under quantum control.
failing "Mismatch between"
  controlledReset : UnitaryGate 1
  controlledReset = Controlled [] [] (Reset 0)

-- Rejects a discard under quantum control.
failing "Mismatch between"
  controlledDiscard : UnitaryGate 1
  controlledDiscard = Controlled [] [] (DiscardQubit 0)

-- Public helpers preserve the constructor's proof obligations.

-- Rejects the circuit helper ctrl with a repeated control wire.
failing "Can't find an implementation for AllDistinct"
  circuitHelperDuplicateControls : Circuit 2 2
  circuitHelperDuplicateControls = DSL.GateHelpers.ctrl [0, 0] [One, Zero] (X 1) EmptyCircuit

-- Accepts the circuit helper ctrl with two different control wires.
circuitHelperDistinctControls : Circuit 3 3
circuitHelperDistinctControls = DSL.GateHelpers.ctrl [0, 1] [One, Zero] (X 2) EmptyCircuit

-- Rejects the circuit helper ctrl with a control on the target wire.
failing "Can't find an implementation for All ("
  circuitHelperControlOverlapsTarget : Circuit 1 1
  circuitHelperControlOverlapsTarget = DSL.GateHelpers.ctrl [0] [One] singleWireGate EmptyCircuit

-- Accepts the circuit helper ctrl with a control separate from the target.
circuitHelperControlDisjointFromTarget : Circuit 2 2
circuitHelperControlDisjointFromTarget = DSL.GateHelpers.ctrl [0] [One] (X 1) EmptyCircuit

-- Rejects the builder ctrl with a repeated control wire.
failing "Can't find an implementation for AllDistinct"
  builderDuplicateControls : Builder 2 ()
  builderDuplicateControls = DSL.CircuitBuilder.ctrl [0, 0] [One, Zero] (X 1)

-- Accepts the builder ctrl with two different control wires.
builderDistinctControls : Builder 3 ()
builderDistinctControls = DSL.CircuitBuilder.ctrl [0, 1] [One, Zero] (X 2)

-- Rejects the builder ctrl with a control on the target wire.
failing "Can't find an implementation for All ("
  builderControlOverlapsTarget : Builder 1 ()
  builderControlOverlapsTarget = DSL.CircuitBuilder.ctrl [0] [One] singleWireGate

-- Accepts the builder ctrl with a control separate from the target.
builderControlDisjointFromTarget : Builder 2 ()
builderControlDisjointFromTarget = DSL.CircuitBuilder.ctrl [0] [One] (X 1)

-- Circuit indices enforce gate widths, sequential connections, parallel sums
-- and the number of wires introduced by initialization or removed by discard.

-- Rejects wrapping a unitary gate into a Gate of a different register width.
failing "Mismatch between"
  unitaryGateWithDifferentRegisterWidth : Gate 1
  unitaryGateWithDifferentRegisterWidth = UGate innerCnot

-- Accepts wrapping a unitary gate into a Gate of the same register width.
unitaryGateWithSameRegisterWidth : Gate 2
unitaryGateWithSameRegisterWidth = UGate innerCnot

-- Rejects an empty circuit whose output width differs from its input width.
failing "Mismatch between"
  identityChangesWidth : Circuit 1 2
  identityChangesWidth = EmptyCircuit

-- Accepts an empty circuit with equal input and output widths.
identityPreservesWidth : Circuit 1 1
identityPreservesWidth = EmptyCircuit

-- Accepts an empty circuit on an empty register.
zeroWireCircuit : Circuit 0 0
zeroWireCircuit = EmptyCircuit

-- Rejects a gate application that claims to change the circuit width.
failing "Mismatch between"
  gateApplicationChangesWidth : Circuit 1 2
  gateApplicationChangesWidth = SingleGate (UGate singleWireGate)

-- Accepts a gate application that keeps the circuit width.
gateApplicationPreservesWidth : Circuit 1 1
gateApplicationPreservesWidth = SingleGate (UGate singleWireGate)

-- Rejects sequencing circuits whose intermediate widths do not connect.
failing "Mismatch between"
  sequentialWidthsDoNotMatch : Circuit 1 2
  sequentialWidthsDoNotMatch = Sequence oneWireCircuit twoWireCircuit

-- Rejects a sequence whose second circuit ignores a wire added by the first.
failing "Mismatch between"
  sequenceIgnoresInitializedWire : Circuit 1 1
  sequenceIgnoresInitializedWire = Sequence initializeOneWire oneWireCircuit

-- Accepts a sequence whose second circuit uses the wire added by the first.
sequentialAllocation : Circuit 1 2
sequentialAllocation = Sequence initializeOneWire twoWireCircuit

-- Rejects a parallel composition whose input width is not the sum of its parts.
failing "Mismatch between"
  parallelInputWidthIsNotSum : Circuit 1 2
  parallelInputWidthIsNotSum = Parallel oneWireCircuit oneWireCircuit

-- Rejects a parallel composition whose output width is not the sum of its parts.
failing "Mismatch between"
  parallelOutputWidthIsNotSum : Circuit 2 3
  parallelOutputWidthIsNotSum = Parallel oneWireCircuit oneWireCircuit

-- Accepts a parallel composition whose widths are the sums of its parts.
localWiresInParallel : Circuit 2 2
localWiresInParallel = Parallel oneWireCircuit oneWireCircuit

-- Rejects a parallel composition that drops a wire allocated by one side.
failing "Mismatch between"
  parallelAllocationOmitsOutput : Circuit 2 3
  parallelAllocationOmitsOutput = Parallel initializeOneWire initializeOneWire

-- Accepts a parallel composition that keeps the wires allocated by both sides.
parallelAllocation : Circuit 2 4
parallelAllocation = Parallel initializeOneWire initializeOneWire

-- Rejects an initialization whose output omits the newly allocated wire.
failing "Mismatch between"
  initializationOmitsOutput : Circuit 1 1
  initializationOmitsOutput = AllocateQubits [Zero]

-- Rejects an initialization that claims more new wires than it allocates.
failing "Mismatch between"
  initializationAddsExtraOutput : Circuit 1 3
  initializationAddsExtraOutput = AllocateQubits [Zero]

-- Accepts an initialization that adds exactly one wire per initial state.
initializationAddsOneOutput : Circuit 1 2
initializationAddsOneOutput = AllocateQubits [Zero]

-- Rejects an empty initialization that claims to remove a wire.
failing "Mismatch between"
  initializationRemovesWire : Circuit 2 1
  initializationRemovesWire = AllocateQubits []

-- Accepts an empty initialization that keeps the width unchanged.
emptyInitialization : Circuit 1 1
emptyInitialization = AllocateQubits []

-- Rejects a discard that claims to keep the circuit width.
failing "Mismatch between"
  discardKeepsWidth : Circuit 2 2
  discardKeepsWidth = DiscardQubit 0

-- Accepts a discard that removes exactly one wire.
discardRemovesOneWire : Circuit 2 1
discardRemovesOneWire = DiscardQubit 0

-- Rejects a gate after a discard on a wire index that no longer exists.
failing "Can't find an implementation for So"
  gateAfterDiscardUsesRemovedWire : Circuit 2 1
  gateAfterDiscardUsesRemovedWire = Sequence (DiscardQubit 1) (SingleGate (UGate (X 1)))

-- Accepts a gate after a discard on a wire that remains.
gateAfterDiscardUsesRemainingWire : Circuit 2 1
gateAfterDiscardUsesRemainingWire = Sequence (DiscardQubit 1) (SingleGate (UGate (X 0)))

-- Accepts discarding a freshly allocated wire, which restores the original width.
discardAfterAllocation : Circuit 1 1
discardAfterAllocation = Sequence initializeOneWire (DiscardQubit 1)

-- Rejects repeating a circuit that changes the register width.
failing "Mismatch between"
  repeatCircuitThatChangesWidth : Circuit 1 1
  repeatCircuitThatChangesWidth = pow 2 initializeOneWire

-- Accepts repeating a circuit that keeps the register width.
repeatedCircuit : Circuit 1 1
repeatedCircuit = pow 2 oneWireCircuit

-- Rejects appending a circuit that changes the register width.
failing "Mismatch between"
  appendCircuitThatChangesWidth : Builder 1 ()
  appendCircuitThatChangesWidth = append initializeOneWire

-- Rejects appending a circuit built for a different register width.
failing "Mismatch between"
  appendCircuitWithDifferentRegisterWidth : Builder 1 ()
  appendCircuitWithDifferentRegisterWidth = append twoWireCircuit

-- Accepts appending a circuit with the builder's register width.
appendedCircuit : Circuit 1 1
appendedCircuit = build (append oneWireCircuit)

-- Circuit helpers and builder operations keep no register width at run time,
-- so functions that erase the width can call them.

-- Accepts the circuit helper hadamard in a function whose output width is erased.
hadamardHelperWithErasedWidth : {0 width : Nat} -> Fin width -> Circuit 0 width -> Circuit 0 width
hadamardHelperWithErasedWidth wire circuit = DSL.GateHelpers.hadamard wire circuit

-- Accepts the circuit helper cnot with an erased width, given that its wires differ.
cnotHelperWithErasedWidth : {0 width : Nat} -> (control, target : Fin width) ->
  {auto 0 controlDiffersFromTarget : Not (control = target)} ->
  Circuit 0 width -> Circuit 0 width
cnotHelperWithErasedWidth control target circuit = DSL.GateHelpers.cnot control target circuit

-- Accepts the builder hadamard in a function whose register width is erased.
hadamardBuilderWithErasedWidth : {0 width : Nat} -> Fin width -> Builder width ()
hadamardBuilderWithErasedWidth wire = DSL.CircuitBuilder.hadamard wire

-- Accepts building a circuit in a function whose register width is erased.
builtHadamardWithErasedWidth : {0 width : Nat} -> Fin width -> Circuit width width
builtHadamardWithErasedWidth wire = build (DSL.CircuitBuilder.hadamard wire)
