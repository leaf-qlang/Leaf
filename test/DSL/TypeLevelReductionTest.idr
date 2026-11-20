module DSL.TypeLevelReductionTest

import Data.Fin
import Data.Maybe
import Data.Vect
import DSL.Adjoint
import DSL.Circuit
import DSL.CircuitBuilder
import DSL.Core
import DSL.GateHelpers
import DSL.Gates
import DSL.Helpers

%default total

-- Each test states an equation that must hold by evaluation alone, so Refl
-- proves it while the module is type checked. The proofs in DSL.Gates and
-- DSL.Control rely on these functions reducing during type checking; a test
-- also fails if a function stops being public export. Selected wrong equations
-- sit in failing blocks to show that Refl does not accept every equation.
-- Expected values are written out in full: Idris may stop reducing when one
-- side of the equation is the name of a top-level definition.

-- wiresUnitary computes the wire list checked by the Controlled constructor.

-- A single-wire gate uses exactly its operand, for any wire.
wiresOfSingleWireGate : {n : Nat} -> (q : Fin n) -> wiresUnitary (H q) = (1 ** [q])
wiresOfSingleWireGate q = Refl

-- A two-wire gate lists its control before its target, for any wires.
wiresOfTwoWireGateListControlFirst : {n : Nat} -> (c, t : Fin n) ->
  {auto 0 neq : Not (c = t)} -> wiresUnitary (CX c t) = (2 ** [c, t])
wiresOfTwoWireGateListControlFirst c t = Refl

-- Rejects an equation listing the target of a two-wire gate before its control.
failing "Mismatch between"
  wiresOfTwoWireGateListTargetFirst :
    wiresUnitary (CX {n = 2} 0 1) = (2 ** [1, 0])
  wiresOfTwoWireGateListTargetFirst = Refl

-- SWAP keeps its operands in the order they were given.
wiresOfSwapKeepOperandOrder : {n : Nat} -> (a, b : Fin n) ->
  {auto 0 neq : Not (a = b)} -> wiresUnitary (SWAP a b) = (2 ** [a, b])
wiresOfSwapKeepOperandOrder a b = Refl

-- A Toffoli gate lists both controls and then its target.
wiresOfToffoliListControlsThenTarget : {n : Nat} -> (c1, c2, t : Fin n) ->
  {auto 0 d12 : Not (c1 = c2)} -> {auto 0 d1t : Not (c1 = t)} ->
  {auto 0 d2t : Not (c2 = t)} -> wiresUnitary (CCX c1 c2 t) = (3 ** [c1, c2, t])
wiresOfToffoliListControlsThenTarget c1 c2 t = Refl

-- A Fredkin gate lists its control and then both swap targets.
wiresOfFredkinListControlThenTargets : {n : Nat} -> (c, a, b : Fin n) ->
  {auto 0 ab : Not (a = b)} -> {auto 0 ca : Not (c = a)} ->
  {auto 0 cb : Not (c = b)} -> wiresUnitary (CSWAP c a b) = (3 ** [c, a, b])
wiresOfFredkinListControlThenTargets c a b = Refl

-- An empty control list adds no wires to the inner gate.
wiresOfEmptyControlsAreInnerWires :
  wiresUnitary (the (UnitaryGate 1) (Controlled [] [] (X 0))) = (1 ** [0])
wiresOfEmptyControlsAreInnerWires = Refl

-- Generic controls come first, in order, followed by the inner gate's wires.
wiresOfControlledGateListControlsFirst :
  wiresUnitary (the (UnitaryGate 3) (Controlled [0, 1] [One, Zero] (X 2)))
    = (3 ** [0, 1, 2])
wiresOfControlledGateListControlsFirst = Refl

-- Nested controls are flattened, outer controls first.
wiresOfNestedControlledGateListOuterControlsFirst :
  wiresUnitary (the (UnitaryGate 4) (Controlled [0] [Zero] (Controlled [1] [One] (CX 2 3))))
    = (4 ** [0, 1, 2, 3])
wiresOfNestedControlledGateListOuterControlsFirst = Refl

-- Rejects an equation that omits the wires of a nested Controlled gate.
failing "Mismatch between"
  wiresOfNestedControlledGateOmitInnerControls :
    wiresUnitary (the (UnitaryGate 4) (Controlled [0] [Zero] (Controlled [1] [One] (CX 2 3))))
      = (3 ** [0, 2, 3])
  wiresOfNestedControlledGateOmitInnerControls = Refl

-- adjointUnitary maps every gate to its inverse.

-- Self-adjoint single-wire gates are unchanged, for any wire.
adjointOfSelfAdjointSingleWireGates : {n : Nat} -> (q : Fin n) ->
  ( adjointUnitary (Id q) = Id q
  , adjointUnitary (X q) = X q
  , adjointUnitary (Y q) = Y q
  , adjointUnitary (Z q) = Z q
  , adjointUnitary (H q) = H q
  )
adjointOfSelfAdjointSingleWireGates q = (Refl, Refl, Refl, Refl, Refl)

-- Phase-type gates map to their daggered versions and back, for any wire.
adjointOfPhaseGatesSwapsDaggeredVersions : {n : Nat} -> (q : Fin n) ->
  ( adjointUnitary (S q) = SDG q
  , adjointUnitary (SDG q) = S q
  , adjointUnitary (T q) = TDG q
  , adjointUnitary (TDG q) = T q
  , adjointUnitary (SX q) = SXDG q
  , adjointUnitary (SXDG q) = SX q
  )
adjointOfPhaseGatesSwapsDaggeredVersions q = (Refl, Refl, Refl, Refl, Refl, Refl)

-- Rejects an equation claiming that S is self-adjoint.
failing "Mismatch between"
  adjointOfSIsS : adjointUnitary (S {n = 1} 0) = S 0
  adjointOfSIsS = Refl

-- Taking the adjoint twice returns the original phase gate.
adjointOfAdjointOfSIsS : {n : Nat} -> (q : Fin n) ->
  adjointUnitary (adjointUnitary (S q)) = S q
adjointOfAdjointOfSIsS q = Refl

-- Single-wire rotations negate their angle, for any angle and wire. The angle
-- stays symbolic, so no floating-point arithmetic runs during type checking.
adjointOfRotationsNegateAngle : {n : Nat} -> (theta : Radians) -> (q : Fin n) ->
  ( adjointUnitary (RX theta q) = RX (-theta) q
  , adjointUnitary (RY theta q) = RY (-theta) q
  , adjointUnitary (RZ theta q) = RZ (-theta) q
  )
adjointOfRotationsNegateAngle theta q = (Refl, Refl, Refl)

-- Self-adjoint two-wire gates keep their operands in order.
adjointOfSelfAdjointTwoWireGates : {n : Nat} -> (c, t : Fin n) ->
  {auto 0 neq : Not (c = t)} ->
  ( adjointUnitary (CX c t) = CX c t
  , adjointUnitary (CZ c t) = CZ c t
  , adjointUnitary (SWAP c t) = SWAP c t
  )
adjointOfSelfAdjointTwoWireGates c t = (Refl, Refl, Refl)

-- Controlled phase gates map to their daggered versions on the same wires.
adjointOfControlledPhaseGatesSwapsDaggeredVersions : {n : Nat} -> (c, t : Fin n) ->
  {auto 0 neq : Not (c = t)} ->
  ( adjointUnitary (CS c t) = CSDG c t
  , adjointUnitary (CT c t) = CTDG c t
  , adjointUnitary (CSX c t) = CSXDG c t
  )
adjointOfControlledPhaseGatesSwapsDaggeredVersions c t = (Refl, Refl, Refl)

-- Two-wire rotations negate their angle and keep their operands.
adjointOfTwoWireRotationsNegateAngle : {n : Nat} -> (theta : Radians) ->
  (c, t : Fin n) -> {auto 0 neq : Not (c = t)} ->
  ( adjointUnitary (CRZ theta c t) = CRZ (-theta) c t
  , adjointUnitary (RZZ theta c t) = RZZ (-theta) c t
  )
adjointOfTwoWireRotationsNegateAngle theta c t = (Refl, Refl)

-- Three-wire primitives are self-adjoint.
adjointOfThreeWirePrimitives :
  ( adjointUnitary (CCX {n = 3} 0 1 2) = CCX 0 1 2
  , adjointUnitary (CSWAP {n = 3} 0 1 2) = CSWAP 0 1 2
  )
adjointOfThreeWirePrimitives = (Refl, Refl)

-- The adjoint of a Controlled gate keeps its controls and takes the adjoint of
-- the inner gate.
adjointOfControlledGateKeepsControls :
  adjointUnitary (the (UnitaryGate 2) (Controlled [0] [One] (S 1)))
    = Controlled [0] [One] (SDG 1)
adjointOfControlledGateKeepsControls = Refl

-- The adjoint reaches through nested controls to the innermost gate.
adjointOfNestedControlledGateReachesInnermostGate :
  adjointUnitary (the (UnitaryGate 3) (Controlled [0] [Zero] (Controlled [1] [One] (S 2))))
    = Controlled [0] [Zero] (Controlled [1] [One] (SDG 2))
adjointOfNestedControlledGateReachesInnermostGate = Refl

-- Rejects an equation in which the adjoint drops an outer control.
failing "Mismatch between"
  adjointOfControlledGateDropsControls :
    adjointUnitary (the (UnitaryGate 2) (Controlled [0] [One] (S 1))) = SDG 1
  adjointOfControlledGateDropsControls = Refl

-- adjointGate and inv decide which gates and circuits have an inverse.

-- A unitary gate has an adjoint.
adjointOfUnitaryGateExists : {n : Nat} -> (q : Fin n) ->
  adjointGate (UGate (T q)) = Just (UGate (TDG q))
adjointOfUnitaryGateExists q = Refl

-- Measurement, reset and discard have no adjoint.
nonunitaryGatesHaveNoAdjoint : {n : Nat} -> (q : Fin n) ->
  ( adjointGate (Measure q) = Nothing
  , adjointGate (Reset q) = Nothing
  , adjointGate (Discard q) = Nothing
  )
nonunitaryGatesHaveNoAdjoint q = (Refl, Refl, Refl)

-- Rejects an equation claiming that a measurement is its own adjoint.
failing "Mismatch between"
  measurementIsSelfAdjoint : adjointGate (Measure {n = 1} 0) = Just (Measure 0)
  measurementIsSelfAdjoint = Refl

-- The identity circuit is its own inverse.
inverseOfIdentityIsIdentity : inv (Id {n = 1}) = Just Id
inverseOfIdentityIsIdentity = Refl

-- Inverting a sequence reverses its order and takes each gate's adjoint.
inverseReversesSequence : {n : Nat} -> (q : Fin n) ->
  inv (Seq (GateApplication (UGate (S q))) (GateApplication (UGate (T q))))
    = Just (Seq (GateApplication (UGate (TDG q))) (GateApplication (UGate (SDG q))))
inverseReversesSequence q = Refl

-- Rejects an equation in which inverting a sequence keeps its original order.
failing "Mismatch between"
  inverseKeepsSequenceOrder :
    inv (Seq (GateApplication (UGate (S {n = 1} 0))) (GateApplication (UGate (T 0))))
      = Just (Seq (GateApplication (UGate (SDG 0))) (GateApplication (UGate (TDG 0))))
  inverseKeepsSequenceOrder = Refl

-- Inverting a parallel composition inverts each side in place.
inverseOfParallelInvertsEachSide :
  inv (Par (GateApplication (UGate (S {n = 1} 0))) (GateApplication (UGate (T {n = 1} 0))))
    = Just (Par (GateApplication (UGate (SDG {n = 1} 0))) (GateApplication (UGate (TDG {n = 1} 0))))
inverseOfParallelInvertsEachSide = Refl

-- A circuit that measures has no inverse, even when its other gates do.
inverseOfSequenceWithMeasurementIsNothing : {n : Nat} -> (q : Fin n) ->
  inv (Seq (GateApplication (UGate (H q))) (GateApplication (Measure q))) = Nothing
inverseOfSequenceWithMeasurementIsNothing q = Refl

-- Allocating wires cannot be inverted.
inverseOfInitializationIsNothing : inv (Init {n = 1} [Zero]) = Nothing
inverseOfInitializationIsNothing = Refl

-- pow unfolds by recursion on its literal count, for any circuit.

-- Repeating a circuit zero times gives the identity circuit.
powerZeroIsIdentity : {n : Nat} -> (circuit : Circuit n n) -> pow 0 circuit = Id
powerZeroIsIdentity circuit = Refl

-- Repeating a circuit twice gives two copies in sequence.
powerTwoUnfoldsToTwoCopies : {n : Nat} -> (circuit : Circuit n n) ->
  pow 2 circuit = Seq circuit (Seq circuit Id)
powerTwoUnfoldsToTwoCopies circuit = Refl

-- Rejects an equation in which repeating a circuit twice gives one copy.
failing "Mismatch between"
  powerTwoUnfoldsToOneCopy : (circuit : Circuit 1 1) -> pow 2 circuit = Seq circuit Id
  powerTwoUnfoldsToOneCopy circuit = Refl

-- Circuit helpers and the builder append gates in call order.

-- The circuit helpers append each gate after the circuit built so far.
circuitHelpersAppendGatesInOrder : {n : Nat} -> (c, t : Fin n) ->
  {auto 0 neq : Not (c = t)} ->
  DSL.GateHelpers.cnot c t (DSL.GateHelpers.hadamard c Id)
    = Seq (Seq Id (GateApplication (UGate (H c)))) (GateApplication (UGate (CX c t)))
circuitHelpersAppendGatesInOrder c t = Refl

-- Building a builder that does nothing gives the empty circuit.
buildingEmptyBuilderGivesIdentity : build {n = 1} (pure ()) = Id
buildingEmptyBuilderGivesIdentity = Refl

-- Appending a circuit to a builder sequences it after the empty circuit.
buildingAppendedCircuitSequencesIt : {n : Nat} -> (circuit : Circuit n n) ->
  build (append circuit) = Seq Id circuit
buildingAppendedCircuitSequencesIt circuit = Refl

-- The builder records gates in the order its steps run.
builderAppendsGatesInOrder :
  build {n = 2} (do DSL.CircuitBuilder.hadamard 0; DSL.CircuitBuilder.cnot 0 1)
    = Seq (Seq Id (GateApplication (UGate (H 0)))) (GateApplication (UGate (CX 0 1)))
builderAppendsGatesInOrder = Refl

-- Wire literals and inequality decisions reduce to concrete values.

-- A literal reduces to the matching Fin constructors.
literalReducesToFinConstructors : fromLiteral {n = 3} 2 = FS (FS FZ)
literalReducesToFinConstructors = Refl

-- Rejects an equation in which a literal reduces to a smaller index.
failing "Mismatch between"
  literalReducesToSmallerIndex : fromLiteral {n = 3} 2 = FS FZ
  literalReducesToSmallerIndex = Refl

-- Deciding inequality for different wires returns a proof.
inequalityOfDifferentWiresIsDecided : isJust (mkNeq {n = 2} 0 1) = True
inequalityOfDifferentWiresIsDecided = Refl

-- Deciding inequality for a repeated wire returns no proof.
inequalityOfRepeatedWireIsRefuted : mkNeq {n = 2} 1 1 = Nothing
inequalityOfRepeatedWireIsRefuted = Refl
