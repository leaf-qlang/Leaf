module DSL.CircuitInverseReductionTest

-- This module does not import DSL.Adjoint, so it checks that importing
-- DSL.Circuit is enough for inv to reduce while type checking: inv calls
-- adjointGate, which Idris unfolds only when DSL.Adjoint is visible.
import Data.Fin
import DSL.Circuit
import DSL.Core
import DSL.Gates

%default total

-- The inverse of a gate is its adjoint.
inverseOfSGateIsSDaggerGate : inv (SingleGate (UGate (S {n = 1} 0))) = Just (SingleGate (UGate (SDG 0)))
inverseOfSGateIsSDaggerGate = Refl

-- Inverting a concrete rotation evaluates its negated angle as well.
inverseOfLiteralRotationReduces :
  inv (SingleGate (UGate (RZ {n = 1} (MkRadians 0.25) 0)))
    = Just (SingleGate (UGate (RZ (MkRadians (-0.25)) 0)))
inverseOfLiteralRotationReduces = Refl

-- The inverse of "allocate nothing, then H" is "H, then the empty circuit".
inverseOfEmptyAllocationBeforeHadamard :
  inv (Sequence (AllocateQubits {n = 1} []) (SingleGate (UGate (H 0))))
    = Just (Sequence (SingleGate (UGate (H 0))) EmptyCircuit)
inverseOfEmptyAllocationBeforeHadamard = Refl
