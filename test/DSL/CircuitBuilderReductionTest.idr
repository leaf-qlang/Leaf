module DSL.CircuitBuilderReductionTest

-- DSL.GateHelpers must be visible through DSL.CircuitBuilder for its public
-- definitions to reduce. Import only the builder and the gate/wire definitions
-- needed to state these equations.
import Data.Fin
import DSL.CircuitBuilder
import DSL.Gates

%default total

buildingEmptyBuilderGivesIdentity : build {n = 1} (pure ()) = EmptyCircuit
buildingEmptyBuilderGivesIdentity = Refl

buildingSingleGateBuilderReduces :
  build {n = 1} (x 0) = Sequence EmptyCircuit (SingleGate (UGate (X 0)))
buildingSingleGateBuilderReduces = Refl

buildingIdentityGateBuilderReduces :
  build {n = 1} (identity 0) = Sequence EmptyCircuit (SingleGate (UGate (Id 0)))
buildingIdentityGateBuilderReduces = Refl

-- Unqualified gate calls must still select the builder operations when their
-- circuit helper counterparts are re-exported.
builderAppendsGatesInOrder :
  build {n = 2} (do hadamard 0; cnot 0 1)
    = Sequence (Sequence EmptyCircuit (SingleGate (UGate (H 0)))) (SingleGate (UGate (CX 0 1)))
builderAppendsGatesInOrder = Refl
