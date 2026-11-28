module DSL.CircuitBuilderCompileTimeTest

-- Compile-time checks for DSL.CircuitBuilder. Each equation below is proved by
-- Refl, so the compiler must evaluate `build` on a concrete builder while this
-- module type checks. A broken check stops the test package from compiling;
-- nothing runs at test time.
--
-- The module imports DSL.CircuitBuilder but not DSL.GateHelpers, so it also
-- checks that DSL.CircuitBuilder re-exports DSL.GateHelpers, which `build`
-- needs in order to evaluate in other modules.

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
