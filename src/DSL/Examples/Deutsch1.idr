module DSL.Examples.Deutsch1

import Data.Fin
import DSL.Circuit
import DSL.GateHelpers

%default total

-- Let proof search establish that wire 0 differs from wire 1.
%hint
zeroNotSuccessor : {n : Nat} -> {q : Fin n} -> Not (FZ = FS q)
zeroNotSuccessor Refl impossible

public export
constantOracle : Circuit 2 2
constantOracle = emptyCircuit

public export
balancedOracle : Circuit 2 2
balancedOracle = cnot 0 1 emptyCircuit

public export
deutsch : Circuit 2 2 -> Circuit 0 2
deutsch oracle =
  let prepared = hadamard 1 (hadamard 0 emptyCircuit)
      queried = Seq prepared oracle
      result = measure 0 (hadamard 0 queried)
  in Seq (Init [Zero, One]) result

||| The measurement of wire 0 is deterministically 0.
public export
constantExample : Circuit 0 2
constantExample = deutsch constantOracle

||| The measurement of wire 0 is deterministically 1.
public export
balancedExample : Circuit 0 2
balancedExample = deutsch balancedOracle
