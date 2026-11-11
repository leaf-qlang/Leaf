module DSL.Examples.Deutsch2

import Data.Fin
import DSL.CircuitBuilder

%default total

-- Let proof search establish that wire 0 differs from wire 1.
%hint
zeroNotSuccessor : {n : Nat} -> {q : Fin n} -> Not (FZ = FS q)
zeroNotSuccessor Refl impossible

public export
constantOracle : Circuit 2 2
constantOracle = build (pure ())

public export
balancedOracle : Circuit 2 2
balancedOracle = build $ do
  cnot 0 1

public export
deutsch : Circuit 2 2 -> Circuit 0 2
deutsch oracle = Seq (Init [Zero, One]) $ build $ do
  hadamard 0
  hadamard 1
  append oracle
  hadamard 0
  measure 0

||| The measurement of wire 0 is deterministically 0.
public export
constantExample : Circuit 0 2
constantExample = deutsch constantOracle

||| The measurement of wire 0 is deterministically 1.
public export
balancedExample : Circuit 0 2
balancedExample = deutsch balancedOracle
