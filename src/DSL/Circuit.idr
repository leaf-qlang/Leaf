module DSL.Circuit

import Data.Fin

import DSL.Adjoint
import DSL.Core
import DSL.Gates

%default total

-- Quantum circuits with n inputs and m outputs
public export
data Circuit : Nat -> Nat -> Type where
  -- Identity circuit: n wires and no gates
  Identity : {0 n : Nat} -> Circuit n n

  -- A single primitive gate
  SingleGate : {0 n : Nat} -> Gate n -> Circuit n n

  -- Sequential composition
  Sequence : {0 n : Nat} ->
             {0 m : Nat} ->
             {0 k : Nat} ->
             Circuit n m -> Circuit m k -> Circuit n k

  -- n1 and m1 are kept at run time
  Parallel : {n1 : Nat} ->
             {m1 : Nat} ->
             {0 n2 : Nat} ->
             {0 m2 : Nat} ->
             Circuit n1 m1 ->
             Circuit n2 m2 ->
             Circuit (n1 + n2) (m1 + m2)

  -- Add one fresh qubit per initial state
  AllocateQubits : {0 n : Nat} -> (states : List QState) -> Circuit n (n + length states)

  -- The output width is n, so no later gate can refer to the discarded qubit.
  DiscardQubit : {0 n : Nat} -> (q : Fin (S n)) -> Circuit (S n) n

-- Inverse of a circuit, if it exists
public export
inv : Circuit n m -> Maybe (Circuit m n)

inv Identity = Just Identity

inv (SingleGate g) =
  case adjointGate g of
    Just g' => Just (SingleGate g')
    Nothing => Nothing    -- non-unitary gate, no inverse

inv (Sequence c1 c2) = do
  c1' <- inv c1
  c2' <- inv c2
  pure (Sequence c2' c1')

inv (Parallel c1 c2) = do
  c1' <- inv c1
  c2' <- inv c2
  pure (Parallel c1' c2')

inv (AllocateQubits _) = Nothing

inv (DiscardQubit _) = Nothing


-- Repeated application of a circuit
public export
pow : (k : Nat) -> Circuit n n -> Circuit n n
pow Z     _ = Identity
pow (S k) c = Sequence c (pow k c)
