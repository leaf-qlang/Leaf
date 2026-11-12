module DSL.Circuit

import DSL.Adjoint
import DSL.Gates

%default total

public export
data State = Zero | One

-- Quantum circuits with n inputs and m outputs
public export
data Circuit : Nat -> Nat -> Type where
  -- Identity / “empty” circuit
  Id : {0 n : Nat} -> Circuit n n

  -- A single primitive gate
  GateApplication : {0 n : Nat} -> Gate n -> Circuit n n

  -- Sequential composition
  Seq : {0 n : Nat} ->
        {0 m : Nat} ->
        {0 k : Nat} ->
        Circuit n m -> Circuit m k -> Circuit n k

  -- n1 and m1 are kept at run time
  Par : {n1 : Nat} ->
        {m1 : Nat} ->
        {0 n2 : Nat} ->
        {0 m2 : Nat} ->
        Circuit n1 m1 ->
        Circuit n2 m2 ->
        Circuit (n1 + n2) (m1 + m2)

  -- Add one qubit per initial state
  Init : {0 n : Nat} -> (states : List State) -> Circuit n (n + length states)


-- Inverse of a circuit, if it exists
public export
inv : Circuit n m -> Maybe (Circuit m n)

inv Id = Just Id

inv (GateApplication g) =
  case adjointGate g of
    Just g' => Just (GateApplication g')
    Nothing => Nothing    -- non-unitary gate, no inverse

inv (Seq c1 c2) = do
  c1' <- inv c1
  c2' <- inv c2
  pure (Seq c2' c1')

inv (Par c1 c2) = do
  c1' <- inv c1
  c2' <- inv c2
  pure (Par c1' c2')

inv (Init _) = Nothing


-- Repeated application of a circuit
public export
pow : (k : Nat) -> Circuit n n -> Circuit n n
pow Z     _ = Id
pow (S k) c = Seq c (pow k c)
