module DSL.Circuit

import Data.Fin
import public Data.List.Elem

import public DSL.Adjoint
import public DSL.Classical
import DSL.Core
import DSL.Gates

%default total

-- Quantum circuits with n inputs and m outputs
public export
data Circuit : (ctx : ClassicalContext) -> (n, m : Nat) -> (t : ClassicalType) -> Type where

  -- Empty circuit: n wires and no gates
  EmptyCircuit : {0 ctx : ClassicalContext} -> {0 n : Nat} ->
                 Circuit ctx n n UnitType

  -- A single primitive gate
  SingleGate : {0 ctx : ClassicalContext} -> {0 n : Nat} -> Gate n ->
               Circuit ctx n n UnitType

  -- Sequential composition
  Sequence : {0 ctx : ClassicalContext} ->
             {0 l, m, n : Nat} ->
             {0 t : ClassicalType} ->
             Circuit ctx l m UnitType ->
             Circuit ctx m n t ->
             Circuit ctx l n t

  -- n1 and m1 are kept at run time
  Parallel : {0 ctx : ClassicalContext} ->
             {n1, m1 : Nat} ->
             {0 n2, m2 : Nat} ->
             Circuit ctx n1 m1 UnitType ->
             Circuit ctx n2 m2 UnitType ->
             Circuit ctx (n1 + n2) (m1 + m2) UnitType

  -- Add one fresh qubit per initial state
  AllocateQubits : {0 ctx : ClassicalContext} -> {0 n : Nat} -> (states : List QState) ->
                   Circuit ctx n (n + length states) UnitType

  -- The output width is n, so no later gate can refer to the discarded qubit.
  DiscardQubit : {0 ctx : ClassicalContext} -> {0 n : Nat} -> (q : Fin (S n)) ->
                 Circuit ctx (S n) n UnitType

  -- Measurement outcome is the circuit's result
  Measure : {0 ctx : ClassicalContext} -> {0 n : Nat} -> (q : Fin n) ->
            Circuit ctx n n BitType

   -- The result of the first circuit is the innermost variable of the second.
  Bind : {0 ctx : ClassicalContext} ->
         {0 n, m, k : Nat} ->
         {s : ClassicalType} ->
         {0 t : ClassicalType} ->
         Circuit ctx n m s -> Circuit (s :: ctx) m k t -> Circuit ctx n k t

  -- Returns a classical variable in scope as the circuit's result.
  Return : {0 ctx : ClassicalContext} ->
           {0 n : Nat} ->
           {0 t : ClassicalType} ->
           Elem t ctx ->
           Circuit ctx n n t

-- Inverse of a circuit, if it exists. Only circuits without a classical
-- result can be inverted, so a circuit ending in a measurement is ruled out by
-- its type.
public export
inv : Circuit ctx n m UnitType -> Maybe (Circuit ctx m n UnitType)

inv EmptyCircuit = Just EmptyCircuit

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

-- An empty allocation adds no wire, so its inverse is the empty circuit.
inv {n} (AllocateQubits []) = Just (rewrite plusZeroRightNeutral n in EmptyCircuit)
inv (AllocateQubits (_ :: _)) = Nothing

inv (DiscardQubit _) = Nothing

-- Every Bind is rejected. A useful Bind binds a measurement outcome, which has
-- no inverse; the others, such as binding the unit result of a gate, add nothing.
inv (Bind _ _) = Nothing

-- Returning a variable has no quantum effect.
inv (Return _) = Just EmptyCircuit

-- Repeated application of a circuit
public export
pow : (k : Nat) -> Circuit ctx n n UnitType -> Circuit ctx n n UnitType
pow Z     _ = EmptyCircuit
pow (S k) c = Sequence c (pow k c)
