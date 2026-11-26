module DSL.Control

import Data.Vect
import Data.Fin
import Data.So
-- Clients must see the All constructors to build Disjoint proofs by search.
import public Data.Vect.Quantifiers
-- Clients must be able to reduce the decision used by the public proof hint.
import public Decidable.Decidable
import public Decidable.Equality

%default total

-- Decide inequality only after the wire indices are known. Structural hints
-- such as Not (FZ = FS q) can otherwise force an unresolved index to FZ while
-- Idris is still elaborating the gate's arguments.
%hint
public export
wireIndicesAreDifferent : {left, right : Fin n} ->
  {auto 0 different : So (isNo (decEq left right))} -> Not (left = right)
wireIndicesAreDifferent {left} {right} {different} with (decEq left right)
  wireIndicesAreDifferent {different = Oh} | Yes _ impossible
  wireIndicesAreDifferent | No inequalityProof = inequalityProof

public export
data NotElem : (x : a) -> Vect n a -> Type where
  NotHere  : NotElem x []
  NotThere : NotElem x xs -> {auto 0 neq : Not (x = y)} -> NotElem x (y :: xs)

public export
data AllDistinct : Vect n a -> Type where
  ADNil  : AllDistinct []
  ADCons : {xs : Vect n a} ->
           NotElem x xs ->
           AllDistinct xs ->
           AllDistinct (x :: xs)

public export
Disjoint : {a : Type} -> Vect m a -> Vect n a -> Type
Disjoint xs ys = Data.Vect.Quantifiers.All.All (\x => NotElem x ys) xs
