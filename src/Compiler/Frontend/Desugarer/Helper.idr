module Compiler.Frontend.Desugarer.Helper

import Data.List1
import Data.Maybe
import Compiler.Frontend.ASTData
import Compiler.Frontend.ASTPhases
import Compiler.Frontend.Source
import Compiler.Frontend.Syntax.AST
import Compiler.Frontend.Syntax.Common
import Compiler.Frontend.Syntax.Name
import Compiler.Frontend.Syntax.Operator
import Compiler.Frontend.Syntax.Type
import Compiler.Frontend.Token

%default total

export
mapWithId :
  {a : Type} ->
  {b : Type} ->
  (fun : Nat -> a -> (b, Nat)) ->
  (startingId : Nat) ->
  (values : List a) ->
  (List b, Nat)
mapWithId fun fstId [] = ([], fstId)
mapWithId fun fstId (x :: xs) =
  let (result, sndId) = fun fstId x
      (remaining, finalId) = mapWithId fun sndId xs
  in (result :: remaining, finalId)

export
incrementedAstInfo : AstInfo -> Nat -> AstInfo
incrementedAstInfo astInfo inc =
  MkAstInfo (MkNodeId astInfo.nodeId.surfaceId (astInfo.nodeId.desugarId + inc)) astInfo.span

||| A quantum usage qualifier to insert into a type, and where it came from.
public export
record QuantumUsageInsertion where
  constructor MkQuantumUsageInsertion
  quantumUsage : QuantumUsageQualifier
  provenance   : NodeProvenance
  keywordSpan  : Maybe SourceSpan  -- the `let` keyword it was moved from; Nothing for the default

defaultLinearInsertion : QuantumUsageInsertion
defaultLinearInsertion =
  MkQuantumUsageInsertion QuantumUsageLinear DesugaredDefaultQbitQualifier Nothing

-- The wrapper and qualifier take the next two desugar ids of the wrapped type
-- node. The wrapper spans the wrapped type; a qualifier moved from a `let`
-- spans the keyword it was written as, so diagnostics point at that keyword
-- (and so lies outside its wrapper's span), while a default one spans the type.
wrapInQuantumUsage : QuantumUsageInsertion -> CanonicalTy -> CanonicalTy
wrapInQuantumUsage insertion qualifiedType@(MkAstNode typeInfo _ _) =
  let qualifierInfo =
        { span := fromMaybe typeInfo.span insertion.keywordSpan } (incrementedAstInfo typeInfo 2)
  in canonicalAstNode (incrementedAstInfo typeInfo 1) insertion.provenance $
       TyQualified
         (canonicalAstNode qualifierInfo insertion.provenance insertion.quantumUsage)
         qualifiedType

-- Qualifies every owned position of a type that has no quantum usage qualifier
-- yet (see "Owned positions" in Compiler.Frontend.Syntax.Type).
qualifyOwnedQbits : QuantumUsageInsertion -> CanonicalTy -> CanonicalTy
qualifyOwnedQbits insertion = mapOwnedPositions qualify
  where
    qualify : CanonicalTy -> CanonicalTy
    qualify position =
      case positionQualifier position of
        Just _ => position
        Nothing => wrapInQuantumUsage insertion position

||| Adds the default `linear` to every unqualified owned position of a type.
export
defaultQbitQuantumUsage : CanonicalTy -> CanonicalTy
defaultQbitQuantumUsage = qualifyOwnedQbits defaultLinearInsertion

||| Moves a `let` binding's `linear`/`affine` into the owned positions of its
||| annotation, or adds the default `linear` when none was written. Each moved
||| qualifier keeps the span of the keyword written on the `let`. The qualifier
||| stays on the `let` when there is no annotation, or when the annotation has
||| no unqualified owned position (typechecking reports that case). `scratch`
||| always stays on the `let`.
export
moveLetQuantumUsageIntoType :
     List (CanonicalAstNode QuantumStorageQualifier)
  -> Maybe CanonicalTy
  -> (List (CanonicalAstNode QuantumStorageQualifier), Maybe CanonicalTy)
moveLetQuantumUsageIntoType qualifiers Nothing = (qualifiers, Nothing)
moveLetQuantumUsageIntoType qualifiers (Just annotation) =
  case mapMaybe writtenQuantumUsage qualifiers of
    [] => (qualifiers, Just (defaultQbitQuantumUsage annotation))
    insertion :: _ =>
      if any (isNothing . positionQualifier) (ownedPositions annotation)
        then
          ( filter (\qualifier => qualifier.nodeValue == QualifierScratch) qualifiers
          , Just (qualifyOwnedQbits insertion annotation)
          )
        else (qualifiers, Just annotation)
  where
    writtenQuantumUsage : CanonicalAstNode QuantumStorageQualifier -> Maybe QuantumUsageInsertion
    writtenQuantumUsage (MkAstNode keywordInfo _ keyword) =
      map (\quantumUsage => MkQuantumUsageInsertion quantumUsage DesugaredMovedQbitQualifier (Just keywordInfo.span))
          (storageQuantumUsage keyword)

export
assignmentOperatorToBinary : AssignmentOperator -> Maybe BinaryOperator
assignmentOperatorToBinary AssignValue = Nothing
assignmentOperatorToBinary AssignAdd = Just BinaryAdd
assignmentOperatorToBinary AssignSubtract = Just BinarySubtract
assignmentOperatorToBinary AssignMultiply = Just BinaryMultiply
assignmentOperatorToBinary AssignDivide = Just BinaryDivide
assignmentOperatorToBinary AssignRemainder = Just BinaryRemainder
assignmentOperatorToBinary AssignBitAnd = Just BinaryBitAnd
assignmentOperatorToBinary AssignBitOr = Just BinaryBitOr
assignmentOperatorToBinary AssignBitXor = Just BinaryBitXor
assignmentOperatorToBinary AssignShiftLeft = Just BinaryShiftLeft
assignmentOperatorToBinary AssignShiftRight = Just BinaryShiftRight
