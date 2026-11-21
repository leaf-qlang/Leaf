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

||| Maps over a list with a function that also takes the next free desugar id
||| offset and returns the one after what it used, threading it through the list.
export
mapThreadingDesugarIdOffset :
  {a : Type} ->
  {b : Type} ->
  (desugarWithOffset : Nat -> a -> (b, Nat)) ->
  (startingOffset : Nat) ->
  (inputs : List a) ->
  (List b, Nat)
mapThreadingDesugarIdOffset desugarWithOffset currentOffset [] = ([], currentOffset)
mapThreadingDesugarIdOffset desugarWithOffset currentOffset (firstInput :: remainingInputs) =
  let (firstOutput, nextOffset) = desugarWithOffset currentOffset firstInput
      (remainingOutputs, finalOffset) = mapThreadingDesugarIdOffset desugarWithOffset nextOffset remainingInputs
  in (firstOutput :: remainingOutputs, finalOffset)

||| The same node position with its desugar id raised by `desugarIdOffset`: the
||| identity of a node generated from the given one.
export
astInfoWithDesugarIdOffset : AstInfo -> (desugarIdOffset : Nat) -> AstInfo
astInfoWithDesugarIdOffset astInfo desugarIdOffset =
  MkAstInfo (MkNodeId astInfo.nodeId.surfaceId (astInfo.nodeId.desugarId + desugarIdOffset)) astInfo.span

||| A quantum usage qualifier to insert into a type, and where it came from.
public export
record QuantumUsageInsertion where
  constructor MkQuantumUsageInsertion
  quantumUsage : QuantumUsageQualifier
  provenance   : NodeProvenance
  keywordSpan  : Maybe SourceSpan  -- the qualifier keyword written on the `let` it was moved from; Nothing for the default

defaultLinearInsertion : QuantumUsageInsertion
defaultLinearInsertion =
  MkQuantumUsageInsertion QuantumUsageLinear DesugaredDefaultQbitQualifier Nothing

-- The wrapper and qualifier take the next two desugar ids of the wrapped type
-- node. The wrapper spans the wrapped type; a qualifier moved from a `let`
-- spans the keyword it was written as, so diagnostics point at that keyword
-- (and so lies outside its wrapper's span), while a default one spans the type.
wrapInQuantumUsage : QuantumUsageInsertion -> CanonicalTy -> CanonicalTy
wrapInQuantumUsage quantumUsageInsertion qualifiedType@(MkAstNode typeInfo _ _) =
  let qualifierInfo =
        { span := fromMaybe typeInfo.span quantumUsageInsertion.keywordSpan } (astInfoWithDesugarIdOffset typeInfo 2)
  in canonicalAstNode (astInfoWithDesugarIdOffset typeInfo 1) quantumUsageInsertion.provenance $
       TyQualified
         (canonicalAstNode qualifierInfo quantumUsageInsertion.provenance quantumUsageInsertion.quantumUsage)
         qualifiedType

-- Qualifies every owned position of a type that has no quantum usage qualifier
-- yet (see "Owned positions" in Compiler.Frontend.Syntax.Type).
qualifyUnqualifiedOwnedQbits : QuantumUsageInsertion -> CanonicalTy -> CanonicalTy
qualifyUnqualifiedOwnedQbits quantumUsageInsertion = mapOwnedPositions qualifyIfUnqualified
  where
    qualifyIfUnqualified : CanonicalTy -> CanonicalTy
    qualifyIfUnqualified ownedPosition =
      case positionQualifier ownedPosition of
        Just _ => ownedPosition
        Nothing => wrapInQuantumUsage quantumUsageInsertion ownedPosition

||| Adds the default `linear` to every unqualified owned position of a type.
export
addDefaultLinearToUnqualifiedQbits : CanonicalTy -> CanonicalTy
addDefaultLinearToUnqualifiedQbits = qualifyUnqualifiedOwnedQbits defaultLinearInsertion

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
moveLetQuantumUsageIntoType letQualifiers Nothing = (letQualifiers, Nothing)
moveLetQuantumUsageIntoType letQualifiers (Just typeAnnotation) =
  case mapMaybe quantumUsageInsertionFromKeyword letQualifiers of
    [] => (letQualifiers, Just (addDefaultLinearToUnqualifiedQbits typeAnnotation))
    writtenInsertion :: _ =>
      if any (isNothing . positionQualifier) (ownedPositions typeAnnotation)
        then
          ( filter (\letQualifier => letQualifier.nodeValue == QualifierScratch) letQualifiers
          , Just (qualifyUnqualifiedOwnedQbits writtenInsertion typeAnnotation)
          )
        else (letQualifiers, Just typeAnnotation)
  where
    -- A written `linear`/`affine` as an insertion carrying its keyword's span; `scratch` gives none.
    quantumUsageInsertionFromKeyword : CanonicalAstNode QuantumStorageQualifier -> Maybe QuantumUsageInsertion
    quantumUsageInsertionFromKeyword (MkAstNode keywordInfo _ storageQualifier) =
      map (\quantumUsage => MkQuantumUsageInsertion quantumUsage DesugaredMovedQbitQualifier (Just keywordInfo.span))
          (storageQuantumUsage storageQualifier)

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
