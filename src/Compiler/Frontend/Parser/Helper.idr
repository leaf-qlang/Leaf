module Compiler.Frontend.Parser.Helper

import Text.Bounds
import Text.Parse.Manual

import Compiler.Frontend.Source
import Compiler.Frontend.Token
import Compiler.Frontend.ASTData
import Compiler.Frontend.ASTPhases
import Compiler.Frontend.Parser.Error
import Compiler.Frontend.Syntax.Attribute
import Compiler.Frontend.Syntax.AST
import Compiler.Frontend.Syntax.Common
import Compiler.Frontend.Syntax.Doc
import Compiler.Frontend.Syntax.Literal
import Compiler.Frontend.Syntax.Name
import Compiler.Frontend.Syntax.Operator
import public Compiler.Frontend.Syntax.ParseRules
import Compiler.Frontend.Syntax.Pattern
import Compiler.Frontend.Syntax.Type

%default total

||| Creates a NodeId with current Id, and returns the next Id for the next node.
public export
reserveNodeId : Nat -> (NodeId, Nat)
reserveNodeId currentSurfaceId = (MkNodeId currentSurfaceId 0, S currentSurfaceId)

public export
snocList1 : List1 a -> a -> List1 a
snocList1 (firstElement ::: remainingElements) appendedElement = firstElement ::: (remainingElements ++ [appendedElement])

-- Text.Bounds positions use zero-based lines and columns, while Leaf's
-- SourcePos uses one-based lines and columns. There is also an endpoint
-- mismatch specific to bounds emitted by ILex: they originate as ByteBounds,
-- whose end is the position of the token's last byte, and integer literal preserves
-- that inclusive end. Leaf's SourceSpan instead uses a half-open end position.
--
-- Start and end must consequently be converted differently. The start only
-- changes index base; the end changes index base and advances past the final
-- character. This conversion is for ILex-produced Bounds, not arbitrary
-- Text.Bounds values. Advancing the column is safe as long as tokens do not
-- end with a newline which is actually the case for tokens in Token.idr.

sourceStartPos : Position -> SourcePos
sourceStartPos (P line column) =
  MkSourcePos (S line) (S column)

sourceEndPos : Position -> SourcePos
sourceEndPos (P line column) =
  MkSourcePos (S line) (S (S column))

public export
sourceSpan : {auto sourceFileName : SourceFileName} -> Bounds -> SourceSpan
sourceSpan NoBounds =
  let fileStartPosition = MkSourcePos 1 1
  in MkSourceSpan sourceFileName.fileName fileStartPosition fileStartPosition
sourceSpan (BS startPosition lastCharacterPosition) =
  MkSourceSpan sourceFileName.fileName (sourceStartPos startPosition) (sourceEndPos lastCharacterPosition)

lastItemSpan : SurfaceItem -> List SurfaceItem -> SourceSpan
lastItemSpan currentItem [] =
    currentItem.astInfo.span
lastItemSpan _ (nextItem :: remainingItems) =
    lastItemSpan nextItem remainingItems

public export
sourceFileInfo : {auto sourceFileName : SourceFileName} -> NodeId -> List SurfaceItem -> AstInfo
sourceFileInfo sourceFileNodeId [] =
    let fileStartPosition = MkSourcePos 1 1 in
        MkAstInfo sourceFileNodeId (MkSourceSpan sourceFileName.fileName fileStartPosition fileStartPosition)
sourceFileInfo sourceFileNodeId (firstItem :: remainingItems) =
    MkAstInfo sourceFileNodeId (mergeSpans firstItem.astInfo.span (lastItemSpan firstItem remainingItems))

||| Legal states reached while collecting a top-level item's declaration prefix.
||| Each constructor represents one accepted modifier sequence and retains the
||| visibility that may precede it. `PrefixConstEffect` represents
||| `const <effect> fn`; the reverse order is deliberately not constructible.
||| A lone `const` keeps only its bounds: it may still start a const item, which
||| has no constness node. `const <effect>` can only continue as a function, so
||| its constness node is created then, keeping node IDs in source order.
public export
data ItemPrefixState
  = PrefixOrdinary (Maybe (SurfaceAstNode VisibilityQualifier))
  | PrefixConst (Maybe (SurfaceAstNode VisibilityQualifier)) Bounds
  | PrefixEffect
      (Maybe (SurfaceAstNode VisibilityQualifier))
      (SurfaceAstNode FunctionEffect)
  | PrefixConstEffect
      (Maybe (SurfaceAstNode VisibilityQualifier))
      (SurfaceAstNode FunctionConstness)
      (SurfaceAstNode FunctionEffect)

||| The `const` of a function prefix: absent, seen but not yet given a node,
||| or already located.
public export
data PrefixConstness
  = NoPrefixConstness
  | PendingPrefixConstness Bounds
  | LocatedPrefixConstness (SurfaceAstNode FunctionConstness)

||| Decomposes an accumulated prefix state into its visibility, `const`, and
||| effect components for uniform `fn` dispatch.
public export
prefixComponents :
     ItemPrefixState
  -> ( Maybe (SurfaceAstNode VisibilityQualifier)
     , PrefixConstness
     , Maybe (SurfaceAstNode FunctionEffect))
prefixComponents (PrefixOrdinary visibility) =
  (visibility, NoPrefixConstness, Nothing)
prefixComponents (PrefixConst visibility constBounds) =
  (visibility, PendingPrefixConstness constBounds, Nothing)
prefixComponents (PrefixEffect visibility functionEffect) =
  (visibility, NoPrefixConstness, Just functionEffect)
prefixComponents (PrefixConstEffect visibility constness functionEffect) =
  (visibility, LocatedPrefixConstness constness, Just functionEffect)

public export
record CommaList a where
  constructor MkCommaList
  values : List a
  closeBounds : Bounds

public export
record TypePathTail where
    constructor MkTypePathTail
    pathSegments : List SurfacePathSegment
    lastBounds : Bounds

public export
record ItemPrefix where
  constructor MkItemPrefix
  itemNodeId : NodeId
  declarationStart : Bounds
  attributes : SnocList SurfaceAttribute
  state : ItemPrefixState

public export
failWithCustomError : CustomParseError -> Bounds -> Res isStrict Token tokens CustomParseError a
failWithCustomError customParseError bounds = Fail0 (B (Custom customParseError) bounds)

public export
parameterStartSpan :
     List SurfaceDocComment
  -> Maybe (SurfaceAstNode Mutability)
  -> SurfaceName
  -> SourceSpan
parameterStartSpan (firstDocComment :: _) _ _ = firstDocComment.astInfo.span
parameterStartSpan [] (Just mutability) _ = mutability.astInfo.span
parameterStartSpan [] Nothing parameterName = parameterName.astInfo.span

public export
assignmentOperator : Symbol -> Maybe AssignmentOperator
assignmentOperator SymEq        = Just AssignValue
assignmentOperator SymPlusEq    = Just AssignAdd
assignmentOperator SymMinusEq   = Just AssignSubtract
assignmentOperator SymStarEq    = Just AssignMultiply
assignmentOperator SymSlashEq   = Just AssignDivide
assignmentOperator SymPercentEq = Just AssignRemainder
assignmentOperator SymAndEq     = Just AssignBitAnd
assignmentOperator SymOrEq      = Just AssignBitOr
assignmentOperator SymCaretEq   = Just AssignBitXor
assignmentOperator SymShlEq     = Just AssignShiftLeft
assignmentOperator SymShrEq     = Just AssignShiftRight
assignmentOperator _            = Nothing

public export
unaryOperator : Symbol -> Maybe UnaryOperator
unaryOperator SymMinus = Just UnaryNegate
unaryOperator SymBang  = Just UnaryLogicalNot
unaryOperator SymAmp   = Just (UnaryBorrow SharedBorrow)
unaryOperator _        = Nothing

public export
binaryOperator : Symbol -> Maybe (BinaryOperator, Nat)
binaryOperator SymStar   = Just (BinaryMultiply, 80)
binaryOperator SymSlash  = Just (BinaryDivide, 80)
binaryOperator SymPercent = Just (BinaryRemainder, 80)
binaryOperator SymPlus   = Just (BinaryAdd, 75)
binaryOperator SymMinus  = Just (BinarySubtract, 75)
binaryOperator SymShl    = Just (BinaryShiftLeft, 70)
binaryOperator SymShr    = Just (BinaryShiftRight, 70)
binaryOperator SymAmp    = Just (BinaryBitAnd, 65)
binaryOperator SymCaret  = Just (BinaryBitXor, 60)
binaryOperator SymPipe   = Just (BinaryBitOr, 55)
binaryOperator SymLt     = Just (BinaryLess, 50)
binaryOperator SymLe     = Just (BinaryLessEqual, 50)
binaryOperator SymGt     = Just (BinaryGreater, 50)
binaryOperator SymGe     = Just (BinaryGreaterEqual, 50)
binaryOperator SymEqEq   = Just (BinaryEqual, 50)
binaryOperator SymNotEq  = Just (BinaryNotEqual, 50)
binaryOperator SymAndAnd = Just (BinaryLogicalAnd, 45)
binaryOperator SymOrOr   = Just (BinaryLogicalOr, 40)
binaryOperator _         = Nothing

public export
rangeOperator : Symbol -> Maybe RangeOperator
rangeOperator SymDotDot   = Just RangeExclusive
rangeOperator SymDotDotEq = Just RangeInclusive
rangeOperator _           = Nothing

public export
initializerMarker : Symbol -> Maybe InitializerMarker
initializerMarker SymEq       = Just InitializerEquals
initializerMarker SymWalrusEq = Just InitializerAutoUncompute
initializerMarker _           = Nothing

public export
functionEffectFromKeyword : Keyword -> Maybe FunctionEffect
functionEffectFromKeyword KwClassical  = Just EffectClassical
functionEffectFromKeyword KwUncompsafe = Just EffectUncompsafe
functionEffectFromKeyword KwUnitary    = Just EffectUnitary
functionEffectFromKeyword KwIsometry   = Just EffectIsometry
functionEffectFromKeyword KwCoisometry = Just EffectCoisometry
functionEffectFromKeyword KwGeneral    = Just EffectGeneral
functionEffectFromKeyword _            = Nothing

public export
storageQualifierFromKeyword : Keyword -> Maybe QuantumStorageQualifier
storageQualifierFromKeyword KwLinear  = Just QualifierLinear
storageQualifierFromKeyword KwAffine  = Just QualifierAffine
storageQualifierFromKeyword KwScratch = Just QualifierScratch
storageQualifierFromKeyword _         = Nothing

public export
storageQualifierFromToken : Token -> Maybe QuantumStorageQualifier
storageQualifierFromToken (TokKw keyword) = storageQualifierFromKeyword keyword
storageQualifierFromToken _               = Nothing

||| The quantum usage qualifier a `linear` or `affine` token denotes.
public export
quantumUsageQualifierFromToken : Token -> Maybe QuantumUsageQualifier
quantumUsageQualifierFromToken token =
  case storageQualifierFromToken token of
    Just storageQualifier => storageQuantumUsage storageQualifier
    Nothing => Nothing

public export
unsupportedTopLevelItem : Keyword -> Maybe CustomParseError
unsupportedTopLevelItem KwMod =
  Just (UnsupportedFeature "Modules are not yet supported.")
unsupportedTopLevelItem KwUse =
  Just (UnsupportedFeature "Use statements are not yet supported.")
unsupportedTopLevelItem KwEnum =
  Just (UnsupportedFeature "Enums are not yet supported.")
unsupportedTopLevelItem KwQenum =
  Just (UnsupportedFeature "Qenums are not yet supported.")
unsupportedTopLevelItem KwImpl =
  Just (UnsupportedFeature "Impl blocks and structs are not yet supported.")
unsupportedTopLevelItem KwStruct =
  Just (UnsupportedFeature "Structs are not yet supported.")
unsupportedTopLevelItem _ = Nothing

public export
makeLiteralExpression : SourceFileName => LiteralNode -> Bounds -> Nat -> (SurfaceExpr, Nat)
makeLiteralExpression literalNode bounds nodeId =
  let (expressionNodeId, afterExpressionNodeId) = reserveNodeId nodeId
      (literalNodeId, nextNodeId) = reserveNodeId afterExpressionNodeId
      literal = surfaceAstNode (MkAstInfo literalNodeId (sourceSpan bounds))
                               literalNode
      literalExpression = surfaceAstNode (MkAstInfo expressionNodeId (sourceSpan bounds))
                                         (ExprLiteral literal)
   in (literalExpression, nextNodeId)

public export
makeName : SourceFileName => String -> Bounds -> Nat -> (SurfaceName, Nat)
makeName nameText bounds nodeId =
  let (nameNodeId, nextNodeId) = reserveNodeId nodeId
      surfaceName = surfaceAstNode (MkAstInfo nameNodeId (sourceSpan bounds)) (MkNameNode nameText)
   in (surfaceName, nextNodeId)

public export
makeNameExpression : SourceFileName => String -> Bounds -> Nat -> (SurfaceExpr, Nat)
makeNameExpression nameText bounds nodeId =
  let (expressionNodeId, afterExpressionNodeId) = reserveNodeId nodeId
      (surfaceName, nextNodeId) = makeName nameText bounds afterExpressionNodeId
      nameExpression = surfaceAstNode (MkAstInfo expressionNodeId (sourceSpan bounds))
                                      (ExprName surfaceName)
   in (nameExpression, nextNodeId)

public export
makeBuiltinExpression : SourceFileName => Builtin -> Bounds -> Nat -> (SurfaceExpr, Nat)
makeBuiltinExpression builtin bounds nodeId =
  let (expressionNodeId, nextNodeId) = reserveNodeId nodeId
      builtinExpression = surfaceAstNode (MkAstInfo expressionNodeId (sourceSpan bounds))
                                         (ExprBuiltin builtin)
   in (builtinExpression, nextNodeId)


public export
assignmentTargetFromExpression : SurfaceExpr -> Maybe (AssignmentTargetNode SurfaceAstPhase)
assignmentTargetFromExpression (MkAstNode _ _ expressionNode) =
  case expressionNode of
    ExprName targetName => Just (AssignTargetName targetName)
    ExprIndex targetObject index => Just (AssignTargetIndex targetObject index)
    ExprField targetObject fieldName => Just (AssignTargetField targetObject fieldName)
    ExprTupleIndex targetObject tupleIndexRawText => Just (AssignTargetTupleIndex targetObject tupleIndexRawText)
    _ => Nothing

public export
isComparisonOperator : BinaryOperator -> Bool
isComparisonOperator BinaryEqual = True
isComparisonOperator BinaryNotEqual = True
isComparisonOperator BinaryGreater = True
isComparisonOperator BinaryGreaterEqual = True
isComparisonOperator BinaryLess = True
isComparisonOperator BinaryLessEqual = True
isComparisonOperator _ = False

public export
isUnparenthesizedComparison : SurfaceExpr -> Bool
isUnparenthesizedComparison (MkAstNode _ _ (ExprBinary binaryOperator _ _)) =
  isComparisonOperator binaryOperator.nodeValue
isUnparenthesizedComparison _ = False

public export
nextTokenSatisfies :
  (Token -> Bool) -> List (Bounded Token) -> Bool
nextTokenSatisfies predicate ((B token _) :: _) = predicate token
nextTokenSatisfies _ [] = False

||| Valid quantum-storage qualifiers collected in source order. Quantum usage and
||| scratch occupy separate slots so duplicates and conflicting quantum usage
||| qualifiers can be rejected consistently by every grammar that uses them.
public export
record StorageQualifiers where
  constructor MkStorageQualifiers
  quantumUsage : Maybe (SurfaceAstNode QuantumStorageQualifier)
  scratch : Maybe (SurfaceAstNode QuantumStorageQualifier)
  ordered : SnocList (SurfaceAstNode QuantumStorageQualifier)

public export
emptyStorageQualifiers : StorageQualifiers
emptyStorageQualifiers = MkStorageQualifiers Nothing Nothing [<]

||| Diagnostic for a qualifier written after one occupying the same slot.
secondQualifierMessage : (Eq qualifier, Show qualifier) => qualifier -> qualifier -> String
secondQualifierMessage firstQualifier secondQualifier =
  if firstQualifier == secondQualifier
    then "Duplicate `" ++ show secondQualifier ++ "` storage qualifier."
    else "Cannot combine `" ++ show firstQualifier ++ "` and `" ++ show secondQualifier ++ "` storage qualifiers."

||| Adds one located qualifier or returns the diagnostic for an invalid combination.
public export
addStorageQualifier :
     StorageQualifiers
  -> SurfaceAstNode QuantumStorageQualifier
  -> Either String StorageQualifiers
addStorageQualifier collectedQualifiers newQualifier =
  case newQualifier.nodeValue of
    QualifierScratch =>
      case collectedQualifiers.scratch of
        Just existingQualifier => Left (secondQualifierMessage existingQualifier.nodeValue newQualifier.nodeValue)
        Nothing => Right $ MkStorageQualifiers collectedQualifiers.quantumUsage
          (Just newQualifier) (collectedQualifiers.ordered :< newQualifier)
    QualifierLinear => addQuantumUsageQualifier
    QualifierAffine => addQuantumUsageQualifier
  where
    addQuantumUsageQualifier : Either String StorageQualifiers
    addQuantumUsageQualifier =
      case collectedQualifiers.quantumUsage of
        Nothing => Right $ MkStorageQualifiers (Just newQualifier)
          collectedQualifiers.scratch (collectedQualifiers.ordered :< newQualifier)
        Just existingQualifier => Left (secondQualifierMessage existingQualifier.nodeValue newQualifier.nodeValue)

||| `scratch` describes cleanup at the end of a binding's scope, so it is only
||| valid on `let` bindings, never inside a type.
public export
scratchInTypeMessage : String
scratchInTypeMessage = "The `scratch` qualifier is only allowed on `let` bindings, not in types: write `let scratch q: qbit = ...`."

||| The quantum usage qualifier a storage keyword denotes inside a type, or the
||| diagnostic for `scratch`.
public export
typeQuantumUsageQualifier : QuantumStorageQualifier -> Either String QuantumUsageQualifier
typeQuantumUsageQualifier storageQualifier =
  maybe (Left scratchInTypeMessage) Right (storageQuantumUsage storageQualifier)

||| Diagnostic for a second storage keyword following a quantum usage qualifier
||| inside a type: a type holds exactly one quantum usage qualifier.
secondTypeQualifierMessage : QuantumUsageQualifier -> QuantumStorageQualifier -> String
secondTypeQualifierMessage firstQualifier secondQualifier =
  either id (secondQualifierMessage firstQualifier) (typeQuantumUsageQualifier secondQualifier)

||| Diagnostic for a token other than `qbit` following a quantum usage qualifier
||| inside a type: a qualifier applies to a single qbit, so a qbit array or
||| tuple qualifies each of its qbits instead. A slice is only ever borrowed,
||| and nothing behind a reference is qualified, so no slice suggestion.
public export
qualifiedNonQbitMessage : QuantumUsageQualifier -> Token -> String
qualifiedNonQbitMessage writtenQualifier token =
  case storageQualifierFromToken token of
    Just secondQualifier => secondTypeQualifierMessage writtenQualifier secondQualifier
    Nothing =>
      case token of
        TokSym SymLBracket =>
          qualifierDescription ++ " cannot qualify an array or slice: qualify the qbits of an array instead, e.g. `[" ++
          qualifiedQbit ++ "; 2]`."
        TokSym SymLParen =>
          qualifierDescription ++ " cannot qualify a parenthesized type or tuple: qualify each qbit inside it instead, e.g. `" ++
          qualifiedQbit ++ "` or `(" ++ qualifiedQbit ++ ", " ++ qualifiedQbit ++ ")`."
        _ => qualifierDescription ++ " can only qualify `qbit`, not " ++ describeToken token ++ "."
  where
    qualifierDescription : String
    qualifierDescription = "The `" ++ show writtenQualifier ++ "` qualifier"

    qualifiedQbit : String
    qualifiedQbit = show writtenQualifier ++ " qbit"

||| Diagnostic for a quantum usage qualifier written directly after `&` or `&mut`.
public export
qualifierBehindReferenceMessage : QuantumUsageQualifier -> String
qualifierBehindReferenceMessage writtenQualifier =
  "The `" ++ show writtenQualifier ++ "` qualifier cannot be written behind a reference: " ++
  "a reference borrows its referent without owning it, so remove the qualifier."
