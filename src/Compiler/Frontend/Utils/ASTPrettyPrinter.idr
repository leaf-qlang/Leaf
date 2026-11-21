module Compiler.Frontend.Utils.ASTPrettyPrinter

import Data.List1
import Data.String
import Data.Maybe
import Compiler.Frontend.Utils.SourceText

import Compiler.Frontend.Token
import Compiler.Frontend.ASTPhases
import Compiler.Frontend.Syntax.AST
import Compiler.Frontend.Syntax.Attribute
import Compiler.Frontend.Syntax.Common
import Compiler.Frontend.Syntax.Contract
import Compiler.Frontend.Syntax.Doc
import Compiler.Frontend.Syntax.Literal
import Compiler.Frontend.Syntax.Name
import Compiler.Frontend.Syntax.Operator
import Compiler.Frontend.Syntax.ParseRules
import Compiler.Frontend.Syntax.Pattern
import Compiler.Frontend.Syntax.Type

%hide Prelude.Ops.infixl.(<+>)
%default total

--------------------------------------------------------------------------------
-- Pretty-printing the AST back to Leaf source.
--------------------------------------------------------------------------------
-- STYLES
--   PrettyLax     parentheses only where the output would otherwise re-parse
--                 differently (minimal parenthesization).
--   PrettyStrict  additionally every OPTIONAL parenthesis, around each unary,
--                 binary, cast and range expression, except one ending in a
--                 `return` or `break` without a value (see `needsParens`).
--
-- Both styles print the MANDATORY parentheses the output needs to re-parse to
-- the same tree:
--   * operator precedence and associativity (see "Precedence");
--   * a block-like expression that starts a longer expression in statement
--     position, where the parser would end the statement after it
--     (see "Statement position");
--   * the head of if/while/for/match/qmatch/smatch when the `{` that follows
--     would be read as part of it, as by an open range (see "Head position");
--   * a qif condition with those hazards, or ending in a qif without qelse,
--     which would take the then-branch (see "Quantum if branches");
--   * an integer base or nested tuple index before `.<digits>`;
--   * an expression ending in an open range `a..` before a keyword (`then`,
--     `selse`, `=>`): a range ends without an upper bound only before a
--     delimiter (see "Right edge").
-- A qif branch that parentheses cannot protect is printed as a block instead
-- (see "Quantum if branches").
--
-- PHASES: every printer is generic over `phase`. Only names, member names and
-- paths differ between phases; the `PhasePretty` interface renders them as
-- their written text, dropping any resolved SymbolId.
--
-- RENDERING: internal helpers build lazy SourceText documents. The public
-- String printers consume the complete document; the debug printer consumes
-- only a bounded prefix, without constructing full strings for its subtrees.
--
-- TOTALITY: Idris's size-change checker only credits constructor patterns,
-- so printers that are genuinely mutually recursive destructure records in
-- the pattern head and walk lists with hand-written recursive helpers rather
-- than `map`. Three groups are: patterns, types (tuples, function types), and
-- items (inline module bodies). Everything else reaches itself only through
-- `showExprAtDoc`, whose single `assert_total` in `wrapExprDoc` breaks the
-- cycle, so it can walk lists with the generic `mapDocs`.
--------------------------------------------------------------------------------

public export
data PrettyStyle
  = PrettyLax
  | PrettyStrict

isPrettyStrict : PrettyStyle -> Bool
isPrettyStrict PrettyStrict = True
isPrettyStrict PrettyLax    = False

--------------------------------------------------------------------------------
-- Text helpers
--------------------------------------------------------------------------------

-- Delay both each child document and the remainder of the collection. A
-- normal `map render children` evaluates later children before a preview can
-- stop, even when concatenation inside each document is lazy.
data SourceDocs = NoDocs | MoreDocs (Lazy SourceText) (Lazy SourceDocs)

mapDocs : (a -> SourceText) -> List a -> SourceDocs
mapDocs _ [] = NoDocs
mapDocs render (firstItem :: remainingItems) = MoreDocs (render firstItem) (mapDocs render remainingItems)

appendDocs : SourceDocs -> Lazy SourceDocs -> SourceDocs
appendDocs NoDocs suffix = suffix
appendDocs (MoreDocs firstItem remainingItems) suffix = MoreDocs firstItem (appendDocs remainingItems suffix)

joinRest : SourceText -> SourceDocs -> SourceText
joinRest _ NoDocs = ""
joinRest separator (MoreDocs firstItem remainingItems) = separator <+> firstItem <+> joinRest separator remainingItems

joinWith : SourceText -> SourceDocs -> SourceText
joinWith _ NoDocs = ""
joinWith separator (MoreDocs firstItem remainingItems) = firstItem <+> joinRest separator remainingItems

concatDocs : (a -> SourceText) -> List a -> SourceText
concatDocs _ [] = ""
concatDocs render (firstItem :: remainingItems) = render firstItem <+> concatDocs render remainingItems

commaList : SourceDocs -> SourceText
commaList = joinWith ", "

parens : Lazy SourceText -> SourceText
parens enclosedText = "(" <+> enclosedText <+> ")"

brackets : Lazy SourceText -> SourceText
brackets enclosedText = "[" <+> enclosedText <+> "]"

braces : Lazy SourceText -> SourceText
braces enclosedText = "{ " <+> (if sourceIsEmpty enclosedText then "}" else enclosedText <+> " }")

argumentList : Lazy SourceDocs -> SourceText
argumentList argumentDocs = parens (commaList argumentDocs)

optionalText : SourceText -> (a -> SourceText) -> Maybe a -> SourceText
optionalText _ _ Nothing = ""
optionalText leading render (Just presentValue) = leading <+> render presentValue

modifier : Show a => Maybe a -> SourceText
modifier = optionalText "" (\presentValue => text (show presentValue) <+> " ")

locatedModifier : Show a => Maybe (AstNode phase a) -> SourceText
locatedModifier = modifier . map nodeValue

-- A one-character prefix operator, spaced from an operand that starts with
-- the same character: `& &x` must not lex as `&&x`, and `- -x` would read
-- like a decrement.
prefixOperator : Char -> Lazy SourceText -> SourceText
prefixOperator operatorCharacter operandText = text (singleton operatorCharacter) <+> (if sourceStartsWith operatorCharacter operandText then " " else "") <+> operandText

showBorrowPrefixed : BorrowKind -> Lazy SourceText -> SourceText
showBorrowPrefixed SharedBorrow operandText = prefixOperator '&' operandText
showBorrowPrefixed MutableBorrow operandText = "&mut " <+> operandText

showTupleLike : SourceDocs -> SourceText
showTupleLike NoDocs = "()"
showTupleLike (MoreDocs onlyElement NoDocs) = "(" <+> onlyElement <+> ",)"
showTupleLike elementDocs = argumentList elementDocs

--------------------------------------------------------------------------------
-- Names and paths
--------------------------------------------------------------------------------

showPathSegmentDoc : PathSegment phase -> SourceText
showPathSegmentDoc (MkAstNode _ _ (PathSegmentName spelling)) = text spelling
showPathSegmentDoc (MkAstNode _ _ PathSegmentSelf)        = "self"

prettyNameNode : NameNode -> String
prettyNameNode (MkNameNode nameText) = nameText

prettyResolvedNameNode : ResolvedNameNode -> String
prettyResolvedNameNode (MkResolvedNameNode nameText _) = nameText

prettyPathNodeDoc : PathNode phase -> SourceText
prettyPathNodeDoc (MkPathNode firstSegment remainingSegments) = joinWith "::" (mapDocs showPathSegmentDoc (firstSegment :: remainingSegments))

prettyResolvedPathNodeDoc : ResolvedPathNode -> SourceText
prettyResolvedPathNodeDoc (MkResolvedPathNode firstSegment remainingSegments _) = joinWith "::" (mapDocs text (firstSegment :: remainingSegments))

-- The three payloads that differ between phases, rendered as written.
public export
interface PhasePretty phase where
  prettyName : NameFor phase -> String
  prettyMemberName : MemberNameFor phase -> String
  -- Keep segments lazy for previews; full payloads explicitly render them.
  prettyPathDoc : PathFor phase -> SourceText
  prettyPath : PathFor phase -> String
  prettyPath pathPayload = renderSource (prettyPathDoc pathPayload)

public export
PhasePretty SurfaceAstPhase where
  prettyName = prettyNameNode
  prettyMemberName = prettyNameNode
  prettyPathDoc = prettyPathNodeDoc

public export
PhasePretty CanonicalAstPhase where
  prettyName = prettyNameNode
  prettyMemberName = prettyNameNode
  prettyPathDoc = prettyPathNodeDoc

public export
PhasePretty ResolvedAstPhase where
  prettyName = prettyResolvedNameNode
  prettyMemberName = prettyNameNode
  prettyPathDoc = prettyResolvedPathNodeDoc

public export
PhasePretty TypedAstPhase where
  prettyName = prettyResolvedNameNode
  prettyMemberName = prettyResolvedNameNode
  prettyPathDoc = prettyResolvedPathNodeDoc

showNameDoc : PhasePretty phase => Name phase -> SourceText
showNameDoc (MkAstNode _ _ namePayload) = text (prettyName namePayload)

showMemberNameDoc : PhasePretty phase => MemberName phase -> SourceText
showMemberNameDoc (MkAstNode _ _ namePayload) = text (prettyMemberName namePayload)

showPathDoc : PhasePretty phase => Path phase -> SourceText
showPathDoc (MkAstNode _ _ pathPayload) = prettyPathDoc pathPayload

-- Attribute names, import aliases and function-type parameter names keep their
-- plain spelling at every phase.
showPlainNameDoc : AstNode phase NameNode -> SourceText
showPlainNameDoc (MkAstNode _ _ (MkNameNode spelling)) = text spelling

--------------------------------------------------------------------------------
-- Leaves: literals, doc comments, attributes, modifiers, Pauli strings
--------------------------------------------------------------------------------

-- Every literal payload is its raw source spelling or has exactly one spelling.
showLiteralDoc : Literal phase -> SourceText
showLiteralDoc (MkAstNode _ _ literalNode) =
  case literalNode of
    LiteralIntegerRaw rawSpelling     => text rawSpelling
    LiteralFloatRaw rawSpelling       => text rawSpelling
    LiteralStringRaw rawSpelling      => text rawSpelling
    LiteralByteRaw rawSpelling        => text rawSpelling
    LiteralByteStringRaw rawSpelling  => text rawSpelling
    LiteralBasisStringRaw rawSpelling => text rawSpelling
    LiteralBoolean booleanValue       => if booleanValue then "true" else "false"
    LiteralUnit                       => "()"
    LiteralQuantumState basisState    => text (show basisState)

-- The raw spelling of a doc comment includes its delimiters.
showDocCommentDoc : DocComment phase -> SourceText
showDocCommentDoc (MkAstNode _ _ (MkDocCommentNode _ _ rawText)) = text rawText

-- Doc comments, each ending its own line so that a line doc cannot swallow
-- the code or closing brace that follows.
docsPrefix : List (DocComment phase) -> SourceText
docsPrefix = concatDocs (\docComment => showDocCommentDoc docComment <+> "\n")

showAttributeDoc : Attribute phase -> SourceText
showAttributeDoc (MkAstNode _ _ (MkAttributeNode attributeName attributeArguments)) =
  "#[" <+> showPlainNameDoc attributeName <+>
    optionalText "" (\attributeArguments => argumentList (mapDocs showArgumentDoc attributeArguments)) attributeArguments <+> "]"
  where
    showArgumentDoc : AttributeArgument phase -> SourceText
    showArgumentDoc (MkAstNode _ _ (AttributeArgumentStringLit rawSpelling)) = text rawSpelling

attributesPrefix : List (Attribute phase) -> SourceText
attributesPrefix = concatDocs (\attribute => showAttributeDoc attribute <+> "\n")

showQualifiersPrefixDoc : List (AstNode phase QuantumStorageQualifier) -> SourceText
showQualifiersPrefixDoc = concatDocs (\qualifier => text (show qualifier.nodeValue) <+> " ")

showOnBasisDoc : Maybe (AstNode phase String) -> SourceText
showOnBasisDoc = optionalText ".on" (\onBasis => parens (text onBasis.nodeValue))

showPauliStringDoc : PauliString phase -> SourceText
showPauliStringDoc (MkAstNode _ _ (MkPauliStringNode pauliOperators)) = concatDocs (text . show) (forget pauliOperators)

showSignedPauliTermDoc : SignedPauliTerm phase -> SourceText
showSignedPauliTermDoc (MkAstNode _ _ (MkSignedPauliTermNode sign pauliString)) =
  (case sign of StabilizerPlus => "+"; StabilizerMinus => "-") <+> showPauliStringDoc pauliString

--------------------------------------------------------------------------------
-- Patterns (recursive group)
--------------------------------------------------------------------------------

mutual
  showPatternDoc : PhasePretty phase => Pattern phase -> SourceText
  showPatternDoc (MkAstNode _ _ patternNode) = showPatternNodeDoc patternNode

  showPatternNodeDoc : PhasePretty phase => PatternNode phase -> SourceText
  showPatternNodeDoc patternNode =
    case patternNode of
      PatternWildcard                                   => "_"
      PatternName mutability binderName                 => modifier mutability <+> showNameDoc binderName
      PatternPath patternPath                           => showPathDoc patternPath
      PatternLiteral literal                            => showLiteralDoc literal
      PatternParenthesized innerPattern                 => parens (showPatternDoc innerPattern)
      PatternTuple (firstPattern ::: remainingPatterns) => showTupleLike (MoreDocs (showPatternDoc firstPattern) (showPatternListDoc remainingPatterns))
      PatternArray elementPatterns                      => brackets (commaList (showPatternListDoc elementPatterns))
      PatternStruct patternPath fieldPatterns           =>
        showPathDoc patternPath <+> " " <+> braces (commaList (showStructPatternFieldsDoc fieldPatterns))
      PatternEnumTuple patternPath elementPatterns => showPathDoc patternPath <+> argumentList (showPatternListDoc elementPatterns)

  showPatternListDoc : PhasePretty phase => List (Pattern phase) -> SourceDocs
  showPatternListDoc []                    = NoDocs
  showPatternListDoc (firstPattern :: remainingPatterns) = MoreDocs (showPatternDoc firstPattern) (showPatternListDoc remainingPatterns)

  showStructPatternFieldsDoc : PhasePretty phase => List (StructPatternField phase) -> SourceDocs
  showStructPatternFieldsDoc [] = NoDocs
  showStructPatternFieldsDoc (MkAstNode _ _ fieldNode :: remainingFields) =
    MoreDocs (case fieldNode of
       StructPatternFieldShorthand mutability fieldName   => modifier mutability <+> showNameDoc fieldName
       StructPatternFieldExplicit fieldName nestedPattern => showNameDoc fieldName <+> ": " <+> showPatternDoc nestedPattern)
    (showStructPatternFieldsDoc remainingFields)

showQuantumMatchPatternDoc : PhasePretty phase => QuantumMatchPattern phase -> SourceText
showQuantumMatchPatternDoc (MkAstNode _ _ patternNode) =
  case patternNode of
    QuantumPatternBasisStringRaw rawSpelling           => text rawSpelling
    QuantumPatternIntegerRaw rawSpelling               => text rawSpelling
    QuantumPatternWildcard                             => "_"
    QuantumPatternQenumVariant variantPath binderNames => showPathDoc variantPath <+> argumentList (mapDocs showNameDoc binderNames)

--------------------------------------------------------------------------------
-- Precedence
--------------------------------------------------------------------------------
-- Higher binds tighter; the binary levels match the parser's table.
-- An expression is parenthesized when its own precedence is below what its
-- position requires, and in strict style whenever it is operator class.
-- Forms ending in an open expression (return, break, sif, and qif with an
-- expression branch) have the lowest precedence because they absorb
-- whatever follows them, so they need parentheses only where something that
-- could continue them does follow: `a + return b`, but `(return b) * c`.
--------------------------------------------------------------------------------

precAtomic, precPostfix, precUnary, precCast, precMul, precAdd, precShift : Nat
precAtomic  = 110
precPostfix = 100
precUnary   = 90
precCast    = 85
precMul     = 80
precAdd     = 75
precShift   = 70

precBitAnd, precBitXor, precBitOr, precCompare, precLogicalAnd, precLogicalOr, precRange, precLowest : Nat
precBitAnd     = 65
precBitXor     = 60
precBitOr      = 55
precCompare    = 50
precLogicalAnd = 45
precLogicalOr  = 40
precRange      = 30
precLowest     = 0

binaryOperatorPrecedence : BinaryOperator -> Nat
binaryOperatorPrecedence binaryOperator =
  case binaryOperator of
    BinaryMultiply     => precMul
    BinaryDivide       => precMul
    BinaryRemainder    => precMul
    BinaryAdd          => precAdd
    BinarySubtract     => precAdd
    BinaryShiftLeft    => precShift
    BinaryShiftRight   => precShift
    BinaryBitAnd       => precBitAnd
    BinaryBitXor       => precBitXor
    BinaryBitOr        => precBitOr
    BinaryEqual        => precCompare
    BinaryNotEqual     => precCompare
    BinaryGreater      => precCompare
    BinaryGreaterEqual => precCompare
    BinaryLess         => precCompare
    BinaryLessEqual    => precCompare
    BinaryLogicalAnd   => precLogicalAnd
    BinaryLogicalOr    => precLogicalOr

-- The right operand always needs a tighter level, which makes binary operators
-- left-associative. Comparisons are non-associative, so their left operand
-- needs one too.
binaryLeftPrecedence : BinaryOperator -> Nat
binaryLeftPrecedence binaryOperator =
  let operatorPrecedence = binaryOperatorPrecedence binaryOperator in
  if operatorPrecedence == precCompare then S operatorPrecedence else operatorPrecedence

binaryRightPrecedence : BinaryOperator -> Nat
binaryRightPrecedence binaryOperator = S (binaryOperatorPrecedence binaryOperator)

isBlockBranch : QuantumBranchNode phase -> Bool
isBlockBranch (QuantumBranchBlock _)      = True
isBlockBranch (QuantumBranchExpression _) = False

exprOwnPrecedence : ExpressionNode phase -> Nat
exprOwnPrecedence expressionNode =
  case expressionNode of
    -- Postfix forms
    ExprCall _ _         => precPostfix
    ExprMethodCall _ _ _ => precPostfix
    ExprField _ _        => precPostfix
    ExprTupleIndex _ _   => precPostfix
    ExprIndex _ _        => precPostfix
    -- Operators
    ExprUnary _ _                                 => precUnary
    ExprCast _ _                                  => precCast
    ExprBinary (MkAstNode _ _ binaryOperator) _ _ => binaryOperatorPrecedence binaryOperator
    ExprRange _ _ _                               => precRange
    -- Forms ending in an expression, which would absorb a following operator.
    -- A qif ends with its last branch: the then-branch is followed by any
    -- `qelse`, so a block else-branch closes the qif.
    ExprBreak _    => precLowest
    ExprReturn _   => precLowest
    ExprSIf _      => precLowest
    ExprQIf (MkQuantumIfNode _ thenBranch elseBranch) =>
      if maybe (isBlockBranch thenBranch) isBlockBranch elseBranch
        then precAtomic
        else precLowest
    -- Self-delimited forms: atoms, brackets, and forms ending in their own `}`
    ExprLiteral _         => precAtomic
    ExprName _            => precAtomic
    ExprPath _            => precAtomic
    ExprBuiltin _         => precAtomic
    ExprSelf _            => precAtomic
    ExprContinue          => precAtomic
    ExprParenthesized _   => precAtomic
    ExprTuple _           => precAtomic
    ExprArray _           => precAtomic
    ExprRepeatedArray _ _ => precAtomic
    ExprStructLiteral _ _ => precAtomic
    ExprBlock _           => precAtomic
    ExprIf _              => precAtomic
    ExprMatch _           => precAtomic
    ExprQMatch _          => precAtomic
    ExprSMatch _          => precAtomic
    ExprLoop _            => precAtomic
    ExprWhile _ _         => precAtomic
    ExprFor _ _ _         => precAtomic
    ExprCtrl _            => precAtomic
    ExprAdjoint _         => precAtomic

-- A digit after the dot can merge with an integer base or the previous tuple
-- index into a float token: `(1).0` must not become `1.0`, and `(t.0).1`
-- must not become `t.0.1`. A float base is safe: `1.5.0` lexes as `1.5`, `.`,
-- `0`.
tupleIndexBasePrecedence : ExpressionNode phase -> Nat
tupleIndexBasePrecedence (ExprLiteral (MkAstNode _ _ (LiteralIntegerRaw _))) = S precAtomic
tupleIndexBasePrecedence (ExprTupleIndex _ _) = S precPostfix
tupleIndexBasePrecedence _ = precPostfix

-- `(object.field)(args)` calls the value stored in a field. Without the
-- parentheses the parser constructs a method call, `object.field(args)`.
callCalleePrecedence : ExpressionNode phase -> Nat
callCalleePrecedence (ExprField _ _) = S precPostfix
callCalleePrecedence _ = precPostfix

isOperatorClassExpr : ExpressionNode phase -> Bool
isOperatorClassExpr expressionNode =
  case expressionNode of
    ExprUnary _ _    => True
    ExprCast _ _     => True
    ExprBinary _ _ _ => True
    ExprRange _ _ _  => True
    _                => False

--------------------------------------------------------------------------------
-- Edges: the child a rendering begins or ends with
--------------------------------------------------------------------------------
-- What precedes a rendering can join its first child, and what follows it its
-- last. The checks below walk these edges, one child deeper per step, which
-- `assert_smaller` records for the totality checker.
--------------------------------------------------------------------------------

-- The child an expression's rendering begins with, when the rest of the
-- rendering follows it, and the precedence that child is printed at.
leftEdge : ExpressionNode phase -> Maybe (Nat, Expr phase)
leftEdge expressionNode =
  case expressionNode of
    ExprCall callee _                                             => Just (callCalleePrecedence callee.nodeValue, callee)
    ExprMethodCall receiver _ _                                   => Just (precPostfix, receiver)
    ExprField receiverObject _                                    => Just (precPostfix, receiverObject)
    ExprIndex receiverObject _                                    => Just (precPostfix, receiverObject)
    ExprTupleIndex receiverObject@(MkAstNode _ _ tupleBaseNode) _ => Just (tupleIndexBasePrecedence tupleBaseNode, receiverObject)
    ExprCast operand _                                            => Just (precCast, operand)
    ExprBinary (MkAstNode _ _ binaryOperator) leftOperand _       => Just (binaryLeftPrecedence binaryOperator, leftOperand)
    ExprRange rangeStart _ _                                      => map (\startChild => (S precRange, startChild)) rangeStart
    _                                                             => Nothing

-- `value` with `child` in place of the child its rendering begins with.
withLeftEdge : ExpressionNode phase -> Expr phase -> ExpressionNode phase
withLeftEdge expressionNode child =
  case expressionNode of
    ExprCall _ arguments                          => ExprCall child arguments
    ExprMethodCall _ methodName arguments         => ExprMethodCall child methodName arguments
    ExprField _ fieldName                         => ExprField child fieldName
    ExprIndex _ index                             => ExprIndex child index
    ExprTupleIndex _ index                        => ExprTupleIndex child index
    ExprCast _ castTargetType                     => ExprCast child castTargetType
    ExprBinary binaryOperatorNode _ rightOperand  => ExprBinary binaryOperatorNode child rightOperand
    ExprRange (Just _) rangeOperatorNode rangeEnd => ExprRange (Just child) rangeOperatorNode rangeEnd
    _                                             => expressionNode

-- The child an expression's rendering ends with, and the precedence that
-- child is printed at.
rightEdge : ExpressionNode phase -> Maybe (Nat, Expr phase)
rightEdge expressionNode =
  case expressionNode of
    ExprUnary _ operand                                      => Just (precUnary, operand)
    ExprBinary (MkAstNode _ _ binaryOperator) _ rightOperand => Just (binaryRightPrecedence binaryOperator, rightOperand)
    ExprRange _ _ rangeEnd                                   => map (\endChild => (S precRange, endChild)) rangeEnd
    ExprReturn returnValue                                   => map (\endChild => (precLowest, endChild)) returnValue
    ExprBreak breakValue                                     => map (\endChild => (precLowest, endChild)) breakValue
    ExprSIf (MkStateIfNode _ _ elseExpr)                     => Just (precLowest, elseExpr)
    ExprQIf (MkQuantumIfNode _ (QuantumBranchExpression thenExpr) Nothing) => Just (precLowest, thenExpr)
    ExprQIf (MkQuantumIfNode _ _ (Just (QuantumBranchExpression elseExpr))) => Just (precLowest, elseExpr)
    _                                    => Nothing

-- A `return` or `break` without a value can only be followed by `;`, `,` or
-- `}` (`isOptionalValueTerminator`): before any other token the parser reads
-- a value, so `(a || return)` does not parse.
isValuelessExit : ExpressionNode phase -> Bool
isValuelessExit (ExprReturn Nothing) = True
isValuelessExit (ExprBreak Nothing)  = True
isValuelessExit _                    = False

-- Whether the right edge ends in a valueless exit at any depth. It decides on
-- parentheses itself, so unlike `endsWith` it cannot ask which are printed.
endsInValuelessExit : ExpressionNode phase -> Bool
endsInValuelessExit expressionNode =
  isValuelessExit expressionNode ||
  case rightEdge expressionNode of
    Nothing         => False
    Just (_, child) => endsInValuelessExit (assert_smaller expressionNode child.nodeValue)

-- A qif without qelse takes a following `qelse`.
isQIfWithoutElse : ExpressionNode phase -> Bool
isQIfWithoutElse (ExprQIf (MkQuantumIfNode _ _ Nothing)) = True
isQIfWithoutElse _                                       = False

-- An open range `a..` reads the next token as its upper bound unless it is a
-- delimiter (`isOpenRangeTerminator`).
isRangeWithoutEnd : ExpressionNode phase -> Bool
isRangeWithoutEnd (ExprRange _ _ Nothing) = True
isRangeWithoutEnd _                       = False

--------------------------------------------------------------------------------
-- Parentheses
--------------------------------------------------------------------------------

-- Whether a token that could continue an expression comes after it: an
-- operator, a postfix, `as`, `..`, or the `{` after a head. Delimiters and
-- keywords such as `,`, `;`, `)`, `then` and `qelse` cannot continue it.
data Follows = Followed | Delimited

isFollowed : Follows -> Bool
isFollowed Followed  = True
isFollowed Delimited = False

-- Forms of the lowest precedence end in an open expression, which absorbs
-- whatever follows them.
absorbsFollowing : ExpressionNode phase -> Bool
absorbsFollowing expressionNode = exprOwnPrecedence expressionNode == precLowest

-- Whether an expression is parenthesized in a position requiring `outerReq`
-- where `follows` holds. Strict style's optional parentheses are left out
-- where they cannot parse.
needsParens : PrettyStyle -> Nat -> Follows -> ExpressionNode phase -> Bool
needsParens style outerReq follows expressionNode =
  (exprOwnPrecedence expressionNode < outerReq && (isFollowed follows || not (absorbsFollowing expressionNode))) ||
  (isPrettyStrict style && isOperatorClassExpr expressionNode && not (endsInValuelessExit expressionNode))

-- Whether the rendering of an expression, printed in a position requiring
-- `outerReq` where `follows` holds, ends with a node for which `isLast` holds.
-- The right edge inherits `follows`; a parenthesized node ends the walk.
endsWith : (ExpressionNode phase -> Bool) -> PrettyStyle -> Nat -> Follows -> Expr phase -> Bool
endsWith isLast style outerReq follows expression@(MkAstNode _ _ expressionNode) =
  not (needsParens style outerReq follows expressionNode) &&
  (isLast expressionNode ||
   case rightEdge expressionNode of
     Nothing                   => False
     Just (requirement, child) => endsWith isLast style requirement follows (assert_smaller expression child))

--------------------------------------------------------------------------------
-- Statement position
--------------------------------------------------------------------------------
-- At the start of a statement, a block's final expression or a match arm
-- body, the parser ends the statement after a leading block-like expression
-- (`isBlockLikeExpression`): `{ 1 } + 2;` is a block statement followed by
-- `+2`. A block-like expression that starts a longer expression there is
-- wrapped in an ExprParenthesized node before printing, at the first position
-- on the left edge whose rendering would begin with it.
--------------------------------------------------------------------------------

-- Walks the left edge of an expression printed in a position requiring
-- `outerReq`; a node printed in parentheses already starts with `(`. Below the
-- root every node is followed; at the root the flag never changes the result.
parenthesizeLeadingBlock : PrettyStyle -> Nat -> Expr phase -> Expr phase
parenthesizeLeadingBlock style outerReq expression@(MkAstNode expressionInfo metadata expressionNode) =
  if needsParens style outerReq Followed expressionNode then expression else
  case leftEdge expressionNode of
    Just (requirement, child) =>
      MkAstNode expressionInfo metadata
        (withLeftEdge expressionNode (parenthesizeLeadingBlock style requirement (assert_smaller expression child)))
    Nothing =>
      if isBlockLikeExpression expressionNode then MkAstNode expressionInfo metadata (ExprParenthesized expression) else expression

-- A block-like expression on its own is the statement and stays bare.
statementPositionExpr : PrettyStyle -> Expr phase -> Expr phase
statementPositionExpr style expression@(MkAstNode _ _ expressionNode) =
  if isBlockLikeExpression expressionNode then expression else parenthesizeLeadingBlock style precLowest expression

--------------------------------------------------------------------------------
-- Head position: the expression directly before the `{` of a control construct
--------------------------------------------------------------------------------
-- As in Rust, a head does not allow struct literals, so a name directly before
-- the `{` ends it, but a struct literal in it must be parenthesized. A nested
-- expression the parser starts afresh, such as a `return` value, allows them
-- again, and there an uppercase name (`readsAsStructLiteralName`) or a path
-- before `{` would start one. An open range or a bare `return`/`break` takes
-- the block as its operand: `{` is neither an `isOpenRangeTerminator` nor an
-- `isOptionalValueTerminator`. A head with such a shape outside brackets it
-- prints itself is printed in parentheses.
--------------------------------------------------------------------------------

-- Whether the child on an expression's right edge is parsed as a new
-- expression, which allows struct literals again: a `return` or `break`
-- value, or a `sif` or `qif` branch.
startsNewExpression : ExpressionNode phase -> Bool
startsNewExpression expressionNode =
  case expressionNode of
    ExprReturn _ => True
    ExprBreak _  => True
    ExprSIf _    => True
    ExprQIf _    => True
    _            => False

-- Whether an expression's own shape would take the `{` after a head, when its
-- rendering ends the head, or break the head wherever struct literals are not
-- allowed. Paths do not parse yet, so one before `{` is always guarded.
ownHeadHazard :
  PhasePretty phase => (endsHead : Bool) -> (structLiteralsAllowed : Bool) -> ExpressionNode phase -> Bool
ownHeadHazard endsHead structLiteralsAllowed expressionNode =
  case expressionNode of
    ExprName valueName    => endsHead && structLiteralsAllowed && readsAsStructLiteralName (prettyName valueName.nodeValue)
    ExprPath _            => endsHead
    ExprStructLiteral _ _ => not structLiteralsAllowed
    _                     => endsHead && (isRangeWithoutEnd expressionNode || isValuelessExit expressionNode)

-- Whether a head has a hazard outside brackets it prints itself. `endsHead`
-- holds for the part whose rendering ends the head. A head is followed by its
-- `{`, and so is every node in it.
headHazard :
     PhasePretty phase
  => PrettyStyle -> Nat -> (endsHead : Bool) -> (structLiteralsAllowed : Bool) -> Expr phase -> Bool
headHazard style outerReq endsHead structLiteralsAllowed expression@(MkAstNode _ _ expressionNode) =
  not (needsParens style outerReq Followed expressionNode) &&
  (ownHeadHazard endsHead structLiteralsAllowed expressionNode ||
   inEdge False structLiteralsAllowed (leftEdge expressionNode) ||
   inEdge endsHead (structLiteralsAllowed || startsNewExpression expressionNode) (rightEdge expressionNode))
  where
    inEdge : Bool -> Bool -> Maybe (Nat, Expr phase) -> Bool
    inEdge _ _ Nothing = False
    inEdge childEndsHead childAllows (Just (requirement, child)) =
      headHazard style requirement childEndsHead childAllows (assert_smaller expression child)

-- Whether a head must be printed in parentheses: it ends where the head does,
-- and does not allow struct literals.
headNeedsParens : PhasePretty phase => PrettyStyle -> Expr phase -> Bool
headNeedsParens style = headHazard style precLowest True False

--------------------------------------------------------------------------------
-- Quantum if branches
--------------------------------------------------------------------------------
-- The parser reads the longest condition it can, so a then-branch starting
-- with a token that continues an expression would join the condition:
-- `qif a -b` is the condition `a - b`, and `qif a (b)` the call `a(b)`.
-- And `qelse` attaches to the nearest qif without one, so a then-branch
-- ending in such a qif would take the outer `qelse`, and one ending in an open
-- range would read `qelse` as its bound. After `qelse`, a leading
-- `{` is read as a block branch: `qelse { 2 } + 3` adds 3 to the whole qif.
-- Parentheses cannot fix the first case, so an expression branch at risk is
-- printed as a block, which has the same value: `qif a { -b }`,
-- `qif a { qif b x } qelse y`, `qif a x qelse { ({ 2 }) + 3 }`.
--------------------------------------------------------------------------------

-- First characters of the tokens that can continue an expression: `(`, `[`,
-- a block's `{`, `-`, `&`, and the `.` of `..`.
continuesExpression : Char -> Bool
continuesExpression firstCharacter = firstCharacter `elem` ['(', '[', '{', '-', '&', '.']

-- Whether a then-branch, given its rendering's first character, would join
-- the condition or, when `qelse` follows, take it or read it as the bound of
-- an open range. Before `qelse` the branch is delimited: a keyword cannot
-- continue it.
thenBranchAtRisk : PrettyStyle -> (hasElse : Bool) -> Expr phase -> Maybe Char -> Bool
thenBranchAtRisk style hasElse branchExpression firstCharacter =
  maybe False continuesExpression firstCharacter ||
  (hasElse && endsWith (\expressionNode => isQIfWithoutElse expressionNode || isRangeWithoutEnd expressionNode) style precLowest Delimited branchExpression)

--------------------------------------------------------------------------------
-- The recursive core: types, expressions, blocks and statements
--------------------------------------------------------------------------------
-- Declared up front so the printers below can be defined in dependency order:
-- types and expressions embed blocks, blocks embed expressions and types.
--------------------------------------------------------------------------------

||| Renders an expression in a position requiring precedence `outerReq` where
||| `follows` holds, parenthesizing it when it binds more loosely.
showExprAtDoc : PhasePretty phase => PrettyStyle -> Nat -> Follows -> Expr phase -> SourceText

showBlockDoc : PhasePretty phase => PrettyStyle -> Block phase -> SourceText

||| Renders an expression in a delimited position: no precedence requirement,
||| and nothing that could continue it follows.
public export
showExprDoc : PhasePretty phase => PrettyStyle -> Expr phase -> SourceText
showExprDoc style = showExprAtDoc style precLowest Delimited

-- A whole expression where `follows` holds, in parentheses when `hazard` says
-- that what follows would join it.
showGuardedExprDoc : PhasePretty phase => PrettyStyle -> Follows -> (hazard : Bool) -> Expr phase -> SourceText
showGuardedExprDoc style follows hazard expression =
  if hazard then parens (showExprDoc style expression) else showExprAtDoc style precLowest follows expression

-- The head of if/while/for/match/qmatch/smatch, directly before a `{`. A qif
-- condition adds its own rule (see `showQuantumConditionDoc`).
showHeadExprDoc : PhasePretty phase => PrettyStyle -> Expr phase -> SourceText
showHeadExprDoc style expression = showGuardedExprDoc style Followed (headNeedsParens style expression) expression

-- An expression starting a statement, a block's final expression or an arm body.
public export
showStatementPositionExprDoc : PhasePretty phase => PrettyStyle -> Expr phase -> SourceText
showStatementPositionExprDoc style expression = showExprDoc style (statementPositionExpr style expression)

-- An expression followed by a keyword (`then`, `selse`, `=>`), which cannot
-- continue it, except as the upper bound of an open range.
showBeforeKeywordDoc : PhasePretty phase => PrettyStyle -> Expr phase -> SourceText
showBeforeKeywordDoc style expression =
  showGuardedExprDoc style Delimited (endsWith isRangeWithoutEnd style precLowest Delimited expression) expression

------------------------------------------------------------------------------
-- Types (recursive group)
------------------------------------------------------------------------------

mutual
  showTyNodeDoc : PhasePretty phase => PrettyStyle -> TyNode phase (Expr phase) -> SourceText
  showTyNodeDoc style typeNode =
    case typeNode of
      TyPrimitive primitiveName              => text (showTypPrimLeaf primitiveName)
      TyPath typePath                        => showPathDoc typePath
      TyUnit                                 => "()"
      TyParenthesized nestedType             => parens (showTyDoc style nestedType)
      TyTuple (firstType ::: remainingTypes) => showTupleLike (MoreDocs (showTyDoc style firstType) (showTyListDoc style remainingTypes))
      TyArray elementType arrayLength        => brackets (showTyDoc style elementType <+> "; " <+> showExprDoc style arrayLength)
      TySlice elementType                    => brackets (showTyDoc style elementType)
      TyReference (MkAstNode _ _ borrowKind) nestedType => showBorrowPrefixed borrowKind (showTyDoc style nestedType)
      TyQualified (MkAstNode _ _ quantumUsageQualifier) nestedType => text (show quantumUsageQualifier) <+> " " <+> showTyDoc style nestedType
      TyFunction functionEffect functionParameters returnType =>
        locatedModifier functionEffect <+> "fn" <+> argumentList (showFunctionTypeParametersDoc style functionParameters) <+>
          -- An explicit case: passing showTyDoc to a helper would hide the recursion.
          (case returnType of
             Nothing                => ""
             Just writtenReturnType => " -> " <+> showTyDoc style writtenReturnType)

  showTyDoc : PhasePretty phase => PrettyStyle -> Ty phase (Expr phase) -> SourceText
  showTyDoc style (MkAstNode _ _ typeNode) = showTyNodeDoc style typeNode

  showTyListDoc : PhasePretty phase => PrettyStyle -> List (Ty phase (Expr phase)) -> SourceDocs
  showTyListDoc style []          = NoDocs
  showTyListDoc style (firstType :: remainingTypes) = MoreDocs (showTyDoc style firstType) (showTyListDoc style remainingTypes)

  showFunctionTypeParametersDoc :
       PhasePretty phase
    => PrettyStyle
    -> List (AstNode phase (FunctionTypeParameterNode phase (Expr phase)))
    -> SourceDocs
  showFunctionTypeParametersDoc style [] = NoDocs
  showFunctionTypeParametersDoc style (MkAstNode _ _ (MkFunctionTypeParameterNode parameterName parameterType) :: remainingParameters) =
    MoreDocs (showPlainNameDoc parameterName <+> ": " <+> showTyDoc style parameterType) (showFunctionTypeParametersDoc style remainingParameters)

------------------------------------------------------------------------------
-- Expression parts
------------------------------------------------------------------------------

-- Comma-separated expressions, with a trailing comma when the last one ends in
-- a `return` or `break` without a value: only `;`, `,` or `}` may follow it.
showExprListDoc : PhasePretty phase => PrettyStyle -> List (Expr phase) -> SourceText
showExprListDoc style expressions =
  commaList (mapDocs (showExprDoc style) expressions) <+>
    (if maybe False (endsInValuelessExit . nodeValue) (last' expressions) then "," else "")

showFieldInitializerDoc : PhasePretty phase => PrettyStyle -> AstNode phase (FieldInitializerNode phase) -> SourceText
showFieldInitializerDoc style (MkAstNode _ _ fieldInitializer) =
  case fieldInitializer of
    FieldInitShorthand fieldName           => showNameDoc fieldName
    FieldInitExplicit fieldName fieldValue => showNameDoc fieldName <+> ": " <+> showExprDoc style fieldValue

showClassicalIfNodeDoc : PhasePretty phase => PrettyStyle -> ClassicalIfNode phase -> SourceText
showClassicalIfNodeDoc style (MkClassicalIfNode ifCondition thenBlock elseBranch) =
  "if " <+> showHeadExprDoc style ifCondition <+> " " <+> showBlockDoc style thenBlock <+>
    (case elseBranch of
       Nothing                                            => ""
       Just (ElseBlock elseBlock)                         => " else " <+> showBlockDoc style elseBlock
       Just (ElseChainedIf (MkAstNode _ _ chainedIfNode)) => " else " <+> showClassicalIfNodeDoc style chainedIfNode)

-- See "Quantum if branches": an expression branch for which `atRisk` holds,
-- given the first character of its bare rendering, is printed as a block. A
-- block expression is printed as it is: it reads back as the equivalent block
-- branch.
showQuantumBranchDoc :
     PhasePretty phase
  => PrettyStyle -> Follows -> (atRisk : Expr phase -> Maybe Char -> Bool)
  -> QuantumBranchNode phase -> SourceText
showQuantumBranchDoc style _ _ (QuantumBranchBlock branchBlock) = showBlockDoc style branchBlock
showQuantumBranchDoc style _ _ (QuantumBranchExpression (MkAstNode _ _ (ExprBlock branchBlock))) = showBlockDoc style branchBlock
showQuantumBranchDoc style follows atRisk (QuantumBranchExpression branchExpression) =
  let bareRendering : Lazy SourceText = showExprAtDoc style precLowest follows branchExpression in
  if atRisk branchExpression (sourceFirstChar bareRendering)
    then braces (showStatementPositionExprDoc style branchExpression)
    else bareRendering

-- Any `qelse` delimits the then-branch; without one, the branch ends the qif.
showQuantumThenBranchDoc :
     PhasePretty phase
  => PrettyStyle -> Follows -> (elseBranch : Maybe (QuantumBranchNode phase))
  -> QuantumBranchNode phase -> SourceText
showQuantumThenBranchDoc style follows elseBranch =
  showQuantumBranchDoc style (if isJust elseBranch then Delimited else follows)
    (thenBranchAtRisk style (isJust elseBranch))

-- After `qelse`, a leading `{` would be read as a block branch on its own.
showQuantumElseBranchDoc : PhasePretty phase => PrettyStyle -> Follows -> QuantumBranchNode phase -> SourceText
showQuantumElseBranchDoc style follows = showQuantumBranchDoc style follows (\_, firstCharacter => firstCharacter == Just '{')

-- The head rules, and a condition ending in a qif without qelse would take
-- the then-branch as its own. The then-branch follows the condition.
showQuantumConditionDoc : PhasePretty phase => PrettyStyle -> Expr phase -> SourceText
showQuantumConditionDoc style qifCondition =
  showGuardedExprDoc style Followed
    (headNeedsParens style qifCondition || endsWith isQIfWithoutElse style precLowest Followed qifCondition)
    qifCondition

showClassicalMatchArmNodeDoc : PhasePretty phase => PrettyStyle -> ClassicalMatchArmNode phase -> SourceText
showClassicalMatchArmNodeDoc style (MkClassicalMatchArmNode armPattern armGuard armBody) =
  showPatternDoc armPattern <+> optionalText " if " (showBeforeKeywordDoc style) armGuard <+>
    " => " <+> showStatementPositionExprDoc style armBody

showClassicalMatchArmDoc : PhasePretty phase => PrettyStyle -> ClassicalMatchArm phase -> SourceText
showClassicalMatchArmDoc style (MkAstNode _ _ matchArmNode) = showClassicalMatchArmNodeDoc style matchArmNode

showQuantumMatchArmNodeDoc : PhasePretty phase => PrettyStyle -> QuantumMatchArmNode phase -> SourceText
showQuantumMatchArmNodeDoc style (MkQuantumMatchArmNode armPattern armBody) =
  showQuantumMatchPatternDoc armPattern <+> " => " <+> showStatementPositionExprDoc style armBody

showQuantumMatchArmDoc : PhasePretty phase => PrettyStyle -> QuantumMatchArm phase -> SourceText
showQuantumMatchArmDoc style (MkAstNode _ _ matchArmNode) = showQuantumMatchArmNodeDoc style matchArmNode

-- `<keyword> <head> { arm, arm }` for match, qmatch and smatch.
showMatchLikeDoc : PhasePretty phase => PrettyStyle -> SourceText -> Expr phase -> SourceDocs -> SourceText
showMatchLikeDoc style keyword scrutinee armDocs =
  keyword <+> " " <+> showHeadExprDoc style scrutinee <+> " " <+> braces (commaList armDocs)

showControlExprDoc : PhasePretty phase => PrettyStyle -> ControlExpressionNode phase -> SourceText
showControlExprDoc style controlExpression =
  case controlExpression of
    ControlledCallable controlQbits onBasis callable =>
      controlPrefix controlQbits onBasis <+> ".apply" <+> parens (showExprDoc style callable)
    ControlledBlock controlQbits onBasis controlledBlock =>
      controlPrefix controlQbits onBasis <+> " " <+> showBlockDoc style controlledBlock
  where
    controlPrefix : List1 (Expr phase) -> Maybe (AstNode phase String) -> SourceText
    controlPrefix controlQbits onBasis =
      "ctrl" <+> parens (showExprListDoc style (forget controlQbits)) <+> showOnBasisDoc onBasis

showAdjointExprDoc : PhasePretty phase => PrettyStyle -> AdjointExpressionNode phase -> SourceText
showAdjointExprDoc style (AdjointOfCallable callable) = "adjoint" <+> parens (showExprDoc style callable)
showAdjointExprDoc style (AdjointBlock adjointedBlock)          = "adjoint " <+> showBlockDoc style adjointedBlock

------------------------------------------------------------------------------
-- Expressions
------------------------------------------------------------------------------

-- `follows`: whether something that could continue this rendering follows it,
-- inside any parentheses of its own. Its right edge inherits it; its other
-- children are followed by the rest of the rendering, or are delimited.
showExpressionNodeBodyDoc : PhasePretty phase => PrettyStyle -> Follows -> ExpressionNode phase -> SourceText
showExpressionNodeBodyDoc style follows expressionNode =
  case expressionNode of
    ExprLiteral literalNode => showLiteralDoc literalNode
    ExprName valueName      => showNameDoc valueName
    ExprPath valuePath      => showPathDoc valuePath
    ExprBuiltin builtin     => text (show builtin)
    ExprSelf _              => "self"

    ExprParenthesized innerExpression              => parens (showExprDoc style innerExpression)
    ExprTuple (onlyElement ::: [])                 => showTupleLike (MoreDocs (showExprDoc style onlyElement) NoDocs)
    ExprTuple (firstElement ::: remainingElements) => parens (showExprListDoc style (firstElement :: remainingElements))
    ExprArray elementExpressions                   => brackets (showExprListDoc style elementExpressions)
    ExprRepeatedArray repeatedElement repeatCount =>
      brackets (showExprDoc style repeatedElement <+> "; " <+> showExprDoc style repeatCount)
    ExprStructLiteral valuePath fieldInitializers =>
      showPathDoc valuePath <+> " " <+> braces (commaList (mapDocs (showFieldInitializerDoc style) fieldInitializers))

    ExprCall callee arguments =>
      showExprAtDoc style (callCalleePrecedence callee.nodeValue) Followed callee <+>
        parens (showExprListDoc style arguments)
    ExprMethodCall receiver methodName arguments =>
      showExprAtDoc style precPostfix Followed receiver <+> "." <+> showMemberNameDoc methodName <+>
        parens (showExprListDoc style arguments)
    ExprField accessedObject fieldName =>
      showExprAtDoc style precPostfix Followed accessedObject <+> "." <+> showMemberNameDoc fieldName
    ExprTupleIndex accessedObject@(MkAstNode _ _ tupleBaseNode) index =>
      showExprAtDoc style (tupleIndexBasePrecedence tupleBaseNode) Followed accessedObject <+> "." <+> text index
    ExprIndex accessedObject index =>
      showExprAtDoc style precPostfix Followed accessedObject <+> brackets (showExprDoc style index)

    ExprUnary (MkAstNode _ _ unaryOperator) operand =>
      let operandText : Lazy SourceText = showExprAtDoc style precUnary follows operand in
      case unaryOperator of
        UnaryNegate            => prefixOperator '-' operandText
        UnaryLogicalNot        => "!" <+> operandText
        UnaryBorrow borrowKind => showBorrowPrefixed borrowKind operandText
    ExprBinary (MkAstNode _ _ binaryOperator) leftOperand rightOperand =>
      showExprAtDoc style (binaryLeftPrecedence binaryOperator) Followed leftOperand <+> " " <+> text (show binaryOperator) <+> " " <+>
        showExprAtDoc style (binaryRightPrecedence binaryOperator) follows rightOperand
    ExprRange rangeStart (MkAstNode _ _ rangeOperator) rangeEnd =>
      optionalText "" (showExprAtDoc style (S precRange) Followed) rangeStart <+> text (show rangeOperator) <+>
        optionalText "" (showExprAtDoc style (S precRange) follows) rangeEnd
    ExprCast operand castTargetType =>
      showExprAtDoc style precCast Followed operand <+> " as " <+> showTyDoc style castTargetType

    ExprBlock block   => showBlockDoc style block
    ExprIf ifNode     => showClassicalIfNodeDoc style ifNode
    ExprQIf (MkQuantumIfNode qifCondition thenBranch elseBranch) =>
      "qif " <+> showQuantumConditionDoc style qifCondition <+> " " <+>
        showQuantumThenBranchDoc style follows elseBranch thenBranch <+>
        optionalText " qelse " (showQuantumElseBranchDoc style follows) elseBranch
    ExprSIf (MkStateIfNode sifCondition thenExpr elseExpr) =>
      "sif " <+> showBeforeKeywordDoc style sifCondition <+> " then " <+> showBeforeKeywordDoc style thenExpr <+>
        " selse " <+> showExprAtDoc style precLowest follows elseExpr
    ExprMatch (MkClassicalMatchNode scrutinee matchArms) =>
      showMatchLikeDoc style "match" scrutinee (mapDocs (showClassicalMatchArmDoc style) matchArms)
    ExprQMatch (MkQuantumMatchNode scrutinee matchArms) =>
      showMatchLikeDoc style "qmatch" scrutinee (mapDocs (showQuantumMatchArmDoc style) matchArms)
    ExprSMatch (MkStateMatchNode scrutinee matchArms) =>
      showMatchLikeDoc style "smatch" scrutinee (mapDocs (showQuantumMatchArmDoc style) matchArms)
    ExprLoop loopBody => "loop " <+> showBlockDoc style loopBody
    ExprWhile loopCondition loopBody =>
      "while " <+> showHeadExprDoc style loopCondition <+> " " <+> showBlockDoc style loopBody
    ExprFor binderPattern iterable loopBody =>
      "for " <+> showPatternDoc binderPattern <+> " in " <+> showHeadExprDoc style iterable <+> " " <+>
        showBlockDoc style loopBody

    ExprBreak breakValue => "break" <+> optionalText " " (showExprAtDoc style precLowest follows) breakValue
    ExprContinue       => "continue"
    ExprReturn returnValue  => "return" <+> optionalText " " (showExprAtDoc style precLowest follows) returnValue

    ExprCtrl controlExpression   => showControlExprDoc style controlExpression
    ExprAdjoint adjointExpression => showAdjointExprDoc style adjointExpression

-- Decides on an expression's parentheses from its precedence and what follows
-- it. The `assert_total` breaks the cycle expression -> sub-expression; every
-- recursive call is on a subterm.
wrapExprDoc : PhasePretty phase => PrettyStyle -> Nat -> Follows -> ExpressionNode phase -> SourceText
wrapExprDoc style outerReq follows expressionNode =
  let parenthesized = needsParens style outerReq follows expressionNode
      -- Inside parentheses, the closing `)` ends the expression.
      followsInside = if parenthesized then Delimited else follows
      renderedExpression : Lazy SourceText = assert_total $ showExpressionNodeBodyDoc style followsInside expressionNode
  in if parenthesized then parens renderedExpression else renderedExpression

showExprAtDoc style outerReq follows (MkAstNode _ _ expressionNode) = wrapExprDoc style outerReq follows expressionNode

-- Unconstrained rendering of a raw ExpressionNode, for the Show instance.
showExpressionNodeDoc : PhasePretty phase => PrettyStyle -> ExpressionNode phase -> SourceText
showExpressionNodeDoc style = wrapExprDoc style precLowest Delimited

------------------------------------------------------------------------------
-- Blocks and statements
------------------------------------------------------------------------------

showAssignmentTargetNodeDoc : PhasePretty phase => PrettyStyle -> AssignmentTargetNode phase -> SourceText
showAssignmentTargetNodeDoc style targetNode =
  case targetNode of
    AssignTargetName targetName              => showNameDoc targetName
    AssignTargetIndex targetObject index     => targetObjectDoc precPostfix targetObject <+> brackets (showExprDoc style index)
    AssignTargetField targetObject fieldName => targetObjectDoc precPostfix targetObject <+> "." <+> showMemberNameDoc fieldName
    AssignTargetTupleIndex targetObject@(MkAstNode _ _ tupleBaseNode) index =>
      targetObjectDoc (tupleIndexBasePrecedence tupleBaseNode) targetObject <+> "." <+> text index
  where
    -- The object before `[`, `.` or `.<digits>`, which starts the statement.
    targetObjectDoc : Nat -> Expr phase -> SourceText
    targetObjectDoc requirement targetObject =
      showExprAtDoc style requirement Followed (parenthesizeLeadingBlock style requirement targetObject)

showAssignmentTargetDoc : PhasePretty phase => PrettyStyle -> AssignmentTarget phase -> SourceText
showAssignmentTargetDoc style (MkAstNode _ _ targetNode) = showAssignmentTargetNodeDoc style targetNode

showAssignmentNodeDoc : PhasePretty phase => PrettyStyle -> AssignmentNode phase -> SourceText
showAssignmentNodeDoc style (MkAssignmentNode (MkAstNode _ _ targetNode) (MkAstNode _ _ assignmentOperator) assignedValue) =
  showAssignmentTargetNodeDoc style targetNode <+> " " <+> text (show assignmentOperator) <+> " " <+> showExprDoc style assignedValue

showLetBindingNodeDoc : PhasePretty phase => PrettyStyle -> LetBindingNode phase -> SourceText
showLetBindingNodeDoc style (MkLetBindingNode letQualifiers letPattern typeAnnotation letInitializer) =
  "let " <+> showQualifiersPrefixDoc letQualifiers <+> showPatternDoc letPattern <+>
    optionalText ": " (showTyDoc style) typeAnnotation <+> optionalText " " showInitializerDoc letInitializer
  where
    showInitializerDoc : LetInitializerNode phase -> SourceText
    showInitializerDoc (MkLetInitializerNode (MkAstNode _ _ initializerMarker) initializerValue) =
      text (show initializerMarker) <+> " " <+> showExprDoc style initializerValue

showLetBindingDoc : PhasePretty phase => PrettyStyle -> LetBinding phase -> SourceText
showLetBindingDoc style (MkAstNode _ _ letBindingNode) = showLetBindingNodeDoc style letBindingNode

showStatementNodeDoc : PhasePretty phase => PrettyStyle -> StatementNode phase -> SourceText
showStatementNodeDoc style statementNode =
  case statementNode of
    StatementLet letBinding                     => showLetBindingNodeDoc style letBinding <+> ";"
    StatementAssignment assignment              => showAssignmentNodeDoc style assignment <+> ";"
    StatementSemiExpression statementExpression => showStatementPositionExprDoc style statementExpression <+> ";"
    StatementExpression statementExpression     => showStatementPositionExprDoc style statementExpression

public export
showStatementDoc : PhasePretty phase => PrettyStyle -> Statement phase -> SourceText
showStatementDoc style (MkAstNode _ _ statementNode) = showStatementNodeDoc style statementNode

showBlockNodeDoc : PhasePretty phase => PrettyStyle -> BlockNode phase -> SourceText
showBlockNodeDoc style (MkBlockNode innerDocs blockStatements finalExpression) =
  braces (docsPrefix innerDocs <+> joinWith " " (appendDocs (mapDocs (showStatementDoc style) blockStatements) finalText))
  where
    finalText : SourceDocs
    finalText = case finalExpression of
      Nothing                     => NoDocs
      Just presentFinalExpression => MoreDocs (showStatementPositionExprDoc style presentFinalExpression) NoDocs

showBlockDoc style (MkAstNode _ _ blockNode) = showBlockNodeDoc style blockNode

--------------------------------------------------------------------------------
-- Contracts
--------------------------------------------------------------------------------

showContractPredicateNodeDoc :
  PhasePretty phase => PrettyStyle -> ContractPredicateNode phase (Expr phase) -> SourceText
showContractPredicateNodeDoc style predicateNode =
  case predicateNode of
    ContractClean qbitArgument             => "clean" <+> parens (showExprListDoc style [qbitArgument])
    ContractBasis qbitArgument pauliString =>
      "basis" <+> argumentList (MoreDocs (showExprDoc style qbitArgument) (MoreDocs (showPauliStringDoc pauliString) NoDocs))
    ContractSeparable qbitArgument                  => "separable" <+> parens (showExprListDoc style [qbitArgument])
    ContractIsolated qbitArgument                   => "isolated" <+> parens (showExprListDoc style [qbitArgument])
    ContractProduct firstQbitSet otherQbitSets      => "product" <+> parens (showExprListDoc style (firstQbitSet :: forget otherQbitSets))
    ContractStabilized qbitArgument stabilizerTerms =>
      "stabilized" <+> argumentList
        (MoreDocs (showExprDoc style qbitArgument)
          (MoreDocs (brackets (commaList (mapDocs showSignedPauliTermDoc (forget stabilizerTerms)))) NoDocs))

showContractPredicateDoc : PhasePretty phase => PrettyStyle -> ContractPredicate phase (Expr phase) -> SourceText
showContractPredicateDoc style (MkAstNode _ _ predicateNode) = showContractPredicateNodeDoc style predicateNode

showContractClauseNodeDoc : PhasePretty phase => PrettyStyle -> ContractClauseNode phase (Expr phase) -> SourceText
showContractClauseNodeDoc style (RequiresClause predicate) = "requires " <+> showContractPredicateDoc style predicate
showContractClauseNodeDoc style (EnsuresClause predicate)  = "ensures " <+> showContractPredicateDoc style predicate

showContractClauseDoc : PhasePretty phase => PrettyStyle -> ContractClause phase (Expr phase) -> SourceText
showContractClauseDoc style (MkAstNode _ _ clauseNode) = showContractClauseNodeDoc style clauseNode

--------------------------------------------------------------------------------
-- Functions
--------------------------------------------------------------------------------

showFunctionParameterNodeDoc : PhasePretty phase => PrettyStyle -> FunctionParameterNode phase -> SourceText
showFunctionParameterNodeDoc style parameterNode =
  case parameterNode of
    NormalParameter parameterDocs mutability parameterName parameterType =>
      docsPrefix parameterDocs <+> locatedModifier mutability <+> showNameDoc parameterName <+> ": " <+> showTyDoc style parameterType
    ReceiverParameter parameterDocs Nothing => docsPrefix parameterDocs <+> "self"
    ReceiverParameter parameterDocs (Just (MkAstNode _ _ borrowKind)) => docsPrefix parameterDocs <+> showBorrowPrefixed borrowKind "self"

showFunctionParameterDoc : PhasePretty phase => PrettyStyle -> FunctionParameter phase -> SourceText
showFunctionParameterDoc style (MkAstNode _ _ parameterNode) = showFunctionParameterNodeDoc style parameterNode

showFunctionDeclarationNodeDoc : PhasePretty phase => PrettyStyle -> FunctionDeclarationNode phase -> SourceText
showFunctionDeclarationNodeDoc style
    (MkFunctionDeclarationNode functionDocs functionAttributes visibility constness functionEffect functionName functionParameters returnType supportKinds contractClauses functionBody) =
  docsPrefix functionDocs <+> attributesPrefix functionAttributes <+>
    locatedModifier visibility <+> locatedModifier constness <+> locatedModifier functionEffect <+>
    "fn " <+> showNameDoc functionName <+> argumentList (mapDocs (showFunctionParameterDoc style) functionParameters) <+>
    optionalText " -> " (showTyDoc style) returnType <+>
    supportClauseText <+>
    concatDocs (\contractClause => " " <+> showContractClauseDoc style contractClause) contractClauses <+>
    " " <+> showBlockDoc style functionBody
  where
    supportClauseText : SourceText
    supportClauseText = case supportKinds of
      [] => ""
      _  => " supports " <+> commaList (mapDocs (text . show . nodeValue) supportKinds)

public export
showFunctionDeclarationDoc : PhasePretty phase => PrettyStyle -> FunctionDeclaration phase -> SourceText
showFunctionDeclarationDoc style (MkAstNode _ _ functionDeclarationNode) = showFunctionDeclarationNodeDoc style functionDeclarationNode

--------------------------------------------------------------------------------
-- struct, enum, qenum, impl, const and use declarations
--------------------------------------------------------------------------------

-- Docs, attributes, visibility and `<keyword> <name>`: the common head of a
-- type declaration.
declarationHeadDoc :
     PhasePretty phase
  => List (DocComment phase) -> List (Attribute phase) -> Maybe (AstNode phase VisibilityQualifier)
  -> SourceText -> Name phase -> SourceText
declarationHeadDoc declarationDocs declarationAttributes visibility keyword declaredName =
  docsPrefix declarationDocs <+> attributesPrefix declarationAttributes <+> locatedModifier visibility <+> keyword <+> " " <+> showNameDoc declaredName

showStructFieldDoc : PhasePretty phase => PrettyStyle -> AstNode phase (StructFieldNode phase) -> SourceText
showStructFieldDoc style (MkAstNode _ _ (MkStructFieldNode declarationDocs declaredName declaredType)) =
  docsPrefix declarationDocs <+> showNameDoc declaredName <+> ": " <+> showTyDoc style declaredType

showStructFieldsDoc : PhasePretty phase => PrettyStyle -> List (AstNode phase (StructFieldNode phase)) -> SourceText
showStructFieldsDoc style structFields = braces (commaList (mapDocs (showStructFieldDoc style) structFields))

showStructDeclarationNodeDoc : PhasePretty phase => PrettyStyle -> StructDeclarationNode phase -> SourceText
showStructDeclarationNodeDoc style (MkStructDeclarationNode declarationDocs declarationAttributes visibility declaredName structFields) =
  declarationHeadDoc declarationDocs declarationAttributes visibility "struct" declaredName <+> " " <+> showStructFieldsDoc style structFields

showStructDeclarationDoc : PhasePretty phase => PrettyStyle -> StructDeclaration phase -> SourceText
showStructDeclarationDoc style (MkAstNode _ _ declarationNode) = showStructDeclarationNodeDoc style declarationNode

showEnumVariantDoc : PhasePretty phase => PrettyStyle -> AstNode phase (EnumVariantNode phase) -> SourceText
showEnumVariantDoc style (MkAstNode _ _ (MkEnumVariantNode declarationDocs declaredName variantBody)) =
  docsPrefix declarationDocs <+> showNameDoc declaredName <+>
    (case variantBody of
       VariantUnit                => ""
       VariantTuple payloadTypes  => argumentList (mapDocs (showTyDoc style) (forget payloadTypes))
       VariantStruct structFields => " " <+> showStructFieldsDoc style structFields)

showEnumDeclarationNodeDoc : PhasePretty phase => PrettyStyle -> EnumDeclarationNode phase -> SourceText
showEnumDeclarationNodeDoc style (MkEnumDeclarationNode declarationDocs declarationAttributes visibility declaredName variants) =
  declarationHeadDoc declarationDocs declarationAttributes visibility "enum" declaredName <+> " " <+>
    braces (commaList (mapDocs (showEnumVariantDoc style) variants))

showEnumDeclarationDoc : PhasePretty phase => PrettyStyle -> EnumDeclaration phase -> SourceText
showEnumDeclarationDoc style (MkAstNode _ _ declarationNode) = showEnumDeclarationNodeDoc style declarationNode

showQEnumVariantDoc : PhasePretty phase => PrettyStyle -> AstNode phase (QEnumVariantNode phase) -> SourceText
showQEnumVariantDoc style (MkAstNode _ _ (MkQEnumVariantNode declarationDocs declaredName payloadTypes)) =
  docsPrefix declarationDocs <+> showNameDoc declaredName <+> argumentList (mapDocs (showTyDoc style) (forget payloadTypes))

showQEnumDeclarationNodeDoc : PhasePretty phase => PrettyStyle -> QEnumDeclarationNode phase -> SourceText
showQEnumDeclarationNodeDoc style (MkQEnumDeclarationNode declarationDocs declarationAttributes visibility declaredName variants) =
  declarationHeadDoc declarationDocs declarationAttributes visibility "qenum" declaredName <+> " " <+>
    braces (commaList (mapDocs (showQEnumVariantDoc style) variants))

showQEnumDeclarationDoc : PhasePretty phase => PrettyStyle -> QEnumDeclaration phase -> SourceText
showQEnumDeclarationDoc style (MkAstNode _ _ declarationNode) = showQEnumDeclarationNodeDoc style declarationNode

showImplDeclarationNodeDoc : PhasePretty phase => PrettyStyle -> ImplDeclarationNode phase -> SourceText
showImplDeclarationNodeDoc style (MkImplDeclarationNode declarationDocs implTarget implFunctions) =
  docsPrefix declarationDocs <+> "impl " <+> showPathDoc implTarget <+> " " <+>
    braces (joinWith " " (mapDocs (showFunctionDeclarationDoc style) implFunctions))

showImplDeclarationDoc : PhasePretty phase => PrettyStyle -> ImplDeclaration phase -> SourceText
showImplDeclarationDoc style (MkAstNode _ _ declarationNode) = showImplDeclarationNodeDoc style declarationNode

showConstDeclarationNodeDoc : PhasePretty phase => PrettyStyle -> ConstDeclarationNode phase -> SourceText
showConstDeclarationNodeDoc style (MkConstDeclarationNode declarationDocs visibility declaredName declaredType constValue) =
  declarationHeadDoc declarationDocs [] visibility "const" declaredName <+> ": " <+> showTyDoc style declaredType <+>
    " = " <+> showExprDoc style constValue <+> ";"

showConstDeclarationDoc : PhasePretty phase => PrettyStyle -> ConstDeclaration phase -> SourceText
showConstDeclarationDoc style (MkAstNode _ _ declarationNode) = showConstDeclarationNodeDoc style declarationNode

showUseDeclarationNodeDoc : PhasePretty phase => PrettyStyle -> UseDeclarationNode phase -> SourceText
showUseDeclarationNodeDoc style (MkUseDeclarationNode declarationDocs visibility importPath importAlias) =
  docsPrefix declarationDocs <+> locatedModifier visibility <+> "use " <+> showPathDoc importPath <+>
    optionalText " as " showPlainNameDoc importAlias <+> ";"

showUseDeclarationDoc : PhasePretty phase => PrettyStyle -> UseDeclaration phase -> SourceText
showUseDeclarationDoc style (MkAstNode _ _ declarationNode) = showUseDeclarationNodeDoc style declarationNode

--------------------------------------------------------------------------------
-- Modules and items (recursive group, through inline module bodies)
--------------------------------------------------------------------------------

mutual
  showModuleDeclarationNodeDoc : PhasePretty phase => PrettyStyle -> ModuleDeclarationNode phase -> SourceText
  showModuleDeclarationNodeDoc style (MkModuleDeclarationNode moduleDocs visibility moduleName moduleBody) =
    declarationHeadDoc moduleDocs [] visibility "mod" moduleName <+>
      (case moduleBody of
         ModuleInline innerDocs moduleItems =>
           " " <+> braces (docsPrefix innerDocs <+> joinWith "\n" (showItemListDoc style moduleItems))
         ModuleExternal               => ";")

  showItemNodeDoc : PhasePretty phase => PrettyStyle -> ItemNode phase -> SourceText
  showItemNodeDoc style itemNode =
    case itemNode of
      ItemFunction declarationNode => showFunctionDeclarationNodeDoc style declarationNode
      ItemStruct declarationNode   => showStructDeclarationNodeDoc style declarationNode
      ItemEnum declarationNode     => showEnumDeclarationNodeDoc style declarationNode
      ItemQEnum declarationNode    => showQEnumDeclarationNodeDoc style declarationNode
      ItemImpl declarationNode     => showImplDeclarationNodeDoc style declarationNode
      ItemConst declarationNode    => showConstDeclarationNodeDoc style declarationNode
      ItemUse declarationNode      => showUseDeclarationNodeDoc style declarationNode
      ItemModule declarationNode   => showModuleDeclarationNodeDoc style declarationNode

  export
  showItemDoc : PhasePretty phase => PrettyStyle -> Item phase -> SourceText
  showItemDoc style (MkAstNode _ _ itemNode) = showItemNodeDoc style itemNode

  showItemListDoc : PhasePretty phase => PrettyStyle -> List (Item phase) -> SourceDocs
  showItemListDoc style []              = NoDocs
  showItemListDoc style (firstItem :: remainingItems) = MoreDocs (showItemDoc style firstItem) (showItemListDoc style remainingItems)

showModuleDeclarationDoc : PhasePretty phase => PrettyStyle -> ModuleDeclaration phase -> SourceText
showModuleDeclarationDoc style (MkAstNode _ _ declarationNode) = showModuleDeclarationNodeDoc style declarationNode

showSourceFileNodeDoc : PhasePretty phase => PrettyStyle -> SourceFileNode phase -> SourceText
showSourceFileNodeDoc style (MkSourceFileNode innerDocs sourceFileItems) =
  joinWith "\n" (appendDocs (mapDocs showDocCommentDoc innerDocs) (showItemListDoc style sourceFileItems))

showSourceFileDoc : PhasePretty phase => PrettyStyle -> SourceFile phase -> SourceText
showSourceFileDoc style (MkAstNode _ _ sourceFile) = showSourceFileNodeDoc style sourceFile

--------------------------------------------------------------------------------
-- String printers: one per syntactic category, for diagnostics and tests.
--------------------------------------------------------------------------------

public export
showPattern : PhasePretty phase => Pattern phase -> String
showPattern astNode = renderSource (showPatternDoc astNode)

public export
showQuantumMatchPattern : PhasePretty phase => QuantumMatchPattern phase -> String
showQuantumMatchPattern astNode = renderSource (showQuantumMatchPatternDoc astNode)

public export
showBlock : PhasePretty phase => PrettyStyle -> Block phase -> String
showBlock style astNode = renderSource (showBlockDoc style astNode)

public export
showExpr : PhasePretty phase => PrettyStyle -> Expr phase -> String
showExpr style astNode = renderSource (showExprDoc style astNode)

public export
showTy : PhasePretty phase => PrettyStyle -> Ty phase (Expr phase) -> String
showTy style astNode = renderSource (showTyDoc style astNode)

public export
showClassicalMatchArm : PhasePretty phase => PrettyStyle -> ClassicalMatchArm phase -> String
showClassicalMatchArm style astNode = renderSource (showClassicalMatchArmDoc style astNode)

public export
showQuantumMatchArm : PhasePretty phase => PrettyStyle -> QuantumMatchArm phase -> String
showQuantumMatchArm style astNode = renderSource (showQuantumMatchArmDoc style astNode)

public export
showAssignmentTarget : PhasePretty phase => PrettyStyle -> AssignmentTarget phase -> String
showAssignmentTarget style astNode = renderSource (showAssignmentTargetDoc style astNode)

public export
showLetBinding : PhasePretty phase => PrettyStyle -> LetBinding phase -> String
showLetBinding style astNode = renderSource (showLetBindingDoc style astNode)

public export
showStatement : PhasePretty phase => PrettyStyle -> Statement phase -> String
showStatement style astNode = renderSource (showStatementDoc style astNode)

public export
showContractPredicate : PhasePretty phase => PrettyStyle -> ContractPredicate phase (Expr phase) -> String
showContractPredicate style astNode = renderSource (showContractPredicateDoc style astNode)

public export
showContractClause : PhasePretty phase => PrettyStyle -> ContractClause phase (Expr phase) -> String
showContractClause style astNode = renderSource (showContractClauseDoc style astNode)

public export
showFunctionParameter : PhasePretty phase => PrettyStyle -> FunctionParameter phase -> String
showFunctionParameter style astNode = renderSource (showFunctionParameterDoc style astNode)

public export
showFunctionDeclaration : PhasePretty phase => PrettyStyle -> FunctionDeclaration phase -> String
showFunctionDeclaration style astNode = renderSource (showFunctionDeclarationDoc style astNode)

public export
showStructDeclaration : PhasePretty phase => PrettyStyle -> StructDeclaration phase -> String
showStructDeclaration style astNode = renderSource (showStructDeclarationDoc style astNode)

public export
showEnumDeclaration : PhasePretty phase => PrettyStyle -> EnumDeclaration phase -> String
showEnumDeclaration style astNode = renderSource (showEnumDeclarationDoc style astNode)

public export
showQEnumDeclaration : PhasePretty phase => PrettyStyle -> QEnumDeclaration phase -> String
showQEnumDeclaration style astNode = renderSource (showQEnumDeclarationDoc style astNode)

public export
showImplDeclaration : PhasePretty phase => PrettyStyle -> ImplDeclaration phase -> String
showImplDeclaration style astNode = renderSource (showImplDeclarationDoc style astNode)

public export
showConstDeclaration : PhasePretty phase => PrettyStyle -> ConstDeclaration phase -> String
showConstDeclaration style astNode = renderSource (showConstDeclarationDoc style astNode)

public export
showUseDeclaration : PhasePretty phase => PrettyStyle -> UseDeclaration phase -> String
showUseDeclaration style astNode = renderSource (showUseDeclarationDoc style astNode)

public export
showItem : PhasePretty phase => PrettyStyle -> Item phase -> String
showItem style astNode = renderSource (showItemDoc style astNode)

public export
showModuleDeclaration : PhasePretty phase => PrettyStyle -> ModuleDeclaration phase -> String
showModuleDeclaration style astNode = renderSource (showModuleDeclarationDoc style astNode)

public export
showSourceFile : PhasePretty phase => PrettyStyle -> SourceFile phase -> String
showSourceFile style astNode = renderSource (showSourceFileDoc style astNode)

--------------------------------------------------------------------------------
-- Convenience wrappers
--------------------------------------------------------------------------------

public export
showSourceFileLax : PhasePretty phase => SourceFile phase -> String
showSourceFileLax = showSourceFile PrettyLax

public export
showSourceFileStrict : PhasePretty phase => SourceFile phase -> String
showSourceFileStrict = showSourceFile PrettyStrict

public export
showExprStrict : PhasePretty phase => Expr phase -> String
showExprStrict = showExpr PrettyStrict

--------------------------------------------------------------------------------
-- Show instances on the raw payload types, in lax style. ASTPhases shows an
-- AstNode by showing its payload, so every located alias in Syntax.AST is
-- `Show` too. Use the style-taking printers above for strict output.
--------------------------------------------------------------------------------

public export
PhasePretty phase => Show (ExpressionNode phase) where
  show = renderSource . showExpressionNodeDoc PrettyLax

public export
PhasePretty phase => Show (BlockNode phase) where
  show = renderSource . showBlockNodeDoc PrettyLax

public export
PhasePretty phase => Show (StatementNode phase) where
  show = renderSource . showStatementNodeDoc PrettyLax

public export
PhasePretty phase => Show (ItemNode phase) where
  show = renderSource . showItemNodeDoc PrettyLax

public export
PhasePretty phase => Show (TyNode phase (Expr phase)) where
  show = renderSource . showTyNodeDoc PrettyLax

public export
PhasePretty phase => Show (ContractClauseNode phase (Expr phase)) where
  show = renderSource . showContractClauseNodeDoc PrettyLax

public export
PhasePretty phase => Show (ContractPredicateNode phase (Expr phase)) where
  show = renderSource . showContractPredicateNodeDoc PrettyLax

public export
PhasePretty phase => Show (SourceFileNode phase) where
  show = renderSource . showSourceFileNodeDoc PrettyLax

public export
PhasePretty phase => Show (FunctionDeclarationNode phase) where
  show = renderSource . showFunctionDeclarationNodeDoc PrettyLax

public export
PhasePretty phase => Show (FunctionParameterNode phase) where
  show = renderSource . showFunctionParameterNodeDoc PrettyLax

public export
PhasePretty phase => Show (StructDeclarationNode phase) where
  show = renderSource . showStructDeclarationNodeDoc PrettyLax

public export
PhasePretty phase => Show (EnumDeclarationNode phase) where
  show = renderSource . showEnumDeclarationNodeDoc PrettyLax

public export
PhasePretty phase => Show (QEnumDeclarationNode phase) where
  show = renderSource . showQEnumDeclarationNodeDoc PrettyLax

public export
PhasePretty phase => Show (ImplDeclarationNode phase) where
  show = renderSource . showImplDeclarationNodeDoc PrettyLax

public export
PhasePretty phase => Show (ConstDeclarationNode phase) where
  show = renderSource . showConstDeclarationNodeDoc PrettyLax

public export
PhasePretty phase => Show (UseDeclarationNode phase) where
  show = renderSource . showUseDeclarationNodeDoc PrettyLax

public export
PhasePretty phase => Show (ModuleDeclarationNode phase) where
  show = renderSource . showModuleDeclarationNodeDoc PrettyLax

public export
PhasePretty phase => Show (LetBindingNode phase) where
  show = renderSource . showLetBindingNodeDoc PrettyLax

public export
PhasePretty phase => Show (AssignmentTargetNode phase) where
  show = renderSource . showAssignmentTargetNodeDoc PrettyLax

public export
PhasePretty phase => Show (ClassicalMatchArmNode phase) where
  show = renderSource . showClassicalMatchArmNodeDoc PrettyLax

public export
PhasePretty phase => Show (QuantumMatchArmNode phase) where
  show = renderSource . showQuantumMatchArmNodeDoc PrettyLax
