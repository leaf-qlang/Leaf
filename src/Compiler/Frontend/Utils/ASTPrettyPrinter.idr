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
mapDocs render (value :: rest) = MoreDocs (render value) (mapDocs render rest)

appendDocs : SourceDocs -> Lazy SourceDocs -> SourceDocs
appendDocs NoDocs suffix = suffix
appendDocs (MoreDocs value rest) suffix = MoreDocs value (appendDocs rest suffix)

joinRest : SourceText -> SourceDocs -> SourceText
joinRest _ NoDocs = ""
joinRest separator (MoreDocs value rest) = separator <+> value <+> joinRest separator rest

joinWith : SourceText -> SourceDocs -> SourceText
joinWith _ NoDocs = ""
joinWith separator (MoreDocs value rest) = value <+> joinRest separator rest

concatDocs : (a -> SourceText) -> List a -> SourceText
concatDocs _ [] = ""
concatDocs render (value :: rest) = render value <+> concatDocs render rest

commaList : SourceDocs -> SourceText
commaList = joinWith ", "

parens : Lazy SourceText -> SourceText
parens body = "(" <+> body <+> ")"

brackets : Lazy SourceText -> SourceText
brackets body = "[" <+> body <+> "]"

braces : Lazy SourceText -> SourceText
braces body = "{ " <+> (if sourceIsEmpty body then "}" else body <+> " }")

argumentList : Lazy SourceDocs -> SourceText
argumentList values = parens (commaList values)

optionalText : SourceText -> (a -> SourceText) -> Maybe a -> SourceText
optionalText _ _ Nothing = ""
optionalText leading render (Just value) = leading <+> render value

modifier : Show a => Maybe a -> SourceText
modifier = optionalText "" (\value => text (show value) <+> " ")

locatedModifier : Show a => Maybe (AstNode phase a) -> SourceText
locatedModifier = modifier . map nodeValue

-- A one-character prefix operator, spaced from an operand that starts with
-- the same character: `& &x` must not lex as `&&x`, and `- -x` would read
-- like a decrement.
prefixOperator : Char -> Lazy SourceText -> SourceText
prefixOperator op body = text (singleton op) <+> (if sourceStartsWith op body then " " else "") <+> body

showBorrowPrefixed : BorrowKind -> Lazy SourceText -> SourceText
showBorrowPrefixed SharedBorrow body = prefixOperator '&' body
showBorrowPrefixed MutableBorrow body = "&mut " <+> body

showTupleLike : SourceDocs -> SourceText
showTupleLike NoDocs = "()"
showTupleLike (MoreDocs value NoDocs) = "(" <+> value <+> ",)"
showTupleLike values = argumentList values

--------------------------------------------------------------------------------
-- Names and paths
--------------------------------------------------------------------------------

showPathSegmentDoc : PathSegment phase -> SourceText
showPathSegmentDoc (MkAstNode _ _ (PathSegmentName spelling)) = text spelling
showPathSegmentDoc (MkAstNode _ _ PathSegmentSelf)        = "self"

prettyNameNode : NameNode -> String
prettyNameNode (MkNameNode text) = text

prettyResolvedNameNode : ResolvedNameNode -> String
prettyResolvedNameNode (MkResolvedNameNode text _) = text

prettyPathNodeDoc : PathNode phase -> SourceText
prettyPathNodeDoc (MkPathNode first rest) = joinWith "::" (mapDocs showPathSegmentDoc (first :: rest))

prettyResolvedPathNodeDoc : ResolvedPathNode -> SourceText
prettyResolvedPathNodeDoc (MkResolvedPathNode first rest _) = joinWith "::" (mapDocs text (first :: rest))

-- The three payloads that differ between phases, rendered as written.
public export
interface PhasePretty phase where
  prettyName : NameFor phase -> String
  prettyMemberName : MemberNameFor phase -> String
  -- Keep segments lazy for previews; full payloads explicitly render them.
  prettyPathDoc : PathFor phase -> SourceText
  prettyPath : PathFor phase -> String
  prettyPath path = renderSource (prettyPathDoc path)

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
showNameDoc (MkAstNode _ _ name) = text (prettyName name)

showMemberNameDoc : PhasePretty phase => MemberName phase -> SourceText
showMemberNameDoc (MkAstNode _ _ name) = text (prettyMemberName name)

showPathDoc : PhasePretty phase => Path phase -> SourceText
showPathDoc (MkAstNode _ _ path) = prettyPathDoc path

-- Attribute names, import aliases and function-type parameter names keep their
-- plain spelling at every phase.
showPlainNameDoc : AstNode phase NameNode -> SourceText
showPlainNameDoc (MkAstNode _ _ (MkNameNode spelling)) = text spelling

--------------------------------------------------------------------------------
-- Leaves: literals, doc comments, attributes, modifiers, Pauli strings
--------------------------------------------------------------------------------

-- Every literal payload is its raw source spelling or has exactly one spelling.
showLiteralDoc : Literal phase -> SourceText
showLiteralDoc (MkAstNode _ _ literal) =
  case literal of
    LiteralIntegerRaw raw     => text raw
    LiteralFloatRaw raw       => text raw
    LiteralStringRaw raw      => text raw
    LiteralByteRaw raw        => text raw
    LiteralByteStringRaw raw  => text raw
    LiteralBasisStringRaw raw => text raw
    LiteralBoolean value      => if value then "true" else "false"
    LiteralUnit               => "()"
    LiteralQuantumState state => text (show state)

-- The raw spelling of a doc comment includes its delimiters.
showDocCommentDoc : DocComment phase -> SourceText
showDocCommentDoc (MkAstNode _ _ (MkDocCommentNode _ _ rawText)) = text rawText

-- Doc comments, each ending its own line so that a line doc cannot swallow
-- the code or closing brace that follows.
docsPrefix : List (DocComment phase) -> SourceText
docsPrefix = concatDocs (\doc => showDocCommentDoc doc <+> "\n")

showAttributeDoc : Attribute phase -> SourceText
showAttributeDoc (MkAstNode _ _ (MkAttributeNode name arguments)) =
  "#[" <+> showPlainNameDoc name <+>
    optionalText "" (\arguments => argumentList (mapDocs showArgumentDoc arguments)) arguments <+> "]"
  where
    showArgumentDoc : AttributeArgument phase -> SourceText
    showArgumentDoc (MkAstNode _ _ (AttributeArgumentStringLit raw)) = text raw

attrsPrefix : List (Attribute phase) -> SourceText
attrsPrefix = concatDocs (\attribute => showAttributeDoc attribute <+> "\n")

showQualifiersPrefixDoc : List (AstNode phase QuantumStorageQualifier) -> SourceText
showQualifiersPrefixDoc = concatDocs (\qualifier => text (show qualifier.nodeValue) <+> " ")

showOnBasisDoc : Maybe (AstNode phase String) -> SourceText
showOnBasisDoc = optionalText ".on" (\basis => parens (text basis.nodeValue))

showPauliStringDoc : PauliString phase -> SourceText
showPauliStringDoc (MkAstNode _ _ (MkPauliStringNode operators)) = concatDocs (text . show) (forget operators)

showSignedPauliTermDoc : SignedPauliTerm phase -> SourceText
showSignedPauliTermDoc (MkAstNode _ _ (MkSignedPauliTermNode sign pauli)) =
  (case sign of StabilizerPlus => "+"; StabilizerMinus => "-") <+> showPauliStringDoc pauli

--------------------------------------------------------------------------------
-- Patterns (recursive group)
--------------------------------------------------------------------------------

mutual
  showPatternDoc : PhasePretty phase => Pattern phase -> SourceText
  showPatternDoc (MkAstNode _ _ pattern) = showPatternNodeDoc pattern

  showPatternNodeDoc : PhasePretty phase => PatternNode phase -> SourceText
  showPatternNodeDoc pattern =
    case pattern of
      PatternWildcard                => "_"
      PatternName mutability name    => modifier mutability <+> showNameDoc name
      PatternPath path               => showPathDoc path
      PatternLiteral literal         => showLiteralDoc literal
      PatternParenthesized inner     => parens (showPatternDoc inner)
      PatternTuple (first ::: rest)  => showTupleLike (MoreDocs (showPatternDoc first) (showPatternListDoc rest))
      PatternArray elements          => brackets (commaList (showPatternListDoc elements))
      PatternStruct path fields      =>
        showPathDoc path <+> " " <+> braces (commaList (showStructPatternFieldsDoc fields))
      PatternEnumTuple path elements => showPathDoc path <+> argumentList (showPatternListDoc elements)

  showPatternListDoc : PhasePretty phase => List (Pattern phase) -> SourceDocs
  showPatternListDoc []                    = NoDocs
  showPatternListDoc (pattern :: patterns) = MoreDocs (showPatternDoc pattern) (showPatternListDoc patterns)

  showStructPatternFieldsDoc : PhasePretty phase => List (StructPatternField phase) -> SourceDocs
  showStructPatternFieldsDoc [] = NoDocs
  showStructPatternFieldsDoc (MkAstNode _ _ field :: fields) =
    MoreDocs (case field of
       StructPatternFieldShorthand mutability name => modifier mutability <+> showNameDoc name
       StructPatternFieldExplicit name pattern     => showNameDoc name <+> ": " <+> showPatternDoc pattern)
    (showStructPatternFieldsDoc fields)

showQuantumMatchPatternDoc : PhasePretty phase => QuantumMatchPattern phase -> SourceText
showQuantumMatchPatternDoc (MkAstNode _ _ pattern) =
  case pattern of
    QuantumPatternBasisStringRaw raw        => text raw
    QuantumPatternIntegerRaw raw            => text raw
    QuantumPatternWildcard                  => "_"
    QuantumPatternQenumVariant path binders => showPathDoc path <+> argumentList (mapDocs showNameDoc binders)

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
binaryOperatorPrecedence op =
  case op of
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
binaryLeftPrecedence op =
  let p = binaryOperatorPrecedence op in
  if p == precCompare then S p else p

binaryRightPrecedence : BinaryOperator -> Nat
binaryRightPrecedence op = S (binaryOperatorPrecedence op)

isBlockBranch : QuantumBranchNode phase -> Bool
isBlockBranch (QuantumBranchBlock _)      = True
isBlockBranch (QuantumBranchExpression _) = False

exprOwnPrecedence : ExpressionNode phase -> Nat
exprOwnPrecedence e =
  case e of
    -- Postfix forms
    ExprCall _ _         => precPostfix
    ExprMethodCall _ _ _ => precPostfix
    ExprField _ _        => precPostfix
    ExprTupleIndex _ _   => precPostfix
    ExprIndex _ _        => precPostfix
    -- Operators
    ExprUnary _ _                     => precUnary
    ExprCast _ _                      => precCast
    ExprBinary (MkAstNode _ _ op) _ _ => binaryOperatorPrecedence op
    ExprRange _ _ _                   => precRange
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
isOperatorClassExpr e =
  case e of
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
leftEdge value =
  case value of
    ExprCall callee _                            => Just (callCalleePrecedence callee.nodeValue, callee)
    ExprMethodCall receiver _ _                  => Just (precPostfix, receiver)
    ExprField object _                           => Just (precPostfix, object)
    ExprIndex object _                           => Just (precPostfix, object)
    ExprTupleIndex object@(MkAstNode _ _ base) _ => Just (tupleIndexBasePrecedence base, object)
    ExprCast operand _                           => Just (precCast, operand)
    ExprBinary (MkAstNode _ _ op) lhs _          => Just (binaryLeftPrecedence op, lhs)
    ExprRange start _ _                          => map (\first => (S precRange, first)) start
    _                                            => Nothing

-- `value` with `child` in place of the child its rendering begins with.
withLeftEdge : ExpressionNode phase -> Expr phase -> ExpressionNode phase
withLeftEdge value child =
  case value of
    ExprCall _ args              => ExprCall child args
    ExprMethodCall _ method args => ExprMethodCall child method args
    ExprField _ field            => ExprField child field
    ExprIndex _ index            => ExprIndex child index
    ExprTupleIndex _ index       => ExprTupleIndex child index
    ExprCast _ ty                => ExprCast child ty
    ExprBinary operator _ rhs    => ExprBinary operator child rhs
    ExprRange (Just _) op end    => ExprRange (Just child) op end
    _                            => value

-- The child an expression's rendering ends with, and the precedence that
-- child is printed at.
rightEdge : ExpressionNode phase -> Maybe (Nat, Expr phase)
rightEdge value =
  case value of
    ExprUnary _ operand                  => Just (precUnary, operand)
    ExprBinary (MkAstNode _ _ op) _ rhs  => Just (binaryRightPrecedence op, rhs)
    ExprRange _ _ end                    => map (\last => (S precRange, last)) end
    ExprReturn returned                  => map (\last => (precLowest, last)) returned
    ExprBreak breakValue                 => map (\last => (precLowest, last)) breakValue
    ExprSIf (MkStateIfNode _ _ elseExpr) => Just (precLowest, elseExpr)
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
endsInValuelessExit value =
  isValuelessExit value ||
  case rightEdge value of
    Nothing         => False
    Just (_, child) => endsInValuelessExit (assert_smaller value child.nodeValue)

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
absorbsFollowing value = exprOwnPrecedence value == precLowest

-- Whether an expression is parenthesized in a position requiring `outerReq`
-- where `follows` holds. Strict style's optional parentheses are left out
-- where they cannot parse.
needsParens : PrettyStyle -> Nat -> Follows -> ExpressionNode phase -> Bool
needsParens style outerReq follows value =
  (exprOwnPrecedence value < outerReq && (isFollowed follows || not (absorbsFollowing value))) ||
  (isPrettyStrict style && isOperatorClassExpr value && not (endsInValuelessExit value))

-- Whether the rendering of an expression, printed in a position requiring
-- `outerReq` where `follows` holds, ends with a node for which `isLast` holds.
-- The right edge inherits `follows`; a parenthesized node ends the walk.
endsWith : (ExpressionNode phase -> Bool) -> PrettyStyle -> Nat -> Follows -> Expr phase -> Bool
endsWith isLast style outerReq follows ast@(MkAstNode _ _ value) =
  not (needsParens style outerReq follows value) &&
  (isLast value ||
   case rightEdge value of
     Nothing                   => False
     Just (requirement, child) => endsWith isLast style requirement follows (assert_smaller ast child))

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
parenthesizeLeadingBlock style outerReq ast@(MkAstNode info metadata value) =
  if needsParens style outerReq Followed value then ast else
  case leftEdge value of
    Just (requirement, child) =>
      MkAstNode info metadata
        (withLeftEdge value (parenthesizeLeadingBlock style requirement (assert_smaller ast child)))
    Nothing =>
      if isBlockLikeExpression value then MkAstNode info metadata (ExprParenthesized ast) else ast

-- A block-like expression on its own is the statement and stays bare.
statementPositionExpr : PrettyStyle -> Expr phase -> Expr phase
statementPositionExpr style ast@(MkAstNode _ _ value) =
  if isBlockLikeExpression value then ast else parenthesizeLeadingBlock style precLowest ast

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
startsNewExpression value =
  case value of
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
ownHeadHazard endsHead structLiteralsAllowed value =
  case value of
    ExprName name         => endsHead && structLiteralsAllowed && readsAsStructLiteralName (prettyName name.nodeValue)
    ExprPath _            => endsHead
    ExprStructLiteral _ _ => not structLiteralsAllowed
    _                     => endsHead && (isRangeWithoutEnd value || isValuelessExit value)

-- Whether a head has a hazard outside brackets it prints itself. `endsHead`
-- holds for the part whose rendering ends the head. A head is followed by its
-- `{`, and so is every node in it.
headHazard :
     PhasePretty phase
  => PrettyStyle -> Nat -> (endsHead : Bool) -> (structLiteralsAllowed : Bool) -> Expr phase -> Bool
headHazard style outerReq endsHead structLiteralsAllowed ast@(MkAstNode _ _ value) =
  not (needsParens style outerReq Followed value) &&
  (ownHeadHazard endsHead structLiteralsAllowed value ||
   inEdge False structLiteralsAllowed (leftEdge value) ||
   inEdge endsHead (structLiteralsAllowed || startsNewExpression value) (rightEdge value))
  where
    inEdge : Bool -> Bool -> Maybe (Nat, Expr phase) -> Bool
    inEdge _ _ Nothing = False
    inEdge childEndsHead childAllows (Just (requirement, child)) =
      headHazard style requirement childEndsHead childAllows (assert_smaller ast child)

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
continuesExpression c = c `elem` ['(', '[', '{', '-', '&', '.']

-- Whether a then-branch, given its rendering's first character, would join
-- the condition or, when `qelse` follows, take it or read it as the bound of
-- an open range. Before `qelse` the branch is delimited: a keyword cannot
-- continue it.
thenBranchAtRisk : PrettyStyle -> (hasElse : Bool) -> Expr phase -> Maybe Char -> Bool
thenBranchAtRisk style hasElse expr first =
  maybe False continuesExpression first ||
  (hasElse && endsWith (\value => isQIfWithoutElse value || isRangeWithoutEnd value) style precLowest Delimited expr)

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
showGuardedExprDoc style follows hazard e =
  if hazard then parens (showExprDoc style e) else showExprAtDoc style precLowest follows e

-- The head of if/while/for/match/qmatch/smatch, directly before a `{`. A qif
-- condition adds its own rule (see `showQuantumConditionDoc`).
showHeadExprDoc : PhasePretty phase => PrettyStyle -> Expr phase -> SourceText
showHeadExprDoc style e = showGuardedExprDoc style Followed (headNeedsParens style e) e

-- An expression starting a statement, a block's final expression or an arm body.
public export
showStatementPositionExprDoc : PhasePretty phase => PrettyStyle -> Expr phase -> SourceText
showStatementPositionExprDoc style e = showExprDoc style (statementPositionExpr style e)

-- An expression followed by a keyword (`then`, `selse`, `=>`), which cannot
-- continue it, except as the upper bound of an open range.
showBeforeKeywordDoc : PhasePretty phase => PrettyStyle -> Expr phase -> SourceText
showBeforeKeywordDoc style e =
  showGuardedExprDoc style Delimited (endsWith isRangeWithoutEnd style precLowest Delimited e) e

------------------------------------------------------------------------------
-- Types (recursive group)
------------------------------------------------------------------------------

mutual
  showTyNodeDoc : PhasePretty phase => PrettyStyle -> TyNode phase (Expr phase) -> SourceText
  showTyNodeDoc style ty =
    case ty of
      TyPrimitive primitive          => text (showTypPrimLeaf primitive)
      TyPath path                    => showPathDoc path
      TyUnit                         => "()"
      TyParenthesized inner          => parens (showTyDoc style inner)
      TyTuple (first ::: rest)       => showTupleLike (MoreDocs (showTyDoc style first) (showTyListDoc style rest))
      TyArray element size           => brackets (showTyDoc style element <+> "; " <+> showExprDoc style size)
      TySlice element                => brackets (showTyDoc style element)
      TyReference (MkAstNode _ _ borrow) inner => showBorrowPrefixed borrow (showTyDoc style inner)
      TyQualified (MkAstNode _ _ qualifier) inner => text (show qualifier) <+> " " <+> showTyDoc style inner
      TyFunction effect params result =>
        locatedModifier effect <+> "fn" <+> argumentList (showFunctionTypeParametersDoc style params) <+>
          -- An explicit case: passing showTyDoc to a helper would hide the recursion.
          (case result of
             Nothing       => ""
             Just resultTy => " -> " <+> showTyDoc style resultTy)

  showTyDoc : PhasePretty phase => PrettyStyle -> Ty phase (Expr phase) -> SourceText
  showTyDoc style (MkAstNode _ _ ty) = showTyNodeDoc style ty

  showTyListDoc : PhasePretty phase => PrettyStyle -> List (Ty phase (Expr phase)) -> SourceDocs
  showTyListDoc style []          = NoDocs
  showTyListDoc style (ty :: tys) = MoreDocs (showTyDoc style ty) (showTyListDoc style tys)

  showFunctionTypeParametersDoc :
       PhasePretty phase
    => PrettyStyle
    -> List (AstNode phase (FunctionTypeParameterNode phase (Expr phase)))
    -> SourceDocs
  showFunctionTypeParametersDoc style [] = NoDocs
  showFunctionTypeParametersDoc style (MkAstNode _ _ (MkFunctionTypeParameterNode name ty) :: rest) =
    MoreDocs (showPlainNameDoc name <+> ": " <+> showTyDoc style ty) (showFunctionTypeParametersDoc style rest)

------------------------------------------------------------------------------
-- Expression parts
------------------------------------------------------------------------------

-- Comma-separated expressions, with a trailing comma when the last one ends in
-- a `return` or `break` without a value: only `;`, `,` or `}` may follow it.
showExprListDoc : PhasePretty phase => PrettyStyle -> List (Expr phase) -> SourceText
showExprListDoc style values =
  commaList (mapDocs (showExprDoc style) values) <+>
    (if maybe False (endsInValuelessExit . nodeValue) (last' values) then "," else "")

showFieldInitializerDoc : PhasePretty phase => PrettyStyle -> AstNode phase (FieldInitializerNode phase) -> SourceText
showFieldInitializerDoc style (MkAstNode _ _ field) =
  case field of
    FieldInitShorthand name      => showNameDoc name
    FieldInitExplicit name value => showNameDoc name <+> ": " <+> showExprDoc style value

showClassicalIfNodeDoc : PhasePretty phase => PrettyStyle -> ClassicalIfNode phase -> SourceText
showClassicalIfNodeDoc style (MkClassicalIfNode condition thenBlock elseBranch) =
  "if " <+> showHeadExprDoc style condition <+> " " <+> showBlockDoc style thenBlock <+>
    (case elseBranch of
       Nothing                                      => ""
       Just (ElseBlock elseBlock)                   => " else " <+> showBlockDoc style elseBlock
       Just (ElseChainedIf (MkAstNode _ _ chained)) => " else " <+> showClassicalIfNodeDoc style chained)

-- See "Quantum if branches": an expression branch for which `atRisk` holds,
-- given the first character of its bare rendering, is printed as a block. A
-- block expression is printed as it is: it reads back as the equivalent block
-- branch.
showQuantumBranchDoc :
     PhasePretty phase
  => PrettyStyle -> Follows -> (atRisk : Expr phase -> Maybe Char -> Bool)
  -> QuantumBranchNode phase -> SourceText
showQuantumBranchDoc style _ _ (QuantumBranchBlock block) = showBlockDoc style block
showQuantumBranchDoc style _ _ (QuantumBranchExpression (MkAstNode _ _ (ExprBlock block))) = showBlockDoc style block
showQuantumBranchDoc style follows atRisk (QuantumBranchExpression expr) =
  let bare : Lazy SourceText = showExprAtDoc style precLowest follows expr in
  if atRisk expr (sourceFirstChar bare)
    then braces (showStatementPositionExprDoc style expr)
    else bare

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
showQuantumElseBranchDoc style follows = showQuantumBranchDoc style follows (\_, first => first == Just '{')

-- The head rules, and a condition ending in a qif without qelse would take
-- the then-branch as its own. The then-branch follows the condition.
showQuantumConditionDoc : PhasePretty phase => PrettyStyle -> Expr phase -> SourceText
showQuantumConditionDoc style condition =
  showGuardedExprDoc style Followed
    (headNeedsParens style condition || endsWith isQIfWithoutElse style precLowest Followed condition)
    condition

showClassicalMatchArmNodeDoc : PhasePretty phase => PrettyStyle -> ClassicalMatchArmNode phase -> SourceText
showClassicalMatchArmNodeDoc style (MkClassicalMatchArmNode pattern guard body) =
  showPatternDoc pattern <+> optionalText " if " (showBeforeKeywordDoc style) guard <+>
    " => " <+> showStatementPositionExprDoc style body

showClassicalMatchArmDoc : PhasePretty phase => PrettyStyle -> ClassicalMatchArm phase -> SourceText
showClassicalMatchArmDoc style (MkAstNode _ _ arm) = showClassicalMatchArmNodeDoc style arm

showQuantumMatchArmNodeDoc : PhasePretty phase => PrettyStyle -> QuantumMatchArmNode phase -> SourceText
showQuantumMatchArmNodeDoc style (MkQuantumMatchArmNode pattern body) =
  showQuantumMatchPatternDoc pattern <+> " => " <+> showStatementPositionExprDoc style body

showQuantumMatchArmDoc : PhasePretty phase => PrettyStyle -> QuantumMatchArm phase -> SourceText
showQuantumMatchArmDoc style (MkAstNode _ _ arm) = showQuantumMatchArmNodeDoc style arm

-- `<keyword> <head> { arm, arm }` for match, qmatch and smatch.
showMatchLikeDoc : PhasePretty phase => PrettyStyle -> SourceText -> Expr phase -> SourceDocs -> SourceText
showMatchLikeDoc style keyword scrutinee arms =
  keyword <+> " " <+> showHeadExprDoc style scrutinee <+> " " <+> braces (commaList arms)

showControlExprDoc : PhasePretty phase => PrettyStyle -> ControlExpressionNode phase -> SourceText
showControlExprDoc style control =
  case control of
    ControlledCallable controls basis callable =>
      controlPrefix controls basis <+> ".apply" <+> parens (showExprDoc style callable)
    ControlledBlock controls basis body =>
      controlPrefix controls basis <+> " " <+> showBlockDoc style body
  where
    controlPrefix : List1 (Expr phase) -> Maybe (AstNode phase String) -> SourceText
    controlPrefix controls basis =
      "ctrl" <+> parens (showExprListDoc style (forget controls)) <+> showOnBasisDoc basis

showAdjointExprDoc : PhasePretty phase => PrettyStyle -> AdjointExpressionNode phase -> SourceText
showAdjointExprDoc style (AdjointOfCallable callable) = "adjoint" <+> parens (showExprDoc style callable)
showAdjointExprDoc style (AdjointBlock body)          = "adjoint " <+> showBlockDoc style body

------------------------------------------------------------------------------
-- Expressions
------------------------------------------------------------------------------

-- `follows`: whether something that could continue this rendering follows it,
-- inside any parentheses of its own. Its right edge inherits it; its other
-- children are followed by the rest of the rendering, or are delimited.
showExpressionNodeBodyDoc : PhasePretty phase => PrettyStyle -> Follows -> ExpressionNode phase -> SourceText
showExpressionNodeBodyDoc style follows value =
  case value of
    ExprLiteral literal => showLiteralDoc literal
    ExprName name       => showNameDoc name
    ExprPath path       => showPathDoc path
    ExprBuiltin builtin => text (show builtin)
    ExprSelf _          => "self"

    ExprParenthesized inner      => parens (showExprDoc style inner)
    ExprTuple (only ::: [])      => showTupleLike (MoreDocs (showExprDoc style only) NoDocs)
    ExprTuple (first ::: rest)   => parens (showExprListDoc style (first :: rest))
    ExprArray elements           => brackets (showExprListDoc style elements)
    ExprRepeatedArray element count =>
      brackets (showExprDoc style element <+> "; " <+> showExprDoc style count)
    ExprStructLiteral path fields =>
      showPathDoc path <+> " " <+> braces (commaList (mapDocs (showFieldInitializerDoc style) fields))

    ExprCall callee args =>
      showExprAtDoc style (callCalleePrecedence callee.nodeValue) Followed callee <+>
        parens (showExprListDoc style args)
    ExprMethodCall receiver method args =>
      showExprAtDoc style precPostfix Followed receiver <+> "." <+> showMemberNameDoc method <+>
        parens (showExprListDoc style args)
    ExprField object field =>
      showExprAtDoc style precPostfix Followed object <+> "." <+> showMemberNameDoc field
    ExprTupleIndex object@(MkAstNode _ _ base) index =>
      showExprAtDoc style (tupleIndexBasePrecedence base) Followed object <+> "." <+> text index
    ExprIndex object index =>
      showExprAtDoc style precPostfix Followed object <+> brackets (showExprDoc style index)

    ExprUnary (MkAstNode _ _ op) operand =>
      let operandText : Lazy SourceText = showExprAtDoc style precUnary follows operand in
      case op of
        UnaryNegate     => prefixOperator '-' operandText
        UnaryLogicalNot => "!" <+> operandText
        UnaryBorrow b   => showBorrowPrefixed b operandText
    ExprBinary (MkAstNode _ _ op) lhs rhs =>
      showExprAtDoc style (binaryLeftPrecedence op) Followed lhs <+> " " <+> text (show op) <+> " " <+>
        showExprAtDoc style (binaryRightPrecedence op) follows rhs
    ExprRange start (MkAstNode _ _ op) end =>
      optionalText "" (showExprAtDoc style (S precRange) Followed) start <+> text (show op) <+>
        optionalText "" (showExprAtDoc style (S precRange) follows) end
    ExprCast operand ty =>
      showExprAtDoc style precCast Followed operand <+> " as " <+> showTyDoc style ty

    ExprBlock block   => showBlockDoc style block
    ExprIf ifNode     => showClassicalIfNodeDoc style ifNode
    ExprQIf (MkQuantumIfNode condition thenBranch elseBranch) =>
      "qif " <+> showQuantumConditionDoc style condition <+> " " <+>
        showQuantumThenBranchDoc style follows elseBranch thenBranch <+>
        optionalText " qelse " (showQuantumElseBranchDoc style follows) elseBranch
    ExprSIf (MkStateIfNode condition thenExpr elseExpr) =>
      "sif " <+> showBeforeKeywordDoc style condition <+> " then " <+> showBeforeKeywordDoc style thenExpr <+>
        " selse " <+> showExprAtDoc style precLowest follows elseExpr
    ExprMatch (MkClassicalMatchNode scrutinee arms) =>
      showMatchLikeDoc style "match" scrutinee (mapDocs (showClassicalMatchArmDoc style) arms)
    ExprQMatch (MkQuantumMatchNode scrutinee arms) =>
      showMatchLikeDoc style "qmatch" scrutinee (mapDocs (showQuantumMatchArmDoc style) arms)
    ExprSMatch (MkStateMatchNode scrutinee arms) =>
      showMatchLikeDoc style "smatch" scrutinee (mapDocs (showQuantumMatchArmDoc style) arms)
    ExprLoop body => "loop " <+> showBlockDoc style body
    ExprWhile condition body =>
      "while " <+> showHeadExprDoc style condition <+> " " <+> showBlockDoc style body
    ExprFor pattern iterable body =>
      "for " <+> showPatternDoc pattern <+> " in " <+> showHeadExprDoc style iterable <+> " " <+>
        showBlockDoc style body

    ExprBreak breakValue => "break" <+> optionalText " " (showExprAtDoc style precLowest follows) breakValue
    ExprContinue       => "continue"
    ExprReturn returned  => "return" <+> optionalText " " (showExprAtDoc style precLowest follows) returned

    ExprCtrl control   => showControlExprDoc style control
    ExprAdjoint adjoint => showAdjointExprDoc style adjoint

-- Decides on an expression's parentheses from its precedence and what follows
-- it. The `assert_total` breaks the cycle expression -> sub-expression; every
-- recursive call is on a subterm.
wrapExprDoc : PhasePretty phase => PrettyStyle -> Nat -> Follows -> ExpressionNode phase -> SourceText
wrapExprDoc style outerReq follows value =
  let parenthesized = needsParens style outerReq follows value
      -- Inside parentheses, the closing `)` ends the expression.
      inside = if parenthesized then Delimited else follows
      body : Lazy SourceText = assert_total $ showExpressionNodeBodyDoc style inside value
  in if parenthesized then parens body else body

showExprAtDoc style outerReq follows (MkAstNode _ _ value) = wrapExprDoc style outerReq follows value

-- Unconstrained rendering of a raw ExpressionNode, for the Show instance.
showExpressionNodeDoc : PhasePretty phase => PrettyStyle -> ExpressionNode phase -> SourceText
showExpressionNodeDoc style = wrapExprDoc style precLowest Delimited

------------------------------------------------------------------------------
-- Blocks and statements
------------------------------------------------------------------------------

showAssignmentTargetNodeDoc : PhasePretty phase => PrettyStyle -> AssignmentTargetNode phase -> SourceText
showAssignmentTargetNodeDoc style target =
  case target of
    AssignTargetName name          => showNameDoc name
    AssignTargetIndex object index => objectDoc precPostfix object <+> brackets (showExprDoc style index)
    AssignTargetField object field => objectDoc precPostfix object <+> "." <+> showMemberNameDoc field
    AssignTargetTupleIndex object@(MkAstNode _ _ base) index =>
      objectDoc (tupleIndexBasePrecedence base) object <+> "." <+> text index
  where
    -- The object before `[`, `.` or `.<digits>`, which starts the statement.
    objectDoc : Nat -> Expr phase -> SourceText
    objectDoc requirement object =
      showExprAtDoc style requirement Followed (parenthesizeLeadingBlock style requirement object)

showAssignmentTargetDoc : PhasePretty phase => PrettyStyle -> AssignmentTarget phase -> SourceText
showAssignmentTargetDoc style (MkAstNode _ _ target) = showAssignmentTargetNodeDoc style target

showAssignmentNodeDoc : PhasePretty phase => PrettyStyle -> AssignmentNode phase -> SourceText
showAssignmentNodeDoc style (MkAssignmentNode (MkAstNode _ _ target) (MkAstNode _ _ op) value) =
  showAssignmentTargetNodeDoc style target <+> " " <+> text (show op) <+> " " <+> showExprDoc style value

showLetBindingNodeDoc : PhasePretty phase => PrettyStyle -> LetBindingNode phase -> SourceText
showLetBindingNodeDoc style (MkLetBindingNode qualifiers pattern annotation initializer) =
  "let " <+> showQualifiersPrefixDoc qualifiers <+> showPatternDoc pattern <+>
    optionalText ": " (showTyDoc style) annotation <+> optionalText " " showInitializerDoc initializer
  where
    showInitializerDoc : LetInitializerNode phase -> SourceText
    showInitializerDoc (MkLetInitializerNode (MkAstNode _ _ marker) value) =
      text (show marker) <+> " " <+> showExprDoc style value

showLetBindingDoc : PhasePretty phase => PrettyStyle -> LetBinding phase -> SourceText
showLetBindingDoc style (MkAstNode _ _ binding) = showLetBindingNodeDoc style binding

showStatementNodeDoc : PhasePretty phase => PrettyStyle -> StatementNode phase -> SourceText
showStatementNodeDoc style statement =
  case statement of
    StatementLet binding         => showLetBindingNodeDoc style binding <+> ";"
    StatementAssignment assigned => showAssignmentNodeDoc style assigned <+> ";"
    StatementSemiExpression e    => showStatementPositionExprDoc style e <+> ";"
    StatementExpression e        => showStatementPositionExprDoc style e

public export
showStatementDoc : PhasePretty phase => PrettyStyle -> Statement phase -> SourceText
showStatementDoc style (MkAstNode _ _ statement) = showStatementNodeDoc style statement

showBlockNodeDoc : PhasePretty phase => PrettyStyle -> BlockNode phase -> SourceText
showBlockNodeDoc style (MkBlockNode innerDocs statements final) =
  braces (docsPrefix innerDocs <+> joinWith " " (appendDocs (mapDocs (showStatementDoc style) statements) finalText))
  where
    finalText : SourceDocs
    finalText = case final of
      Nothing => NoDocs
      Just e  => MoreDocs (showStatementPositionExprDoc style e) NoDocs

showBlockDoc style (MkAstNode _ _ block) = showBlockNodeDoc style block

--------------------------------------------------------------------------------
-- Contracts
--------------------------------------------------------------------------------

showContractPredicateNodeDoc :
  PhasePretty phase => PrettyStyle -> ContractPredicateNode phase (Expr phase) -> SourceText
showContractPredicateNodeDoc style predicate =
  case predicate of
    ContractClean e              => "clean" <+> parens (showExprListDoc style [e])
    ContractBasis e pauli        =>
      "basis" <+> argumentList (MoreDocs (showExprDoc style e) (MoreDocs (showPauliStringDoc pauli) NoDocs))
    ContractSeparable e          => "separable" <+> parens (showExprListDoc style [e])
    ContractIsolated e           => "isolated" <+> parens (showExprListDoc style [e])
    ContractProduct first others => "product" <+> parens (showExprListDoc style (first :: forget others))
    ContractStabilized e terms   =>
      "stabilized" <+> argumentList
        (MoreDocs (showExprDoc style e)
          (MoreDocs (brackets (commaList (mapDocs showSignedPauliTermDoc (forget terms)))) NoDocs))

showContractPredicateDoc : PhasePretty phase => PrettyStyle -> ContractPredicate phase (Expr phase) -> SourceText
showContractPredicateDoc style (MkAstNode _ _ predicate) = showContractPredicateNodeDoc style predicate

showContractClauseNodeDoc : PhasePretty phase => PrettyStyle -> ContractClauseNode phase (Expr phase) -> SourceText
showContractClauseNodeDoc style (RequiresClause predicate) = "requires " <+> showContractPredicateDoc style predicate
showContractClauseNodeDoc style (EnsuresClause predicate)  = "ensures " <+> showContractPredicateDoc style predicate

showContractClauseDoc : PhasePretty phase => PrettyStyle -> ContractClause phase (Expr phase) -> SourceText
showContractClauseDoc style (MkAstNode _ _ clause) = showContractClauseNodeDoc style clause

--------------------------------------------------------------------------------
-- Functions
--------------------------------------------------------------------------------

showFunctionParameterNodeDoc : PhasePretty phase => PrettyStyle -> FunctionParameterNode phase -> SourceText
showFunctionParameterNodeDoc style parameter =
  case parameter of
    NormalParameter docs mutability name ty =>
      docsPrefix docs <+> locatedModifier mutability <+> showNameDoc name <+> ": " <+> showTyDoc style ty
    ReceiverParameter docs Nothing => docsPrefix docs <+> "self"
    ReceiverParameter docs (Just (MkAstNode _ _ borrow)) => docsPrefix docs <+> showBorrowPrefixed borrow "self"

showFunctionParameterDoc : PhasePretty phase => PrettyStyle -> FunctionParameter phase -> SourceText
showFunctionParameterDoc style (MkAstNode _ _ parameter) = showFunctionParameterNodeDoc style parameter

showFunctionDeclarationNodeDoc : PhasePretty phase => PrettyStyle -> FunctionDeclarationNode phase -> SourceText
showFunctionDeclarationNodeDoc style
    (MkFunctionDeclarationNode docs attrs visibility constness effect name params result supports contracts body) =
  docsPrefix docs <+> attrsPrefix attrs <+>
    locatedModifier visibility <+> locatedModifier constness <+> locatedModifier effect <+>
    "fn " <+> showNameDoc name <+> argumentList (mapDocs (showFunctionParameterDoc style) params) <+>
    optionalText " -> " (showTyDoc style) result <+>
    supportsText <+>
    concatDocs (\clause => " " <+> showContractClauseDoc style clause) contracts <+>
    " " <+> showBlockDoc style body
  where
    supportsText : SourceText
    supportsText = case supports of
      [] => ""
      _  => " supports " <+> commaList (mapDocs (text . show . nodeValue) supports)

public export
showFunctionDeclarationDoc : PhasePretty phase => PrettyStyle -> FunctionDeclaration phase -> SourceText
showFunctionDeclarationDoc style (MkAstNode _ _ function) = showFunctionDeclarationNodeDoc style function

--------------------------------------------------------------------------------
-- struct, enum, qenum, impl, const and use declarations
--------------------------------------------------------------------------------

-- Docs, attributes, visibility and `<keyword> <name>`: the common head of a
-- type declaration.
declarationHeadDoc :
     PhasePretty phase
  => List (DocComment phase) -> List (Attribute phase) -> Maybe (AstNode phase VisibilityQualifier)
  -> SourceText -> Name phase -> SourceText
declarationHeadDoc docs attrs visibility keyword name =
  docsPrefix docs <+> attrsPrefix attrs <+> locatedModifier visibility <+> keyword <+> " " <+> showNameDoc name

showStructFieldDoc : PhasePretty phase => PrettyStyle -> AstNode phase (StructFieldNode phase) -> SourceText
showStructFieldDoc style (MkAstNode _ _ (MkStructFieldNode docs name ty)) =
  docsPrefix docs <+> showNameDoc name <+> ": " <+> showTyDoc style ty

showStructFieldsDoc : PhasePretty phase => PrettyStyle -> List (AstNode phase (StructFieldNode phase)) -> SourceText
showStructFieldsDoc style fields = braces (commaList (mapDocs (showStructFieldDoc style) fields))

showStructDeclarationNodeDoc : PhasePretty phase => PrettyStyle -> StructDeclarationNode phase -> SourceText
showStructDeclarationNodeDoc style (MkStructDeclarationNode docs attrs visibility name fields) =
  declarationHeadDoc docs attrs visibility "struct" name <+> " " <+> showStructFieldsDoc style fields

showStructDeclarationDoc : PhasePretty phase => PrettyStyle -> StructDeclaration phase -> SourceText
showStructDeclarationDoc style (MkAstNode _ _ declaration) = showStructDeclarationNodeDoc style declaration

showEnumVariantDoc : PhasePretty phase => PrettyStyle -> AstNode phase (EnumVariantNode phase) -> SourceText
showEnumVariantDoc style (MkAstNode _ _ (MkEnumVariantNode docs name body)) =
  docsPrefix docs <+> showNameDoc name <+>
    (case body of
       VariantUnit          => ""
       VariantTuple types   => argumentList (mapDocs (showTyDoc style) (forget types))
       VariantStruct fields => " " <+> showStructFieldsDoc style fields)

showEnumDeclarationNodeDoc : PhasePretty phase => PrettyStyle -> EnumDeclarationNode phase -> SourceText
showEnumDeclarationNodeDoc style (MkEnumDeclarationNode docs attrs visibility name variants) =
  declarationHeadDoc docs attrs visibility "enum" name <+> " " <+>
    braces (commaList (mapDocs (showEnumVariantDoc style) variants))

showEnumDeclarationDoc : PhasePretty phase => PrettyStyle -> EnumDeclaration phase -> SourceText
showEnumDeclarationDoc style (MkAstNode _ _ declaration) = showEnumDeclarationNodeDoc style declaration

showQEnumVariantDoc : PhasePretty phase => PrettyStyle -> AstNode phase (QEnumVariantNode phase) -> SourceText
showQEnumVariantDoc style (MkAstNode _ _ (MkQEnumVariantNode docs name payload)) =
  docsPrefix docs <+> showNameDoc name <+> argumentList (mapDocs (showTyDoc style) (forget payload))

showQEnumDeclarationNodeDoc : PhasePretty phase => PrettyStyle -> QEnumDeclarationNode phase -> SourceText
showQEnumDeclarationNodeDoc style (MkQEnumDeclarationNode docs attrs visibility name variants) =
  declarationHeadDoc docs attrs visibility "qenum" name <+> " " <+>
    braces (commaList (mapDocs (showQEnumVariantDoc style) variants))

showQEnumDeclarationDoc : PhasePretty phase => PrettyStyle -> QEnumDeclaration phase -> SourceText
showQEnumDeclarationDoc style (MkAstNode _ _ declaration) = showQEnumDeclarationNodeDoc style declaration

showImplDeclarationNodeDoc : PhasePretty phase => PrettyStyle -> ImplDeclarationNode phase -> SourceText
showImplDeclarationNodeDoc style (MkImplDeclarationNode docs target functions) =
  docsPrefix docs <+> "impl " <+> showPathDoc target <+> " " <+>
    braces (joinWith " " (mapDocs (showFunctionDeclarationDoc style) functions))

showImplDeclarationDoc : PhasePretty phase => PrettyStyle -> ImplDeclaration phase -> SourceText
showImplDeclarationDoc style (MkAstNode _ _ declaration) = showImplDeclarationNodeDoc style declaration

showConstDeclarationNodeDoc : PhasePretty phase => PrettyStyle -> ConstDeclarationNode phase -> SourceText
showConstDeclarationNodeDoc style (MkConstDeclarationNode docs visibility name ty value) =
  declarationHeadDoc docs [] visibility "const" name <+> ": " <+> showTyDoc style ty <+>
    " = " <+> showExprDoc style value <+> ";"

showConstDeclarationDoc : PhasePretty phase => PrettyStyle -> ConstDeclaration phase -> SourceText
showConstDeclarationDoc style (MkAstNode _ _ declaration) = showConstDeclarationNodeDoc style declaration

showUseDeclarationNodeDoc : PhasePretty phase => PrettyStyle -> UseDeclarationNode phase -> SourceText
showUseDeclarationNodeDoc style (MkUseDeclarationNode docs visibility path alias) =
  docsPrefix docs <+> locatedModifier visibility <+> "use " <+> showPathDoc path <+>
    optionalText " as " showPlainNameDoc alias <+> ";"

showUseDeclarationDoc : PhasePretty phase => PrettyStyle -> UseDeclaration phase -> SourceText
showUseDeclarationDoc style (MkAstNode _ _ declaration) = showUseDeclarationNodeDoc style declaration

--------------------------------------------------------------------------------
-- Modules and items (recursive group, through inline module bodies)
--------------------------------------------------------------------------------

mutual
  showModuleDeclarationNodeDoc : PhasePretty phase => PrettyStyle -> ModuleDeclarationNode phase -> SourceText
  showModuleDeclarationNodeDoc style (MkModuleDeclarationNode docs visibility name body) =
    declarationHeadDoc docs [] visibility "mod" name <+>
      (case body of
         ModuleInline innerDocs items =>
           " " <+> braces (docsPrefix innerDocs <+> joinWith "\n" (showItemListDoc style items))
         ModuleExternal               => ";")

  showItemNodeDoc : PhasePretty phase => PrettyStyle -> ItemNode phase -> SourceText
  showItemNodeDoc style item =
    case item of
      ItemFunction declaration => showFunctionDeclarationNodeDoc style declaration
      ItemStruct declaration   => showStructDeclarationNodeDoc style declaration
      ItemEnum declaration     => showEnumDeclarationNodeDoc style declaration
      ItemQEnum declaration    => showQEnumDeclarationNodeDoc style declaration
      ItemImpl declaration     => showImplDeclarationNodeDoc style declaration
      ItemConst declaration    => showConstDeclarationNodeDoc style declaration
      ItemUse declaration      => showUseDeclarationNodeDoc style declaration
      ItemModule declaration   => showModuleDeclarationNodeDoc style declaration

  export
  showItemDoc : PhasePretty phase => PrettyStyle -> Item phase -> SourceText
  showItemDoc style (MkAstNode _ _ item) = showItemNodeDoc style item

  showItemListDoc : PhasePretty phase => PrettyStyle -> List (Item phase) -> SourceDocs
  showItemListDoc style []              = NoDocs
  showItemListDoc style (item :: items) = MoreDocs (showItemDoc style item) (showItemListDoc style items)

showModuleDeclarationDoc : PhasePretty phase => PrettyStyle -> ModuleDeclaration phase -> SourceText
showModuleDeclarationDoc style (MkAstNode _ _ declaration) = showModuleDeclarationNodeDoc style declaration

showSourceFileNodeDoc : PhasePretty phase => PrettyStyle -> SourceFileNode phase -> SourceText
showSourceFileNodeDoc style (MkSourceFileNode innerDocs items) =
  joinWith "\n" (appendDocs (mapDocs showDocCommentDoc innerDocs) (showItemListDoc style items))

showSourceFileDoc : PhasePretty phase => PrettyStyle -> SourceFile phase -> SourceText
showSourceFileDoc style (MkAstNode _ _ sourceFile) = showSourceFileNodeDoc style sourceFile

--------------------------------------------------------------------------------
-- String printers: one per syntactic category, for diagnostics and tests.
--------------------------------------------------------------------------------

public export
showPattern : PhasePretty phase => Pattern phase -> String
showPattern value = renderSource (showPatternDoc value)

public export
showQuantumMatchPattern : PhasePretty phase => QuantumMatchPattern phase -> String
showQuantumMatchPattern value = renderSource (showQuantumMatchPatternDoc value)

public export
showBlock : PhasePretty phase => PrettyStyle -> Block phase -> String
showBlock style value = renderSource (showBlockDoc style value)

public export
showExpr : PhasePretty phase => PrettyStyle -> Expr phase -> String
showExpr style value = renderSource (showExprDoc style value)

public export
showTy : PhasePretty phase => PrettyStyle -> Ty phase (Expr phase) -> String
showTy style value = renderSource (showTyDoc style value)

public export
showClassicalMatchArm : PhasePretty phase => PrettyStyle -> ClassicalMatchArm phase -> String
showClassicalMatchArm style value = renderSource (showClassicalMatchArmDoc style value)

public export
showQuantumMatchArm : PhasePretty phase => PrettyStyle -> QuantumMatchArm phase -> String
showQuantumMatchArm style value = renderSource (showQuantumMatchArmDoc style value)

public export
showAssignmentTarget : PhasePretty phase => PrettyStyle -> AssignmentTarget phase -> String
showAssignmentTarget style value = renderSource (showAssignmentTargetDoc style value)

public export
showLetBinding : PhasePretty phase => PrettyStyle -> LetBinding phase -> String
showLetBinding style value = renderSource (showLetBindingDoc style value)

public export
showStatement : PhasePretty phase => PrettyStyle -> Statement phase -> String
showStatement style value = renderSource (showStatementDoc style value)

public export
showContractPredicate : PhasePretty phase => PrettyStyle -> ContractPredicate phase (Expr phase) -> String
showContractPredicate style value = renderSource (showContractPredicateDoc style value)

public export
showContractClause : PhasePretty phase => PrettyStyle -> ContractClause phase (Expr phase) -> String
showContractClause style value = renderSource (showContractClauseDoc style value)

public export
showFunctionParameter : PhasePretty phase => PrettyStyle -> FunctionParameter phase -> String
showFunctionParameter style value = renderSource (showFunctionParameterDoc style value)

public export
showFunctionDeclaration : PhasePretty phase => PrettyStyle -> FunctionDeclaration phase -> String
showFunctionDeclaration style value = renderSource (showFunctionDeclarationDoc style value)

public export
showStructDeclaration : PhasePretty phase => PrettyStyle -> StructDeclaration phase -> String
showStructDeclaration style value = renderSource (showStructDeclarationDoc style value)

public export
showEnumDeclaration : PhasePretty phase => PrettyStyle -> EnumDeclaration phase -> String
showEnumDeclaration style value = renderSource (showEnumDeclarationDoc style value)

public export
showQEnumDeclaration : PhasePretty phase => PrettyStyle -> QEnumDeclaration phase -> String
showQEnumDeclaration style value = renderSource (showQEnumDeclarationDoc style value)

public export
showImplDeclaration : PhasePretty phase => PrettyStyle -> ImplDeclaration phase -> String
showImplDeclaration style value = renderSource (showImplDeclarationDoc style value)

public export
showConstDeclaration : PhasePretty phase => PrettyStyle -> ConstDeclaration phase -> String
showConstDeclaration style value = renderSource (showConstDeclarationDoc style value)

public export
showUseDeclaration : PhasePretty phase => PrettyStyle -> UseDeclaration phase -> String
showUseDeclaration style value = renderSource (showUseDeclarationDoc style value)

public export
showItem : PhasePretty phase => PrettyStyle -> Item phase -> String
showItem style value = renderSource (showItemDoc style value)

public export
showModuleDeclaration : PhasePretty phase => PrettyStyle -> ModuleDeclaration phase -> String
showModuleDeclaration style value = renderSource (showModuleDeclarationDoc style value)

public export
showSourceFile : PhasePretty phase => PrettyStyle -> SourceFile phase -> String
showSourceFile style value = renderSource (showSourceFileDoc style value)

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
