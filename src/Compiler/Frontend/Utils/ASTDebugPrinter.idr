module Compiler.Frontend.Utils.ASTDebugPrinter

import Data.List1
import Data.Maybe
import Data.String
import Text.ILex
import Text.ILex.RExp.Unicode as Unicode
import Text.ILex.State.Regular

import Compiler.Frontend.ASTData
import Compiler.Frontend.ASTPhases
import Compiler.Frontend.Source
import Compiler.Frontend.Token
import Compiler.Frontend.Syntax.AST
import Compiler.Frontend.Syntax.Attribute
import Compiler.Frontend.Syntax.Common
import Compiler.Frontend.Syntax.Contract
import Compiler.Frontend.Syntax.Doc
import Compiler.Frontend.Syntax.Literal
import Compiler.Frontend.Syntax.Name
import Compiler.Frontend.Syntax.Operator
import Compiler.Frontend.Syntax.Pattern
import Compiler.Frontend.Syntax.Type
import Compiler.Frontend.Utils.SourceText
import Compiler.Frontend.Utils.ASTPrettyPrinter

--------------------------------------------------------------------------------
-- Structural AST dump: one line per located node, children indented below.
--
--   phase=<phase> file=<file>
--   <node> [> <node>...] @<span> [`snippet`]
--   where <node> = #<surfaceId>[.<desugarId>] <Label> [payload...] [sym=<id>] [[provenance]]
--
-- * A node whose only child covers the same span shares its line: in
--   `#12 ExprName > #13 Name H @10:5-6`, Name is the only child of ExprName
--   and the span belongs to both. Children of the last node on a line are
--   indented below it, and a snippet belongs to the first. `[same]` marks a
--   node whose provenance is that of the node before it on the line.
-- * The desugar component of an ID is shown only when it is not 0.
-- * Spans are half-open, `line:col-col` on one line or `line:col-line:col`;
--   the file is printed once on the first line and repeated on a span only if
--   it differs.
-- * Provenance is shown only for compiler-generated nodes, never for
--   user-written ones.
-- * Labels are constructor names. Located tokens (operators, qualifiers,
--   effects, ...) are labelled by their type, with their Leaf spelling as
--   payload. Names, member names and paths are labelled `Name`, `MemberName`
--   and `Path`; plain names that never resolve are `MkNameNode`.
-- * Items, statements and block-final expressions carry their strict source
--   rendering, limited while it is produced so previews do not render whole
--   subtrees. An item's snippet starts at its head: its outer docs and
--   attributes are listed as its children. Indentation and full leaf payloads still
--   contribute to dump size.
-- * Backslashes, backticks, control characters and invisible format
--   characters (zero-width, bidirectional) in payloads and snippets are shown
--   escaped: `\n`, `\x1b`, `\u{202e}`. Payloads also escape `#`, so every bare
--   `#` before the span starts a node.
--
-- Constructor matches are exhaustive so new syntax cannot silently disappear
-- from the dump. Children are listed in source order.
--------------------------------------------------------------------------------
%default covering

--------------------------------------------------------------------------------
-- Phase-specific information
--------------------------------------------------------------------------------

-- Phases are erased from AstNode, so a dictionary supplies what differs
-- between them: provenance from the canonical phase on, symbols from
-- resolution on, and member symbols only after type checking.
public export
interface PhasePretty phase => PhaseDebug phase where
  phaseLabel : String
  nodeProvenance : MetadataFor phase -> Maybe NodeProvenance
  nameSymbol : NameFor phase -> Maybe SymbolId
  memberSymbol : MemberNameFor phase -> Maybe SymbolId
  selfSymbol : SelfFor phase -> Maybe SymbolId
  -- Segment nodes until resolution collapses a path into its target symbol.
  pathParts : PathFor phase -> (List (PathSegment phase), Maybe SymbolId)

public export
PhaseDebug SurfaceAstPhase where
  phaseLabel = "surface"
  nodeProvenance _ = Nothing
  nameSymbol _ = Nothing
  memberSymbol _ = Nothing
  selfSymbol _ = Nothing
  pathParts (MkPathNode first rest) = (first :: rest, Nothing)

public export
PhaseDebug CanonicalAstPhase where
  phaseLabel = "canonical"
  nodeProvenance metadata = Just metadata.provenance
  nameSymbol _ = Nothing
  memberSymbol _ = Nothing
  selfSymbol _ = Nothing
  pathParts (MkPathNode first rest) = (first :: rest, Nothing)

public export
PhaseDebug ResolvedAstPhase where
  phaseLabel = "resolved"
  nodeProvenance metadata = Just metadata.provenance
  nameSymbol name = Just name.nameNodeSymbolId
  memberSymbol _ = Nothing
  selfSymbol symbol = Just symbol
  pathParts path = ([], Just path.referencedSymbolId)

public export
PhaseDebug TypedAstPhase where
  phaseLabel = "typed"
  nodeProvenance metadata = Just metadata.provenance
  nameSymbol name = Just name.nameNodeSymbolId
  memberSymbol name = Just name.nameNodeSymbolId
  selfSymbol symbol = Just symbol
  pathParts path = ([], Just path.referencedSymbolId)

--------------------------------------------------------------------------------
-- Line text
--------------------------------------------------------------------------------

||| Maximum escaped preview length. Source rendering stops after the prefix;
||| no complete subtree strings are retained in the debug tree.
export
snippetLimit : Nat
snippetLimit = 60

hexDigit : Int -> Char
hexDigit digit = chr (if digit < 10 then ord '0' + digit else ord 'a' + digit - 10)

hexText : Int -> List Char
hexText code = (if code >= 16 then hexText (code `div` 16) else []) ++ [hexDigit (code `mod` 16)]

-- Use the lexer's Unicode category data for all format characters (Cf),
-- including supplementary code points, plus line and paragraph separators.
invisibleFormatValidator : PVal1 q Void ()
invisibleFormatValidator = value Nothing
  [ (Unicode.format, const ())
  , (Unicode.lineSeparator, const ())
  , (Unicode.paragraphSeparator, const ())
  ]

isInvisibleFormat : Char -> Bool
isInvisibleFormat c =
  -- The first format character is U+00AD; ordinary ASCII needs no lookup.
  ord c >= 0xAD && case runString invisibleFormatValidator (singleton c) of
    Right () => True
    Left _ => False

-- Escape the escape character itself so literal `\n` stays distinguishable
-- from a newline. Controls and invisible format characters cannot affect how
-- the dump is displayed, and backticks cannot be mistaken for snippet
-- delimiters.
escapeSourceChar : Char -> List Char
escapeSourceChar '\\' = ['\\', '\\']
escapeSourceChar '`' = ['\\', '`']
escapeSourceChar '\n' = ['\\', 'n']
escapeSourceChar '\r' = ['\\', 'r']
escapeSourceChar '\t' = ['\\', 't']
escapeSourceChar c =
  let code = ord c in
  if code < 32 || (code >= 127 && code <= 159)
    then ['\\', 'x', hexDigit (code `div` 16), hexDigit (code `mod` 16)]
    else if isInvisibleFormat c then unpack "\\u{" ++ hexText code ++ ['}']
    else [c]

-- Payloads also escape `#`: a bare `#` always starts a node, so no payload can
-- imitate the ` > #` that joins nodes sharing a line. Snippets, which follow
-- the span inside backticks, keep `#` as written.
escapeChar : Char -> List Char
escapeChar '#' = ['\\', '#']
escapeChar c   = escapeSourceChar c

escape : String -> String
escape = pack . concatMap escapeChar . unpack

nodeIdText : NodeId -> String
nodeIdText (MkNodeId surfaceId Z)         = show surfaceId
nodeIdText (MkNodeId surfaceId desugarId) = show surfaceId ++ "." ++ show desugarId

positionText : SourcePos -> String
positionText position = show position.line ++ ":" ++ show position.column

-- `rootFile` is the file named on the first line of the dump.
spanText : String -> SourceSpan -> String
spanText rootFile span =
  (if span.file == rootFile then "" else escape span.file ++ ":") ++
  positionText span.start ++ "-" ++
  (if span.end.line == span.start.line then show span.end.column else positionText span.end)

provenanceText : Maybe NodeProvenance -> String
provenanceText (Just WrittenCode) = ""
provenanceText (Just origin)      = "[" ++ show origin ++ "]"
provenanceText Nothing            = ""

-- The stored preview is already escaped and bounded during tree construction.
snippetText : String -> String
snippetText preview = " `" ++ preview ++ "`"

symbolText : Maybe SymbolId -> String
symbolText = maybe "" (\symbol => "sym=" ++ show symbol.id)

-- Present only when the flag holds: `args` and `guarded`.
flagText : String -> Bool -> String
flagText flag present = if present then flag else ""

--------------------------------------------------------------------------------
-- Tree building
--------------------------------------------------------------------------------
-- Every renderer turns the AST piece it is given into a Forest of DebugTrees,
-- in source order; `showAstDebug` lays the final tree out as text. A node is a
-- tree of its children; `group`, `many` and `optional` collect siblings.
--------------------------------------------------------------------------------

record DebugTree where
  constructor MkDebugTree
  heading    : String       -- `#<id> <Label> [payload...]`
  provenance : String       -- `[provenance]`, or "" for written code
  span       : SourceSpan
  snippet    : Maybe String
  children : List DebugTree

Forest : Type
Forest = List DebugTree

group : List Forest -> Forest
group = concat

many : (a -> Forest) -> List a -> Forest
many = concatMap

optional : (a -> Forest) -> Maybe a -> Forest
optional render = maybe [] render

-- Empty payload entries are dropped.
nodeWith : PhaseDebug phase => String -> List String -> Maybe String -> AstNode phase a -> List Forest -> Forest
nodeWith label payload snippet (MkAstNode info metadata _) children =
  [MkDebugTree heading (provenanceText (nodeProvenance {phase} metadata)) info.span snippet (group children)]
  where
    heading : String
    heading = "#" ++ nodeIdText info.nodeId ++ " " ++ unwords (label :: filter (/= "") payload)

node : PhaseDebug phase => String -> List String -> AstNode phase a -> List Forest -> Forest
node label payload = nodeWith label payload Nothing

-- A node with a snippet of its source.
sourceNode : PhaseDebug phase => String -> List String -> Lazy SourceText -> AstNode phase a -> List Forest -> Forest
sourceNode label payload document =
  nodeWith label payload (Just (renderSourcePreview escapeSourceChar snippetLimit document))

-- A located token, shown by its Leaf spelling.
leaf : (PhaseDebug phase, Show a) => String -> AstNode phase a -> Forest
leaf label ast = node label [escape (show ast.nodeValue)] ast []

--------------------------------------------------------------------------------
-- Layout
--------------------------------------------------------------------------------

sameSpan : SourceSpan -> SourceSpan -> Bool
sameSpan a b =
  a.file == b.file && a.start.line == b.start.line && a.start.column == b.start.column &&
  a.end.line == b.end.line && a.end.column == b.end.column

-- The nodes sharing a tree's line, as (heading, provenance), and the children
-- printed below it: the line continues into an only child with the same span
-- and no snippet.
lineChain : DebugTree -> (List (String, String), List DebugTree)
lineChain (MkDebugTree heading provenance span _ [child@(MkDebugTree _ _ childSpan Nothing _)]) =
  if sameSpan span childSpan
    then let (rest, below) = lineChain child in ((heading, provenance) :: rest, below)
    else ([(heading, provenance)], [child])
lineChain (MkDebugTree heading provenance _ _ children) = ([(heading, provenance)], children)

-- Headings joined by ` > `, each with its provenance or `[same]`.
chainText : List (String, String) -> String
chainText = joinBy " > " . go ""
  where
    withProvenance : String -> String -> String
    withProvenance heading ""         = heading
    withProvenance heading provenance = heading ++ " " ++ provenance

    go : String -> List (String, String) -> List String
    go _ [] = []
    go previous ((heading, provenance) :: rest) =
      withProvenance heading (if provenance /= "" && provenance == previous then "[same]" else provenance)
        :: go provenance rest

-- Keep each completed line as a chunk. Joining child dumps into their parents
-- would repeatedly copy the entire indented subtree on deeply nested ASTs.
mutual
  layout : (rootFile : String) -> (depth : Nat) -> DebugTree -> SourceText
  layout rootFile depth tree@(MkDebugTree _ _ span snippet _) =
    let (chain, below) = lineChain tree
        line = pack (replicate (2 * depth) ' ') ++ chainText chain ++ " @" ++ spanText rootFile span ++
               maybe "" snippetText snippet ++ "\n"
    in Append (text line) (layoutForest rootFile (S depth) below)

  layoutForest : String -> Nat -> Forest -> SourceText
  layoutForest _ _ [] = ""
  layoutForest rootFile depth (tree :: rest) =
    Append (layout rootFile depth tree) (layoutForest rootFile depth rest)

--------------------------------------------------------------------------------
-- Names, literals, docs, attributes, Pauli strings
--------------------------------------------------------------------------------

debugPlainName : PhaseDebug phase => AstNode phase NameNode -> Forest
debugPlainName ast@(MkAstNode _ _ (MkNameNode text)) = node "MkNameNode" [escape text] ast []

debugName : PhaseDebug phase => Name phase -> Forest
debugName ast@(MkAstNode _ _ name) =
  node "Name" [escape (prettyName {phase} name), symbolText (nameSymbol {phase} name)] ast []

debugMember : PhaseDebug phase => MemberName phase -> Forest
debugMember ast@(MkAstNode _ _ name) =
  node "MemberName" [escape (prettyMemberName {phase} name), symbolText (memberSymbol {phase} name)] ast []

debugPathSegment : PhaseDebug phase => PathSegment phase -> Forest
debugPathSegment ast@(MkAstNode _ _ (PathSegmentName text)) = node "PathSegmentName" [escape text] ast []
debugPathSegment ast@(MkAstNode _ _ PathSegmentSelf)        = node "PathSegmentSelf" [] ast []

-- The text is shown only when no segment nodes spell it out.
debugPath : PhaseDebug phase => Path phase -> Forest
debugPath ast@(MkAstNode _ _ path) =
  let (segments, symbol) = pathParts {phase} path
      text = if null segments then escape (prettyPath {phase} path) else ""
  in node "Path" [text, symbolText symbol] ast [many debugPathSegment segments]

debugLiteral : PhaseDebug phase => Literal phase -> Forest
debugLiteral ast@(MkAstNode _ _ literal) =
  case literal of
    LiteralIntegerRaw raw     => spelled "LiteralIntegerRaw" raw
    LiteralFloatRaw raw       => spelled "LiteralFloatRaw" raw
    LiteralStringRaw raw      => spelled "LiteralStringRaw" raw
    LiteralByteRaw raw        => spelled "LiteralByteRaw" raw
    LiteralByteStringRaw raw  => spelled "LiteralByteStringRaw" raw
    LiteralBasisStringRaw raw => spelled "LiteralBasisStringRaw" raw
    LiteralBoolean value      => spelled "LiteralBoolean" (if value then "true" else "false")
    LiteralUnit               => spelled "LiteralUnit" "()"
    LiteralQuantumState state => spelled "LiteralQuantumState" (show state)
  where
    spelled : String -> String -> Forest
    spelled label spelling = node label [escape spelling] ast []

debugDoc : PhaseDebug phase => DocComment phase -> Forest
debugDoc ast@(MkAstNode _ _ (MkDocCommentNode kind placement raw)) =
  node "MkDocCommentNode"
    [ case kind of DocCommentLine => "line"; DocCommentBlock => "block"
    , case placement of DocCommentOuter => "outer"; DocCommentInner => "inner"
    , escape raw ] ast []

debugAttributeArgument : PhaseDebug phase => AttributeArgument phase -> Forest
debugAttributeArgument ast@(MkAstNode _ _ (AttributeArgumentStringLit raw)) =
  node "AttributeArgumentStringLit" [escape raw] ast []

-- `args` marks a written argument list, which distinguishes `#[a()]` from `#[a]`.
debugAttribute : PhaseDebug phase => Attribute phase -> Forest
debugAttribute ast@(MkAstNode _ _ (MkAttributeNode name arguments)) =
  node "MkAttributeNode" [flagText "args" (isJust arguments)] ast
    [debugPlainName name, many debugAttributeArgument (fromMaybe [] arguments)]

debugVisibility : PhaseDebug phase => Maybe (AstNode phase VisibilityQualifier) -> Forest
debugVisibility = optional (leaf "VisibilityQualifier")

debugPauli : PhaseDebug phase => PauliString phase -> Forest
debugPauli ast@(MkAstNode _ _ (MkPauliStringNode operators)) =
  node "MkPauliStringNode" [concatMap show (forget operators)] ast []

debugSignedPauli : PhaseDebug phase => SignedPauliTerm phase -> Forest
debugSignedPauli ast@(MkAstNode _ _ (MkSignedPauliTermNode sign pauli)) =
  node "MkSignedPauliTermNode" [case sign of StabilizerPlus => "+"; StabilizerMinus => "-"] ast [debugPauli pauli]

--------------------------------------------------------------------------------
-- Patterns
--------------------------------------------------------------------------------

mutabilityText : Maybe Mutability -> String
mutabilityText = maybe "" show

mutual
  debugPattern : PhaseDebug phase => Pattern phase -> Forest
  debugPattern ast@(MkAstNode _ _ pattern) =
    case pattern of
      PatternWildcard                => node "PatternWildcard" [] ast []
      PatternName mutability name    => node "PatternName" [mutabilityText mutability] ast [debugName name]
      PatternPath path               => node "PatternPath" [] ast [debugPath path]
      PatternLiteral literal         => node "PatternLiteral" [] ast [debugLiteral literal]
      PatternParenthesized inner     => node "PatternParenthesized" [] ast [debugPattern inner]
      PatternTuple elements          => node "PatternTuple" [] ast [many debugPattern (forget elements)]
      PatternArray elements          => node "PatternArray" [] ast [many debugPattern elements]
      PatternStruct path fields      => node "PatternStruct" [] ast [debugPath path, many debugPatternField fields]
      PatternEnumTuple path elements => node "PatternEnumTuple" [] ast [debugPath path, many debugPattern elements]

  debugPatternField : PhaseDebug phase => StructPatternField phase -> Forest
  debugPatternField ast@(MkAstNode _ _ field) =
    case field of
      StructPatternFieldShorthand mutability name =>
        node "StructPatternFieldShorthand" [mutabilityText mutability] ast [debugName name]
      StructPatternFieldExplicit name pattern =>
        node "StructPatternFieldExplicit" [] ast [debugName name, debugPattern pattern]

debugQuantumPattern : PhaseDebug phase => QuantumMatchPattern phase -> Forest
debugQuantumPattern ast@(MkAstNode _ _ pattern) =
  case pattern of
    QuantumPatternBasisStringRaw raw        => node "QuantumPatternBasisStringRaw" [escape raw] ast []
    QuantumPatternIntegerRaw raw            => node "QuantumPatternIntegerRaw" [escape raw] ast []
    QuantumPatternWildcard                  => node "QuantumPatternWildcard" [] ast []
    QuantumPatternQenumVariant path binders =>
      node "QuantumPatternQenumVariant" [] ast [debugPath path, many debugName binders]

--------------------------------------------------------------------------------
-- The recursive core: expressions, types, blocks and statements
--------------------------------------------------------------------------------

mutual
  debugExpr : PhaseDebug phase => Expr phase -> Forest
  debugExpr ast@(MkAstNode _ _ e) =
    let (label, payload, children) = exprParts e in node label payload ast children

  -- A block's final expression stands in for a statement, so it gets a snippet.
  debugFinalExpr : PhaseDebug phase => Expr phase -> Forest
  debugFinalExpr ast@(MkAstNode _ _ e) =
    let (label, payload, children) = exprParts e
    in sourceNode label payload (showStatementPositionExprDoc PrettyStrict ast) ast children

  -- An expression's label, the data it holds directly rather than in child
  -- nodes, and its children in source order. The payload also names the form
  -- of `ctrl`/`adjoint`, which is otherwise only implied by the last child.
  -- Every constructor is listed, so new syntax cannot compile without deciding
  -- how the dump shows it.
  exprParts : PhaseDebug phase => ExpressionNode phase -> (String, List String, List Forest)
  exprParts e =
    case e of
      ExprLiteral literal => ("ExprLiteral", [], [debugLiteral literal])
      ExprName name       => ("ExprName", [], [debugName name])
      ExprPath path       => ("ExprPath", [], [debugPath path])
      ExprBuiltin builtin => ("ExprBuiltin", [show builtin], [])
      ExprSelf receiver   => ("ExprSelf", [symbolText (selfSymbol {phase} receiver)], [])
      ExprParenthesized inner => ("ExprParenthesized", [], [debugExpr inner])
      ExprTuple elements      => ("ExprTuple", [], [many debugExpr (forget elements)])
      ExprArray elements      => ("ExprArray", [], [many debugExpr elements])
      ExprRepeatedArray element count =>
        ("ExprRepeatedArray", [], [debugExpr element, debugExpr count])
      ExprStructLiteral path fields =>
        ("ExprStructLiteral", [], [debugPath path, many debugFieldInitializer fields])
      ExprCall callee args => ("ExprCall", [], [debugExpr callee, many debugExpr args])
      ExprMethodCall receiver method args =>
        ("ExprMethodCall", [], [debugExpr receiver, debugMember method, many debugExpr args])
      ExprField object field       => ("ExprField", [], [debugExpr object, debugMember field])
      ExprTupleIndex object index  => ("ExprTupleIndex", [escape index], [debugExpr object])
      ExprIndex object index       => ("ExprIndex", [], [debugExpr object, debugExpr index])
      ExprUnary op operand         => ("ExprUnary", [], [leaf "UnaryOperator" op, debugExpr operand])
      ExprBinary op lhs rhs        => ("ExprBinary", [], [debugExpr lhs, leaf "BinaryOperator" op, debugExpr rhs])
      ExprRange start op end =>
        ("ExprRange", [], [optional debugExpr start, leaf "RangeOperator" op, optional debugExpr end])
      ExprCast operand ty => ("ExprCast", [], [debugExpr operand, debugTy ty])
      ExprBlock block     => ("ExprBlock", [], [debugBlock block])
      ExprIf conditional  => ("ExprIf", [], [debugIf conditional])
      ExprQIf (MkQuantumIfNode condition thenBranch elseBranch) =>
        ("ExprQIf", [], [debugExpr condition, debugQuantumBranch thenBranch, optional debugQuantumBranch elseBranch])
      ExprSIf (MkStateIfNode condition thenExpr elseExpr) =>
        ("ExprSIf", [], [debugExpr condition, debugExpr thenExpr, debugExpr elseExpr])
      ExprMatch (MkClassicalMatchNode scrutinee arms) =>
        ("ExprMatch", [], [debugExpr scrutinee, many debugMatchArm arms])
      ExprQMatch (MkQuantumMatchNode scrutinee arms) =>
        ("ExprQMatch", [], [debugExpr scrutinee, many debugQuantumArm arms])
      ExprSMatch (MkStateMatchNode scrutinee arms) =>
        ("ExprSMatch", [], [debugExpr scrutinee, many debugQuantumArm arms])
      ExprLoop body                 => ("ExprLoop", [], [debugBlock body])
      ExprWhile condition body      => ("ExprWhile", [], [debugExpr condition, debugBlock body])
      ExprFor pattern iterable body => ("ExprFor", [], [debugPattern pattern, debugExpr iterable, debugBlock body])
      ExprBreak value               => ("ExprBreak", [], [optional debugExpr value])
      ExprContinue                  => ("ExprContinue", [], [])
      ExprReturn value              => ("ExprReturn", [], [optional debugExpr value])
      ExprCtrl (ControlledCallable controls basis callable) =>
        ("ExprCtrl", ["callable"], [many debugExpr (forget controls), optional debugBasis basis, debugExpr callable])
      ExprCtrl (ControlledBlock controls basis body) =>
        ("ExprCtrl", ["block"], [many debugExpr (forget controls), optional debugBasis basis, debugBlock body])
      ExprAdjoint (AdjointOfCallable callable) => ("ExprAdjoint", ["callable"], [debugExpr callable])
      ExprAdjoint (AdjointBlock body)          => ("ExprAdjoint", ["block"], [debugBlock body])

  debugBasis : PhaseDebug phase => AstNode phase String -> Forest
  debugBasis ast = node "ControlBasis" [escape ast.nodeValue] ast []

  debugFieldInitializer : PhaseDebug phase => AstNode phase (FieldInitializerNode phase) -> Forest
  debugFieldInitializer ast@(MkAstNode _ _ field) =
    case field of
      FieldInitShorthand name      => node "FieldInitShorthand" [] ast [debugName name]
      FieldInitExplicit name value => node "FieldInitExplicit" [] ast [debugName name, debugExpr value]

  -- Children only: the owning node already names the construct.
  debugIf : PhaseDebug phase => ClassicalIfNode phase -> Forest
  debugIf (MkClassicalIfNode condition thenBlock elseBranch) =
    group [debugExpr condition, debugBlock thenBlock, optional debugElse elseBranch]

  debugElse : PhaseDebug phase => ClassicalElseNode phase -> Forest
  debugElse (ElseBlock block) = debugBlock block
  debugElse (ElseChainedIf ast@(MkAstNode _ _ chained)) = node "MkClassicalIfNode" [] ast [debugIf chained]

  debugQuantumBranch : PhaseDebug phase => QuantumBranchNode phase -> Forest
  debugQuantumBranch (QuantumBranchBlock block)     = debugBlock block
  debugQuantumBranch (QuantumBranchExpression expr) = debugExpr expr

  debugMatchArm : PhaseDebug phase => ClassicalMatchArm phase -> Forest
  debugMatchArm ast@(MkAstNode _ _ (MkClassicalMatchArmNode pattern guard body)) =
    node "MkClassicalMatchArmNode" [flagText "guarded" (isJust guard)] ast
      [debugPattern pattern, optional debugExpr guard, debugExpr body]

  debugQuantumArm : PhaseDebug phase => QuantumMatchArm phase -> Forest
  debugQuantumArm ast@(MkAstNode _ _ (MkQuantumMatchArmNode pattern body)) =
    node "MkQuantumMatchArmNode" [] ast [debugQuantumPattern pattern, debugExpr body]

  debugTy : PhaseDebug phase => Ty phase (Expr phase) -> Forest
  debugTy ast@(MkAstNode _ _ ty) =
    case ty of
      TyPrimitive primitive => node "TyPrimitive" [showTypPrimLeaf primitive] ast []
      TyPath path           => node "TyPath" [] ast [debugPath path]
      TyUnit                => node "TyUnit" [] ast []
      TyParenthesized inner => node "TyParenthesized" [] ast [debugTy inner]
      TyTuple elements      => node "TyTuple" [] ast [many debugTy (forget elements)]
      TyArray element size  => node "TyArray" [] ast [debugTy element, debugExpr size]
      TySlice element       => node "TySlice" [] ast [debugTy element]
      TyReference borrow inner =>
        node "TyReference" [] ast [leaf "BorrowKind" borrow, debugTy inner]
      TyQualified qualifier inner =>
        node "TyQualified" [] ast [leaf "QuantumUsageQualifier" qualifier, debugTy inner]
      TyFunction effect params result =>
        node "TyFunction" [] ast
          [optional (leaf "FunctionEffect") effect, many debugTypeParameter params, optional debugTy result]

  debugTypeParameter : PhaseDebug phase => AstNode phase (FunctionTypeParameterNode phase (Expr phase)) -> Forest
  debugTypeParameter ast@(MkAstNode _ _ (MkFunctionTypeParameterNode name ty)) =
    node "MkFunctionTypeParameterNode" [] ast [debugPlainName name, debugTy ty]

  debugBlock : PhaseDebug phase => Block phase -> Forest
  debugBlock ast@(MkAstNode _ _ (MkBlockNode docs statements final)) =
    node "MkBlockNode" [] ast [many debugDoc docs, many debugStatement statements, optional debugFinalExpr final]

  debugStatement : PhaseDebug phase => Statement phase -> Forest
  debugStatement ast@(MkAstNode _ _ statement) =
    case statement of
      StatementLet (MkLetBindingNode qualifiers pattern annotation initializer) =>
        withSource "StatementLet"
          [ many (leaf "QuantumStorageQualifier") qualifiers, debugPattern pattern
          , optional debugTy annotation, optional debugInitializer initializer ]
      StatementAssignment (MkAssignmentNode target operator value) =>
        withSource "StatementAssignment"
          [debugAssignmentTarget target, leaf "AssignmentOperator" operator, debugExpr value]
      StatementSemiExpression expr => withSource "StatementSemiExpression" [debugExpr expr]
      StatementExpression expr     => withSource "StatementExpression" [debugExpr expr]
    where
      withSource : String -> List Forest -> Forest
      withSource label = sourceNode label [] (showStatementDoc PrettyStrict ast) ast

  -- Children only: the marker and value belong to the let statement.
  debugInitializer : PhaseDebug phase => LetInitializerNode phase -> Forest
  debugInitializer (MkLetInitializerNode marker value) =
    group [leaf "InitializerMarker" marker, debugExpr value]

  debugAssignmentTarget : PhaseDebug phase => AssignmentTarget phase -> Forest
  debugAssignmentTarget ast@(MkAstNode _ _ target) =
    case target of
      AssignTargetName name          => node "AssignTargetName" [] ast [debugName name]
      AssignTargetIndex object index => node "AssignTargetIndex" [] ast [debugExpr object, debugExpr index]
      AssignTargetField object field => node "AssignTargetField" [] ast [debugExpr object, debugMember field]
      AssignTargetTupleIndex object index =>
        node "AssignTargetTupleIndex" [escape index] ast [debugExpr object]

--------------------------------------------------------------------------------
-- Contracts and functions
--------------------------------------------------------------------------------

debugPredicate : PhaseDebug phase => ContractPredicate phase (Expr phase) -> Forest
debugPredicate ast@(MkAstNode _ _ predicate) =
  case predicate of
    ContractClean e              => node "ContractClean" [] ast [debugExpr e]
    ContractBasis e pauli        => node "ContractBasis" [] ast [debugExpr e, debugPauli pauli]
    ContractSeparable e          => node "ContractSeparable" [] ast [debugExpr e]
    ContractIsolated e           => node "ContractIsolated" [] ast [debugExpr e]
    ContractProduct first others => node "ContractProduct" [] ast [many debugExpr (first :: forget others)]
    ContractStabilized e terms   => node "ContractStabilized" [] ast [debugExpr e, many debugSignedPauli (forget terms)]

debugContract : PhaseDebug phase => ContractClause phase (Expr phase) -> Forest
debugContract ast@(MkAstNode _ _ (RequiresClause predicate)) = node "RequiresClause" [] ast [debugPredicate predicate]
debugContract ast@(MkAstNode _ _ (EnsuresClause predicate))  = node "EnsuresClause" [] ast [debugPredicate predicate]

debugParameter : PhaseDebug phase => FunctionParameter phase -> Forest
debugParameter ast@(MkAstNode _ _ parameter) =
  case parameter of
    NormalParameter docs mutability name ty =>
      node "NormalParameter" [] ast
        [many debugDoc docs, optional (leaf "Mutability") mutability, debugName name, debugTy ty]
    ReceiverParameter docs borrow =>
      node "ReceiverParameter" [] ast [many debugDoc docs, optional (leaf "BorrowKind") borrow]

-- Children only: the owning item or impl member names the declaration.
debugFunction : PhaseDebug phase => FunctionDeclarationNode phase -> Forest
debugFunction
    (MkFunctionDeclarationNode docs attrs visibility constness effect name params result supports contracts body) =
  group
    [ many debugDoc docs, many debugAttribute attrs, debugVisibility visibility
    , optional (leaf "FunctionConstness") constness, optional (leaf "FunctionEffect") effect
    , debugName name, many debugParameter params, optional debugTy result
    , many (leaf "SupportKind") supports, many debugContract contracts, debugBlock body ]

-- Outer docs and attributes are listed as children, so snippets start at the
-- declaration's head instead of repeating them.
functionWithoutPreamble : FunctionDeclarationNode phase -> FunctionDeclarationNode phase
functionWithoutPreamble = { functionDocs := [], functionAttributes := [] }

debugImplFunction : PhaseDebug phase => FunctionDeclaration phase -> Forest
debugImplFunction ast@(MkAstNode info metadata function) =
  sourceNode "MkFunctionDeclarationNode" []
    (showFunctionDeclarationDoc PrettyStrict (MkAstNode info metadata (functionWithoutPreamble function)))
    ast [debugFunction function]

--------------------------------------------------------------------------------
-- Type declarations and items
--------------------------------------------------------------------------------

-- Docs, attributes, visibility and name: the common head of a declaration.
declarationHead :
     PhaseDebug phase
  => List (DocComment phase) -> List (Attribute phase) -> Maybe (AstNode phase VisibilityQualifier)
  -> Name phase -> List Forest
declarationHead docs attrs visibility name =
  [many debugDoc docs, many debugAttribute attrs, debugVisibility visibility, debugName name]

debugStructField : PhaseDebug phase => AstNode phase (StructFieldNode phase) -> Forest
debugStructField ast@(MkAstNode _ _ (MkStructFieldNode docs name ty)) =
  node "MkStructFieldNode" [] ast [many debugDoc docs, debugName name, debugTy ty]

debugEnumVariant : PhaseDebug phase => AstNode phase (EnumVariantNode phase) -> Forest
debugEnumVariant ast@(MkAstNode _ _ (MkEnumVariantNode docs name body)) =
  case body of
    VariantUnit          => variant "unit" []
    VariantTuple types   => variant "tuple" [many debugTy (forget types)]
    VariantStruct fields => variant "struct" [many debugStructField fields]
  where
    variant : String -> List Forest -> Forest
    variant form payload = node "MkEnumVariantNode" [form] ast ([many debugDoc docs, debugName name] ++ payload)

debugQEnumVariant : PhaseDebug phase => AstNode phase (QEnumVariantNode phase) -> Forest
debugQEnumVariant ast@(MkAstNode _ _ (MkQEnumVariantNode docs name types)) =
  node "MkQEnumVariantNode" [] ast [many debugDoc docs, debugName name, many debugTy (forget types)]

itemWithoutPreamble : ItemNode phase -> ItemNode phase
itemWithoutPreamble item =
  case item of
    ItemFunction function  => ItemFunction (functionWithoutPreamble function)
    ItemModule declaration => ItemModule ({ moduleDocs := [] } declaration)
    ItemUse declaration    => ItemUse ({ useDocs := [] } declaration)
    ItemConst declaration  => ItemConst ({ constDocs := [] } declaration)
    ItemStruct declaration => ItemStruct ({ structDocs := [], structAttributes := [] } declaration)
    ItemEnum declaration   => ItemEnum ({ enumDocs := [], enumAttributes := [] } declaration)
    ItemQEnum declaration  => ItemQEnum ({ qenumDocs := [], qenumAttributes := [] } declaration)
    ItemImpl declaration   => ItemImpl ({ implDocs := [] } declaration)

debugItem : PhaseDebug phase => Item phase -> Forest
debugItem ast@(MkAstNode info metadata item) =
  case item of
    ItemFunction function => withSource "ItemFunction" [] [debugFunction function]
    ItemModule (MkModuleDeclarationNode docs visibility name ModuleExternal) =>
      withSource "ItemModule" ["external"] (declarationHead docs [] visibility name)
    ItemModule (MkModuleDeclarationNode docs visibility name (ModuleInline innerDocs items)) =>
      withSource "ItemModule" ["inline"]
        (declarationHead docs [] visibility name ++ [many debugDoc innerDocs, many debugItem items])
    ItemUse (MkUseDeclarationNode docs visibility path alias) =>
      withSource "ItemUse" []
        [many debugDoc docs, debugVisibility visibility, debugPath path, optional debugPlainName alias]
    ItemConst (MkConstDeclarationNode docs visibility name ty value) =>
      withSource "ItemConst" [] (declarationHead docs [] visibility name ++ [debugTy ty, debugExpr value])
    ItemStruct (MkStructDeclarationNode docs attrs visibility name fields) =>
      withSource "ItemStruct" [] (declarationHead docs attrs visibility name ++ [many debugStructField fields])
    ItemEnum (MkEnumDeclarationNode docs attrs visibility name variants) =>
      withSource "ItemEnum" [] (declarationHead docs attrs visibility name ++ [many debugEnumVariant variants])
    ItemQEnum (MkQEnumDeclarationNode docs attrs visibility name variants) =>
      withSource "ItemQEnum" [] (declarationHead docs attrs visibility name ++ [many debugQEnumVariant variants])
    ItemImpl (MkImplDeclarationNode docs target functions) =>
      withSource "ItemImpl" [] [many debugDoc docs, debugPath target, many debugImplFunction functions]
  where
    withSource : String -> List String -> List Forest -> Forest
    withSource label payload =
      sourceNode label payload (showItemDoc PrettyStrict (MkAstNode info metadata (itemWithoutPreamble item))) ast

--------------------------------------------------------------------------------
-- Entry point
--------------------------------------------------------------------------------

||| Structural dump of the AST with every located node, its full NodeId,
||| half-open source span, compiler provenance and resolved symbols; see the
||| format at the top of this module. Inferred types live in the type
||| checker's tables, not in this AST.
public export
showAstDebug : PhaseDebug phase => SourceFile phase -> String
showAstDebug ast@(MkAstNode info _ (MkSourceFileNode docs items)) =
  "phase=" ++ phaseLabel {phase} ++ " file=" ++ escape info.span.file ++ "\n" ++
  renderSource (layoutForest info.span.file 0
    (node "MkSourceFileNode" [] ast [many debugDoc docs, many debugItem items]))
