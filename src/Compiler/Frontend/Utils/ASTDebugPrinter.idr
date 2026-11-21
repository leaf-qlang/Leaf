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
  pathParts (MkPathNode firstSegment remainingSegments) = (firstSegment :: remainingSegments, Nothing)

public export
PhaseDebug CanonicalAstPhase where
  phaseLabel = "canonical"
  nodeProvenance metadata = Just metadata.provenance
  nameSymbol _ = Nothing
  memberSymbol _ = Nothing
  selfSymbol _ = Nothing
  pathParts (MkPathNode firstSegment remainingSegments) = (firstSegment :: remainingSegments, Nothing)

public export
PhaseDebug ResolvedAstPhase where
  phaseLabel = "resolved"
  nodeProvenance metadata = Just metadata.provenance
  nameSymbol resolvedName = Just resolvedName.nameNodeSymbolId
  memberSymbol _ = Nothing
  selfSymbol selfSymbolId = Just selfSymbolId
  pathParts resolvedPath = ([], Just resolvedPath.referencedSymbolId)

public export
PhaseDebug TypedAstPhase where
  phaseLabel = "typed"
  nodeProvenance metadata = Just metadata.provenance
  nameSymbol resolvedName = Just resolvedName.nameNodeSymbolId
  memberSymbol resolvedName = Just resolvedName.nameNodeSymbolId
  selfSymbol selfSymbolId = Just selfSymbolId
  pathParts resolvedPath = ([], Just resolvedPath.referencedSymbolId)

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
hexText codePoint = (if codePoint >= 16 then hexText (codePoint `div` 16) else []) ++ [hexDigit (codePoint `mod` 16)]

-- Use the lexer's Unicode category data for all format characters (Cf),
-- including supplementary code points, plus line and paragraph separators.
invisibleFormatValidator : PVal1 q Void ()
invisibleFormatValidator = value Nothing
  [ (Unicode.format, const ())
  , (Unicode.lineSeparator, const ())
  , (Unicode.paragraphSeparator, const ())
  ]

isInvisibleFormat : Char -> Bool
isInvisibleFormat character =
  -- The first format character is U+00AD; ordinary ASCII needs no lookup.
  ord character >= 0xAD && case runString invisibleFormatValidator (singleton character) of
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
escapeSourceChar character =
  let codePoint = ord character in
  if codePoint < 32 || (codePoint >= 127 && codePoint <= 159)
    then ['\\', 'x', hexDigit (codePoint `div` 16), hexDigit (codePoint `mod` 16)]
    else if isInvisibleFormat character then unpack "\\u{" ++ hexText codePoint ++ ['}']
    else [character]

-- Payloads also escape `#`: a bare `#` always starts a node, so no payload can
-- imitate the ` > #` that joins nodes sharing a line. Snippets, which follow
-- the span inside backticks, keep `#` as written.
escapePayloadChar : Char -> List Char
escapePayloadChar '#' = ['\\', '#']
escapePayloadChar character   = escapeSourceChar character

escapePayloadText : String -> String
escapePayloadText = pack . concatMap escapePayloadChar . unpack

nodeIdText : NodeId -> String
nodeIdText (MkNodeId surfaceId Z)         = show surfaceId
nodeIdText (MkNodeId surfaceId desugarId) = show surfaceId ++ "." ++ show desugarId

positionText : SourcePos -> String
positionText position = show position.line ++ ":" ++ show position.column

-- `rootFile` is the file named on the first line of the dump.
spanText : String -> SourceSpan -> String
spanText rootFile sourceSpan =
  (if sourceSpan.file == rootFile then "" else escapePayloadText sourceSpan.file ++ ":") ++
  positionText sourceSpan.start ++ "-" ++
  (if sourceSpan.end.line == sourceSpan.start.line then show sourceSpan.end.column else positionText sourceSpan.end)

provenanceText : Maybe NodeProvenance -> String
provenanceText (Just WrittenCode) = ""
provenanceText (Just desugaredProvenance)      = "[" ++ show desugaredProvenance ++ "]"
provenanceText Nothing            = ""

-- The stored preview is already escaped and bounded during tree construction.
snippetText : String -> String
snippetText preview = " `" ++ preview ++ "`"

symbolText : Maybe SymbolId -> String
symbolText = maybe "" (\symbolId => "sym=" ++ show symbolId.id)

-- Present only when the flag holds: `args` and `guarded`.
flagText : String -> Bool -> String
flagText flagName present = if present then flagName else ""

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
optional renderItem = maybe [] renderItem

-- Empty payload entries are dropped.
nodeWith : PhaseDebug phase => String -> List String -> Maybe String -> AstNode phase a -> List Forest -> Forest
nodeWith label payload snippet (MkAstNode astInfo metadata _) children =
  [MkDebugTree heading (provenanceText (nodeProvenance {phase} metadata)) astInfo.span snippet (group children)]
  where
    heading : String
    heading = "#" ++ nodeIdText astInfo.nodeId ++ " " ++ unwords (label :: filter (/= "") payload)

node : PhaseDebug phase => String -> List String -> AstNode phase a -> List Forest -> Forest
node label payload = nodeWith label payload Nothing

-- A node with a snippet of its source.
sourceNode : PhaseDebug phase => String -> List String -> Lazy SourceText -> AstNode phase a -> List Forest -> Forest
sourceNode label payload document =
  nodeWith label payload (Just (renderSourcePreview escapeSourceChar snippetLimit document))

-- A located token, shown by its Leaf spelling.
leaf : (PhaseDebug phase, Show a) => String -> AstNode phase a -> Forest
leaf label astNode = node label [escapePayloadText (show astNode.nodeValue)] astNode []

--------------------------------------------------------------------------------
-- Layout
--------------------------------------------------------------------------------

sameSpan : SourceSpan -> SourceSpan -> Bool
sameSpan firstSpan secondSpan =
  firstSpan.file == secondSpan.file && firstSpan.start.line == secondSpan.start.line && firstSpan.start.column == secondSpan.start.column &&
  firstSpan.end.line == secondSpan.end.line && firstSpan.end.column == secondSpan.end.column

-- The nodes sharing a tree's line, as (heading, provenance), and the children
-- printed below it: the line continues into an only child with the same span
-- and no snippet.
lineChain : DebugTree -> (List (String, String), List DebugTree)
lineChain (MkDebugTree heading provenance treeSpan _ [child@(MkDebugTree _ _ childSpan Nothing _)]) =
  if sameSpan treeSpan childSpan
    then let (followingNodes, childrenBelow) = lineChain child in ((heading, provenance) :: followingNodes, childrenBelow)
    else ([(heading, provenance)], [child])
lineChain (MkDebugTree heading provenance _ _ children) = ([(heading, provenance)], children)

-- Headings joined by ` > `, each with its provenance or `[same]`.
chainText : List (String, String) -> String
chainText = joinBy " > " . markRepeatedProvenance ""
  where
    withProvenance : String -> String -> String
    withProvenance heading ""         = heading
    withProvenance heading provenance = heading ++ " " ++ provenance

    markRepeatedProvenance : String -> List (String, String) -> List String
    markRepeatedProvenance _ [] = []
    markRepeatedProvenance previousProvenance ((heading, provenance) :: remainingNodes) =
      withProvenance heading (if provenance /= "" && provenance == previousProvenance then "[same]" else provenance)
        :: markRepeatedProvenance provenance remainingNodes

-- Keep each completed line as a chunk. Joining child dumps into their parents
-- would repeatedly copy the entire indented subtree on deeply nested ASTs.
mutual
  layout : (rootFile : String) -> (depth : Nat) -> DebugTree -> SourceText
  layout rootFile depth tree@(MkDebugTree _ _ treeSpan snippet _) =
    let (nodesOnLine, childrenBelow) = lineChain tree
        lineText = pack (replicate (2 * depth) ' ') ++ chainText nodesOnLine ++ " @" ++ spanText rootFile treeSpan ++
               maybe "" snippetText snippet ++ "\n"
    in Append (text lineText) (layoutForest rootFile (S depth) childrenBelow)

  layoutForest : String -> Nat -> Forest -> SourceText
  layoutForest _ _ [] = ""
  layoutForest rootFile depth (tree :: remainingTrees) =
    Append (layout rootFile depth tree) (layoutForest rootFile depth remainingTrees)

--------------------------------------------------------------------------------
-- Names, literals, docs, attributes, Pauli strings
--------------------------------------------------------------------------------

debugPlainName : PhaseDebug phase => AstNode phase NameNode -> Forest
debugPlainName astNode@(MkAstNode _ _ (MkNameNode nameText)) = node "MkNameNode" [escapePayloadText nameText] astNode []

debugName : PhaseDebug phase => Name phase -> Forest
debugName astNode@(MkAstNode _ _ namePayload) =
  node "Name" [escapePayloadText (prettyName {phase} namePayload), symbolText (nameSymbol {phase} namePayload)] astNode []

debugMember : PhaseDebug phase => MemberName phase -> Forest
debugMember astNode@(MkAstNode _ _ namePayload) =
  node "MemberName" [escapePayloadText (prettyMemberName {phase} namePayload), symbolText (memberSymbol {phase} namePayload)] astNode []

debugPathSegment : PhaseDebug phase => PathSegment phase -> Forest
debugPathSegment astNode@(MkAstNode _ _ (PathSegmentName segmentText)) = node "PathSegmentName" [escapePayloadText segmentText] astNode []
debugPathSegment astNode@(MkAstNode _ _ PathSegmentSelf)        = node "PathSegmentSelf" [] astNode []

-- The text is shown only when no segment nodes spell it out.
debugPath : PhaseDebug phase => Path phase -> Forest
debugPath astNode@(MkAstNode _ _ pathPayload) =
  let (segments, targetSymbol) = pathParts {phase} pathPayload
      pathText = if null segments then escapePayloadText (prettyPath {phase} pathPayload) else ""
  in node "Path" [pathText, symbolText targetSymbol] astNode [many debugPathSegment segments]

debugLiteral : PhaseDebug phase => Literal phase -> Forest
debugLiteral astNode@(MkAstNode _ _ literalNode) =
  case literalNode of
    LiteralIntegerRaw rawSpelling     => spelled "LiteralIntegerRaw" rawSpelling
    LiteralFloatRaw rawSpelling       => spelled "LiteralFloatRaw" rawSpelling
    LiteralStringRaw rawSpelling      => spelled "LiteralStringRaw" rawSpelling
    LiteralByteRaw rawSpelling        => spelled "LiteralByteRaw" rawSpelling
    LiteralByteStringRaw rawSpelling  => spelled "LiteralByteStringRaw" rawSpelling
    LiteralBasisStringRaw rawSpelling => spelled "LiteralBasisStringRaw" rawSpelling
    LiteralBoolean booleanValue       => spelled "LiteralBoolean" (if booleanValue then "true" else "false")
    LiteralUnit                       => spelled "LiteralUnit" "()"
    LiteralQuantumState basisState    => spelled "LiteralQuantumState" (show basisState)
  where
    spelled : String -> String -> Forest
    spelled label spelling = node label [escapePayloadText spelling] astNode []

debugDoc : PhaseDebug phase => DocComment phase -> Forest
debugDoc astNode@(MkAstNode _ _ (MkDocCommentNode commentKind commentPlacement rawText)) =
  node "MkDocCommentNode"
    [ case commentKind of DocCommentLine => "line"; DocCommentBlock => "block"
    , case commentPlacement of DocCommentOuter => "outer"; DocCommentInner => "inner"
    , escapePayloadText rawText ] astNode []

debugAttributeArgument : PhaseDebug phase => AttributeArgument phase -> Forest
debugAttributeArgument astNode@(MkAstNode _ _ (AttributeArgumentStringLit rawSpelling)) =
  node "AttributeArgumentStringLit" [escapePayloadText rawSpelling] astNode []

-- `args` marks a written argument list, which distinguishes `#[a()]` from `#[a]`.
debugAttribute : PhaseDebug phase => Attribute phase -> Forest
debugAttribute astNode@(MkAstNode _ _ (MkAttributeNode attributeName attributeArguments)) =
  node "MkAttributeNode" [flagText "args" (isJust attributeArguments)] astNode
    [debugPlainName attributeName, many debugAttributeArgument (fromMaybe [] attributeArguments)]

debugVisibility : PhaseDebug phase => Maybe (AstNode phase VisibilityQualifier) -> Forest
debugVisibility = optional (leaf "VisibilityQualifier")

debugPauli : PhaseDebug phase => PauliString phase -> Forest
debugPauli astNode@(MkAstNode _ _ (MkPauliStringNode pauliOperators)) =
  node "MkPauliStringNode" [concatMap show (forget pauliOperators)] astNode []

debugSignedPauli : PhaseDebug phase => SignedPauliTerm phase -> Forest
debugSignedPauli astNode@(MkAstNode _ _ (MkSignedPauliTermNode sign pauliString)) =
  node "MkSignedPauliTermNode" [case sign of StabilizerPlus => "+"; StabilizerMinus => "-"] astNode [debugPauli pauliString]

--------------------------------------------------------------------------------
-- Patterns
--------------------------------------------------------------------------------

mutabilityText : Maybe Mutability -> String
mutabilityText = maybe "" show

mutual
  debugPattern : PhaseDebug phase => Pattern phase -> Forest
  debugPattern astNode@(MkAstNode _ _ patternNode) =
    case patternNode of
      PatternWildcard                              => node "PatternWildcard" [] astNode []
      PatternName mutability binderName            => node "PatternName" [mutabilityText mutability] astNode [debugName binderName]
      PatternPath patternPath                      => node "PatternPath" [] astNode [debugPath patternPath]
      PatternLiteral literalNode                   => node "PatternLiteral" [] astNode [debugLiteral literalNode]
      PatternParenthesized innerPattern            => node "PatternParenthesized" [] astNode [debugPattern innerPattern]
      PatternTuple elementPatterns                 => node "PatternTuple" [] astNode [many debugPattern (forget elementPatterns)]
      PatternArray elementPatterns                 => node "PatternArray" [] astNode [many debugPattern elementPatterns]
      PatternStruct patternPath fieldPatterns      => node "PatternStruct" [] astNode [debugPath patternPath, many debugPatternField fieldPatterns]
      PatternEnumTuple patternPath elementPatterns => node "PatternEnumTuple" [] astNode [debugPath patternPath, many debugPattern elementPatterns]

  debugPatternField : PhaseDebug phase => StructPatternField phase -> Forest
  debugPatternField astNode@(MkAstNode _ _ fieldNode) =
    case fieldNode of
      StructPatternFieldShorthand mutability fieldName =>
        node "StructPatternFieldShorthand" [mutabilityText mutability] astNode [debugName fieldName]
      StructPatternFieldExplicit fieldName nestedPattern =>
        node "StructPatternFieldExplicit" [] astNode [debugName fieldName, debugPattern nestedPattern]

debugQuantumPattern : PhaseDebug phase => QuantumMatchPattern phase -> Forest
debugQuantumPattern astNode@(MkAstNode _ _ patternNode) =
  case patternNode of
    QuantumPatternBasisStringRaw rawSpelling           => node "QuantumPatternBasisStringRaw" [escapePayloadText rawSpelling] astNode []
    QuantumPatternIntegerRaw rawSpelling               => node "QuantumPatternIntegerRaw" [escapePayloadText rawSpelling] astNode []
    QuantumPatternWildcard                             => node "QuantumPatternWildcard" [] astNode []
    QuantumPatternQenumVariant variantPath binderNames =>
      node "QuantumPatternQenumVariant" [] astNode [debugPath variantPath, many debugName binderNames]

--------------------------------------------------------------------------------
-- The recursive core: expressions, types, blocks and statements
--------------------------------------------------------------------------------

mutual
  debugExpr : PhaseDebug phase => Expr phase -> Forest
  debugExpr astNode@(MkAstNode _ _ expressionNode) =
    let (label, payload, children) = exprParts expressionNode in node label payload astNode children

  -- A block's final expression stands in for a statement, so it gets a snippet.
  debugFinalExpr : PhaseDebug phase => Expr phase -> Forest
  debugFinalExpr astNode@(MkAstNode _ _ expressionNode) =
    let (label, payload, children) = exprParts expressionNode
    in sourceNode label payload (showStatementPositionExprDoc PrettyStrict astNode) astNode children

  -- An expression's label, the data it holds directly rather than in child
  -- nodes, and its children in source order. The payload also names the form
  -- of `ctrl`/`adjoint`, which is otherwise only implied by the last child.
  -- Every constructor is listed, so new syntax cannot compile without deciding
  -- how the dump shows it.
  exprParts : PhaseDebug phase => ExpressionNode phase -> (String, List String, List Forest)
  exprParts expressionNode =
    case expressionNode of
      ExprLiteral literalNode => ("ExprLiteral", [], [debugLiteral literalNode])
      ExprName valueName      => ("ExprName", [], [debugName valueName])
      ExprPath valuePath      => ("ExprPath", [], [debugPath valuePath])
      ExprBuiltin builtin     => ("ExprBuiltin", [show builtin], [])
      ExprSelf selfReceiver   => ("ExprSelf", [symbolText (selfSymbol {phase} selfReceiver)], [])
      ExprParenthesized innerExpression => ("ExprParenthesized", [], [debugExpr innerExpression])
      ExprTuple elementExpressions      => ("ExprTuple", [], [many debugExpr (forget elementExpressions)])
      ExprArray elementExpressions      => ("ExprArray", [], [many debugExpr elementExpressions])
      ExprRepeatedArray repeatedElement repeatCount =>
        ("ExprRepeatedArray", [], [debugExpr repeatedElement, debugExpr repeatCount])
      ExprStructLiteral valuePath fieldInitializers =>
        ("ExprStructLiteral", [], [debugPath valuePath, many debugFieldInitializer fieldInitializers])
      ExprCall callee arguments => ("ExprCall", [], [debugExpr callee, many debugExpr arguments])
      ExprMethodCall receiver methodName arguments =>
        ("ExprMethodCall", [], [debugExpr receiver, debugMember methodName, many debugExpr arguments])
      ExprField accessedObject fieldName                 => ("ExprField", [], [debugExpr accessedObject, debugMember fieldName])
      ExprTupleIndex accessedObject index                => ("ExprTupleIndex", [escapePayloadText index], [debugExpr accessedObject])
      ExprIndex accessedObject index                     => ("ExprIndex", [], [debugExpr accessedObject, debugExpr index])
      ExprUnary unaryOperator operand                    => ("ExprUnary", [], [leaf "UnaryOperator" unaryOperator, debugExpr operand])
      ExprBinary binaryOperator leftOperand rightOperand => ("ExprBinary", [], [debugExpr leftOperand, leaf "BinaryOperator" binaryOperator, debugExpr rightOperand])
      ExprRange rangeStart rangeOperator rangeEnd =>
        ("ExprRange", [], [optional debugExpr rangeStart, leaf "RangeOperator" rangeOperator, optional debugExpr rangeEnd])
      ExprCast operand castTargetType => ("ExprCast", [], [debugExpr operand, debugTy castTargetType])
      ExprBlock block                 => ("ExprBlock", [], [debugBlock block])
      ExprIf ifNode                   => ("ExprIf", [], [debugIf ifNode])
      ExprQIf (MkQuantumIfNode qifCondition thenBranch elseBranch) =>
        ("ExprQIf", [], [debugExpr qifCondition, debugQuantumBranch thenBranch, optional debugQuantumBranch elseBranch])
      ExprSIf (MkStateIfNode sifCondition thenExpr elseExpr) =>
        ("ExprSIf", [], [debugExpr sifCondition, debugExpr thenExpr, debugExpr elseExpr])
      ExprMatch (MkClassicalMatchNode scrutinee matchArms) =>
        ("ExprMatch", [], [debugExpr scrutinee, many debugMatchArm matchArms])
      ExprQMatch (MkQuantumMatchNode scrutinee matchArms) =>
        ("ExprQMatch", [], [debugExpr scrutinee, many debugQuantumArm matchArms])
      ExprSMatch (MkStateMatchNode scrutinee matchArms) =>
        ("ExprSMatch", [], [debugExpr scrutinee, many debugQuantumArm matchArms])
      ExprLoop loopBody                       => ("ExprLoop", [], [debugBlock loopBody])
      ExprWhile loopCondition loopBody        => ("ExprWhile", [], [debugExpr loopCondition, debugBlock loopBody])
      ExprFor binderPattern iterable loopBody => ("ExprFor", [], [debugPattern binderPattern, debugExpr iterable, debugBlock loopBody])
      ExprBreak breakValue                    => ("ExprBreak", [], [optional debugExpr breakValue])
      ExprContinue                            => ("ExprContinue", [], [])
      ExprReturn returnValue                  => ("ExprReturn", [], [optional debugExpr returnValue])
      ExprCtrl (ControlledCallable controlQbits onBasis callable) =>
        ("ExprCtrl", ["callable"], [many debugExpr (forget controlQbits), optional debugBasis onBasis, debugExpr callable])
      ExprCtrl (ControlledBlock controlQbits onBasis controlledBlock) =>
        ("ExprCtrl", ["block"], [many debugExpr (forget controlQbits), optional debugBasis onBasis, debugBlock controlledBlock])
      ExprAdjoint (AdjointOfCallable callable)  => ("ExprAdjoint", ["callable"], [debugExpr callable])
      ExprAdjoint (AdjointBlock adjointedBlock) => ("ExprAdjoint", ["block"], [debugBlock adjointedBlock])

  debugBasis : PhaseDebug phase => AstNode phase String -> Forest
  debugBasis astNode = node "ControlBasis" [escapePayloadText astNode.nodeValue] astNode []

  debugFieldInitializer : PhaseDebug phase => AstNode phase (FieldInitializerNode phase) -> Forest
  debugFieldInitializer astNode@(MkAstNode _ _ fieldInitializer) =
    case fieldInitializer of
      FieldInitShorthand fieldName           => node "FieldInitShorthand" [] astNode [debugName fieldName]
      FieldInitExplicit fieldName fieldValue => node "FieldInitExplicit" [] astNode [debugName fieldName, debugExpr fieldValue]

  -- Children only: the owning node already names the construct.
  debugIf : PhaseDebug phase => ClassicalIfNode phase -> Forest
  debugIf (MkClassicalIfNode ifCondition thenBlock elseBranch) =
    group [debugExpr ifCondition, debugBlock thenBlock, optional debugElse elseBranch]

  debugElse : PhaseDebug phase => ClassicalElseNode phase -> Forest
  debugElse (ElseBlock elseBlock) = debugBlock elseBlock
  debugElse (ElseChainedIf astNode@(MkAstNode _ _ chainedIfNode)) = node "MkClassicalIfNode" [] astNode [debugIf chainedIfNode]

  debugQuantumBranch : PhaseDebug phase => QuantumBranchNode phase -> Forest
  debugQuantumBranch (QuantumBranchBlock branchBlock)     = debugBlock branchBlock
  debugQuantumBranch (QuantumBranchExpression branchExpression) = debugExpr branchExpression

  debugMatchArm : PhaseDebug phase => ClassicalMatchArm phase -> Forest
  debugMatchArm astNode@(MkAstNode _ _ (MkClassicalMatchArmNode armPattern armGuard armBody)) =
    node "MkClassicalMatchArmNode" [flagText "guarded" (isJust armGuard)] astNode
      [debugPattern armPattern, optional debugExpr armGuard, debugExpr armBody]

  debugQuantumArm : PhaseDebug phase => QuantumMatchArm phase -> Forest
  debugQuantumArm astNode@(MkAstNode _ _ (MkQuantumMatchArmNode armPattern armBody)) =
    node "MkQuantumMatchArmNode" [] astNode [debugQuantumPattern armPattern, debugExpr armBody]

  debugTy : PhaseDebug phase => Ty phase (Expr phase) -> Forest
  debugTy astNode@(MkAstNode _ _ typeNode) =
    case typeNode of
      TyPrimitive primitiveName       => node "TyPrimitive" [showTypPrimLeaf primitiveName] astNode []
      TyPath typePath                 => node "TyPath" [] astNode [debugPath typePath]
      TyUnit                          => node "TyUnit" [] astNode []
      TyParenthesized nestedType      => node "TyParenthesized" [] astNode [debugTy nestedType]
      TyTuple elementTypes            => node "TyTuple" [] astNode [many debugTy (forget elementTypes)]
      TyArray elementType arrayLength => node "TyArray" [] astNode [debugTy elementType, debugExpr arrayLength]
      TySlice elementType             => node "TySlice" [] astNode [debugTy elementType]
      TyReference borrowKind nestedType =>
        node "TyReference" [] astNode [leaf "BorrowKind" borrowKind, debugTy nestedType]
      TyQualified quantumUsageQualifier nestedType =>
        node "TyQualified" [] astNode [leaf "QuantumUsageQualifier" quantumUsageQualifier, debugTy nestedType]
      TyFunction functionEffect functionParameters returnType =>
        node "TyFunction" [] astNode
          [optional (leaf "FunctionEffect") functionEffect, many debugTypeParameter functionParameters, optional debugTy returnType]

  debugTypeParameter : PhaseDebug phase => AstNode phase (FunctionTypeParameterNode phase (Expr phase)) -> Forest
  debugTypeParameter astNode@(MkAstNode _ _ (MkFunctionTypeParameterNode parameterName parameterType)) =
    node "MkFunctionTypeParameterNode" [] astNode [debugPlainName parameterName, debugTy parameterType]

  debugBlock : PhaseDebug phase => Block phase -> Forest
  debugBlock astNode@(MkAstNode _ _ (MkBlockNode innerDocs blockStatements finalExpression)) =
    node "MkBlockNode" [] astNode [many debugDoc innerDocs, many debugStatement blockStatements, optional debugFinalExpr finalExpression]

  debugStatement : PhaseDebug phase => Statement phase -> Forest
  debugStatement astNode@(MkAstNode _ _ statementNode) =
    case statementNode of
      StatementLet (MkLetBindingNode letQualifiers letPattern typeAnnotation letInitializer) =>
        withSource "StatementLet"
          [ many (leaf "QuantumStorageQualifier") letQualifiers, debugPattern letPattern
          , optional debugTy typeAnnotation, optional debugInitializer letInitializer ]
      StatementAssignment (MkAssignmentNode assignmentTarget assignmentOperator assignedValue) =>
        withSource "StatementAssignment"
          [debugAssignmentTarget assignmentTarget, leaf "AssignmentOperator" assignmentOperator, debugExpr assignedValue]
      StatementSemiExpression statementExpression => withSource "StatementSemiExpression" [debugExpr statementExpression]
      StatementExpression statementExpression     => withSource "StatementExpression" [debugExpr statementExpression]
    where
      withSource : String -> List Forest -> Forest
      withSource label = sourceNode label [] (showStatementDoc PrettyStrict astNode) astNode

  -- Children only: the marker and value belong to the let statement.
  debugInitializer : PhaseDebug phase => LetInitializerNode phase -> Forest
  debugInitializer (MkLetInitializerNode initializerMarker initializerValue) =
    group [leaf "InitializerMarker" initializerMarker, debugExpr initializerValue]

  debugAssignmentTarget : PhaseDebug phase => AssignmentTarget phase -> Forest
  debugAssignmentTarget astNode@(MkAstNode _ _ targetNode) =
    case targetNode of
      AssignTargetName targetName              => node "AssignTargetName" [] astNode [debugName targetName]
      AssignTargetIndex targetObject index     => node "AssignTargetIndex" [] astNode [debugExpr targetObject, debugExpr index]
      AssignTargetField targetObject fieldName => node "AssignTargetField" [] astNode [debugExpr targetObject, debugMember fieldName]
      AssignTargetTupleIndex targetObject index =>
        node "AssignTargetTupleIndex" [escapePayloadText index] astNode [debugExpr targetObject]

--------------------------------------------------------------------------------
-- Contracts and functions
--------------------------------------------------------------------------------

debugPredicate : PhaseDebug phase => ContractPredicate phase (Expr phase) -> Forest
debugPredicate astNode@(MkAstNode _ _ predicateNode) =
  case predicateNode of
    ContractClean qbitArgument                      => node "ContractClean" [] astNode [debugExpr qbitArgument]
    ContractBasis qbitArgument pauliString          => node "ContractBasis" [] astNode [debugExpr qbitArgument, debugPauli pauliString]
    ContractSeparable qbitArgument                  => node "ContractSeparable" [] astNode [debugExpr qbitArgument]
    ContractIsolated qbitArgument                   => node "ContractIsolated" [] astNode [debugExpr qbitArgument]
    ContractProduct firstQbitSet otherQbitSets      => node "ContractProduct" [] astNode [many debugExpr (firstQbitSet :: forget otherQbitSets)]
    ContractStabilized qbitArgument stabilizerTerms => node "ContractStabilized" [] astNode [debugExpr qbitArgument, many debugSignedPauli (forget stabilizerTerms)]

debugContract : PhaseDebug phase => ContractClause phase (Expr phase) -> Forest
debugContract astNode@(MkAstNode _ _ (RequiresClause predicate)) = node "RequiresClause" [] astNode [debugPredicate predicate]
debugContract astNode@(MkAstNode _ _ (EnsuresClause predicate))  = node "EnsuresClause" [] astNode [debugPredicate predicate]

debugParameter : PhaseDebug phase => FunctionParameter phase -> Forest
debugParameter astNode@(MkAstNode _ _ parameterNode) =
  case parameterNode of
    NormalParameter parameterDocs mutability parameterName parameterType =>
      node "NormalParameter" [] astNode
        [many debugDoc parameterDocs, optional (leaf "Mutability") mutability, debugName parameterName, debugTy parameterType]
    ReceiverParameter parameterDocs receiverBorrow =>
      node "ReceiverParameter" [] astNode [many debugDoc parameterDocs, optional (leaf "BorrowKind") receiverBorrow]

-- Children only: the owning item or impl member names the declaration.
debugFunction : PhaseDebug phase => FunctionDeclarationNode phase -> Forest
debugFunction
    (MkFunctionDeclarationNode functionDocs functionAttributes visibility constness functionEffect functionName functionParameters returnType supportKinds contractClauses functionBody) =
  group
    [ many debugDoc functionDocs, many debugAttribute functionAttributes, debugVisibility visibility
    , optional (leaf "FunctionConstness") constness, optional (leaf "FunctionEffect") functionEffect
    , debugName functionName, many debugParameter functionParameters, optional debugTy returnType
    , many (leaf "SupportKind") supportKinds, many debugContract contractClauses, debugBlock functionBody ]

-- Outer docs and attributes are listed as children, so snippets start at the
-- declaration's head instead of repeating them.
functionWithoutPreamble : FunctionDeclarationNode phase -> FunctionDeclarationNode phase
functionWithoutPreamble = { functionDocs := [], functionAttributes := [] }

debugImplFunction : PhaseDebug phase => FunctionDeclaration phase -> Forest
debugImplFunction astNode@(MkAstNode astInfo metadata functionDeclarationNode) =
  sourceNode "MkFunctionDeclarationNode" []
    (showFunctionDeclarationDoc PrettyStrict (MkAstNode astInfo metadata (functionWithoutPreamble functionDeclarationNode)))
    astNode [debugFunction functionDeclarationNode]

--------------------------------------------------------------------------------
-- Type declarations and items
--------------------------------------------------------------------------------

-- Docs, attributes, visibility and name: the common head of a declaration.
declarationHead :
     PhaseDebug phase
  => List (DocComment phase) -> List (Attribute phase) -> Maybe (AstNode phase VisibilityQualifier)
  -> Name phase -> List Forest
declarationHead declarationDocs declarationAttributes visibility declaredName =
  [many debugDoc declarationDocs, many debugAttribute declarationAttributes, debugVisibility visibility, debugName declaredName]

debugStructField : PhaseDebug phase => AstNode phase (StructFieldNode phase) -> Forest
debugStructField astNode@(MkAstNode _ _ (MkStructFieldNode declarationDocs declaredName declaredType)) =
  node "MkStructFieldNode" [] astNode [many debugDoc declarationDocs, debugName declaredName, debugTy declaredType]

debugEnumVariant : PhaseDebug phase => AstNode phase (EnumVariantNode phase) -> Forest
debugEnumVariant astNode@(MkAstNode _ _ (MkEnumVariantNode declarationDocs declaredName variantBody)) =
  case variantBody of
    VariantUnit                 => variant "unit" []
    VariantTuple payloadTypes   => variant "tuple" [many debugTy (forget payloadTypes)]
    VariantStruct payloadFields => variant "struct" [many debugStructField payloadFields]
  where
    variant : String -> List Forest -> Forest
    variant variantForm payload = node "MkEnumVariantNode" [variantForm] astNode ([many debugDoc declarationDocs, debugName declaredName] ++ payload)

debugQEnumVariant : PhaseDebug phase => AstNode phase (QEnumVariantNode phase) -> Forest
debugQEnumVariant astNode@(MkAstNode _ _ (MkQEnumVariantNode declarationDocs declaredName payloadTypes)) =
  node "MkQEnumVariantNode" [] astNode [many debugDoc declarationDocs, debugName declaredName, many debugTy (forget payloadTypes)]

itemWithoutPreamble : ItemNode phase -> ItemNode phase
itemWithoutPreamble itemNode =
  case itemNode of
    ItemFunction functionDeclaration => ItemFunction (functionWithoutPreamble functionDeclaration)
    ItemModule declarationNode       => ItemModule ({ moduleDocs := [] } declarationNode)
    ItemUse declarationNode          => ItemUse ({ useDocs := [] } declarationNode)
    ItemConst declarationNode        => ItemConst ({ constDocs := [] } declarationNode)
    ItemStruct declarationNode       => ItemStruct ({ structDocs := [], structAttributes := [] } declarationNode)
    ItemEnum declarationNode         => ItemEnum ({ enumDocs := [], enumAttributes := [] } declarationNode)
    ItemQEnum declarationNode        => ItemQEnum ({ qenumDocs := [], qenumAttributes := [] } declarationNode)
    ItemImpl declarationNode         => ItemImpl ({ implDocs := [] } declarationNode)

debugItem : PhaseDebug phase => Item phase -> Forest
debugItem astNode@(MkAstNode astInfo metadata itemNode) =
  case itemNode of
    ItemFunction functionDeclaration => withSource "ItemFunction" [] [debugFunction functionDeclaration]
    ItemModule (MkModuleDeclarationNode declarationDocs visibility declaredName ModuleExternal) =>
      withSource "ItemModule" ["external"] (declarationHead declarationDocs [] visibility declaredName)
    ItemModule (MkModuleDeclarationNode declarationDocs visibility declaredName (ModuleInline innerDocs moduleItems)) =>
      withSource "ItemModule" ["inline"]
        (declarationHead declarationDocs [] visibility declaredName ++ [many debugDoc innerDocs, many debugItem moduleItems])
    ItemUse (MkUseDeclarationNode declarationDocs visibility importPath importAlias) =>
      withSource "ItemUse" []
        [many debugDoc declarationDocs, debugVisibility visibility, debugPath importPath, optional debugPlainName importAlias]
    ItemConst (MkConstDeclarationNode declarationDocs visibility declaredName declaredType constValue) =>
      withSource "ItemConst" [] (declarationHead declarationDocs [] visibility declaredName ++ [debugTy declaredType, debugExpr constValue])
    ItemStruct (MkStructDeclarationNode declarationDocs declarationAttributes visibility declaredName structFields) =>
      withSource "ItemStruct" [] (declarationHead declarationDocs declarationAttributes visibility declaredName ++ [many debugStructField structFields])
    ItemEnum (MkEnumDeclarationNode declarationDocs declarationAttributes visibility declaredName variants) =>
      withSource "ItemEnum" [] (declarationHead declarationDocs declarationAttributes visibility declaredName ++ [many debugEnumVariant variants])
    ItemQEnum (MkQEnumDeclarationNode declarationDocs declarationAttributes visibility declaredName variants) =>
      withSource "ItemQEnum" [] (declarationHead declarationDocs declarationAttributes visibility declaredName ++ [many debugQEnumVariant variants])
    ItemImpl (MkImplDeclarationNode declarationDocs implTarget implFunctions) =>
      withSource "ItemImpl" [] [many debugDoc declarationDocs, debugPath implTarget, many debugImplFunction implFunctions]
  where
    withSource : String -> List String -> List Forest -> Forest
    withSource label payload =
      sourceNode label payload (showItemDoc PrettyStrict (MkAstNode astInfo metadata (itemWithoutPreamble itemNode))) astNode

--------------------------------------------------------------------------------
-- Entry point
--------------------------------------------------------------------------------

||| Structural dump of the AST with every located node, its full NodeId,
||| half-open source span, compiler provenance and resolved symbols; see the
||| format at the top of this module. Inferred types live in the type
||| checker's tables, not in this AST.
public export
showAstDebug : PhaseDebug phase => SourceFile phase -> String
showAstDebug astNode@(MkAstNode astInfo _ (MkSourceFileNode fileDocs sourceFileItems)) =
  "phase=" ++ phaseLabel {phase} ++ " file=" ++ escapePayloadText astInfo.span.file ++ "\n" ++
  renderSource (layoutForest astInfo.span.file 0
    (node "MkSourceFileNode" [] astNode [many debugDoc fileDocs, many debugItem sourceFileItems]))
