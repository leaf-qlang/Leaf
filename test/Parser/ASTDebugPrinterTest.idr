module Parser.ASTDebugPrinterTest

import Data.List
import Data.List1
import Data.Maybe
import Data.String

import Compiler.Frontend.ASTData
import Compiler.Frontend.ASTPhases
import Compiler.Frontend.Desugarer.Desugar
import Compiler.Frontend.Source
import Compiler.Frontend.Syntax.AST
import Compiler.Frontend.Syntax.Attribute
import Compiler.Frontend.Syntax.Common
import Compiler.Frontend.Syntax.Contract
import Compiler.Frontend.Syntax.Doc
import Compiler.Frontend.Syntax.Literal
import Compiler.Frontend.Syntax.Name
import Compiler.Frontend.Syntax.Pattern
import Compiler.Frontend.Syntax.Type
import Compiler.Frontend.Token
import Compiler.Frontend.Utils.ASTDebugPrinter
import Compiler.Frontend.Utils.ASTPrettyPrinter
import Compiler.Frontend.Utils.SourceText
import Expect
import Parser.Fixtures
import Parser.Helper

%default covering

--------------------------------------------------------------------------------
-- Reading dumps
--------------------------------------------------------------------------------

||| The fragments that occur on no node heading, e.g. `"BinaryOperator +"`.
missingLines : List String -> String -> List String
missingLines fragments output = filter (\fragment => not (any (isInfixOf fragment) (debugNodeHeaders output))) fragments

||| The fragments missing from the dump of a parsed source.
missingFromParsed : List String -> String -> Either String (List String)
missingFromParsed fragments source = map (missingLines fragments) (debugAstOf source)

||| Lines of a parsed dump containing a fragment.
parsedLinesWith : String -> String -> Either String (List String)
parsedLinesWith fragment source = map (filter (isInfixOf fragment) . debugNodeLines) (debugAstOf source)

||| The expected (ID, label) pairs with no node heading. Direct fixtures
||| exercise AST families intentionally rejected by today's parser. IDs
||| identify the actual descendants, not text in snippets.
missingNodes : List (Nat, String) -> String -> List (Nat, String)
missingNodes expected output = filter (not . present) expected
  where
    present : (Nat, String) -> Bool
    present (number, label) =
      any (\header => take 2 (words header) == ["#" ++ show number, label]) (debugNodeHeaders output)

||| The leading `phase=... file=...` line.
phaseLine : String -> String
phaseLine output = fromMaybe "" (head' (lines output))

||| A heading's snippet, with its backticks.
snippetOf : String -> String
snippetOf header = pack (dropWhile (/= '`') (unpack header))

||| The last `count` characters of a text.
ending : Nat -> String -> String
ending count text = substr (minus (length text) count) count text

||| Whether a snippet, with its two backticks, fits the preview limit.
snippetWithinLimit : String -> Bool
snippetWithinLimit header = length (snippetOf header) <= snippetLimit + 2

--------------------------------------------------------------------------------
-- Fixtures
--------------------------------------------------------------------------------

function : SurfaceBlock -> FunctionDeclarationNode SurfaceAstPhase
function body = MkFunctionDeclarationNode [] [] Nothing Nothing Nothing (nameAt 2 "f") [] Nothing [] [] body

sourceWith : List SurfaceItem -> SurfaceSourceFile
sourceWith items = surfaceAt 0 (MkSourceFileNode [] items)

expressionDump : ExpressionNode SurfaceAstPhase -> String
expressionDump expression = showAstDebug $ sourceWith
  [surfaceAt 1 (ItemFunction (function (valueBlockAt 3 (surfaceAt 4 expression))))]

nestedBlocks : Nat -> SurfaceExpr
nestedBlocks Z = integerAt 10 "1"
nestedBlocks (S depth) = surfaceAt (11 + depth * 2)
  (ExprBlock (valueBlockAt (12 + depth * 2) (nestedBlocks depth)))

||| The dump of a file holding only an inner block doc with this text.
docDump : String -> String
docDump raw = showAstDebug (surfaceAt 0 (MkSourceFileNode [innerDocAt 1 DocCommentBlock raw] []))

||| The doc comment's heading in `docDump`.
docHeading : String -> String
docHeading raw = fromMaybe "" (find (isInfixOf "MkDocCommentNode") (debugNodeHeaders (docDump raw)))

||| The characters of a dump that are among the given code points.
rawCharsIn : List Int -> String -> List Char
rawCharsIn codes output = filter (\c => elem (ord c) codes) (unpack output)

||| Code points the dump must not show raw, with the escape it shows instead:
||| terminal controls, line separators, and invisible format characters across
||| Unicode scripts and planes. The snippet delimiter, which the dump also
||| uses raw around snippets, is checked separately.
escapedCharacters : List (Int, String)
escapedCharacters =
  [ (0, "\\x00"), (8, "\\x08"), (27, "\\x1b"), (127, "\\x7f"), (133, "\\x85"), (159, "\\x9f")
  , (0x2028, "\\u{2028}"), (0x2029, "\\u{2029}")
  , (0x00AD, "\\u{ad}"), (0x0600, "\\u{600}"), (0x061C, "\\u{61c}"), (0x06DD, "\\u{6dd}")
  , (0x070F, "\\u{70f}"), (0x0890, "\\u{890}"), (0x08E2, "\\u{8e2}"), (0x180E, "\\u{180e}")
  , (0x200B, "\\u{200b}"), (0x200F, "\\u{200f}"), (0x202A, "\\u{202a}"), (0x202E, "\\u{202e}")
  , (0x2066, "\\u{2066}"), (0x2069, "\\u{2069}"), (0x206A, "\\u{206a}"), (0x206F, "\\u{206f}")
  , (0xFEFF, "\\u{feff}"), (0xFFF9, "\\u{fff9}"), (0x110BD, "\\u{110bd}"), (0x110CD, "\\u{110cd}")
  , (0x13430, "\\u{13430}"), (0x1343F, "\\u{1343f}"), (0x1BCA0, "\\u{1bca0}"), (0x1D173, "\\u{1d173}")
  , (0xE0001, "\\u{e0001}"), (0xE0020, "\\u{e0020}"), (0xE007F, "\\u{e007f}")
  ]

||| Whether a string literal holding the character with this code point shows
||| it, in both its payload and its snippet, only as the given escape.
escapedEverywhere : (Int, String) -> Bool
escapedEverywhere (code, escaped) =
  let output = expressionDump (ExprLiteral (surfaceAt 11 (LiteralStringRaw ("\"" ++ singleton (chr code) ++ "\""))))
  in null (rawCharsIn [code] output) &&
     null (missingLines ["LiteralStringRaw \"" ++ escaped ++ "\"", "`\"" ++ escaped ++ "\"`"] output)

resolvedAt : Nat -> a -> ResolvedAstNode a
resolvedAt number = resolvedAstNode (fixtureInfo number) WrittenCode

typedAt : Nat -> a -> TypedAstNode a
typedAt number = typedAstNode (fixtureInfo number) WrittenCode

resolvedName : Nat -> String -> Nat -> ResolvedName
resolvedName number text symbol = resolvedAt number (MkResolvedNameNode text (MkSymbolId symbol))

resolvedDump : String
resolvedDump =
  let body : ResolvedExpr = resolvedAt 4 $ ExprTuple $
        resolvedAt 5 (ExprName (resolvedName 6 "x" 20)) :::
          [ resolvedAt 7 (ExprName (resolvedName 8 "x" 21))
          , resolvedAt 9 (ExprPath (resolvedAt 10 (MkResolvedPathNode "M" ["N"] (MkSymbolId 22))))
          , resolvedAt 11 (ExprSelf (MkSymbolId 23))
          , resolvedAt 12 (ExprField (resolvedAt 13 (ExprSelf (MkSymbolId 23))) (resolvedAt 14 (MkNameNode "field")))
          ]
      declaration : ConstDeclarationNode ResolvedAstPhase =
        MkConstDeclarationNode [] Nothing (resolvedName 2 "N" 19) (resolvedAt 3 TyUnit) body
  in showAstDebug (resolvedAt 0 (MkSourceFileNode [] [resolvedAt 1 (ItemConst declaration)]))

typedDump : String
typedDump =
  let receiver : TypedExpr = typedAt 4 (ExprSelf (MkSymbolId 30))
      member : MemberName TypedAstPhase = typedAt 5 (MkResolvedNameNode "field" (MkSymbolId 31))
      value : TypedExpr = typedAt 6 (ExprField receiver member)
      declaration : ConstDeclarationNode TypedAstPhase = MkConstDeclarationNode [] Nothing
        (typedAt 2 (MkResolvedNameNode "N" (MkSymbolId 32))) (typedAt 3 TyUnit) value
  in showAstDebug (typedAt 0 (MkSourceFileNode [] [typedAt 1 (ItemConst declaration)]))

--------------------------------------------------------------------------------
-- Previews
--------------------------------------------------------------------------------

previewEscape : Char -> List Char
previewEscape '\n' = ['\\', 'n']
previewEscape c = [c]

||| Deliberately failing sentinel: the prefix renderer must never force this.
||| assert_total permits this unreachable test branch under %default covering.
unrequestedText : () -> SourceText
unrequestedText () = assert_total (idris_crash "preview evaluated text past its limit")

||| Exercise AST-to-document rendering, not just consumption of a document
||| already built by hand. Rendering a later child must fail these tests even
||| if its eventual text would be discarded by truncation.
previewName : NameNode -> String
previewName (MkNameNode spelling) =
  if spelling == "hidden"
    then assert_total (idris_crash "preview rendered an unrequested AST child")
    else spelling

[previewPhase] PhasePretty SurfaceAstPhase where
  prettyName = previewName
  prettyMemberName = previewName
  prettyPathDoc _ = assert_total (idris_crash "preview rendered an unrequested type path")

||| Rendering the complete path would force the sentinel. Its visible prefix
||| already exceeds the preview limit, so path consumers must keep it lazy.
[pathPreviewPhase] PhasePretty SurfaceAstPhase where
  prettyName (MkNameNode spelling) = spelling
  prettyMemberName (MkNameNode spelling) = spelling
  prettyPathDoc _ = Append (text (pack (replicate 100 'p'))) (unrequestedText ())

preview : SourceText -> String
preview = renderSourcePreview (\c => [c]) snippetLimit

longInteger : SurfaceExpr
longInteger = integerAt 10 (pack (replicate 100 '1'))

||| A preview that starts with `leading`, continues with `filler` and is cut
||| off by the ellipsis, which takes the limit's last character.
truncatedPreview : String -> Char -> String
truncatedPreview leading filler =
  leading ++ pack (replicate (minus (minus snippetLimit 1) (length leading)) filler) ++ "…"

||| The preview of `longInteger` after `leading`.
expectedPrefix : String -> String
expectedPrefix leading = truncatedPreview leading '1'

export
runASTDebugPrinterTests : IO Bool
runASTDebugPrinterTests = runTests $ Test.do
  test "path previews do not request the full path string" $
    let target = pathAt 10 "Target"
        expression = surfaceAt 11 (ExprPath target)
        binding = surfaceAt 12 (StatementLet (MkLetBindingNode []
          (surfaceAt 13 (PatternName Nothing (nameAt 14 "x")))
          (Just (surfaceAt 15 (TyPath target))) Nothing))
    in [ preview (showExprDoc @{pathPreviewPhase} PrettyStrict expression)
       , preview (showStatementDoc @{pathPreviewPhase} PrettyStrict binding)
       ] `shouldBe` [truncatedPreview "" 'p', truncatedPreview "let x: " 'p']

  test "full paths and previews agree across all AST phases" $
    let first = "self"
        rest = replicate 20 "part"
        surfacePath : PathNode SurfaceAstPhase = MkPathNode
          (surfaceAt 1 PathSegmentSelf) (map (\s => surfaceAt 2 (PathSegmentName s)) rest)
        canonicalPath : PathNode CanonicalAstPhase = MkPathNode
          (canonicalAstNode (fixtureInfo 1) WrittenCode PathSegmentSelf)
          (map (\s => canonicalAstNode (fixtureInfo 2) WrittenCode (PathSegmentName s)) rest)
        resolvedPath = MkResolvedPathNode first rest (MkSymbolId 5)
        documents = [ prettyPathDoc {phase=SurfaceAstPhase} surfacePath
                    , prettyPathDoc {phase=CanonicalAstPhase} canonicalPath
                    , prettyPathDoc {phase=ResolvedAstPhase} resolvedPath
                    , prettyPathDoc {phase=TypedAstPhase} resolvedPath ]
        full = joinBy "::" (first :: rest)
    in map (\document => (renderSource document, preview document)) documents
      `shouldBe` replicate 4 (full, substr 0 (minus snippetLimit 1) full ++ "…")

  test "collection previews never render children beyond the visible prefix" $
    let hidden = nameExprAt 20 "hidden"
        callee = nameExprAt 22 "f"
        receiver = nameExprAt 24 "x"
        expressions = [surfaceAt 4 (ExprTuple (longInteger ::: [hidden])),
                       surfaceAt 4 (ExprArray [longInteger, hidden]),
                       surfaceAt 4 (ExprCall callee [longInteger, hidden]),
                       surfaceAt 4 (ExprMethodCall receiver (nameAt 26 "m") [longInteger, hidden])]
    in sameInBothStyles (\style => map (\expr => preview (showExprDoc @{previewPhase} style expr)) expressions)
         (map expectedPrefix ["(", "[", "f(", "x.m("])

  test "pattern and type collections defer their later children" $
    let pattern = surfaceAt 30 (PatternTuple
          (surfaceAt 31 (PatternLiteral (surfaceAt 32 (LiteralIntegerRaw (pack (replicate 100 '1'))))) :::
            [surfaceAt 33 (PatternName Nothing (nameAt 34 "hidden"))]))
        ty = surfaceAt 40 (TyTuple (surfaceAt 41 (TyArray (surfaceAt 42 (TyPrimitive TypPrimI32)) longInteger) :::
               [surfaceAt 43 (TyPath (pathAt 44 "Hidden"))]))
        binding = surfaceAt 50 (StatementLet (MkLetBindingNode [] pattern Nothing Nothing))
        typedBinding = surfaceAt 51 (StatementLet (MkLetBindingNode []
          (surfaceAt 52 (PatternName Nothing (nameAt 53 "x"))) (Just ty) Nothing))
    in map (\statement => preview (showStatementDoc @{previewPhase} PrettyStrict statement)) [binding, typedBinding]
      `shouldBe` map expectedPrefix ["let (", "let x: ([i32; "]

  test "function parameter previews defer later parameter names" $
    let first = surfaceAt 60 (NormalParameter [] Nothing (nameAt 61 "x")
          (surfaceAt 62 (TyArray (surfaceAt 63 (TyPrimitive TypPrimI32)) longInteger)))
        later = surfaceAt 64 (NormalParameter [] Nothing (nameAt 65 "hidden") (surfaceAt 66 TyUnit))
        declaration = { functionParameters := [first, later] } (function (valueBlockAt 3 (integerAt 4 "0")))
    in preview (showFunctionDeclarationDoc @{previewPhase} PrettyStrict (surfaceAt 1 declaration))
      `shouldBe` expectedPrefix "fn f(x: [i32; "

  test "debug escaping distinguishes control characters from literal backslash sequences" $
    map docHeading ["/*! a\nb */", "/*! a\\nb */", "/*! a\tb */", "/*! a\\tb */"] `shouldBe`
      [ "#1 MkDocCommentNode block inner /*! a\\nb */ @2:3-9"
      , "#1 MkDocCommentNode block inner /*! a\\\\nb */ @2:3-9"
      , "#1 MkDocCommentNode block inner /*! a\\tb */ @2:3-9"
      , "#1 MkDocCommentNode block inner /*! a\\\\tb */ @2:3-9" ]

  test "payloads and snippets escape control and format characters" $
    filter (not . escapedEverywhere) escapedCharacters `shouldBe` []

  test "debug escaping preserves visible Unicode text" $
    docHeading "/*! café λ 漢字 😀 */" `shouldBe` "#1 MkDocCommentNode block inner /*! café λ 漢字 😀 */ @2:3-9"

  test "a payload cannot imitate the separator of nodes sharing a line" $
    let raw = "/*! a > #7 Name b */"
    in (docHeading raw, debugNodeSurfaceIds (docDump raw))
      `shouldBe` ("#1 MkDocCommentNode block inner /*! a > \\#7 Name b */ @2:3-9", Just [0, 1])

  test "node headings are not split inside a snippet" $
    debugNodeHeaders "#1 StatementLet > #2 ExprName @1:1-9 `let a > #3`"
      `shouldBe` ["#1 StatementLet", "#2 ExprName @1:1-9 `let a > #3`"]

  test "a final expression's snippet keeps its statement-position parentheses" $
    parsedLinesWith "ExprMethodCall" "fn p() { let x = { (if a { 1 } else { 2 }).f() }; }"
      `shouldBe` Right ["#20 ExprMethodCall @1:20-47 `(if a { 1 } else { 2 }).f()`"]

  test "an item's snippet starts at its head, after the attributes it lists as children" $
    parsedLinesWith "ItemFunction" "#[qasm_gate]\nfn f() {}"
      `shouldBe` Right ["#1 ItemFunction @1:1-2:10 `fn f() { }`"]

  test "snippets use the same escaping as full payloads, the snippet delimiter included" $
    missingLines ["LiteralStringRaw \"a\\\\nb\\`\"", "`\"a\\\\nb\\`\"`"]
      (expressionDump (ExprLiteral (surfaceAt 11 (LiteralStringRaw "\"a\\nb`\""))))
      `shouldBe` []

  test "constants include their names, types, operators and literal nodes" $
    map debugNodeLabels (debugAstOf "const N: i32 = 1 + 2;") `shouldBe`
      Right ["MkSourceFileNode", "ItemConst", "Name", "TyPrimitive", "ExprBinary",
            "ExprLiteral", "LiteralIntegerRaw", "BinaryOperator", "ExprLiteral", "LiteralIntegerRaw"]

  test "the file is named once and spans are compact" $
    debugAstOf "const N: i32 = 1;" `shouldBe` Right (unlines
      [ "phase=surface file=\{fixtureFile}"
      , "#0 MkSourceFileNode @1:1-18"
      , "  #1 ItemConst @1:1-18 `const N: i32 = 1;`"
      , "    #2 Name N @1:7-8"
      , "    #3 TyPrimitive i32 @1:10-13"
      , "    #4 ExprLiteral > #5 LiteralIntegerRaw 1 @1:16-17"
      ])

  test "an only child with the same span shares its parent's line" $
    (parsedLinesWith " > " "fn f() { let y = x; }", parsedLinesWith "Name" "fn f() { g(x) }")
      `shouldBe` (Right ["#5 PatternName > #6 Name y @1:14-15", "#8 ExprName > #9 Name x @1:18-19"],
                  Right ["#2 Name f @1:4-5", "#4 ExprName > #5 Name g @1:10-11", "#7 ExprName > #8 Name x @1:12-13"])

  test "repeated provenance on a shared line is marked as the same" $
    map (\ast => filter (isInfixOf "ExprReturn") (debugNodeLines (showAstDebug (desugarSurfaceSyntax ast))))
      (lexThenParse "fn f() -> i32 { g() }")
      `shouldBe` Right [("#4.1 StatementSemiExpression [desugared return statement] > #4.2 " ++
                         "ExprReturn [same] > #7 ExprCall @1:17-20 `return g();`")]

  test "assignments traverse all target forms and their values" $
    missingFromParsed ["AssignTargetName", "AssignTargetIndex", "AssignTargetField", "AssignTargetTupleIndex 0",
                   "AssignmentOperator +=", "ExprBinary", "LiteralIntegerRaw 5", "MemberName x"]
      "fn f() { x = 1 + 2; a[0] += 3; p.x = 4; t.0 = 5; }" `shouldBe` Right []

  test "statements carry their strict source" $
    missingFromParsed ["StatementAssignment @1:10-20 `x = (1 + 2);`"] "fn f() { x = 1 + 2; }" `shouldBe` Right []

  test "only items, statements and final expressions carry snippets" $
    map (map headerLabel) (parsedLinesWith "`" "fn f() { g(1 + 2); h }")
      `shouldBe` Right ["ItemFunction", "StatementSemiExpression", "ExprName"]

  test "long snippets are truncated" $
    map (map (\line => let snippet = snippetOf line in (ending 2 snippet, length snippet)))
      (parsedLinesWith "StatementLet" ("fn f() { let x = " ++ joinBy " + " (replicate 40 "1") ++ "; }"))
      `shouldBe` Right [("…`", snippetLimit + 2)]

  test "preview truncation handles empty, exact and escaped boundaries" $
    map (\limit => renderSourcePreview previewEscape limit (Append "a" "\nb")) [0, 1, 2, 3, 4, 5]
      `shouldBe` ["", "…", "a…", "a…", "a\\nb", "a\\nb"]

  test "previews keep escapes whole across document chunks" $
    let document = Append "" (Append "λ\n" (Append "" (Append "abc" "\nxyz")))
    in map (\limit => renderSourcePreview previewEscape limit document) [1, 3, 4, 10, 11]
      `shouldBe` ["…", "λ…", "λ\\n…", "λ\\nabc\\nx…", "λ\\nabc\\nxyz"]

  test "a full preview never evaluates the remaining document" $
    renderSourcePreview previewEscape 3 (Append (Append "ab" "cd") (unrequestedText ()))
      `shouldBe` "ab…"

  -- 29 two-character escapes and the ellipsis fill the 60 characters.
  test "escaped overflow stops before an unrequested document tail" $
    renderSourcePreview previewEscape 60 (Append (text (pack (replicate 31 '\n'))) (unrequestedText ()))
      `shouldBe` (fastConcat (replicate 29 "\\n") ++ "…")

  test "escaped overflow stops across chunk boundaries" $
    renderSourcePreview previewEscape 4 (Append "\n" (Append "\n\n" (unrequestedText ())))
      `shouldBe` "\\n…"

  test "one escape larger than the preview proves overflow without reading the tail" $
    renderSourcePreview (\_ => unpack "\\u{61c}") 3 (Append "x" (unrequestedText ()))
      `shouldBe` "…"

  test "zero-length previews do not evaluate document contents" $
    renderSourcePreview previewEscape 0 (Append (unrequestedText ()) "")
      `shouldBe` ""

  test "deep debug trees retain every node while bounding each snippet" $
    let output = expressionDump (nestedBlocks 800).nodeValue
        headers = debugNodeHeaders output
        snippets = filter (isInfixOf "`") (debugNodeLines output)
    in (length (filter (isInfixOf "MkBlockNode") headers),
        filter (not . snippetWithinLimit) snippets,
        missingNodes [(10, "ExprLiteral"), (11, "LiteralIntegerRaw")] output)
      `shouldBe` (801, [], [])

  test "function types include effects, parameter names, array lengths and results" $
    missingFromParsed ["TyFunction", "FunctionEffect unitary", "MkFunctionTypeParameterNode", "MkNameNode x", "TyArray",
                   "ExprBinary", "LiteralIntegerRaw 2", "TyPrimitive bool"]
      "fn f(g: unitary fn(x: [i32; 2 + 2]) -> bool) {}" `shouldBe` Right []

  test "control and adjoint blocks expose their calls and operands" $
    missingFromParsed ["ExprCtrl block", "ExprAdjoint block", "ExprCall", "ExprUnary", "UnaryOperator &",
                       "Name H", "Name X", "MkBlockNode"]
      "fn f() { ctrl(&c) { H(&q); } adjoint { X(&q); } }" `shouldBe` Right []

  test "control and adjoint callable forms expose the basis and target" $
    missingFromParsed ["ExprCtrl callable", "ExprAdjoint callable", "ControlBasis bs\"10\"", "Name d",
                       "Name H", "Name g"]
      "fn f() { ctrl(c, d).on(bs\"10\").apply(H); adjoint(g) }" `shouldBe` Right []

  test "patterns and let qualifiers have structural nodes" $
    missingFromParsed ["PatternTuple", "PatternName", "PatternWildcard", "Name x", "QuantumStorageQualifier scratch",
                   "QuantumStorageQualifier affine", "InitializerMarker ="]
      "fn f() { let (x, _) = (1, 2); let scratch affine q = qalloc(); }" `shouldBe` Right []

  test "attributes, effects and qualified reference types keep their tokens" $
    missingFromParsed ["MkAttributeNode args", "MkNameNode qasm_gate", "AttributeArgumentStringLit \"g\"",
                       "VisibilityQualifier pub", "FunctionConstness const", "FunctionEffect unitary",
                       "TyQualified", "QuantumUsageQualifier affine", "TyReference", "BorrowKind &mut"]
      "#[qasm_gate(\"g\")] pub const unitary fn f(q: affine qbit, r: &mut i32) {}" `shouldBe` Right []

  test "attributes without an argument list are not marked" $
    parsedLinesWith "MkAttributeNode" "#[qasm_gate]\nfn f() {}" `shouldBe` Right ["#2 MkAttributeNode @1:1-13"]

  test "chained else-if is one node, not a repeated header" $
    map length (parsedLinesWith "MkClassicalIfNode" "fn f() { if a {1} else if b {2} else {3} }") `shouldBe` Right 1

  test "node ID extraction ignores hashes inside source strings" $
    debugNodeSurfaceIds (expressionDump (ExprLiteral (surfaceAt 10 (LiteralStringRaw "\"#123\""))))
      `shouldBe` Just [0, 1, 2, 3, 4, 10]

  test "desugared nodes show both ID components and only generated provenance" $
    map (\ast => let output = showAstDebug (desugarSurfaceSyntax ast) in
      (missingLines ["#5.1 TyQualified", "#5 TyPrimitive qbit", "#5.2 QuantumUsageQualifier linear",
                     "[inferred default qbit qualifier]"] output,
       phaseLine output,
       filter (isInfixOf "user written code") (lines output)))
      (lexThenParse "fn f(q: qbit) {}")
      `shouldBe` Right ([], "phase=canonical file=\{fixtureFile}", [])

  test "spans are half-open and name a file only when it differs" $
    let foreign : SurfaceExpr = surfaceAstNode (MkAstInfo (MkNodeId 4 0)
          (MkSourceSpan "other.lf" (MkSourcePos 1 2) (MkSourcePos 3 4))) ExprContinue
        output = showAstDebug (sourceWith [surfaceAt 1 (ItemFunction (function (valueBlockAt 3 foreign)))])
    in (phaseLine output, missingLines ["#3 MkBlockNode @2:3-9", "#4 ExprContinue @other.lf:1:2-3:4"] output)
      `shouldBe` ("phase=surface file=\{fixtureFile}", [])

  test "resolved names, paths and self retain distinct symbol IDs" $
    (phaseLine resolvedDump,
     missingLines ["Name N sym=19", "Name x sym=20", "Name x sym=21", "Path M::N sym=22", "ExprSelf sym=23"]
       resolvedDump)
      `shouldBe` ("phase=resolved file=\{fixtureFile}", [])

  test "members gain a symbol only at the typed phase" $
    (length (filter (isInfixOf "sym=") (debugNodeHeaders resolvedDump)),
     phaseLine typedDump,
     missingLines ["ExprSelf sym=30", "MemberName field sym=31"] typedDump)
      `shouldBe` (6, "phase=typed file=\{fixtureFile}", [])

  test "quantum if visits block and expression branches" $
    missingNodes [(10, "ExprLiteral"), (20, "MkBlockNode"), (21, "ExprLiteral"), (30, "ExprLiteral")]
      (expressionDump (ExprQIf (MkQuantumIfNode (integerAt 10 "0")
        (QuantumBranchBlock (valueBlockAt 20 (integerAt 21 "1")))
        (Just (QuantumBranchExpression (integerAt 30 "2")))))) `shouldBe` []

  test "state if visits its condition and both branches" $
    missingNodes [(10, "ExprLiteral"), (20, "ExprLiteral"), (30, "ExprLiteral")]
      (expressionDump (ExprSIf (MkStateIfNode (integerAt 10 "0") (integerAt 20 "1") (integerAt 30 "2")))) `shouldBe` []

  test "classical match visits patterns, guards and bodies" $
    missingNodes [(10, "ExprLiteral"), (20, "MkClassicalMatchArmNode"), (21, "PatternLiteral"),
                  (22, "LiteralIntegerRaw"), (30, "ExprLiteral"), (40, "ExprLiteral")]
      (expressionDump (ExprMatch (MkClassicalMatchNode (integerAt 10 "0")
        [surfaceAt 20 (MkClassicalMatchArmNode (surfaceAt 21 (PatternLiteral (surfaceAt 22 (LiteralIntegerRaw "1"))))
          (Just (integerAt 30 "2")) (integerAt 40 "3"))]))) `shouldBe` []

  test "quantum match visits variant paths and bound names" $
    missingNodes [(10, "ExprLiteral"), (20, "MkQuantumMatchArmNode"), (21, "QuantumPatternQenumVariant"),
                  (22, "Path"), (23, "PathSegmentName"), (24, "Name"), (30, "ExprLiteral")]
      (expressionDump (ExprQMatch (MkQuantumMatchNode (integerAt 10 "0")
        [surfaceAt 20 (MkQuantumMatchArmNode
          (surfaceAt 21 (QuantumPatternQenumVariant (pathAt 22 "Some") [nameAt 24 "q"]))
          (integerAt 30 "1"))]))) `shouldBe` []

  test "state match visits all arm pattern forms and bodies" $
    missingNodes [(20, "QuantumPatternBasisStringRaw"), (30, "QuantumPatternIntegerRaw"),
                  (40, "QuantumPatternWildcard"), (50, "ExprLiteral")]
      (expressionDump (ExprSMatch (MkStateMatchNode (integerAt 10 "0")
        [ surfaceAt 19 (MkQuantumMatchArmNode (surfaceAt 20 (QuantumPatternBasisStringRaw "bs\"0\""))
            (integerAt 21 "1"))
        , surfaceAt 29 (MkQuantumMatchArmNode (surfaceAt 30 (QuantumPatternIntegerRaw "1")) (integerAt 31 "2"))
        , surfaceAt 39 (MkQuantumMatchArmNode (surfaceAt 40 QuantumPatternWildcard) (integerAt 50 "3"))
        ]))) `shouldBe` []

  test "struct literals visit shorthand and explicit fields" $
    missingNodes [(10, "Path"), (20, "FieldInitShorthand"), (21, "Name"), (30, "FieldInitExplicit"),
                  (31, "Name"), (40, "ExprLiteral")]
      (expressionDump (ExprStructLiteral (pathAt 10 "Pair")
        [surfaceAt 20 (FieldInitShorthand (nameAt 21 "x")),
         surfaceAt 30 (FieldInitExplicit (nameAt 31 "y") (integerAt 40 "1"))])) `shouldBe` []

  test "nested modules traverse every declaration family" $
    let field = surfaceAt 20 (MkStructFieldNode [] (nameAt 21 "x") (surfaceAt 22 (TyPrimitive TypPrimI32)))
        items =
          [ surfaceAt 10 (ItemStruct (MkStructDeclarationNode [] [] Nothing (nameAt 11 "Point") [field]))
          , surfaceAt 30 (ItemEnum (MkEnumDeclarationNode [] [] Nothing (nameAt 31 "E")
              [ surfaceAt 32 (MkEnumVariantNode [] (nameAt 33 "A") VariantUnit)
              , surfaceAt 34 (MkEnumVariantNode [] (nameAt 35 "B") (VariantTuple (surfaceAt 36 TyUnit ::: [])))
              , surfaceAt 37 (MkEnumVariantNode [] (nameAt 38 "C") (VariantStruct [field])) ]))
          , surfaceAt 40 (ItemQEnum (MkQEnumDeclarationNode [] [] Nothing (nameAt 41 "Q")
              [surfaceAt 42 (MkQEnumVariantNode [] (nameAt 43 "A") (surfaceAt 44 (TyPrimitive TypPrimQbit) ::: []))]))
          , surfaceAt 50 (ItemImpl (MkImplDeclarationNode [] (pathAt 51 "Point")
              [surfaceAt 53 (function (valueBlockAt 54 (integerAt 55 "1")))]))
          , surfaceAt 60 (ItemUse (MkUseDeclarationNode [] Nothing (pathAt 61 "Point") (Just (nameAt 63 "P"))))
          , surfaceAt 70 (ItemModule (MkModuleDeclarationNode [] Nothing (nameAt 71 "external") ModuleExternal))
          ]
        outer = surfaceAt 1 (ItemModule (MkModuleDeclarationNode [] Nothing (nameAt 2 "M") (ModuleInline [] items)))
        output = showAstDebug (sourceWith [outer])
    in (missingNodes [(20, "MkStructFieldNode"), (22, "TyPrimitive"), (36, "TyUnit"), (42, "MkQEnumVariantNode"),
                      (44, "TyPrimitive"), (53, "MkFunctionDeclarationNode"), (55, "ExprLiteral"),
                      (63, "MkNameNode"), (71, "Name")] output,
        missingLines ["#1 ItemModule inline", "#70 ItemModule external", "#32 MkEnumVariantNode unit",
                      "#34 MkEnumVariantNode tuple", "#37 MkEnumVariantNode struct"] output)
      `shouldBe` ([], [])

  test "docs, support clauses and all contract predicates are traversed" $
    let pauli = surfaceAt 50 (MkPauliStringNode (PauliX ::: [PauliZ]))
        term = surfaceAt 51 (MkSignedPauliTermNode StabilizerMinus pauli)
        predicates = [ ContractClean (integerAt 10 "0"), ContractBasis (integerAt 12 "1") pauli,
                       ContractSeparable (integerAt 14 "2"), ContractIsolated (integerAt 16 "3"),
                       ContractProduct (integerAt 18 "4") (integerAt 20 "5" ::: []),
                       ContractStabilized (integerAt 22 "6") (term ::: []) ]
        contracts = map (\predicate => surfaceAt 40 (RequiresClause (surfaceAt 41 predicate))) predicates ++
          [surfaceAt 42 (EnsuresClause (surfaceAt 43 (ContractClean (integerAt 24 "7"))))]
        declaration = { functionDocs := [surfaceAt 60 (MkDocCommentNode DocCommentLine DocCommentOuter "/// docs")],
                        supportClause := [surfaceAt 61 SupportAdjoint, surfaceAt 62 SupportCtrl],
                        contractClauses := contracts } (function (valueBlockAt 3 (integerAt 4 "8")))
        output = showAstDebug (sourceWith [surfaceAt 1 (ItemFunction declaration)])
    in missingLines ["MkDocCommentNode line outer /// docs", "SupportKind adjoint", "SupportKind ctrl",
                     "RequiresClause", "EnsuresClause", "ContractClean", "ContractBasis", "ContractSeparable",
                     "ContractIsolated", "ContractProduct", "ContractStabilized", "MkSignedPauliTermNode -",
                     "MkPauliStringNode XZ"] output `shouldBe` []
