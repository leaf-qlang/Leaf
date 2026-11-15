module Utils.ASTPrettyPrinterTest

import Data.List1
import Data.String

import Compiler.Frontend.ASTPhases
import Compiler.Frontend.Desugarer.Desugar
import Compiler.Frontend.Syntax.AST
import Compiler.Frontend.Syntax.Doc
import Compiler.Frontend.Syntax.Name
import Compiler.Frontend.Syntax.Operator
import Compiler.Frontend.Syntax.ParseRules
import Compiler.Frontend.Syntax.Pattern
import Compiler.Frontend.Syntax.Type
import Compiler.Frontend.Token
import Compiler.Frontend.Utils.ASTDebugPrinter
import Compiler.Frontend.Utils.ASTPrettyPrinter
import Expect
import Parser.Fixtures
import Parser.Helper

%default covering

--------------------------------------------------------------------------------
-- Round trips
--------------------------------------------------------------------------------

||| Whether two trees print the same and have the same constructors in the same
||| order. Reparsed nodes have different IDs, spans and provenance, and text
||| alone would miss a call turning into a block statement followed by a
||| separate unit-expression statement.
sameSyntax : CanonicalSourceFile -> CanonicalSourceFile -> Bool
sameSyntax first second =
  debugNodeLabels (showAstDebug first) == debugNodeLabels (showAstDebug second) &&
  showSourceFileStrict first == showSourceFileStrict second

||| The printed forms of a source that do not reparse to its canonical tree:
||| both styles, for the surface tree and for the canonical tree, where explicit
||| parentheses have been removed and the printer must reconstruct grouping.
||| Left if the source itself does not parse.
roundTripFailures : String -> Either String (List String)
roundTripFailures source = do
  original <- lexThenParse source
  let canonical = desugarSurfaceSyntax original
      printed = concatMap (\style => [showSourceFile style original, showSourceFile style canonical])
                  [PrettyLax, PrettyStrict]
  Right (filter (not . reparsesAs canonical) printed)
  where
    reparsesAs : CanonicalSourceFile -> String -> Bool
    reparsesAs canonical text = either (const False) (sameSyntax canonical . desugarSurfaceSyntax) (lexThenParse text)

roundTrips : String -> Expectation (Either String (List String))
roundTrips source = roundTripFailures source `shouldBe` Right []

||| A source that lax style prints exactly as written, and that round trips.
printsAsWritten : String -> Expectation (Either String String, Either String (List String))
printsAsWritten source = (parseAndPrettyPrintLax source, roundTripFailures source) `shouldBe` (Right source, Right [])

||| Whether the lax rendering of the canonical tree, where every source
||| parenthesis is gone, contains every fragment; if not, the missing ones and
||| the rendering. Checking fragments rather than the whole rendering keeps
||| these tests independent of what desugaring adds, such as a function's
||| default effect and result or an `if`'s empty `else`.
canonicalHasAll : List String -> String -> Either String ()
canonicalHasAll fragments source = do
  printed <- map (showSourceFileLax . desugarSurfaceSyntax) (lexThenParse source)
  case filter (\fragment => not (isInfixOf fragment printed)) fragments of
    [] => Right ()
    missing => Left "missing \{show missing} from: \{printed}"

canonicalContains : List String -> String -> Expectation (Either String ())
canonicalContains fragments source = canonicalHasAll fragments source `shouldBe` Right ()

comparisonOperators : List String
comparisonOperators = ["==", "!=", "<", "<=", ">", ">="]

comparisonCases : List String
comparisonCases = do
  outer <- comparisonOperators
  inner <- comparisonOperators
  [ "fn f() { (a " ++ inner ++ " b) " ++ outer ++ " c }"
  , "fn f() { a " ++ outer ++ " (b " ++ inner ++ " c) }"
  ]

||| The symbols a token rule classifies differently from the given set, in
||| either direction. The result does not depend on the order of either.
misclassified : (Token -> Bool) -> List Symbol -> List Symbol
misclassified rule expected =
  filter (\symbol => rule (TokSym symbol) /= elem symbol expected) (map snd symbolTable)

--------------------------------------------------------------------------------
-- Fixtures
--------------------------------------------------------------------------------

moduleWith : List SurfaceDocComment -> List SurfaceItem -> SurfaceItem
moduleWith docs items = surface (ItemModule (MkModuleDeclarationNode [] Nothing (name "m") (ModuleInline docs items)))

export
runASTPrettyPrinterTests : IO Bool
runASTPrettyPrinterTests = runTests $ Test.do
  test "calls through fields remain distinct from method calls after desugaring" $
    roundTrips ("fn f() { (obj.f)(x); (obj.f)(); (obj.f)(x)(y); (obj.f(x))(y); " ++
                "(({ obj }).f)(x); ((if c { a } else { b }).f)(x); let z = (obj.f)(x); " ++
                "if (obj.f)(x) {} (obj.f)(x)[0] = y; }")

  test "field callees get parentheses while ordinary method calls stay compact" $
    canonicalContains ["(obj.f)(x);", "obj.f(x);", "({ obj }.f)(x);", "if (obj.f)(x) { }"]
      "fn f() { (obj.f)(x); obj.f(x); (({ obj }).f)(x); if (obj.f)(x) {} }"

  test "tuple indexing preserves numeric token boundaries" $
    roundTrips "fn f() { (1).0; (1.5).0; (1usize).0; (t.0).1 }"

  test "unparenthesized tuple indices separated by whitespace still round trip" $
    roundTrips "fn f() { t.0 .1 }"

  test "tuple-index assignment targets keep their parentheses" $
    roundTrips "fn f() { (t.0).1 = x; ((t.0).1).2 += y; (1).0 = z; }"

  test "block-like assignment bases keep statement-position parentheses after desugaring" $
    roundTrips ("fn f() { ({ a })[0] = x; ({ p }).x += y; ({ t }).0 = z; " ++
                "(if c { a } else { b })[0] = x; (ctrl(c) { a }).x = y; (adjoint { t }).0 = z; " ++
                "({ a }).field[0].0 = x; }")

  test "ordinary assignment targets remain compact" $
    canonicalContains ["a[0] = x;", "p.x += y;", "t.0 = z;"] "fn f() { a[0] = x; p.x += y; t.0 = z; }"

  -- Quantum if is currently rejected by the parser, so exercise its AST
  -- directly and distinguish the two possible owners of qelse.
  test "nested quantum ifs preserve which branch owns qelse in both styles" $
    let outerElse = qif (integer "0") (qif (integer "1") (integer "2") Nothing) (Just (integer "3"))
        innerElse = qif (integer "0") (qif (integer "1") (integer "2") (Just (integer "3"))) Nothing
    in sameInBothStyles (\style => (showExpr style outerElse, showExpr style innerElse))
         ("qif 0 { qif 1 2 } qelse 3", "qif 0 qif 1 2 qelse 3")

  test "quantum else cannot attach inside a return expression branch" $
    let branch = returning (qif (integer "1") (integer "2") Nothing)
    in sameInBothStyles (\style => showExpr style (qif (integer "0") branch (Just (integer "3"))))
         "qif 0 { return qif 1 2 } qelse 3"

  -- The condition is the longest expression, so these branches would join it:
  -- `qif 0 -2` is `0 - 2` and `qif 0 (1)` the call `0(1)`.
  test "a negated quantum then-branch is printed as a block" $
    inBothStyles (\style => showExpr style (qif (integer "0") (negated (integer "2")) Nothing))
      `shouldBe` ["qif 0 { -2 }", "qif 0 { (-2) }"]

  test "parenthesized and tuple quantum then-branches are printed as blocks" $
    let grouped = surface (ExprParenthesized (integer "1"))
        tuple = surface (ExprTuple (integer "1" ::: [integer "2"]))
    in map (showExpr PrettyLax) [qif (integer "0") grouped (Just (integer "3")), qif (integer "0") tuple Nothing]
      `shouldBe` ["qif 0 { (1) } qelse 3", "qif 0 { (1, 2) }"]

  test "a block quantum then-branch is not wrapped in a second block" $
    showExpr PrettyLax (qif (integer "0") (blockOf (integer "1")) Nothing) `shouldBe` "qif 0 { 1 }"

  -- After `qelse`, a leading `{` would be read as the whole branch, leaving
  -- `+ 3` to apply to the qif.
  test "quantum else-branches that start with a block are printed as blocks" $
    let leading = plus (blockOf (integer "2")) (integer "3")
    in inBothStyles (\style => showExpr style (qif (integer "0") (integer "1") (Just leading)))
      `shouldBe` ["qif 0 1 qelse { ({ 2 }) + 3 }", "qif 0 1 qelse ({ 2 } + 3)"]

  test "quantum else-branches that are a block or start with an operator print as they are" $
    map (\branch => showExpr PrettyLax (qif (integer "0") (integer "1") (Just branch)))
        [blockOf (integer "2"), negated (integer "2")]
      `shouldBe` ["qif 0 1 qelse { 2 }", "qif 0 1 qelse -2"]

  -- The then-branch is followed by `qelse`, so a block else-branch closes the
  -- qif and an operator after it applies to the whole qif.
  test "a quantum if ending in a block else-branch needs no parentheses before an operator" $
    let closed = qifWithBranches (integer "0") (QuantumBranchExpression (integer "1"))
                   (Just (QuantumBranchBlock (valueBlock (integer "2"))))
        unclosed = qif (integer "0") (integer "1") (Just (integer "2"))
    in map (\operand => showExpr PrettyLax (plus operand (integer "3"))) [closed, unclosed]
      `shouldBe` ["qif 0 1 qelse { 2 } + 3", "(qif 0 1 qelse 2) + 3"]

  -- An open range reads the next token as its bound unless it is a delimiter,
  -- so before `then`, `selse`, `qelse` or `=>` it must be closed off.
  test "an open range before a keyword is parenthesized, or printed as a block in a qif" $
    let openRange = surface (ExprRange (Just (integer "1")) (surface RangeExclusive) Nothing)
        arm = surface (MkClassicalMatchArmNode (surface PatternWildcard) (Just openRange) (integer "2"))
        matched = surface (ExprMatch (MkClassicalMatchNode (integer "0") [arm]))
    in map (showExpr PrettyLax)
         [ sif openRange (integer "2") (integer "3"), sif (integer "0") openRange (integer "3")
         , sif (integer "0") (returning openRange) (integer "3"), sif (integer "0") (integer "2") openRange
         , qif (integer "0") openRange (Just (integer "3")), qif (integer "0") openRange Nothing
         , matched ]
      `shouldBe`
         [ "sif (1..) then 2 selse 3", "sif 0 then (1..) selse 3"
         , "sif 0 then (return 1..) selse 3", "sif 0 then 2 selse 1.."
         , "qif 0 { 1.. } qelse 3", "qif 0 1.."
         , "match 0 { _ if (1..) => 2 }" ]

  test "a quantum then-branch printed as a block prints the same once it is a block" $
    let grouped = surface (ExprParenthesized (integer "1"))
        asBlock = qifWithBranches (integer "0") (QuantumBranchBlock (valueBlock grouped))
                    (Just (QuantumBranchExpression (integer "3")))
    in showExpr PrettyLax asBlock `shouldBe` showExpr PrettyLax (qif (integer "0") grouped (Just (integer "3")))

  test "a quantum condition ending in a quantum if without qelse is parenthesized" $
    showExpr PrettyLax (qif (qif (integer "1") (integer "2") Nothing) (integer "3") Nothing)
      `shouldBe` "qif (qif 1 2) 3"

  -- An exit absorbs whatever follows it, so it needs parentheses only where
  -- something that could continue it follows.
  test "return and break are parenthesized only where something follows them" $
    printsAsWritten ("fn f() { let x = a + return b; let y = a || return; let z = -return; " ++
                     "let w = a + (return b) * c; g(a + return b, c); let r = a..return b; " ++
                     "let s = (return 1) as u8; loop { break return 1; } }")

  -- Dropping the comma would leave the exit before `)` or `]`, where the parser
  -- reads a value.
  test "a list ending in a valueless exit keeps its trailing comma" $
    printsAsWritten ("fn f() { g(x, return,); h.m(return,); let a = [1, return,]; " ++
                     "let t = (1, return,); let u = (return,); loop { g(break,); } }")

  test "other lists lose their trailing comma" $
    parseAndPrettyPrintLax "fn f() { g(x, y,); let a = [1, 2,]; }"
      `shouldBe` Right "fn f() { g(x, y); let a = [1, 2]; }"

  test "continue needs no parentheses before an operator or postfix" $
    printsAsWritten "fn f() { loop { let y = continue + a; let z = continue.f(); let w = -continue; } }"

  -- The printer's handling of valueless exits (`endsInValuelessExit`, strict
  -- style's parentheses, trailing commas) and of open ranges in heads depends
  -- on these exact sets. If this fails, revisit those printer rules.
  test "the parser's terminator rules are the ones the printer is written for" $
    (misclassified isOptionalValueTerminator [SymSemi, SymComma, SymRBrace],
     misclassified isOpenRangeTerminator [SymSemi, SymComma, SymRParen, SymRBracket, SymRBrace])
      `shouldBe` ([], [])

  -- A `return` or `break` without a value can only precede `;`, `,` or `}`.
  test "strict style leaves out optional parentheses that would close after a valueless exit" $
    parseAndPrettyPrintStrict ("fn f() { let y = a || return; let z = -return; " ++
                               "let x = a + b || return; let v = a + return 1; }")
      `shouldBe` Right ("fn f() { let y = a || return; let z = -return; " ++
                        "let x = (a + b) || return; let v = (a + return 1); }")

  test "repeated prefix operators are spaced apart" $
    printsAsWritten "fn f() { - -x; a - - -b; & &x; !!x; }"

  test "quantum blocks used as postfix bases remain expressions" $
    roundTrips ("fn f() { (adjoint { g })(); (adjoint { q })[0]; (ctrl(c) { q }).x; " ++
                "(ctrl(c) { q }).0; (adjoint { q }).m(); }")

  test "quantum blocks keep grouping in operator and cast positions" $
    roundTrips ("fn f() { (adjoint { 1 }) + x; !(ctrl(c) { true }); " ++
                "(ctrl(c) { 0 })..(adjoint { 2 }); (adjoint { 1 }) as i32; }")

  test "standalone quantum block statements remain statements" $
    roundTrips "fn f() { ctrl(c) { H(&q); } adjoint { X(&q); } finish(); }"

  test "callable ctrl and adjoint forms need no extra parentheses" $
    parseAndPrettyPrintLax "fn f() { ctrl(c).apply(g)(q); adjoint(g)(q) }"
      `shouldBe` Right "fn f() { ctrl(c).apply(g)(q); adjoint(g)(q) }"

  test "all nested comparison operator combinations round trip on either side" $
    filter (\source => roundTripFailures source /= Right []) comparisonCases `shouldBe` []

  test "comparison grouping coexists with logical and arithmetic precedence" $
    roundTrips "fn f() { ((a + b < c) == flag) && (d > e || f <= g) }"

  test "arithmetic still uses minimal left-associative parentheses" $
    parseAndPrettyPrintLax "fn f() { a + b + c * d }" `shouldBe` Right "fn f() { a + b + c * d }"

  test "an inner line doc cannot swallow an empty block's closing brace" $
    let body = surface (MkBlockNode [innerDoc DocCommentLine "//! docs"] [] Nothing)
    in sameInBothStyles (\style => lexFixture (showBlock style body))
         (Right [TokSym SymLBrace, TokInnerDoc "//! docs", TokSym SymRBrace, TokEOF])

  test "mixed inner docs leave statements and the block value outside comments" $
    let docs = [innerDoc DocCommentBlock "/*! block */", innerDoc DocCommentLine "//! first",
                innerDoc DocCommentLine "//! second"]
        body = surface (MkBlockNode docs [surface (StatementSemiExpression (integer "7"))] (Just (integer "8")))
    in sameInBothStyles (\style => lexFixture (showBlock style body))
         (Right [TokSym SymLBrace, TokInnerDoc "/*! block */", TokInnerDoc "//! first", TokInnerDoc "//! second",
                TokIntLitRaw "7", TokSym SymSemi, TokIntLitRaw "8", TokSym SymRBrace, TokEOF])

  test "a module containing only an inner line doc retains its closing brace" $
    let item = moduleWith [innerDoc DocCommentLine "//! docs"] []
    in sameInBothStyles (\style => lexFixture (showItem style item))
         (Right [TokKw KwMod, TokIdent "m", TokSym SymLBrace, TokInnerDoc "//! docs", TokSym SymRBrace, TokEOF])

  test "module items remain outside preceding inner line docs" $
    let constant = surface (ItemConst (MkConstDeclarationNode [] Nothing (name "N")
                     (surface (TyPrimitive TypPrimI32)) (integer "7")))
        item = moduleWith [innerDoc DocCommentLine "//! docs"] [constant]
    in sameInBothStyles (\style => lexFixture (showItem style item))
         (Right [TokKw KwMod, TokIdent "m", TokSym SymLBrace, TokInnerDoc "//! docs",
                TokKw KwConst, TokIdent "N", TokSym SymColon, TokTypPrim TypPrimI32,
                TokSym SymEq, TokIntLitRaw "7", TokSym SymSemi, TokSym SymRBrace, TokEOF])

  test "heads round trip with and without parentheses" $
    roundTrips "fn f() { if (FLAG) {} if FLAG {} if -B {} while x < B {} for i in a..B {} for i in (0..) {} }"

  -- As in Rust, a head does not allow struct literals, so a name before the
  -- block needs no parentheses; an open range would still take the block.
  test "heads are parenthesized only when the following block is at risk" $
    canonicalContains ["if FLAG { }", "if a { }", "while x < B { }", "while x < b { }",
                       "if x == B[0] { }", "for i in (0..) { }", "for i in 0..N { }"]
      ("fn f() { if (FLAG) {} if (a) {} while (x < (B)) {} while (x < (b)) {} if (x == B[0]) {} " ++
       "for i in (0..) {} for i in 0..(N) {} }")

  -- A `return` value is a new expression, which allows struct literals again,
  -- so there an uppercase name before the block would start one.
  test "an uppercase name in a head's return value is still parenthesized" $
    map (\head => showExpr PrettyLax (surface (ExprWhile head emptyBlock))) [returning (nameExpr "X"),
                                                                             returning (nameExpr "x")]
      `shouldBe` ["while (return X) { }", "while return x { }"]

  test "block-like operands outside statement position need no parentheses" $
    printsAsWritten ("fn f() { let x = if a { 1 } else { 2 } + 3; let y = { 1 }.foo(); " ++
                     "let z = a + loop { break 1 }; }")

  test "a block-like expression starting a longer statement is parenthesized" $
    let source = ("fn f() { ({ 1 }) + 2 * 3; (if a {1} else {2}).foo(); (({ 1 }) + 2) * 3; " ++
                  "(loop { break 1 })..2; }")
        fragments = ["({ 1 }) + 2 * 3;", "(if a { 1 } else { 2 }).foo();", "({ 1 } + 2) * 3;", "(loop { break 1 })..2;"]
    in (canonicalHasAll fragments source, roundTripFailures source) `shouldBe` (Right (), Right [])

  test "a block-like expression starting a final expression is parenthesized" $
    map (showBlock PrettyLax) [valueBlock (plus (blockOf (integer "1")) (integer "2")),
                               valueBlock (blockOf (integer "1"))]
      `shouldBe` ["{ ({ 1 }) + 2 }", "{ { 1 } }"]

  test "a float tuple-index base needs no parentheses" $
    canonicalContains ["let x = 1.5.0;", "let y = (1).0;"] "fn f() { let x = (1.5).0; let y = (1).0; }"

  test "empty braces print like an empty block" $
    sameInBothStyles (\style => showItem style (moduleWith [] [])) "mod m { }"
