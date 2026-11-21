module Parser.ExpressionParseTest

import TestFramework
import Parser.Helper

%default total

||| Tokens that cannot start a let pattern, with the kind the error names.
nonPatternTokens : List (String, String)
nonPatternTokens =
  [ ("measr", "builtin measr")
  , ("5", "raw integer literal `5`")
  , ("5.0", "raw float literal `5.0`")
  , ("b'a'", "raw byte literal `b'a'`")
  , ("b\"hi\"", "raw byte string literal `b\"hi\"`")
  , ("bs\"01\"", "raw basis string literal `bs\"01\"`")
  , ("\"hi\"", "raw string literal `\"hi\"`")
  , ("true", "boolean literal true")
  , ("zero", "state literal zero")
  , ("i32", "primitive type i32")
  ]

||| Each token stands where `fn f() {let ` expects a pattern, at column 13.
nonPatternTokenTests : List TestResult
nonPatternTokenTests = concatMap describedByKind nonPatternTokens
  where
    describedByKind : (String, String) -> List TestResult
    describedByKind (token, kind) =
      test "\{kind} in place of a let pattern is described by kind" $
        parseErrorDetails "fn f() {let \{token} = 1;}" `shouldBe`
          parseErrorAt (1, 13) (1, 13 + length token) "expected 'a pattern', but got \{kind}"

||| Expressions the parser rejects as not yet supported: the token that starts
||| each one, the rest of it, and the message, which spans the first token.
unsupportedExpressions : List (String, String, String)
unsupportedExpressions =
  [ ("qif", " &q {1} qelse {0}", "Quantum if expressions are not yet supported.")
  , ("match", " value {0 => false}", "Match expressions are not yet supported.")
  , ("qmatch", " &q {0 => f(), 1 => g()}", "Quantum match expressions are not yet supported.")
  , ("sif", " &q then zero selse one", "State if expressions are not yet supported.")
  , ("smatch", " &q {0 => zero, 1 => one}", "State match expressions are not yet supported.")
  , ("Point", " {x: 1, y: 2}", "Struct literal expressions are not yet supported.")
  , ("self", ".field", "Self expressions are not yet supported.")
  , ("Data", "::Left", "Path expressions are not yet supported.")
  , ("b'a'", "", "Byte literals are not yet supported.")
  , ("b\"hi\"", "", "Byte string literals are not yet supported.")
  , ("zero", "", "State literals are not yet supported.")
  ]

||| Each expression is a function body, `fn f() {...}`, so it starts at column 9.
unsupportedExpressionTests : List TestResult
unsupportedExpressionTests = concatMap rejectionTest unsupportedExpressions
  where
    rejectionTest : (String, String, String) -> List TestResult
    rejectionTest (token, followingText, message) =
      test "\{token}\{followingText} is rejected: \{message}" $
        parseErrorDetails "fn f() {\{token}\{followingText}}" `shouldBe`
          parseErrorAt (1, 9) (1, 9 + length token) message

||| Each form whose element may be followed only by a separator or by the
||| form's closing token.
misplacedNames : List (String, Nat, String)
misplacedNames =
  [ ("fn f() {g(a z)}", 13, "',' or ')'")
  , ("fn f() {x.m(a z)}", 15, "',' or ')'")
  , ("fn f() {ctrl(a z) {}}", 16, "',' or ')'")
  , ("fn f() {ctrl(q).apply(H z)}", 25, "')'")
  , ("fn f() {adjoint(g z)}", 19, "')'")
  , ("fn f() {(a z)}", 12, "',' or ')'")
  , ("fn f() {(a, b z)}", 15, "',' or ')'")
  , ("fn f() {[a z]}", 12, "',', ';' or ']'")
  , ("fn f() {[a, b z]}", 15, "',' or ']'")
  , ("fn f() {[a; b z]}", 15, "']'")
  , ("fn f() {a[i z]}", 13, "']'")
  , ("fn f() {let (a z) = t;}", 16, "',' or ')'")
  , ("fn f() {let (a, b z) = t;}", 19, "',' or ')'")
  , ("fn f() {let [a z] = t;}", 16, "',' or ']'")
  ]

export
runExpressionParseTests : IO Bool
runExpressionParseTests = runTests $ Test.do

  -- Literals

  test "boolean literals parse" $
    printsUnchangedStrict "fn booleans() { true; false }"

  test "float literals keep their spelling" $
    printsUnchangedStrict "fn floats() { 1.0; 12E+99_f64 }"

  test "the unit literal parses" $
    printsUnchangedStrict "fn unit() { () }"

  test "string literals keep their spelling" $
    printsUnchangedStrict "fn string() { \"hello\" }"

  -- Assignments

  -- The other print tests are written in the printer's spacing; this one
  -- checks that spacing is normalized.
  test "braces are printed with a space inside" $
    parseAndPrettyPrintStrict "fn assign() {x = 1; {2}}" `shouldBe` Right "fn assign() { x = 1; { 2 } }"

  test "compound assignment statements parse" $
    printsUnchangedStrict "fn assign() { x += 1; x <<= 2; x &= 3; }"

  test "index and field expressions are assignment targets" $
    printsUnchangedStrict "fn assign() { a[i] = 1; p.x = 2; }"

  test "a call is not an assignment target" $
    parseErrorDetails "fn f() {f() = 1;}" `shouldBe`
      parseErrorAt (1, 13) (1, 14) "Expression is not a valid assignment target."

  test "an assignment must end in a semicolon" $
    parseErrorDetails "fn f() {x = 1 y = 2;}" `shouldBe`
      parseErrorAt (1, 15) (1, 16) "expected ';', but got identifier \"y\""

  -- Let bindings

  test "basis string literals initialize inferred let bindings" $
    printsUnchangedStrict ("fn states() { let a = bs\"10110010\"; let b = bs\"++----++\"; " ++
                           "let c = bs\"10+-+-001\"; let d = bs\"iiiiIIIII\"; }")

  test "let patterns may be tuples with wildcards" $
    printsUnchangedStrict "fn destructure() { let (a, b, c) = (1, 2, 3); let (x, _, z) = (1, 2, 3); }"

  test "an array let pattern may have a type annotation" $
    printsUnchangedStrict "fn measure() { let [b0, b1, b2]: [bit; 3] = measr(qs); }"

  test "mutable let bindings can be reassigned" $
    printsUnchangedStrict ("fn mutable() { let mut x: i32 = 0; x = 5; let mut values = [0, 0]; " ++
                           "values[0] = 10; }")

  test "let bindings accept quantum storage qualifiers" $
    printsUnchangedStrict ("fn allocate() { let linear q: qbit = qalloc(); " ++
                           "let affine a: qbit = qalloc(); let scratch linear qs: [qbit; " ++
                           "2] = qalloc(2); let affine scratch t: qbit = qalloc(); }")

  test "conflicting quantum usage qualifiers on let bindings are rejected" $
    parseErrorDetails "fn bad() {let linear affine q: qbit = qalloc();}" `shouldBe`
      parseErrorAt (1, 22) (1, 28) "Cannot combine `linear` and `affine` storage qualifiers."

  test "duplicate scratch qualifiers on let bindings are rejected" $
    parseErrorDetails "fn bad() {let scratch scratch q: qbit = qalloc();}" `shouldBe`
      parseErrorAt (1, 23) (1, 30) "Duplicate `scratch` storage qualifier."

  test "let bindings accept the auto-uncompute initializer" $
    printsUnchangedStrict "fn compute() { let q: qbit := f(q); let result := compute_value(); }"

  test "let bindings report the markers accepted after a pattern" $
    parseErrorDetails "fn f() {let x + 1;}" `shouldBe`
      parseErrorAt (1, 15) (1, 16) "expected ':', '=' or ':=', but got symbol +"

  test "let bindings report the markers accepted after a type annotation" $
    parseErrorDetails "fn f() {let x: i32 + 1;}" `shouldBe`
      parseErrorAt (1, 20) (1, 21) "expected '=' or ':=', but got symbol +"

  testEach "a let binding must end in a semicolon" parseErrorDetails
    [ ("fn f() {let x = 1 let y = 2;}", parseErrorAt (1, 19) (1, 22) "expected ';', but got keyword let")
    , ("fn f() {let x: i32 = 1 let y = 2;}", parseErrorAt (1, 24) (1, 27) "expected ';', but got keyword let")
    ]

  test "mut in a let pattern must be followed by a name" $
    parseErrorDetails "fn f() {let mut 5 = 1;}" `shouldBe`
      parseErrorAt (1, 13) (1, 16) "`mut` must be followed by a binder name."

  nonPatternTokenTests

  test "an outer doc comment in place of a let pattern is described by kind" $
    parseErrorDetails "fn f() { let /// doc\nx = 1; }" `shouldBe`
      parseErrorAt (1, 14) (1, 21) "expected 'a pattern', but got outer doc comment \"/// doc\""

  test "an inner doc comment in place of a let pattern is described by kind" $
    parseErrorDetails "fn f() { let //! doc\nx = 1; }" `shouldBe`
      parseErrorAt (1, 14) (1, 21) "expected 'a pattern', but got inner doc comment \"//! doc\""

  -- Array types

  test "an array type's length may be an expression" $
    printsUnchangedLax "fn arrays() { let b: [i32; 2 + 2]; }"

  test "an array type's parenthesized length keeps its parentheses" $
    printsUnchangedLax "fn arrays() { let b: [i32; (2 + 2)] = [1, 2, 3, 4]; }"

  test "an array type's length may be a named constant" $
    parseAndPrettyPrintStrict "const N: i64 = 4;\nfn arrays() { let c: [i32; N]; }" `shouldBe`
      Right "const N: i64 = 4;\nfn arrays() { let c: [i32; N]; }"

  test "array type reports valid continuations after its element type" $
    parseErrorDetails "fn arrays() { let b: [i32 value]; }" `shouldBe`
      parseErrorAt (1, 27) (1, 32) "expected ']' or ';', but got identifier \"value\""

  test "end of input in place of a closing bracket is described by kind" $
    parseErrorDetails "fn f() { let b: [i32; 2 " `shouldBe`
      parseErrorAt (1, 25) (1, 26) "expected ']', but got end of input"

  -- Parentheses, tuples and arrays

  test "parenthesized expressions keep their parentheses" $
    printsUnchangedStrict "fn parenthesized() { (value) }"

  test "tuples keep the comma of a single element and drop other trailing commas" $
    parseAndPrettyPrintStrict "fn tuples() {(value,); (1, true); (1, (2, 3),)}" `shouldBe`
      Right "fn tuples() { (value,); (1, true); (1, (2, 3)) }"

  test "arrays may be empty or end in a trailing comma" $
    parseAndPrettyPrintStrict "fn arrays() {[]; [1, 2, 3]; [1, 2, 3,]}" `shouldBe`
      Right "fn arrays() { []; [1, 2, 3]; [1, 2, 3] }"

  test "repeated arrays parse" $
    printsUnchangedStrict "fn repeated() { [0; 3] }"

  -- Names and calls

  test "names are expressions" $
    printsUnchangedStrict "fn names() { value; result }"

  test "builtins may be called" $
    printsUnchangedStrict "fn builtins() { qalloc(); measr(q) }"

  test "functions may be called with or without arguments" $
    printsUnchangedStrict "fn calls() { f(); f(x, y) }"

  test "an underscore in place of an expression is described by kind" $
    parseErrorDetails "fn f() { let _ = 1; _(); }" `shouldBe`
      parseErrorAt (1, 21) (1, 22) "expected 'an expression', but got underscore"

  -- Operators and precedence

  test "unary operators group their operand" $
    parseAndPrettyPrintStrict "fn unary() {-x; !x; &x; &mut x}" `shouldBe`
      Right "fn unary() { (-x); (!x); (&x); (&mut x) }"

  test "unary operators nest and bind looser than postfix operators" $
    parseAndPrettyPrintStrict "fn unary() {!!flag; -f(x); &values[i]}" `shouldBe`
      Right "fn unary() { (!(!flag)); (-f(x)); (&values[i]) }"

  test "multiplicative operators bind tighter than additive ones, left to right" $
    parseAndPrettyPrintStrict "fn arithmetic() {1 + 2 * 3; 8 / 2 % 3 - 1}" `shouldBe`
      Right "fn arithmetic() { (1 + (2 * 3)); (((8 / 2) % 3) - 1) }"

  test "shifts bind tighter than comparisons, which bind tighter than logical and" $
    parseAndPrettyPrintStrict "fn comparisons() {a + b << c < d && e == f}" `shouldBe`
      Right "fn comparisons() { ((((a + b) << c) < d) && (e == f)) }"

  test "bitwise operators bind tighter than logical ones" $
    parseAndPrettyPrintStrict "fn logic() {a & b ^ c | d && e || f}" `shouldBe`
      Right "fn logic() { (((((a & b) ^ c) | d) && e) || f) }"

  test "every comparison operator parses" $
    parseAndPrettyPrintStrict "fn comparisons() {a <= b; a > b; a >= b; a != b}" `shouldBe`
      Right "fn comparisons() { (a <= b); (a > b); (a >= b); (a != b) }"

  test "comparison operators cannot be chained" $
    parseErrorDetails "fn f() {a < b < c}" `shouldBe`
      parseErrorAt (1, 15) (1, 16) ("Comparison operators cannot be chained. Parenthesize one " ++
                                    "of the comparisons.")

  test "mixed equality and ordering comparisons cannot be chained" $
    parseErrorDetails "fn f() {a < b == c}" `shouldBe`
      parseErrorAt (1, 15) (1, 17) ("Comparison operators cannot be chained. Parenthesize one " ++
                                    "of the comparisons.")

  test "parenthesized comparisons may be compared explicitly" $
    parseAndPrettyPrintStrict "fn comparisons() {(a < b) < c; a < (b < c)}" `shouldBe`
      Right "fn comparisons() { (((a < b)) < c); (a < ((b < c))) }"

  test "casts chain left to right" $
    parseAndPrettyPrintStrict "fn casts() {x as i32; value as i32 as i64}" `shouldBe`
      Right "fn casts() { (x as i32); ((value as i32) as i64) }"

  test "a cast may target an array type with an expression length" $
    printsUnchangedLax "fn casts() { x as [i32; 2 + 2] }"

  test "casts bind tighter than binary operators and looser than unary ones" $
    parseAndPrettyPrintStrict "fn casts() {-x as i32 + y as i32}" `shouldBe`
      Right "fn casts() { (((-x) as i32) + (y as i32)) }"

  -- Ranges

  test "ranges may omit either bound" $
    parseAndPrettyPrintStrict "fn ranges() {1..5; 1..=5; 1..; ..5; ..=5; ..}" `shouldBe`
      Right "fn ranges() { (1..5); (1..=5); (1..); (..5); (..=5); (..) }"

  test "inclusive range requires an end expression" $
    parseErrorDetails "fn ranges() {1..=}" `shouldBe`
      parseErrorAt (1, 18) (1, 19) "expected 'an expression', but got symbol }"

  test "range bounds bind tighter than the range" $
    parseAndPrettyPrintStrict "fn ranges() {1 + 2..3 * 4; ..x as i32}" `shouldBe`
      Right "fn ranges() { ((1 + 2)..(3 * 4)); (..(x as i32)) }"

  test "open-ended ranges terminate at commas and closing delimiters" $
    parseAndPrettyPrintStrict "fn ranges() {g(1.., ..2, ..); [1.., ..]; (1.., ..)}" `shouldBe`
      Right "fn ranges() { g((1..), (..2), (..)); [(1..), (..)]; ((1..), (..)) }"

  -- Blocks and control flow

  test "a block may be a function's value" $
    printsUnchangedStrict "fn block() { { 1 } }"

  test "else-if chains nest to arbitrary depth" $
    printsUnchangedStrict "fn choose() { if a { 1 } else if b { 2 } else if c { 3 } else { 4 } }"

  test "if expressions require a braced body" $
    parseErrorDetails "fn f() {if ready}" `shouldBe`
      parseErrorAt (1, 17) (1, 18) "Expected a braced block starting with `{`, found instead: `}`."

  test "else must be followed by a block or an if" $
    parseErrorDetails "fn f() {if ready {1} else 2}" `shouldBe`
      parseErrorAt (1, 27) (1, 28) "expected '{' or 'if', but got raw integer literal `2`"

  test "loop, while and for expressions parse" $
    printsUnchangedStrict "fn control() { loop { break }; while ready { continue }; for x in values { x } }"

  test "loop expressions require a braced body" $
    parseErrorDetails "fn f() {loop}" `shouldBe`
      parseErrorAt (1, 13) (1, 14) "Expected a braced block starting with `{`, found instead: `}`."

  test "while expressions require a braced body after their condition" $
    parseErrorDetails "fn f() {while ready}" `shouldBe`
      parseErrorAt (1, 20) (1, 21) "Expected a braced block starting with `{`, found instead: `}`."

  test "for expressions require in after their binder" $
    parseErrorDetails "fn f() {for x y {}}" `shouldBe`
      parseErrorAt (1, 15) (1, 16) "expected 'in', but got identifier \"y\""

  test "for expressions require a binder before in" $
    parseErrorDetails "fn f() {for in values {}}" `shouldBe`
      parseErrorAt (1, 13) (1, 15) "expected 'for loop binder name', but got keyword in"

  test "non-final block-like expression statements need no semicolon" $
    printsUnchangedStrict ("fn control() { if ready { work(); } loop { break; " ++
                           "} while ready { continue; } for x in values { use_value(x); " ++
                           "} finish() }")

  test "a block may mix calls, ifs, lets, assignments and loops before its value" $
    printsUnchangedStrict ("fn progress() { first(); if ready { second(); } let x = third(); " ++
                           "target.field = fourth(); loop { break; } last() }")

  test "a missing semicolon is reported after several well-formed statements" $
    parseErrorDetails ("fn progress() {first(); if ready {second();} let x = third(); " ++
                       "fourth() let y = fifth();}") `shouldBe`
      parseErrorAt (1, 72) (1, 75) "Expected `;` or `}`, found instead: `let`."

  -- Strict style shows each statement's grouping, so `(-value)` is visibly a
  -- statement of its own rather than a subtraction from the block.
  test "statement-leading block expressions stop before following expression tokens" $
    parseAndPrettyPrintStrict ("fn boundaries() {if ready {} -value; loop {} (value); " ++
                               "while ready {} [0]; for x in values {} {1} ctrl(&q0) {} -other; " ++
                               "adjoint {} [1]}") `shouldBe`
      Right ("fn boundaries() { if ready { } (-value); loop { } (value); while ready { } [0]; " ++
             "for x in values { } { 1 } ctrl((&q0)) { } (-other); adjoint { } [1] }")

  test "parenthesized block-like expressions retain ordinary continuation syntax" $
    parseAndPrettyPrintStrict "fn continuation() {(if ready {1} else {2}) + 3}" `shouldBe`
      Right "fn continuation() { ((if ready { 1 } else { 2 }) + 3) }"

  test "break and return accept values; continue is valueless" $
    printsUnchangedStrict "fn exits() { break 1; continue; return; return value }"

  -- Heads of if, while and for

  -- As in Rust, the head of `if`, `while` or `for` does not allow struct
  -- literals, so a constant directly before the block is just a name.
  testEach "an uppercase name directly before a head's block is a name" parseAndPrettyPrintLax
    [ ("fn f() {if FLAG {} else if FLAG {}}", Right "fn f() { if FLAG { } else if FLAG { } }")
    , ("fn f() {while i < N {}}", Right "fn f() { while i < N { } }")
    , ("fn f() {for i in 0..N {}}", Right "fn f() { for i in 0..N { } }")
    , ("fn f() {if !FLAG {}}", Right "fn f() { if !FLAG { } }")
    ]

  testEach "struct literals stay unsupported inside a head's nested expressions" parseErrorDetails
    [ ("fn f() {if g(X {}) {}}", parseErrorAt (1, 14) (1, 15) "Struct literal expressions are not yet supported.")
    , ("fn f() {if (X {}) {}}", parseErrorAt (1, 13) (1, 14) "Struct literal expressions are not yet supported.")
    ]

  -- Quantum control and adjoint

  test "controlled callables may be applied" $
    printsUnchangedLax "fn f() { ctrl(q0, q1).apply(H)(q2) }"

  test "controlled callables accept borrowed qbits and a basis" $
    printsUnchangedLax "fn f() { ctrl(&q0, &q1).on(bs\"10\").apply(H)(&q2) }"

  test "controlled callables may apply any function" $
    printsUnchangedLax "fn f() { ctrl(q0, q1).on(bs\"++\").apply(f)(q2, q3) }"

  test "controlled blocks parse" $
    printsUnchangedLax "fn f() { ctrl(&q0, &q1) { H(&q2); } }"

  test "controlled blocks accept a basis" $
    printsUnchangedLax "fn f() { ctrl(&q0, &q1).on(bs\"++\") { f(&q2, &q3); } }"

  test "non-final quantum modifier blocks need no semicolon" $
    printsUnchangedLax "fn f() { ctrl(&q0) { H(&q1); } adjoint { H(&q1); } finish() }"

  test "control expression requires a control qbit" $
    parseErrorDetails "fn f() {ctrl().apply(H)(q)}" `shouldBe`
      parseErrorAt (1, 9) (1, 15) "`ctrl` requires at least one control qbit."

  test "a control expression accepts only one basis" $
    parseErrorDetails "fn f() {ctrl(q).on(bs\"1\").on(bs\"0\").apply(H)(r)}" `shouldBe`
      parseErrorAt (1, 27) (1, 29) "A control expression can contain only one `.on(...)` clause."

  test "ctrl must be followed by its controls" $
    parseErrorDetails "fn f() {ctrl q}" `shouldBe`
      parseErrorAt (1, 14) (1, 15) "expected '`(` after `ctrl`', but got identifier \"q\""

  test "controls must be followed by apply or a block" $
    parseErrorDetails "fn f() {ctrl(q) + 1}" `shouldBe`
      parseErrorAt (1, 17) (1, 18) "expected '`.apply(...)` or a controlled block', but got symbol +"

  test "adjoint makes a higher-order callable" $
    printsUnchangedLax "fn use_adjoint() { let f_adjoint = adjoint(f); }"

  test "adjoint callables may be applied" $
    printsUnchangedLax "fn f() { adjoint(f)(q1, q2, q3) }"

  test "adjoint blocks parse" $
    printsUnchangedLax "fn f() { adjoint { f(&q1, &q2, &q3); } }"

  test "adjoint requires one callable" $
    parseErrorDetails "fn f() {adjoint()}" `shouldBe`
      parseErrorAt (1, 16) (1, 18) "`adjoint(...)` requires one callable expression."

  test "adjoint must be followed by a callable or a block" $
    parseErrorDetails "fn f() {adjoint q}" `shouldBe`
      parseErrorAt (1, 17) (1, 18) "expected '`(` or `{` after `adjoint`', but got identifier \"q\""

  -- Postfix expressions and comma lists

  test "calls, indexing, fields, methods and tuple indices chain in any order" $
    printsUnchangedStrict "fn postfix() { factory(a, b)[i].field.method(c)[j].0.next().value }"

  test "an unclosed index ending a postfix chain is reported at end of input" $
    parseErrorDetails "fn postfix() {factory(a)[i].field.method(c)[j" `shouldBe`
      parseErrorAt (1, 46) (1, 47) "expected ']', but got end of input"

  test "nested comma lists each accept a trailing comma" $
    parseAndPrettyPrintStrict "fn commas() {outer(inner(a, b,), [first(), second(),], (x, y,),)}" `shouldBe`
      Right "fn commas() { outer(inner(a, b), [first(), second()], (x, y)) }"

  test "a comma list rejects a missing middle element" $
    parseErrorDetails "fn commas() {outer(first(),, third())}" `shouldBe`
      parseErrorAt (1, 28) (1, 29) "expected 'an expression', but got symbol ,"

  misplacedNameTests "what may follow an element is reported" misplacedNames

  -- Not yet supported

  unsupportedExpressionTests

  -- Node identifiers

  testEach "node identifiers follow source order through nested control flow" parseAndListNodeIds
    [ ("fn f() { if a {1} else if b {2} else {3} }",
       Right [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18])
    , ("fn f() { for x in v { x } }", Right [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11])
    ]
