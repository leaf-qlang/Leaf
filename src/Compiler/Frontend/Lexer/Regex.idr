module Compiler.Frontend.Lexer.Regex

import Text.ILex
import Text.ILex.RExp.Unicode as Uni

%default total
%hide Prelude.(>>)
%hide Prelude.not

--------------------------------------------------------------------------------
-- Whitespace and line structure.
--
-- Leaf accepts CRLF, LF, and bare CR as line breaks. Like Rust (Unicode
-- Pattern_White_Space), it also accepts space, tab, vertical tab, form feed,
-- next line (U+0085), the left-to-right and right-to-left marks (U+200E,
-- U+200F), and the line and paragraph separators (U+2028, U+2029) as
-- whitespace. Only CR and LF end a line or a line comment.
--
-- The non-ASCII whitespace characters are matched one at a time by their own
-- rule instead of inside the `plus` loop of `asciiWhitespace`: inside the loop,
-- the first byte of such a character would make the pinned ilex DFA keep
-- extending after already accepted whitespace, so an unsupported character
-- sharing that first byte (such as U+2012) would be reported at the start of
-- the whitespace instead of at its own position (see the known-limitation note
-- at the top of Rules.idr).
--------------------------------------------------------------------------------
lineBreak : RExp True
lineBreak =
      "\r\n"
  <|> '\n'
  <|> '\r'

horizontalAsciiWhitespace : RExp True
horizontalAsciiWhitespace =
  oneof [' ', '\t', '\x0B', '\x0C']

export
asciiWhitespace : RExp True
asciiWhitespace =
  plus (horizontalAsciiWhitespace <|> lineBreak)

||| The non-ASCII characters Leaf treats as whitespace.
export
nonAsciiWhitespaceCharacters : List Char
nonAsciiWhitespaceCharacters = ['\x85', '\x200E', '\x200F', '\x2028', '\x2029']

export
nonAsciiWhitespaceCharacter : RExp True
nonAsciiWhitespaceCharacter = oneof (map chr nonAsciiWhitespaceCharacters)

-- In ilex, `dot` means a printable (non-control) code point, not an arbitrary
-- character. Comments and broad literal candidates must also consume tabs and
-- other control code points so that they cannot terminate a match prematurely.
-- `range32` intersects this range with Unicode's valid scalar values when the
-- DFA is generated.
validCodePoint : RExp True
validCodePoint =
  range32 0x0 0x10ffff

nonAsciiCodePoint : RExp True
nonAsciiCodePoint =
  range32 0x80 0x10ffff

notLineBreakChar : RExp True
notLineBreakChar =
  validCodePoint && not '\n' && not '\r'

--------------------------------------------------------------------------------
-- ASCII helpers used by string and number candidates.
--------------------------------------------------------------------------------
asciiLower : RExp True
asciiLower = range 'a' 'z'

asciiUpper : RExp True
asciiUpper = range 'A' 'Z'

asciiLetter : RExp True
asciiLetter = asciiLower <|> asciiUpper

asciiAlphaNum : RExp True
asciiAlphaNum = asciiLetter <|> digit

asciiAlphaNumUnderscore : RExp True
asciiAlphaNumUnderscore = asciiAlphaNum <|> '_'

--------------------------------------------------------------------------------
-- Identifier-like text.
--
-- There is intentionally one identifier rule.  `tokenFromIdentLike` in
-- Compiler.Frontend.Token owns the classification into TokUnderscore, booleans,
-- keywords, primitive types, state literals, builtins, and ordinary identifiers.
--
-- Leaf follows Rust's identifier syntax (Unicode XID_Start / XID_Continue),
-- approximated with Unicode general categories:
--   start = letter (Lu, Ll, Lt, Lm, Lo), letter number (Nl), or '_'
--   rest  = a start character, nonspacing mark (Mn), spacing mark (Mc),
--           decimal digit (Nd), or connector punctuation (Pc, which includes '_')
--
-- The marks make words such as `नमस्ते` and a decomposed `é` (`e` followed by
-- U+0301) single identifiers. Like rustc, Leaf normalizes identifiers to NFC
-- (`tokenFromNfcNormalizedIdentifier` in Rules.idr), so a composed and a
-- decomposed `é` spell the same identifier. The NFC tables in
-- `UnicodeNormalizationData` and the general-category tables of
-- `Text.ILex.RExp.Unicode` used here are generated independently and may come
-- from different Unicode versions.
--
-- As in Rust, an apostrophe is never part of an identifier, so `foo'` is the
-- identifier `foo` followed by a separate apostrophe.
--
-- `Text.ILex`'s own `alpha`/`alphaNum` are ASCII-only (`a`-`z`/`A`-`Z`/`0`-`9`),
-- despite reading as generic names, so they cannot be used here. The Unicode
-- categories come from `Text.ILex.RExp.Unicode`'s generated tables instead.
--------------------------------------------------------------------------------
identifierStart : RExp True
identifierStart = Uni.letter <|> Uni.letterNumber <|> '_'

identifierRest : RExp True
identifierRest =
      identifierStart
  <|> Uni.nonspacingMark
  <|> Uni.spacingMark
  <|> Uni.decimalNumber
  <|> Uni.connectorPunctuation

export
identifierLike : RExp True
identifierLike = identifierStart >> star identifierRest

-- An identifier directly followed by one more non-ASCII character. It exists
-- only to work around the ilex limitation described at the top of Rules.idr:
-- after an identifier, the first byte of any non-ASCII character could still
-- begin an identifier character, so without this rule an identifier followed
-- by, say, `→` or U+2028 would fail at the start of the identifier instead of
-- falling back to it. When the extra character continues the identifier, the
-- plain identifier rule matches the same text and wins because it is listed
-- first, so this rule is the longest match only when the character cannot
-- continue the identifier.
export
identifierFollowedByNonAsciiCharacter : RExp True
identifierFollowedByNonAsciiCharacter = identifierLike >> nonAsciiCodePoint

--------------------------------------------------------------------------------
-- Numeric literal components.
--
-- Unary minus is deliberately not included here.  `-7` is lexed as the symbol
-- `-` followed by `TokIntLitRaw "7"`.
--------------------------------------------------------------------------------
--------------------------------------------------------------------------------
-- Digit runs follow Rust:
--
--   * a decimal digit run starts with a digit, followed by any mix of digits
--     and `_` (`1_000`, `1_`, `1__2`);
--   * the digits after a radix prefix (`0b`/`0o`/`0x`) and the digits of an
--     exponent may start and end with `_` but must contain at least one digit
--     (`0x_FF_`, `1e_3`, but not `0x_` or `1e_`);
--   * radix prefixes are lowercase only. An uppercase prefix such as the one in
--     `0X1F` is consumed whole by `suffixedDecimalNumberCandidate` and rejected
--     as a single malformed literal, rather than split into `0` and `X1F`.
--
-- `decimalDigits` is used both by the broad candidates below and by the
-- strict literal regexes, since every match of it is a valid decimal digit
-- run. Radix candidates (`radixNumberCandidate` below) instead swallow any
-- alphanumeric run after the prefix, so an out-of-range digit like the `2` in
-- `0b102` still ends up in one malformed-literal token instead of being split
-- off, and the strict radix digit runs then reject it.
--------------------------------------------------------------------------------
decimalDigits : RExp True
decimalDigits = digit >> star (digit <|> '_')

digitRunWithAtLeastOneDigit : RExp True -> RExp True
digitRunWithAtLeastOneDigit singleDigit =
  star (singleDigit <|> '_') >> singleDigit >> star (singleDigit <|> '_')

strictBinaryDigits : RExp True
strictBinaryDigits = digitRunWithAtLeastOneDigit bindigit

strictOctalDigits : RExp True
strictOctalDigits = digitRunWithAtLeastOneDigit octdigit

strictHexDigits : RExp True
strictHexDigits = digitRunWithAtLeastOneDigit hexdigit

strictExponentDigits : RExp True
strictExponentDigits = digitRunWithAtLeastOneDigit digit

signedIntegerTypeSuffix : RExp True
signedIntegerTypeSuffix =
      "i8"
  <|> "i16"
  <|> "i32"
  <|> "i64"
  <|> "i128"

unsignedIntegerTypeSuffix : RExp True
unsignedIntegerTypeSuffix =
      "u8"
  <|> "u16"
  <|> "u32"
  <|> "u64"
  <|> "u128"
  <|> "usize"

integerTypeSuffix : RExp True
integerTypeSuffix = signedIntegerTypeSuffix <|> unsignedIntegerTypeSuffix

-- No separate `_` before a suffix is needed: a digit run may already end with
-- `_`, so `10_u32` is the digits `10_` followed by the suffix `u32`.
floatTypeSuffix : RExp True
floatTypeSuffix = "f32" <|> "f64"

exponentPart : RExp True
exponentPart =
  oneof ['e', 'E'] >> opt (oneof ['+', '-']) >> strictExponentDigits

--------------------------------------------------------------------------------
-- Valid numeric regexes.
--
-- These are the actual source of truth for what counts as a well-formed
-- integer/float literal: `Rules.idr`'s `numberClassifier` runs the already
-- broadly-matched raw text back through these via
-- `Text.ILex.State.Regular.value`,
-- rather than re-validating it with hand-written `List Char` recursion.
--------------------------------------------------------------------------------
binaryIntegerLiteral : RExp True
binaryIntegerLiteral =
  "0b" >> strictBinaryDigits >> opt integerTypeSuffix

octalIntegerLiteral : RExp True
octalIntegerLiteral =
  "0o" >> strictOctalDigits >> opt integerTypeSuffix

hexIntegerLiteral : RExp True
hexIntegerLiteral =
  "0x" >> strictHexDigits >> opt integerTypeSuffix

decimalIntegerLiteral : RExp True
decimalIntegerLiteral =
  decimalDigits >> opt integerTypeSuffix

export
integerLiteral : RExp True
integerLiteral =
      binaryIntegerLiteral
  <|> octalIntegerLiteral
  <|> hexIntegerLiteral
  <|> decimalIntegerLiteral

--------------------------------------------------------------------------------
-- Supported float forms:
--
--   digit+ '.' digit+ exp? suf?
--   digit+ exp suf?
--   digit+ ('f32' | 'f64')
--
-- The rule does not admit trailing-dot floats.  This also preserves the required
-- tokenization of `1..2` as integer, range operator, integer.
--------------------------------------------------------------------------------
export
floatLiteral : RExp True
floatLiteral =
      (decimalDigits >> '.' >> decimalDigits >> opt exponentPart >> opt floatTypeSuffix)
  <|> (decimalDigits >> exponentPart >> opt floatTypeSuffix)
  <|> (decimalDigits >> floatTypeSuffix)

--------------------------------------------------------------------------------
-- Broad numeric candidates.
--
-- The lexer must not split malformed numeric spellings into smaller legal
-- tokens.  For example, `0b102` must become a number-literal error rather than
-- `0b10` followed by `2`.  These candidates therefore consume complete
-- number-looking spans, and Rules.idr validates/classifies the raw spelling.
--
-- We intentionally do not consume a bare trailing dot.  That keeps `1..2`
-- correct and leaves `1.` as `1` followed by `.`, which the parser can reject if
-- it appears in a context where a member-access dot is not meaningful.
--------------------------------------------------------------------------------
radixNumberCandidate : RExp True
radixNumberCandidate =
      ("0b" >> star (asciiAlphaNum <|> '_'))
  <|> ("0o" >> star (asciiAlphaNum <|> '_'))
  <|> ("0x" >> star (asciiAlphaNum <|> '_'))

looseExponentPart : RExp True
looseExponentPart =
  oneof ['e', 'E'] >> opt (oneof ['+', '-']) >> star (asciiAlphaNum <|> '_')

dottedDecimalNumberCandidate : RExp True
dottedDecimalNumberCandidate =
  decimalDigits >> '.' >> decimalDigits >> opt looseExponentPart >> star (asciiAlphaNum <|> '_')

exponentNumberCandidate : RExp True
exponentNumberCandidate =
  decimalDigits >> looseExponentPart >> star (asciiAlphaNum <|> '_')

suffixedDecimalNumberCandidate : RExp True
suffixedDecimalNumberCandidate =
  decimalDigits >> (asciiLetter <|> '_') >> star (asciiAlphaNum <|> '_')

plainDecimalNumberCandidate : RExp True
plainDecimalNumberCandidate = decimalDigits

export
numberCandidate : RExp True
numberCandidate =
      dottedDecimalNumberCandidate
  <|> radixNumberCandidate
  <|> exponentNumberCandidate
  <|> suffixedDecimalNumberCandidate
  <|> plainDecimalNumberCandidate

--------------------------------------------------------------------------------
-- Digits immediately followed by `.`, `..`, or `..=`.
--
-- This regex also matches the prefix of a dotted float such as `1.2`, but
-- `dottedDecimalNumberCandidate` consumes the longer span and wins by ilex's
-- maximal-munch rule. When no digit follows the first dot, this candidate wins
-- instead and the action splits the match into an integer plus `.`, `..`, or
-- `..=`; thus `1..2` lexes as `1`, `..`, `2` and `1.` as `1`, `.`. The digits
-- are always a valid decimal integer, since every match of `decimalDigits` is.
--------------------------------------------------------------------------------
export
digitsThenDotOperatorCandidate : RExp True
digitsThenDotOperatorCandidate =
  decimalDigits >> ('.' >> opt ('.' >> opt '='))

--------------------------------------------------------------------------------
-- String, basis-string, byte literal, byte-string, and ordinary char candidates.
--
-- These candidates are deliberately broader than the set of valid literals.
-- Rules.idr validates the raw spelling and raises a structured error instead of
-- letting bad literals split into unrelated tokens.
--------------------------------------------------------------------------------
normalStringBodyCandidate : RExp True
normalStringBodyCandidate =
      ('\\' >> notLineBreakChar)
  <|> (notLineBreakChar && not '"' && not '\\')

export
normalStringCandidate : RExp True
normalStringCandidate =
  '"' >> star normalStringBodyCandidate >> '"'

export
unterminatedNormalStringCandidate : RExp True
unterminatedNormalStringCandidate =
  '"' >> star normalStringBodyCandidate

-- Covers a body ending in a bare backslash cut off by true end of input,
-- before the escape's second character ever arrives -- the same class of
-- backtracking dead end as `bareOuterBlockCommentOpen` below, just for an
-- escape-introducing backslash instead of a doc-comment star run. Without
-- this, `"abc\` hard-fails instead of falling back to an unterminated
-- string, because the node reached after the lone backslash extends toward
-- a two-character escape but isn't itself an accept.
export
unterminatedNormalStringTrailingBackslashCandidate : RExp True
unterminatedNormalStringTrailingBackslashCandidate =
  '"' >> star normalStringBodyCandidate >> '\\'

export
basisStringCandidate : RExp True
basisStringCandidate =
  'b' >> 's' >> '"' >> star (notLineBreakChar && not '"') >> '"'

export
unterminatedBasisStringCandidate : RExp True
unterminatedBasisStringCandidate =
  'b' >> 's' >> '"' >> star (notLineBreakChar && not '"')

-- Byte strings allow the same body characters as normal strings (anything
-- but '"', a line break, or a bare backslash); the two candidates share one
-- definition so they can't silently drift apart.
byteStringBodyCandidate : RExp True
byteStringBodyCandidate = normalStringBodyCandidate

export
byteStringCandidate : RExp True
byteStringCandidate =
  'b' >> '"' >> star byteStringBodyCandidate >> '"'

export
unterminatedByteStringCandidate : RExp True
unterminatedByteStringCandidate =
  'b' >> '"' >> star byteStringBodyCandidate

-- Same dead end as `unterminatedNormalStringTrailingBackslashCandidate`
-- above, for byte strings: `b"abc\` at true end of input.
export
unterminatedByteStringTrailingBackslashCandidate : RExp True
unterminatedByteStringTrailingBackslashCandidate =
  'b' >> '"' >> star byteStringBodyCandidate >> '\\'

byteLiteralBodyCandidate : RExp True
byteLiteralBodyCandidate =
      ('\\' >> notLineBreakChar)
  <|> (notLineBreakChar && not '\'' && not '\\')

export
byteLiteralCandidate : RExp True
byteLiteralCandidate =
  'b' >> '\'' >> star byteLiteralBodyCandidate >> '\''

export
unterminatedByteLiteralCandidate : RExp True
unterminatedByteLiteralCandidate =
  'b' >> '\'' >> star byteLiteralBodyCandidate

-- Same dead end as `unterminatedNormalStringTrailingBackslashCandidate`
-- above, for byte literals: `b'\` at true end of input.
export
unterminatedByteLiteralTrailingBackslashCandidate : RExp True
unterminatedByteLiteralTrailingBackslashCandidate =
  'b' >> '\'' >> star byteLiteralBodyCandidate >> '\\'

export
ordinaryCharLiteralCandidate : RExp True
ordinaryCharLiteralCandidate =
  '\'' >> star byteLiteralBodyCandidate >> '\''

--------------------------------------------------------------------------------
-- Strict string/byte-literal regexes, used only for validating the raw text
-- already matched by the broad candidates above (see `Rules.idr`'s
-- `normalStringValidator`/`basisStringValidator`/`byteLiteralValidator`/
-- `byteStringValidator`), never for matching directly.
--------------------------------------------------------------------------------
export
normalStringLiteralStrict : RExp True
normalStringLiteralStrict =
  '"' >> star asciiAlphaNumUnderscore >> '"'

basisStringChar : RExp True
basisStringChar =
  oneof ['0', '1', '+', '-', 'i', 'I']

export
basisStringLiteralStrict : RExp True
basisStringLiteralStrict =
  'b' >> 's' >> '"' >> star basisStringChar >> '"'

simpleByteEscape : RExp True
simpleByteEscape =
  '\\' >> oneof ['n', 'r', 't', '0', '\\', '\'', '"']

hexByteEscape : RExp True
hexByteEscape =
  "\\x" >> hexdigit >> hexdigit

export
byteLiteralStrict : RExp True
byteLiteralStrict =
  'b' >> '\'' >>
    ((range32 0x20 0x7e && not '\\' && not '\'') <|> simpleByteEscape <|> hexByteEscape) >>
    '\''

export
byteStringLiteralStrict : RExp True
byteStringLiteralStrict =
  'b' >> '"' >>
    star ((range32 0x20 0x7e && not '\\' && not '"') <|> simpleByteEscape <|> hexByteEscape) >>
    '"'

--------------------------------------------------------------------------------
-- Comments and documentation comments.
--
-- Required corner cases:
--   ///!  outer line doc
--   ////  normal line comment
--   //!/  inner line doc
--
-- Maximal munch makes `////` a normal comment because the normal-comment rule
-- consumes the whole line while the outer-doc rule can only consume `///`.
--------------------------------------------------------------------------------
lineCommentTail : RExp False
lineCommentTail = star notLineBreakChar

outerDocLineBody : RExp False
outerDocLineBody =
  opt ((notLineBreakChar && not '/') >> lineCommentTail)

export
outerDocLineComment : RExp True
outerDocLineComment =
  '/' >> '/' >> '/' >> outerDocLineBody

export
innerDocLineComment : RExp True
innerDocLineComment =
  '/' >> '/' >> '!' >> lineCommentTail

export
normalLineComment : RExp True
normalLineComment =
  '/' >> '/' >> lineCommentTail

--------------------------------------------------------------------------------
-- Block comments.
--
-- Rust classifies `/**` as an outer documentation-comment opener only when the
-- following character is neither `*` nor `/`. Thus `/** text */` is a doc
-- comment, while `/**/`, `/***/`, and banner-style `/*** text */` comments are
-- ordinary block comments. Inner block docs may be empty, so `/*!*/` is a
-- valid inner doc comment.
--
-- ilex has no lookahead assertion, so `outerBlockDocOpen` consumes the first
-- body character along with `/**`. The block-comment action preserves that
-- character as part of the raw documentation text.
--------------------------------------------------------------------------------
outerBlockDocFirstBodyChar : RExp True
outerBlockDocFirstBodyChar =
      (notLineBreakChar && not '*' && not '/')
  <|> lineBreak

-- One or more stars beyond the mandatory `*` in `/*`. Under Rust's convention,
-- more than one additional star always begins an ordinary block comment.
additionalBlockCommentStars : RExp True
additionalBlockCommentStars = plus '*'

export
allStarsOuterBlockComment : RExp True
allStarsOuterBlockComment =
  '/' >> '*' >> additionalBlockCommentStars >> '/'

export
outerBlockDocOpen : RExp True
outerBlockDocOpen =
  '/' >> '*' >> '*' >> outerBlockDocFirstBodyChar

-- Covers additional-star runs that should begin an ordinary Rust block comment,
-- including a run cut off at true end of input (for example `/***`). Without
-- this explicit accept, the pinned ilex DFA can lose its shorter `/*` match at
-- the extend-only states in the run and hard-fail instead of reporting an
-- unterminated block comment. It also lets banner-style comments enter the
-- block-comment state after their complete opening star run.
export
bareOuterBlockCommentOpen : RExp True
bareOuterBlockCommentOpen =
  '/' >> '*' >> additionalBlockCommentStars

export
innerBlockDocOpen : RExp True
innerBlockDocOpen =
  '/' >> '*' >> '!'

export
normalBlockCommentOpen : RExp True
normalBlockCommentOpen =
  '/' >> '*'

export
blockCommentClose : RExp True
blockCommentClose =
  '*' >> '/'

export
blockCommentBodyChunk : RExp True
blockCommentBodyChunk =
  plus (notLineBreakChar && not '*' && not '/')

export
blockCommentLineBreak : RExp True
blockCommentLineBreak = lineBreak

export
blockCommentSingleStar : RExp True
blockCommentSingleStar = '*'

export
blockCommentSingleSlash : RExp True
blockCommentSingleSlash = '/'
