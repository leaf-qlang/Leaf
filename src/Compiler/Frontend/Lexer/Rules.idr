module Compiler.Frontend.Lexer.Rules

import Data.List
import Data.Linear.Ref1
import Data.String
import Derive.Finite
import Syntax.T1
import Text.ILex
import Text.ILex.Interfaces
import Text.ILex.State.Derive
import Text.ILex.State.Regular
import Text.ParseError

import Compiler.Frontend.Token
import Compiler.Frontend.Lexer.Error
import Compiler.Frontend.Lexer.Regex

%default total
%language ElabReflection
%hide Prelude.(>>)
%hide Prelude.(>>=)
%hide Prelude.(<*)
%hide Prelude.pure
%hide Prelude.not

--------------------------------------------------------------------------------
-- A known limitation of ilex: backtrack memory is lost across a node that is
-- extensible but not itself an accept. Concretely: if the lexer has already
-- matched a shorter valid token, then continues into a longer candidate that
-- turns out not to be a real accept anywhere along the way, it hard-fails
-- instead of falling back to the shorter match -- but *only* if some byte in
-- between led to a state with further transitions and no accept of its own.
-- A shorter match followed immediately by a dead end backtracks fine; a
-- shorter match, then one or more such "extend-only" bytes, then a dead end,
-- does not. Worked around below for six distinct grammar shapes; if you hit
-- a case that doesn't fit any of these, it is likely the same underlying
-- bug: read this first rather than removing a workaround that appears
-- redundant.
--
-- Confirmed still present as of collection `nightly-260731` (ilex commit
-- 6c0c590035fdba3a4b6cfaff9dd9deb2791e4aff) by disabling each workaround in
-- turn and reproducing the exact failure described below; first observed
-- under `nightly-260629` (ilex commit fffa455256465705891761a61e37d95c26f0f50e).
--
--   - `digitsThenDotOperatorCandidate` / `emitDigitsThenDotOperator`
--     (this file and `Regex.idr`): without it, `1..2` hard-fails instead
--     of lexing as `1`, `..`, `2`, because the node reached after `1.`
--     extends (a digit could follow) but isn't itself an accept.
--   - `allStarsOuterBlockComment` (`Regex.idr`, wired into `initialRules`
--     below): consumes `/**/`, `/***/`, `/****/`, and so on as complete
--     ordinary comments. The star-run fallback below is already accepting,
--     but would otherwise consume the final `*` as part of the opener and
--     leave the closing `/` stranded in block-comment state.
--   - `bareOuterBlockCommentOpen` (`Regex.idr`, wired into `initialRules`
--     below): accepts the additional-star run used by ordinary Rust
--     banner comments, including the same dead end at true end of input
--     -- e.g. a file truncated right after `/***`. It falls back to an
--     (eventually unterminated) plain block comment, like a bare `/*`.
--   - `unterminatedNormalStringTrailingBackslashCandidate` /
--     `unterminatedByteStringTrailingBackslashCandidate` /
--     `unterminatedByteLiteralTrailingBackslashCandidate` (`Regex.idr`,
--     wired into `initialRules` below): without these, `"abc\`, `b"abc\`,
--     and `b'\` (a string/byte-string/byte-literal body ending in a bare
--     backslash cut off by true end of input) hard-fail instead of
--     falling back to their respective unterminated-literal errors,
--     because the node reached after the lone backslash extends toward a
--     two-character escape but isn't itself an accept. Basis strings
--     have no escape syntax, so they don't share this dead end.
--   - `identifierFollowedByNonAsciiCharacter` /
--     `emitIdentifierThenNonAsciiCharacter` (this file and `Regex.idr`):
--     without it, an identifier directly followed by a non-ASCII character
--     that cannot continue it (`x→y`, or `x` followed by U+2028) hard-fails
--     at the start of the identifier, because the first byte of the
--     character could still begin an identifier character.
--   - `nonAsciiWhitespaceCharacter` (`Regex.idr`): the non-ASCII whitespace
--     characters have their own single-character rule instead of joining the
--     `plus` loop of `asciiWhitespace`, so that an unsupported character
--     sharing a first byte with one of them is reported at its own position
--     rather than at the start of the preceding whitespace.
--
-- If you add a new rule whose prefix overlaps an existing shorter rule with
-- a possible dead end in between, test that overlap directly; don't assume
-- maximal munch alone covers it.
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- Lexer states.
--
-- The lexer uses exactly two states:
--   * Initial        ordinary Leaf source text
--   * InBlockComment counting state for nested block comments
--
-- Arbitrary nesting is represented by `commentDepth`, not by adding more states.
--------------------------------------------------------------------------------
%runElab deriveParserState "LeafSz" "LeafState" ["Initial", "InBlockComment"]

--------------------------------------------------------------------------------
-- Documentation-comment mode.
--
-- This mode is chosen by the outermost block-comment opener. Nested block
-- comments only affect the extra nesting depth; they never change the doc/non-doc mode
-- of the outer comment.
--------------------------------------------------------------------------------
data CommentMode
  = NormalBlockComment
  | OuterBlockDocComment
  | InnerBlockDocComment

commentModeToToken : CommentMode -> String -> Maybe Token
commentModeToToken NormalBlockComment _ = Nothing
commentModeToToken OuterBlockDocComment rawText = Just (TokOuterDoc rawText)
commentModeToToken InnerBlockDocComment rawText = Just (TokInnerDoc rawText)

--------------------------------------------------------------------------------
-- Mutable ilex state.
--
-- The installed Text.ILex.State.Regular.State record already supplies HasBytes,
-- HasStringLits, HasBBErr, and HasStack instances (it derives them via
-- `%runElab derive "State" [FullState]`). `LeafStack` only has to carry what
-- that generic record does not already provide: the emitted token buffer and
-- block-comment depth/mode counters. `commentDepth` counts nested comments
-- beyond the outermost block comment while in `InBlockComment`.
--------------------------------------------------------------------------------
record LeafStack where
  constructor MkLeafStack
  outputTokens : SnocList (ByteBounded Token)
  commentDepth : Nat
  commentMode  : CommentMode

0 LeafLexerStack : Type -> Type
LeafLexerStack = State LexerError LeafStack LeafSz

initialLeafStack : LeafStack
initialLeafStack = MkLeafStack [<] Z NormalBlockComment

--------------------------------------------------------------------------------
-- Local rule alias.
--------------------------------------------------------------------------------
0 LeafRule : Type -> Type
LeafRule q = (RExp True, Step q LeafSz LeafLexerStack)

--------------------------------------------------------------------------------
-- Bounds and position helpers built on top of the installed Text.ILex
-- position/error machinery (`Text.ILex.Interfaces`).
--------------------------------------------------------------------------------
oldestOpenPosition : SnocList BytePos -> Maybe BytePos
oldestOpenPosition [<] =
  Nothing
oldestOpenPosition (olderPositions :< openPosition) =
  case olderPositions of
    [<] =>
      Just openPosition

    _ =>
      oldestOpenPosition olderPositions

unterminatedCommentBounds :
     (lexerStack : LeafLexerStack q)
  => BytePos
  -> F1 q ByteBounds
unterminatedCommentBounds openPosition = T1.do
  endPosition <- endPos
  pure (BB openPosition endPosition)

--------------------------------------------------------------------------------
-- UTF-8 byte lengths.
--
-- ilex positions are byte offsets, while Idris strings are sequences of code
-- points. Splitting a match into several tokens, or locating a character by
-- its byte offset, therefore needs each character's UTF-8 encoded length.
--------------------------------------------------------------------------------
||| The number of bytes in the UTF-8 encoding of a character.
export
utf8ByteLength : Char -> Nat
utf8ByteLength character =
  let codePoint = ord character in
  if codePoint < 0x80 then 1
  else if codePoint < 0x800 then 2
  else if codePoint < 0x10000 then 3
  else 4

--------------------------------------------------------------------------------
-- Literal validation.
--
-- Rather than re-parsing the already-matched raw text by hand, run it back
-- through the *strict* regexes from `Compiler.Frontend.Lexer.Regex` (`integerLiteral`,
-- `floatLiteral`, `normalStringLiteralStrict`, ...) via
-- `Text.ILex.State.Regular.value`, ilex's own primitive for classifying a whole
-- string against a set of regex
-- alternatives. Its "done" state has an empty DFA for anything but `Ignore`
-- alternatives, so any leftover unconsumed input after the first match fails
-- outright -- this rejects partial/prefix matches for free, with no
-- hand-rolled slicing, and keeps the strict regexes as the single source of
-- truth for what counts as a well-formed literal instead of a second,
-- independently-maintained copy of the same grammar.
--------------------------------------------------------------------------------
runValueMatch : Parser1 (BBErr Void) a -> String -> Maybe a
runValueMatch literalParser rawText =
  case runString literalParser rawText of
    Right matchedValue => Just matchedValue
    Left _        => Nothing

matchesLiteral : Parser1 (BBErr Void) () -> String -> Bool
matchesLiteral literalParser rawText =
  case runValueMatch literalParser rawText of
    Just () => True
    Nothing => False

data NumberLiteralKind
  = IntegerNumberLiteral
  | FloatingNumberLiteral

numberClassifier : PVal1 q Void NumberLiteralKind
numberClassifier =
  value Nothing
    [ (integerLiteral, const IntegerNumberLiteral)
    , (floatLiteral,   const FloatingNumberLiteral)
    ]

classifyNumberLiteral : String -> Maybe NumberLiteralKind
classifyNumberLiteral = runValueMatch numberClassifier

normalStringValidator : PVal1 q Void ()
normalStringValidator =
  value Nothing [(normalStringLiteralStrict, const ())]

validNormalStringLiteral : String -> Bool
validNormalStringLiteral = matchesLiteral normalStringValidator

basisStringValidator : PVal1 q Void ()
basisStringValidator =
  value Nothing [(basisStringLiteralStrict, const ())]

validBasisStringLiteral : String -> Bool
validBasisStringLiteral = matchesLiteral basisStringValidator

byteLiteralValidator : PVal1 q Void ()
byteLiteralValidator =
  value Nothing [(byteLiteralStrict, const ())]

validByteLiteral : String -> Bool
validByteLiteral = matchesLiteral byteLiteralValidator

byteStringValidator : PVal1 q Void ()
byteStringValidator =
  value Nothing [(byteStringLiteralStrict, const ())]

validByteStringLiteral : String -> Bool
validByteStringLiteral = matchesLiteral byteStringValidator

--------------------------------------------------------------------------------
-- Splits the dot operator matched by `digitsThenDotOperatorCandidate` (one of
-- `.`, `..`, or `..=`) off the end of the matched text, returning the leading
-- digits together with the operator. The longest operator is tried first, so
-- `1..=` splits as `1` and `..=` rather than `1..` and `=`. `Nothing` means the
-- text does not end in a dot operator, which the candidate regex rules out.
--------------------------------------------------------------------------------
splitDigitsFromDotOperator : String -> Maybe (String, Symbol)
splitDigitsFromDotOperator rawText =
  map splitOffOperator
    (Data.List.find (\dotOperator => showSymbolLeaf dotOperator `isSuffixOf` rawText)
       [SymDotDotEq, SymDotDot, SymDot])
  where
    splitOffOperator : Symbol -> (String, Symbol)
    splitOffOperator dotOperator =
      (substr 0 (length rawText `minus` length (showSymbolLeaf dotOperator)) rawText, dotOperator)

--------------------------------------------------------------------------------
-- Token and error actions.
--------------------------------------------------------------------------------
emitBoundedToken :
     (lexerStack : LeafLexerStack q)
  => ByteBounded Token
  -> F1 q LeafState
emitBoundedToken boundedToken = T1.do
  leafStack <- getStack
  putStackAs ({ outputTokens $= (:< boundedToken) } leafStack) Initial

emitToken :
     (lexerStack : LeafLexerStack q)
  => Token
  -> F1 q LeafState
emitToken token = T1.do
  boundedToken <- bounded' token
  emitBoundedToken boundedToken

||| Remembers the first fatal error only. `failHere` itself now keeps the
||| first error and ignores later ones (ilex commit ee97414 onward), so this
||| is just the domain-named entry point Rules.idr's call sites use.
rememberFatalError :
     (lexerStack : LeafLexerStack q)
  => LexerError
  -> F1 q LeafState
rememberFatalError lexerError =
  failHere (Custom lexerError) Initial

||| As `rememberFatalError`, but at an explicit span rather than the current
||| position.
rememberFatalErrorAt :
     (lexerStack : LeafLexerStack q)
  => ByteBounds
  -> LexerError
  -> F1 q LeafState
rememberFatalErrorAt errorBounds lexerError =
  failWith (B (Custom lexerError) errorBounds) Initial

emitValidatedLiteral :
     (lexerStack : LeafLexerStack q)
  => (String -> Bool)
  -> (String -> LexerError)
  -> (String -> Token)
  -> String
  -> F1 q LeafState
emitValidatedLiteral isValidLiteral invalidLiteralError literalToken rawText =
  case isValidLiteral rawText of
    True => emitToken (literalToken rawText)
    False => rememberFatalError (invalidLiteralError rawText)

emitNormalStringLiteral :
     (lexerStack : LeafLexerStack q)
  => String
  -> F1 q LeafState
emitNormalStringLiteral =
  emitValidatedLiteral
    validNormalStringLiteral
    LexInvalidStringLiteral
    TokStringLitRaw

emitBasisStringLiteral :
     (lexerStack : LeafLexerStack q)
  => String
  -> F1 q LeafState
emitBasisStringLiteral =
  emitValidatedLiteral
    validBasisStringLiteral
    LexInvalidBasisStringLiteral
    TokBasisStringLitRaw

emitByteLiteral :
     (lexerStack : LeafLexerStack q)
  => String
  -> F1 q LeafState
emitByteLiteral =
  emitValidatedLiteral
    validByteLiteral
    LexInvalidByteLiteral
    TokByteLitRaw

emitByteStringLiteral :
     (lexerStack : LeafLexerStack q)
  => String
  -> F1 q LeafState
emitByteStringLiteral =
  emitValidatedLiteral
    validByteStringLiteral
    LexInvalidByteStringLiteral
    TokByteStringLitRaw

emitNumberLiteral :
     (lexerStack : LeafLexerStack q)
  => String
  -> F1 q LeafState
emitNumberLiteral rawText =
  case classifyNumberLiteral rawText of
    Just IntegerNumberLiteral =>
      emitToken (TokIntLitRaw rawText)

    Just FloatingNumberLiteral =>
      emitToken (TokFloatLitRaw rawText)

    Nothing =>
      rememberFatalError (LexInvalidNumberLiteral rawText)

emitDigitsThenDotOperator :
     (lexerStack : LeafLexerStack q)
  => String
  -> F1 q LeafState
emitDigitsThenDotOperator rawText =
  case splitDigitsFromDotOperator rawText of
    Nothing =>
      rememberFatalError
        (LexInternalLexerError ("digits before a dot operator without a dot operator: " ++ rawText))

    -- The digits are ASCII, so their character count is their byte count.
    Just (digitText, dotOperator) => T1.do
      let digitsLength = length digitText
      tokenStart <- startPos
      tokenEnd <- endPos
      let integerEnd = incLen digitsLength tokenStart
      let operatorStart = incLen (S digitsLength) tokenStart
      _ <- emitBoundedToken (B (TokIntLitRaw digitText) (BB tokenStart integerEnd))
      emitBoundedToken (B (TokSym dotOperator) (BB operatorStart tokenEnd))

-- Splits a match of `identifierFollowedByNonAsciiCharacter` into the
-- identifier, emitted as its token, and the trailing character, which is
-- skipped when it is whitespace and otherwise reported as unsupported.
emitIdentifierThenNonAsciiCharacter :
     (lexerStack : LeafLexerStack q)
  => String
  -> F1 q LeafState
emitIdentifierThenNonAsciiCharacter rawText =
  case reverse (unpack rawText) of
    [] =>
      rememberFatalError
        (LexInternalLexerError "empty match for an identifier followed by a non-ASCII character")

    trailingCharacter :: reversedIdentifierCharacters => T1.do
      let identifierText = pack (reverse reversedIdentifierCharacters)
      let identifierByteLength = sum (map utf8ByteLength reversedIdentifierCharacters)
      tokenStart <- startPos
      tokenEnd <- endPos
      let identifierEnd = incLen identifierByteLength tokenStart
      let trailingCharacterStart = incLen (S identifierByteLength) tokenStart
      _ <- emitBoundedToken (B (tokenFromIdentLike identifierText) (BB tokenStart identifierEnd))
      case elem trailingCharacter nonAsciiWhitespaceCharacters of
        True => pure Initial
        False =>
          rememberFatalErrorAt
            (BB trailingCharacterStart tokenEnd)
            (LexUnsupportedCharacter trailingCharacter)

--------------------------------------------------------------------------------
-- Block-comment actions.
--
-- The block-comment depth and mode live on `LeafStack`; doc-comment text
-- pieces are accumulated with ilex's built-in string-literal accumulator
-- (`pushStr'`/`getStr`).
--------------------------------------------------------------------------------
appendTextIfDoc :
     (lexerStack : LeafLexerStack q)
  => CommentMode
  -> String
  -> F1' q
appendTextIfDoc NormalBlockComment _ = pure ()
appendTextIfDoc OuterBlockDocComment rawText = pushStr' rawText
appendTextIfDoc InnerBlockDocComment rawText = pushStr' rawText

beginBlockComment :
     (lexerStack : LeafLexerStack q)
  => CommentMode
  -> String
  -> F1 q LeafState
beginBlockComment openingCommentMode rawText = T1.do
  pushPosition
  leafStack <- getStack
  putStack ({ commentDepth := Z, commentMode := openingCommentMode } leafStack)
  appendTextIfDoc openingCommentMode rawText
  pure InBlockComment

beginNestedBlockComment :
     (lexerStack : LeafLexerStack q)
  => String
  -> F1 q LeafState
beginNestedBlockComment rawText = T1.do
  pushPosition
  leafStack <- getStack
  putStack ({ commentDepth $= S } leafStack)
  appendTextIfDoc leafStack.commentMode rawText
  pure InBlockComment

finishOutermostBlockComment :
     (lexerStack : LeafLexerStack q)
  => CommentMode
  -> ByteBounds
  -> F1 q LeafState
finishOutermostBlockComment outermostCommentMode fullCommentBounds = T1.do
  rawCommentText <- getStr
  case commentModeToToken outermostCommentMode rawCommentText of
    Nothing => pure Initial
    Just docToken =>
      emitBoundedToken (B docToken fullCommentBounds)

closeBlockComment :
     (lexerStack : LeafLexerStack q)
  => ByteBounds
  -> F1 q LeafState
closeBlockComment fullCommentBounds = T1.do
  leafStack <- getStack
  appendTextIfDoc leafStack.commentMode "*/"
  case leafStack.commentDepth of
    Z =>
      finishOutermostBlockComment leafStack.commentMode fullCommentBounds

    S remainingDepth => T1.do
      putStack ({ commentDepth := remainingDepth } leafStack)
      pure InBlockComment

consumeBlockCommentText :
     (lexerStack : LeafLexerStack q)
  => String
  -> F1 q LeafState
consumeBlockCommentText rawText = T1.do
  leafStack <- getStack
  appendTextIfDoc leafStack.commentMode rawText
  pure InBlockComment

symbolRules : List (LeafRule q)
symbolRules =
  vals
    showSymbolLeaf
    (\symbol, lexerStack => emitToken {lexerStack = lexerStack} (TokSym symbol))
    values

--------------------------------------------------------------------------------
-- Initial-state rules.
--
-- Overlapping rules are ordered intentionally; ilex still uses maximal munch,
-- so order matters only when alternatives match the same longest prefix:
--   1. documentation comments before ordinary comments and before `/`
--   2. broad literal candidates before identifiers
--   3. broad number candidate before identifier-like suffixes
--   4. single identifier rule through `tokenFromIdentLike`, before the rule for
--      an identifier followed by a non-ASCII character, so that an identifier
--      character wins over that workaround rule (see Regex.idr)
--   5. generated symbol rules from the finite `Symbol` values
--------------------------------------------------------------------------------
initialRules : List (LeafRule q)
initialRules =
  [ string outerDocLineComment (\rawText => emitToken (TokOuterDoc rawText))
  , string innerDocLineComment (\rawText => emitToken (TokInnerDoc rawText))

  , ignore allStarsOuterBlockComment
  , string outerBlockDocOpen (beginBlockComment OuterBlockDocComment)
  , string innerBlockDocOpen (beginBlockComment InnerBlockDocComment)
  , string bareOuterBlockCommentOpen (beginBlockComment NormalBlockComment)
  , ignore normalLineComment
  , string normalBlockCommentOpen (beginBlockComment NormalBlockComment)
  , ignore asciiWhitespace
  , ignore nonAsciiWhitespaceCharacter

  , string basisStringCandidate emitBasisStringLiteral
  , string byteStringCandidate emitByteStringLiteral
  , string byteLiteralCandidate emitByteLiteral
  , string normalStringCandidate emitNormalStringLiteral

  -- Unterminated candidates come after closed-literal candidates, so a valid
  -- string wins by maximal munch. They come before identifiers so `bs"bad` is
  -- not split into `bs` and a string fragment.
  , step unterminatedBasisStringCandidate
      (rememberFatalError LexUnterminatedBasisStringLiteral)
  , step unterminatedByteStringCandidate
      (rememberFatalError LexUnterminatedByteStringLiteral)
  , step unterminatedByteLiteralCandidate
      (rememberFatalError LexUnterminatedByteLiteral)
  , step unterminatedNormalStringCandidate
      (rememberFatalError LexUnterminatedStringLiteral)

  -- Trailing-backslash sub-cases of the three candidates just above (see the
  -- known-limitation note at the top of this file): only ever the longest
  -- match when the escape is cut off by true end of input, since maximal
  -- munch prefers the longer complete-escape match otherwise.
  , step unterminatedByteStringTrailingBackslashCandidate
      (rememberFatalError LexUnterminatedByteStringLiteral)
  , step unterminatedByteLiteralTrailingBackslashCandidate
      (rememberFatalError LexUnterminatedByteLiteral)
  , step unterminatedNormalStringTrailingBackslashCandidate
      (rememberFatalError LexUnterminatedStringLiteral)
  , step ordinaryCharLiteralCandidate
      (rememberFatalError LexUnsupportedCharLiteral)

  , string numberCandidate emitNumberLiteral
  , string digitsThenDotOperatorCandidate emitDigitsThenDotOperator
  , string identifierLike (\rawText => emitToken (tokenFromIdentLike rawText))
  , string identifierFollowedByNonAsciiCharacter emitIdentifierThenNonAsciiCharacter
  ] ++ symbolRules

--------------------------------------------------------------------------------
-- Block-comment rules.
--
-- Active only in `InBlockComment`. `/*` increments depth, `*/` decrements depth,
-- and only the outermost close returns to Initial.
--------------------------------------------------------------------------------
blockCommentRules : List (LeafRule q)
blockCommentRules =
  [ string normalBlockCommentOpen beginNestedBlockComment
  , closeWithBounds blockCommentClose closeBlockComment
  , string blockCommentBodyChunk consumeBlockCommentText
  , string blockCommentLineBreak consumeBlockCommentText
  , string blockCommentSingleStar consumeBlockCommentText
  , string blockCommentSingleSlash consumeBlockCommentText
  ]

--------------------------------------------------------------------------------
-- DFAs, error handlers, and final P1 lexer.
--------------------------------------------------------------------------------
leafLexerSteps : Lex1 q LeafSz LeafLexerStack
leafLexerSteps =
  lex1
    [ E Initial (dfa initialRules)
    , E InBlockComment (dfa blockCommentRules)
    ]

finishLexingAtEndOfInput :
     LeafState
  -> LeafLexerStack q
  -> F1 q (Either (BBErr LexerError) (List (ByteBounded Token)))
finishLexingAtEndOfInput lexerState lexerStack = T1.do
  storedError <- read1 (error lexerStack)
  case storedError of
    Just existingError =>
      pure (Left existingError)

    Nothing =>
      case lexerState == Initial of
        True => T1.do
          leafStack <- read1 (stack lexerStack)
          eofPosition <- endPos
          pure (Right (leafStack.outputTokens <>> [B TokEOF (BB eofPosition eofPosition)]))

        False => T1.do
          openPositions <- read1 (positions lexerStack)
          case oldestOpenPosition openPositions of
            Just openPosition => T1.do
              unclosedBounds <- unterminatedCommentBounds openPosition
              pure (Left (B (Custom LexUnterminatedBlockComment) unclosedBounds))

            Nothing => T1.do
              eofPosition <- endPos
              pure
                (Left
                  (B
                    (Custom
                      (LexInternalLexerError
                        "InBlockComment at end of input without an opening position"))
                    (BB eofPosition eofPosition)))

leafLexer : Lexer LexerError Token
leafLexer =
  P Initial
    (init initialLeafStack)
    leafLexerSteps
    noChunk
    (errs [])
    finishLexingAtEndOfInput

export
runLeafLexer : String -> Either (BBErr LexerError) (List (ByteBounded Token))
runLeafLexer = runString leafLexer
