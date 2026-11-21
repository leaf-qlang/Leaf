module Compiler.Frontend.Lexer.Error

import Data.Bits
import Data.List
import Data.String
import Derive.Prelude
import Language.Reflection
import Text.Bounds
import Text.ParseError

%default total
%language ElabReflection

--------------------------------------------------------------------------------
-- LexerError
--
-- This is the public, user-facing Leaf lexer error type.  The ilex runtime
-- still uses `InnerError LexerError` internally, because native ilex failures
-- such as unexpected input and unexpected or invalid bytes are represented by
-- `InnerError`.  `Compiler.Frontend.Lexer.Lexer` translates those native failures into
-- the constructors below so `lexFile` exposes exactly `Bounded LexerError`.
--------------------------------------------------------------------------------
public export
data LexerError
  = LexUnexpectedEndOfInput
  | LexUnexpectedInput (List String) String
  | LexUnclosed String
  | LexUnexpectedOrInvalidByte Bits8
  | LexUnsupportedCharacter Char
  | LexUnterminatedBlockComment
  | LexInvalidBasisStringLiteral String
  | LexInvalidByteLiteral String
  | LexInvalidByteStringLiteral String
  | LexInvalidStringLiteral String
  | LexInvalidNumberLiteral String
  | LexUnterminatedStringLiteral
  | LexUnterminatedBasisStringLiteral
  | LexUnterminatedByteStringLiteral
  | LexUnterminatedByteLiteral
  | LexUnsupportedCharLiteral
  | LexInternalLexerError String

%runElab derive "LexerError" [Show, Eq]

--------------------------------------------------------------------------------
-- Rendering unsupported characters.
--
-- A character is named by its Unicode code point, followed by the character
-- itself when it is visible on its own. Control characters, whitespace,
-- invisible formatting characters such as U+FEFF, and combining marks (which
-- would attach to the quoting backtick) are named by their code point only.
--------------------------------------------------------------------------------
-- `U+` followed by at least four uppercase hexadecimal digits, as in U+00E9.
unicodeCodePointText : Char -> String
unicodeCodePointText character =
  let codePoint = ord character
      codePointBytes = the (List Int) [codePoint `div` 0x10000, (codePoint `div` 0x100) `mod` 0x100, codePoint `mod` 0x100]
      sixHexDigits = unpack (toUpper (concatMap (\codePointByte => toHex (cast codePointByte)) codePointBytes))
  in "U+" ++ pack (dropLeadingZerosBeyondFourDigits sixHexDigits)
  where
    dropLeadingZerosBeyondFourDigits : List Char -> List Char
    dropLeadingZerosBeyondFourDigits ('0' :: laterDigits) =
      if length laterDigits >= 4
        then dropLeadingZerosBeyondFourDigits laterDigits
        else '0' :: laterDigits
    dropLeadingZerosBeyondFourDigits hexDigits = hexDigits

-- Inclusive code point ranges of characters that do not render visibly on
-- their own.
invisibleOrCombiningCodePointRanges : List (Int, Int)
invisibleOrCombiningCodePointRanges =
  [ (0x0000, 0x0020)  -- ASCII control characters and space
  , (0x007F, 0x00A0)  -- delete, C1 control characters, and no-break space
  , (0x00AD, 0x00AD)  -- soft hyphen
  , (0x0300, 0x036F)  -- combining diacritical marks
  , (0x061C, 0x061C)  -- Arabic letter mark
  , (0x180E, 0x180E)  -- Mongolian vowel separator
  , (0x2000, 0x200F)  -- spaces, zero-width characters, and direction marks
  , (0x2028, 0x202F)  -- line and paragraph separators, embedding controls
  , (0x205F, 0x206F)  -- medium mathematical space and invisible operators
  , (0x3000, 0x3000)  -- ideographic space
  , (0xFE00, 0xFE0F)  -- variation selectors
  , (0xFEFF, 0xFEFF)  -- byte order mark
  , (0xFFF9, 0xFFFB)  -- interlinear annotation controls
  ]

characterIsVisibleOnItsOwn : Char -> Bool
characterIsVisibleOnItsOwn character =
  let codePoint = ord character in
  not (any (\(firstCodePoint, lastCodePoint) => firstCodePoint <= codePoint && codePoint <= lastCodePoint)
           invisibleOrCombiningCodePointRanges)

describeUnsupportedCharacter : Char -> String
describeUnsupportedCharacter character =
  if characterIsVisibleOnItsOwn character
    then unicodeCodePointText character ++ " `" ++ pack [character] ++ "`"
    else unicodeCodePointText character

--------------------------------------------------------------------------------
-- Human-readable error messages.
--------------------------------------------------------------------------------
export
Interpolation LexerError where
  interpolate LexUnexpectedEndOfInput =
    "Unexpected end of input"

  interpolate (LexUnexpectedInput expectedDescriptions actualText) =
    case expectedDescriptions of
      [] =>
        "Unexpected input `" ++ actualText ++ "`"

      _ =>
        "Expected " ++ joinBy " or " expectedDescriptions ++
        ", but got `" ++ actualText ++ "`"

  interpolate (LexUnsupportedCharacter character) =
    "Unsupported character " ++ describeUnsupportedCharacter character

  interpolate (LexUnclosed description) =
    "Unclosed " ++ description

  interpolate (LexUnexpectedOrInvalidByte byteValue) =
    "Unexpected or invalid byte in Leaf source: 0x" ++ toHex byteValue

  interpolate LexUnterminatedBlockComment =
    "Unterminated block comment"

  interpolate (LexInvalidBasisStringLiteral rawText) =
    "Invalid Leaf basis-string literal " ++ rawText ++
    ". Expected bs\"...\" with only 0, 1, +, -, i, and I."

  interpolate (LexInvalidByteLiteral rawText) =
    "Invalid Leaf byte literal " ++ rawText ++
    ". Expected one printable ASCII byte, a simple byte escape, or a hexadecimal byte escape of the form b'\\xNN'."

  interpolate (LexInvalidByteStringLiteral rawText) =
    "Invalid Leaf byte-string literal " ++ rawText ++
    ". Expected printable ASCII bytes or supported byte escapes."

  interpolate (LexInvalidStringLiteral rawText) =
    "Invalid Leaf string literal " ++ rawText ++
    ". Normal Leaf strings currently allow only ASCII letters, digits, and underscores, with no escapes."

  interpolate (LexInvalidNumberLiteral rawText) =
    "Invalid Leaf number literal " ++ rawText ++
    ". Expected a Rust-style integer or floating-point literal supported by Leaf."

  interpolate LexUnterminatedStringLiteral =
    "Unterminated string literal"

  interpolate LexUnterminatedBasisStringLiteral =
    "Unterminated basis-string literal"

  interpolate LexUnterminatedByteStringLiteral =
    "Unterminated byte-string literal"

  interpolate LexUnterminatedByteLiteral =
    "Unterminated byte literal"

  interpolate LexUnsupportedCharLiteral =
    "Character literals such as 'a' are not supported in Leaf yet"

  interpolate (LexInternalLexerError message) =
    "Internal Leaf lexer error: " ++ message

||| Render a lexer error together with its source bounds.
public export
renderLexerError : Bounded LexerError -> String
renderLexerError (B lexerError NoBounds) =
  "Lexer error: " ++ interpolate lexerError
renderLexerError (B lexerError bounds) =
  "Lexer error at " ++ interpolate bounds ++ ": " ++ interpolate lexerError
