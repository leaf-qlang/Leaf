module Compiler.Frontend.Lexer.Lexer

import Text.Bounds
import Text.ByteBounds
import Text.ILex
import Text.ParseError

import Compiler.Frontend.Token
import Compiler.Frontend.Lexer.Error
import Compiler.Frontend.Lexer.Rules

%default total

--------------------------------------------------------------------------------
-- Translating ilex native errors into Leaf's public LexerError.
--
-- `runLeafLexer` returns an `Either (BBErr LexerError) ...`, where an
-- `BBErr e` is a byte-bounded `InnerError e`. This module is the single place
-- where those native ilex failures are translated so `lexFile` exposes only
-- `Bounded LexerError`.
--------------------------------------------------------------------------------
translateInnerLexerError : InnerError LexerError -> LexerError
translateInnerLexerError (Custom lexerError) =
  lexerError

translateInnerLexerError EOI =
  LexUnexpectedEndOfInput

translateInnerLexerError (Expected expectedTokens actualText) =
  LexUnexpectedInput expectedTokens actualText

translateInnerLexerError (ExpectedChar characterClass) =
  LexUnexpectedInput [interpolate characterClass] ""

translateInnerLexerError ExpectedEOI =
  LexUnexpectedInput ["end of input"] "more input"

translateInnerLexerError (InvalidControl characterValue) =
  LexUnexpectedInput [] (show characterValue)

translateInnerLexerError InvalidEscape =
  LexInternalLexerError "Invalid escape sequence reported by ilex"

translateInnerLexerError (OutOfBounds rawText) =
  LexInternalLexerError ("Out-of-bounds value reported by ilex: " ++ rawText)

translateInnerLexerError (Unclosed description) =
  LexUnclosed description

translateInnerLexerError (Unknown actualText) =
  LexUnexpectedInput [] actualText

translateInnerLexerError (InvalidByte byteValue) =
  LexUnexpectedOrInvalidByte byteValue

--------------------------------------------------------------------------------
-- Unsupported characters.
--
-- When no rule matches, ilex reports what it read in several forms: the text
-- it consumed, which for a non-ASCII character can be empty, invisible, or
-- start at an earlier token, or just the first byte of the character. All of
-- them mean that the character at the error's start position cannot start a
-- Leaf token, so they are reported uniformly as that unsupported character,
-- bounded by the character alone.
--------------------------------------------------------------------------------
innerErrorMeansNoRuleMatched : InnerError LexerError -> Bool
innerErrorMeansNoRuleMatched (Expected _ _) = True
innerErrorMeansNoRuleMatched (ExpectedChar _) = True
innerErrorMeansNoRuleMatched (InvalidControl _) = True
innerErrorMeansNoRuleMatched (Unknown _) = True
innerErrorMeansNoRuleMatched (InvalidByte _) = True
innerErrorMeansNoRuleMatched _ = False

-- The character whose UTF-8 encoding starts at the given byte offset, or
-- Nothing when the offset is past the end or inside a character's encoding.
characterAtByteOffset : (byteOffset : Nat) -> List Char -> Maybe Char
characterAtByteOffset _ [] = Nothing
characterAtByteOffset Z (character :: _) = Just character
characterAtByteOffset (S remainingByteOffset) (character :: laterCharacters) =
  let characterByteLength = utf8ByteLength character in
  case characterByteLength <= S remainingByteOffset of
    True => characterAtByteOffset (minus (S remainingByteOffset) characterByteLength) laterCharacters
    False => Nothing

translateLexerFailure : (programText : String) -> BBErr LexerError -> ByteBounded LexerError
translateLexerFailure programText (B innerError (BB errorStart errorEnd)) =
  case innerErrorMeansNoRuleMatched innerError of
    False => B (translateInnerLexerError innerError) (BB errorStart errorEnd)
    True =>
      case characterAtByteOffset errorStart.pos (unpack programText) of
        Just unsupportedCharacter =>
          B (LexUnsupportedCharacter unsupportedCharacter)
            (BB errorStart (incLen (utf8ByteLength unsupportedCharacter) errorStart))
        Nothing => B (translateInnerLexerError innerError) (BB errorStart errorEnd)
translateLexerFailure _ lexerFailure =
  map translateInnerLexerError lexerFailure

--------------------------------------------------------------------------------
-- Position-map input
--
-- Leaf treats a bare carriage return as a line break, but ilex's position map
-- advances lines only for line-feed bytes. Replace only bare carriage returns
-- in the text used to build the map. Both characters occupy one UTF-8 byte, so
-- all byte offsets still refer to the original input. CRLF pairs stay intact,
-- avoiding an extra line advance. The original text is always passed unchanged
-- to `runString`, preserving token contents.
--------------------------------------------------------------------------------
positionMapInput : String -> String
positionMapInput =
  pack . replaceBareCarriageReturns . unpack
  where
    replaceBareCarriageReturns : List Char -> List Char
    replaceBareCarriageReturns [] =
      []
    replaceBareCarriageReturns ('\r' :: '\n' :: remainingCharacters) =
      '\r' :: '\n' :: replaceBareCarriageReturns remainingCharacters
    replaceBareCarriageReturns ('\r' :: remainingCharacters) =
      '\n' :: replaceBareCarriageReturns remainingCharacters
    replaceBareCarriageReturns (character :: remainingCharacters) =
      character :: replaceBareCarriageReturns remainingCharacters

--------------------------------------------------------------------------------
-- Leading byte order mark
--
-- Some editors save UTF-8 files with a leading byte order mark (U+FEFF). As in
-- Rust, a single byte order mark at the very start of the input is not part of
-- the program and is removed before lexing, so positions are reported as if it
-- were absent. A byte order mark anywhere else is ordinary unexpected input.
--------------------------------------------------------------------------------
removeLeadingByteOrderMark : String -> String
removeLeadingByteOrderMark sourceText =
  case strUncons sourceText of
    Just ('\xFEFF', textAfterByteOrderMark) => textAfterByteOrderMark
    _ => sourceText

--------------------------------------------------------------------------------
-- Main entry point: lexFile
--
-- The installed ilex tracks positions as raw byte offsets while lexing and only
-- exposes `Bounded` (line/column) values via a position map built from the whole
-- input once lexing has finished. This module is therefore also the single place
-- where ilex's byte-offset results are converted to line/column positions and
-- native ilex failures are translated into Leaf's public `LexerError`.
--------------------------------------------------------------------------------
public export
lexFile : String -> Either (Bounded LexerError) (List (Bounded Token))
lexFile sourceText =
  let programText := removeLeadingByteOrderMark sourceText
      positionMap := stringPositionMap (positionMapInput programText)
  in case runLeafLexer programText of
    Left byteBoundedError =>
      Left (toBounded (translateLexerFailure programText byteBoundedError))

    Right byteBoundedTokens =>
      Right (map toBounded byteBoundedTokens)
