module Lexer.UnicodeNormalizationTest

import Data.Maybe
import Text.Bounds
import TestFramework

import Compiler.Frontend.Token
import Compiler.Frontend.Lexer.Error
import Compiler.Frontend.Lexer.Lexer
import Compiler.Frontend.Lexer.UnicodeNormalization
import Compiler.Frontend.ScopeAndNameResolver.Data
import ScopeAndNameResolution.Helper

%default total

lexTokenValues : String -> Either LexerError (List Token)
lexTokenValues sourceText =
  case lexFile sourceText of
    Left boundedError => Left boundedError.val
    Right boundedTokens => Right (map val boundedTokens)

lexErrorBounds : String -> Maybe Bounds
lexErrorBounds sourceText =
  case lexFile sourceText of
    Left boundedError => Just boundedError.bounds
    Right _ => Nothing

sourceResolves : String -> Bool
sourceResolves sourceText = isJust (resolvedSource sourceText)

export
runUnicodeNormalizationTests : IO Bool
runUnicodeNormalizationTests = runTests $ Test.do
  ------------------------------------------------------------
  -- Normalization Form C.
  ------------------------------------------------------------
  test "ASCII text is already in NFC" $
    nfcNormalized "counter_1" `shouldBe` "counter_1"

  test "a composed character stays composed" $
    nfcNormalized "\xE9" `shouldBe` "\xE9"

  test "a letter followed by a combining mark is composed" $
    nfcNormalized "e\x301" `shouldBe` "\xE9"

  test "singleton decompositions are replaced by their canonical equivalents" $
    [nfcNormalized "\x212B", nfcNormalized "\x2126"] `shouldBe` ["\xC5", "\x3A9"]

  test "combining marks are put in canonical order" $
    nfcNormalized "q\x307\x323" `shouldBe` "q\x323\x307"

  test "canonical ordering keeps combining marks of an equal class in their order" $
    nfcNormalized "q\x301\x323\x300" `shouldBe` "q\x323\x301\x300"

  test "A composes with a ring above unless an intervening overline blocks it" $
    [nfcNormalized "A\x30A", nfcNormalized "A\x305\x30A"] `shouldBe`
      ["\xC5", "A\x305\x30A"]

  test "a Hangul jamo sequence is composed into its syllable" $
    nfcNormalized "\x1100\x1161\x11A8" `shouldBe` "\xAC01"

  test "a Hangul syllable stays composed" $
    nfcNormalized "\xAC01" `shouldBe` "\xAC01"

  test "a character excluded from composition stays decomposed" $
    nfcNormalized "\x958" `shouldBe` "\x915\x93C"

  ------------------------------------------------------------
  -- Identifiers in the lexer.
  ------------------------------------------------------------
  test "a decomposed identifier is lexed in NFC" $
    lexTokenValues "e\x301" `shouldBe` Right [TokIdent "\xE9", TokEOF]

  test "composed and decomposed spellings of an identifier lex to the same token" $
    (lexTokenValues "caf\xE9" == lexTokenValues "cafe\x301") `shouldBe` True

  test "keywords are unaffected by normalization" $
    lexTokenValues "fn" `shouldBe` Right [TokKw KwFn, TokEOF]

  test "a decomposed identifier is bounded by its source spelling" $
    lexFile "e\x301 x" `shouldBe`
      Right
        [ B (TokIdent "\xE9") (BS (P 0 0) (P 0 1))
        , B (TokIdent "x") (BS (P 0 3) (P 0 3))
        , B TokEOF (BS (P 0 4) (P 0 4))
        ]

  test "a decomposed identifier directly followed by non-ASCII whitespace is lexed in NFC" $
    lexTokenValues "e\x301\x2028y" `shouldBe`
      Right [TokIdent "\xE9", TokIdent "y", TokEOF]

  test "an unsupported character after a decomposed identifier is reported at its own position" $
    lexErrorBounds "e\x301\x2192" `shouldBe` Just (BS (P 0 2) (P 0 2))

  ------------------------------------------------------------
  -- Names.
  ------------------------------------------------------------
  test "a use spelled decomposed resolves to a binding spelled composed" $
    sourceResolves "fn f() { let \xE9 = 1; e\x301; }" `shouldBe` True

  test "a use spelled composed resolves to a binding spelled decomposed" $
    sourceResolves "fn f() { let e\x301 = 1; \xE9; }" `shouldBe` True
