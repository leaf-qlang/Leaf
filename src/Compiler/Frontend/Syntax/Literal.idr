module Compiler.Frontend.Syntax.Literal

import Data.List
import Data.Maybe
import Compiler.Frontend.Token
import Compiler.Frontend.ASTPhases

%default total

--------------------------------------------------------------------------------
-- Literals in the AST
--------------------------------------------------------------------------------
-- One node family for every literal form in Leaf source:
--
--   1000  1_000  0xff_u8  0b1111_0000i64      -- integer literals
--   1.0  1.0e-3  12E+99_f64  5f32             -- float literals
--   "Hello"                                   -- string literals
--   b'a'  b'\n'  b'\x41'                      -- byte literals
--   b"hello"  b"ABC\x41"                      -- byte-string literals
--   bs"10+-iI"                                -- basis-string literals
--   true  false                               -- boolean literals
--   ()                                        -- unit literal
--   zero one plus minus plusi minusi          -- quantum state literals
--
--   * Numeric, string, byte, byte-string, and basis-string literals preserve
--     their RAW SOURCE SPELLING, exactly as the lexer captured it: quotes,
--     prefixes (0x/0o/0b/b/bs), digit separators (1_000), exponents, and
--     type suffixes (0xff_u8, 5f32) all included.
--------------------------------------------------------------------------------

public export
data LiteralNode
  = LiteralIntegerRaw     String          -- e.g. "1_000", "0xff_u8", "0b1010"
  | LiteralFloatRaw       String          -- e.g. "1.0e-3", "12E+99_f64", "5f32"
  | LiteralStringRaw      String          -- raw spelling including quotes
  | LiteralByteRaw        String          -- e.g. "b'a'", "b'\\x41'"
  | LiteralByteStringRaw  String          -- e.g. "b\"hello\""
  | LiteralBasisStringRaw String          -- e.g. "bs\"10+-iI\""
  | LiteralBoolean        Bool            -- true / false, already decoded
  | LiteralUnit                           -- ()
  | LiteralQuantumState   BasisStateName  -- zero / one / plus / minus / plusi / minusi

--------------------------------------------------------------------------------
-- Phase wrappers
--------------------------------------------------------------------------------

public export
Literal : AstPhase -> Type
Literal phase = AstNode phase LiteralNode

public export
SurfaceLiteral : Type
SurfaceLiteral = Literal SurfaceAstPhase

public export
CanonicalLiteral : Type
CanonicalLiteral = Literal CanonicalAstPhase

public export
ResolvedLiteral : Type
ResolvedLiteral = Literal ResolvedAstPhase

public export
TypedLiteral : Type
TypedLiteral = Literal TypedAstPhase

--------------------------------------------------------------------------------
-- Integer literal values and suffixes
--------------------------------------------------------------------------------

||| Value of a well-formed integer literal's raw spelling: digit separators, a
||| 0x/0o/0b prefix and an integer type suffix are accepted, e.g. "1_000",
||| "0xff_u8", "0xFF". The lexer rejects uppercase prefixes such as "0XFF".
public export
integerLiteralValue : String -> Maybe Nat
integerLiteralValue rawLiteralText =
  let (numberBase, digitsAndSuffix) = splitBase (filter (/= '_') (unpack rawLiteralText))
      (digitCharacters, suffixCharacters) = span (isDigitInBase numberBase) digitsAndSuffix
  in if null digitCharacters || not (validSuffix suffixCharacters)
       then Nothing
       else Just $ foldl (\accumulatedValue, digitCharacter => accumulatedValue * numberBase + fromMaybe 0 (digitValue digitCharacter)) 0 digitCharacters
  where
    splitBase : List Char -> (Nat, List Char)
    splitBase literalCharacters@('0' :: baseMarker :: charactersAfterPrefix) =
      case toLower baseMarker of
        'x' => (16, charactersAfterPrefix)
        'o' => (8, charactersAfterPrefix)
        'b' => (2, charactersAfterPrefix)
        _ => (10, literalCharacters)
    splitBase literalCharacters = (10, literalCharacters)

    digitValue : Char -> Maybe Nat
    digitValue character =
      if isDigit character
        then Just (cast (ord character - ord '0'))
        else let lowercaseCharacter = toLower character in
          if lowercaseCharacter >= 'a' && lowercaseCharacter <= 'f' then Just (cast (ord lowercaseCharacter - ord 'a' + 10)) else Nothing

    isDigitInBase : Nat -> Char -> Bool
    isDigitInBase numberBase character = maybe False (< numberBase) (digitValue character)

    validSuffix : List Char -> Bool
    validSuffix [] = True
    validSuffix suffixCharacters = pack suffixCharacters `elem` ["i8", "i16", "i32", "i64", "i128", "u8", "u16", "u32", "u64", "u128", "usize"]

||| The integer type named by the suffix of a well-formed integer literal's raw
||| spelling, if one was written: "0xff_u8" names u8, "1_000" none. No digit
||| or base prefix contains `i` or `u`, so the suffix starts at the first one.
public export
integerLiteralSuffixType : String -> Maybe TypPrimName
integerLiteralSuffixType rawLiteralText =
  case break (\character => character == 'i' || character == 'u') (unpack rawLiteralText) of
    (_, []) => Nothing
    (_, suffixCharacters) => typeFromString (pack suffixCharacters)

||| The current target uses 64-bit pointers, independently of the compiler host.
public export
usizeBitWidth : Nat
usizeBitWidth = 64

||| Largest representable count or index. Object layout imposes a separate
||| byte-size limit; not every array of this length can be allocated.
public export
usizeMaximum : Nat
usizeMaximum = 18446744073709551615

||| The largest value of an unsigned integer type; Nothing for any other type.
public export
unsignedIntegerMaximum : TypPrimName -> Maybe Nat
unsignedIntegerMaximum primitiveName =
  case primitiveName of
    TypPrimU8    => Just 255
    TypPrimU16   => Just 65535
    TypPrimU32   => Just 4294967295
    TypPrimU64   => Just 18446744073709551615
    TypPrimU128  => Just 340282366920938463463374607431768211455
    TypPrimUsize => Just usizeMaximum
    _            => Nothing

public export
data ArrayLengthProblem
  = NonUsizeLengthSuffix TypPrimName                -- `3i8`, `3u64`
  | LengthExceedsSuffixType TypPrimName Nat       -- a suffixed usize literal beyond its maximum

||| The problem with an integer literal's raw spelling as an array length, if any.
public export
arrayLengthProblem : String -> Maybe ArrayLengthProblem
arrayLengthProblem rawLiteralText = do
  suffixType <- integerLiteralSuffixType rawLiteralText
  if suffixType /= TypPrimUsize
    then Just (NonUsizeLengthSuffix suffixType)
    else if maybe False (> usizeMaximum) (integerLiteralValue rawLiteralText)
      then Just (LengthExceedsSuffixType TypPrimUsize usizeMaximum)
      else Nothing
