module Compiler.Frontend.Parser.Error

import Data.List
import Text.Parse.Manual
import public Text.ParseError

import Compiler.Frontend.Source

%default total

public export
data CustomParseError
    = UnsupportedFeature String
    | UnexpectedToken String
    | ParseErrorWithMessage String

public export
0 ParseError : Type
ParseError = InnerError CustomParseError

quoted : String -> String
quoted expectedText = "'" ++ expectedText ++ "'"

renderExpected : String -> List String -> String
renderExpected onlyExpected [] = quoted onlyExpected
renderExpected firstExpected [secondExpected] = quoted firstExpected ++ " or " ++ quoted secondExpected
renderExpected firstExpected (secondExpected :: remainingExpected) = quoted firstExpected ++ ", " ++ renderExpected secondExpected remainingExpected

||| The inner clause of a parse error: what went wrong
public export
renderParseError : ParseError -> String
renderParseError (Custom (UnsupportedFeature message)) = message
renderParseError (Custom (UnexpectedToken message)) = message
renderParseError (Custom (ParseErrorWithMessage message)) = message
renderParseError EOI = "unexpected end of input"
renderParseError (Expected [] actualToken) = "unexpected " ++ actualToken
renderParseError (Expected (firstExpected :: remainingExpected) actualToken) =
  "expected " ++ renderExpected firstExpected remainingExpected ++ ", but got " ++ actualToken
renderParseError (ExpectedChar charClass) = "expected " ++ interpolate charClass
renderParseError ExpectedEOI = "expected end of input"
renderParseError (InvalidControl controlCharacter) = "invalid control character: " ++ show controlCharacter
renderParseError InvalidEscape = "invalid escape sequence"
renderParseError (OutOfBounds valueText) = "value out of bounds: " ++ valueText
renderParseError (Unclosed unclosedText) = "unclosed " ++ unclosedText
renderParseError (Unknown tokenText) = "unknown or invalid token: " ++ tokenText
renderParseError (InvalidByte invalidByte) = "unexpected or invalid byte: " ++ show invalidByte

public export
implementation Show ParseError where
  show = renderParseError

public export
showParseError : Located ParseError -> String
-- `show locatedError.value`, not `\{locatedError.value}`: ilex-core's Text.ParseError ships
-- interpolation with its own wording, which would silently replace ours
showParseError locatedError = "Parse error at: \{locatedError.span}, with message: \{show locatedError.value}"
