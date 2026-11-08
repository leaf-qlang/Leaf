module Compiler.TypeChecker.Numeric

import Data.Bits
import Data.Maybe

import Compiler.TypeChecker.Data
import Compiler.TypeChecker.Type
import Frontend.Source
import Frontend.Syntax.Literal
import Frontend.Syntax.Operator
import Frontend.Token

%default total

public export
integerBitWidth : TypPrimName -> Maybe Nat
integerBitWidth TypPrimI8 = Just 8
integerBitWidth TypPrimI16 = Just 16
integerBitWidth TypPrimI32 = Just 32
integerBitWidth TypPrimI64 = Just 64
integerBitWidth TypPrimI128 = Just 128
integerBitWidth TypPrimU8 = Just 8
integerBitWidth TypPrimU16 = Just 16
integerBitWidth TypPrimU32 = Just 32
integerBitWidth TypPrimU64 = Just 64
integerBitWidth TypPrimU128 = Just 128
integerBitWidth TypPrimUsize = Just usizeBitWidth
integerBitWidth _ = Nothing

public export
isSignedInteger : TypPrimName -> Bool
isSignedInteger TypPrimI8 = True
isSignedInteger TypPrimI16 = True
isSignedInteger TypPrimI32 = True
isSignedInteger TypPrimI64 = True
isSignedInteger TypPrimI128 = True
isSignedInteger _ = False

public export
integerBounds : TypPrimName -> Maybe (Integer, Integer)
integerBounds primitive = do
  bitWidth <- integerBitWidth primitive
  let modulus = the Integer 1 `shiftL` bitWidth
  pure $ if isSignedInteger primitive
    then (negate (modulus `div` 2), modulus `div` 2 - 1)
    else (0, modulus - 1)

fitsInteger : TypPrimName -> Integer -> Bool
fitsInteger primitive value =
  case integerBounds primitive of
    Nothing => False
    Just (lower, upper) => (value >= lower) && (value <= upper)

literalBounds : TypPrimName -> Maybe (Integer, Integer)
literalBounds TypPrimBit = Just (0, 1)
literalBounds primitive = integerBounds primitive

fitsLiteral : TypPrimName -> Integer -> Bool
fitsLiteral primitive value =
  case literalBounds primitive of
    Nothing => False
    Just (lower, upper) => (value >= lower) && (value <= upper)

inferLiteral : (negated : Bool) -> Maybe TypPrimName -> String -> SourceSpan -> Either TypeError (TypPrimName, Integer)
inferLiteral negated expected raw sourceSpan = do
  let contextualTypPrimName = do
        primitiveName <- expected
        _ <- literalBounds primitiveName
        pure primitiveName
  let primitiveName = fromMaybe (fromMaybe TypPrimI32 contextualTypPrimName) (integerLiteralSuffixType raw)
  case expected of
    Just expectedType =>
      if expectedType /= primitiveName
        then Left (TypeMismatch (LeafPrimitiveType expectedType) (LeafPrimitiveType primitiveName) sourceSpan)
        else Right ()
    Nothing => Right ()
  value <- case integerLiteralValue raw of
    Nothing => Left (CannotInferType sourceSpan)
    Just value => Right (the Integer (cast value))
  if negated && not (isSignedInteger primitiveName)
    then Left (InvalidUnaryOperand (show UnaryNegate) (LeafPrimitiveType primitiveName) sourceSpan)
    else do
      let signed = if negated then negate value else value
      if fitsLiteral primitiveName signed
        then Right (primitiveName, signed)
        else Left (IntegerLiteralOutOfRange signed (LeafPrimitiveType primitiveName) sourceSpan)

export
inferIntegerLiteral : Maybe TypPrimName -> String -> SourceSpan -> Either TypeError (TypPrimName, Integer)
inferIntegerLiteral = inferLiteral False

export
inferNegatedIntegerLiteral : Maybe TypPrimName -> String -> SourceSpan -> Either TypeError (TypPrimName, Integer)
inferNegatedIntegerLiteral = inferLiteral True

export
checkArrayLength : LeafType -> Integer -> SourceSpan -> Either TypeError Nat
checkArrayLength actual value sourceSpan =
  if actual /= LeafPrimitiveType TypPrimUsize
    then Left (InvalidArrayLength actual sourceSpan)
    else if value < 0 || value > cast usizeMaximum
      then Left (ArrayLengthTooLarge value sourceSpan)
      else Right (cast value)

truncateAndInterpretInteger : TypPrimName -> Nat -> Integer -> Integer
truncateAndInterpretInteger primitive width value =
  let modulus = the Integer 1 `shiftL` width
      bits = value .&. (modulus - 1)
  in if isSignedInteger primitive && bits >= modulus `div` 2
       then bits - modulus
       else bits

checkedResult : TypPrimName -> Integer -> SourceSpan -> Either TypeError ConstValue
checkedResult primitive value sourceSpan =
  if fitsInteger primitive value
    then Right (ConstInteger value)
    else Left (ArithmeticOverflow (LeafPrimitiveType primitive) sourceSpan)

export
evalIntegerUnary : UnaryOperator -> TypPrimName -> Integer -> SourceSpan -> Either TypeError ConstValue
evalIntegerUnary operator TypPrimBit value sourceSpan =
  case operator of
    UnaryLogicalNot =>
      if fitsLiteral TypPrimBit value
        then Right (ConstInteger (1 - value))
        else invalid
    _ => invalid
  where
    invalid : Either TypeError ConstValue
    invalid = Left (InvalidUnaryOperand (show operator) (LeafPrimitiveType TypPrimBit) sourceSpan)
evalIntegerUnary operator primitive value sourceSpan =
  case integerBitWidth primitive of
    Nothing => Left (InvalidUnaryOperand (show operator) (LeafPrimitiveType primitive) sourceSpan)
    Just width => case operator of
      UnaryNegate =>
        if isSignedInteger primitive
          then checkedResult primitive (negate value) sourceSpan
          else Left (InvalidUnaryOperand (show operator) (LeafPrimitiveType primitive) sourceSpan)
      UnaryLogicalNot => Right (ConstInteger (truncateAndInterpretInteger primitive width (complement value)))
      _ => Left (InvalidUnaryOperand (show operator) (LeafPrimitiveType primitive) sourceSpan)

-- Rust integer division truncates toward zero; remainder has the dividend's sign.
quotient : Integer -> Integer -> Integer
quotient left right =
  let magnitude = abs left `div` abs right
  in if (left < 0) /= (right < 0) then negate magnitude else magnitude

isShiftOperator : BinaryOperator -> Bool
isShiftOperator BinaryShiftLeft = True
isShiftOperator BinaryShiftRight = True
isShiftOperator _ = False

export
evalIntegerBinaryOperation : BinaryOperator -> TypPrimName -> Integer -> TypPrimName -> Integer -> SourceSpan -> Either TypeError ConstValue
evalIntegerBinaryOperation binaryOperator leftType left rightType right sourceSpan =
  case (integerBitWidth leftType, integerBitWidth rightType) of
    (Just width, Just _) =>
      if leftType /= rightType && not (isShiftOperator binaryOperator)
        then invalid
        else evaluate width
    _ => invalid
  where
    invalid : Either TypeError ConstValue
    invalid = Left (InvalidBinaryOperands (show binaryOperator) (LeafPrimitiveType leftType) (LeafPrimitiveType rightType) sourceSpan)

    divide : Bool -> Either TypeError ConstValue
    divide remainder =
      if right == 0 then Left (DivisionByZeroInConstant sourceSpan)
      else if not (fitsInteger leftType (quotient left right))
        then Left (ArithmeticOverflow (LeafPrimitiveType leftType) sourceSpan)
        else checkedResult leftType (if remainder then left - quotient left right * right else quotient left right) sourceSpan

    evaluate : Nat -> Either TypeError ConstValue
    evaluate width = case binaryOperator of
      BinaryAdd => checkedResult leftType (left + right) sourceSpan
      BinarySubtract => checkedResult leftType (left - right) sourceSpan
      BinaryMultiply => checkedResult leftType (left * right) sourceSpan
      BinaryDivide => divide False
      BinaryRemainder => divide True
      BinaryEqual => Right (ConstBool (left == right))
      BinaryNotEqual => Right (ConstBool (left /= right))
      BinaryGreater => Right (ConstBool (left > right))
      BinaryGreaterEqual => Right (ConstBool (left >= right))
      BinaryLess => Right (ConstBool (left < right))
      BinaryLessEqual => Right (ConstBool (left <= right))
      BinaryBitAnd => Right (ConstInteger (truncateAndInterpretInteger leftType width (left .&. right)))
      BinaryBitOr => Right (ConstInteger (truncateAndInterpretInteger leftType width (left .|. right)))
      BinaryBitXor => Right (ConstInteger (truncateAndInterpretInteger leftType width (left `xor` right)))
      BinaryShiftLeft =>
        if right < 0 || right >= cast width
          then Left (ArithmeticOverflow (LeafPrimitiveType leftType) sourceSpan)
          else Right (ConstInteger (truncateAndInterpretInteger leftType width (left `shiftL` cast right)))
      BinaryShiftRight =>
        if right < 0 || right >= cast width
          then Left (ArithmeticOverflow (LeafPrimitiveType leftType) sourceSpan)
          else Right (ConstInteger (left `shiftR` cast right))
      _ => invalid

export
castInteger : TypPrimName -> TypPrimName -> Integer -> SourceSpan -> Either TypeError Integer
castInteger sourceType targetType value sourceSpan =
  case (integerBitWidth sourceType, integerBitWidth targetType) of
    (Just _, Just width) => Right (truncateAndInterpretInteger targetType width value)
    _ => Left (InvalidCast (LeafPrimitiveType sourceType) (LeafPrimitiveType targetType) sourceSpan)

||| Cast an already-rounded floating-point value to an integer: truncate toward
||| zero, saturate at the destination bounds, and convert NaN to zero. An f32
||| evaluator must round to f32 before calling this helper with its Double carrier.
export
castFloatToInteger : TypPrimName -> TypPrimName -> Double -> SourceSpan -> Either TypeError Integer
castFloatToInteger sourceType targetType value sourceSpan =
  if sourceType /= TypPrimF32 && sourceType /= TypPrimF64
    then invalid
    else case integerBounds targetType of
      Nothing => invalid
      Just (lower, upper) =>
        if value /= value then Right 0
        else if value <= cast lower then Right lower
        else if value >= cast upper then Right upper
        else Right (cast (if value < 0 then ceiling value else floor value))
  where
    invalid : Either TypeError Integer
    invalid = Left (InvalidCast (LeafPrimitiveType sourceType) (LeafPrimitiveType targetType) sourceSpan)

public export
maxObjectSize : Nat
maxObjectSize = 9223372036854775807

public export
data ArrayLayoutError
  = LayoutCountTooLarge Nat
  | LayoutSizeTooLarge Nat

||| For layout once an element's byte size (including padding) is known.
||| A zero-sized element still permits usizeMaximum elements. This does not
||| impose a byte-size limit on mere lengths or on an unlaid-out quantum type.
export
arrayLayoutSize : Nat -> Nat -> Either ArrayLayoutError Nat
arrayLayoutSize elementSize count =
  if count > usizeMaximum then Left (LayoutCountTooLarge count)
  else let bytes = elementSize * count in
    if bytes > maxObjectSize then Left (LayoutSizeTooLarge bytes)
    else Right bytes
