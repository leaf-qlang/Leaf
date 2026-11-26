module Compiler.Frontend.TypeChecker.Numeric

import Data.Bits
import Data.Maybe

import Compiler.Helper
import Compiler.Frontend.TypeChecker.Data
import Compiler.Frontend.TypeChecker.Type
import Compiler.Frontend.Source
import Compiler.Frontend.Syntax.Literal
import Compiler.Frontend.Syntax.Operator
import Compiler.Frontend.Token

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
integerBounds integerType = do
  bitWidth <- integerBitWidth integerType
  let modulus = the Integer 1 `shiftL` bitWidth
  pure $ if isSignedInteger integerType
    then (negate (modulus `div` 2), modulus `div` 2 - 1)
    else (0, modulus - 1)

fitsInteger : TypPrimName -> Integer -> Bool
fitsInteger integerType value =
  case integerBounds integerType of
    Nothing => False
    Just (lowerBound, upperBound) => (value >= lowerBound) && (value <= upperBound)

literalBounds : TypPrimName -> Maybe (Integer, Integer)
literalBounds TypPrimBit = Just (0, 1)
literalBounds literalType = integerBounds literalType

fitsLiteral : TypPrimName -> Integer -> Bool
fitsLiteral literalType value =
  case literalBounds literalType of
    Nothing => False
    Just (lowerBound, upperBound) => (value >= lowerBound) && (value <= upperBound)

export
checkIntegerLiteralRange : TypPrimName -> Integer -> SourceSpan -> Either TypeError ()
checkIntegerLiteralRange literalType literalValue sourceSpan =
  case literalBounds literalType of
    Nothing => unreachable __FILE__ {function = "checkIntegerLiteralRange"} {reason = "an integer literal has the non-integer type " ++ show literalType}
    Just (lowerBound, upperBound) =>
      if literalValue >= lowerBound && literalValue <= upperBound
        then Right ()
        else Left (IntegerLiteralOutOfRange literalValue (LeafPrimitiveType literalType) sourceSpan)

inferLiteral : (isNegated : Bool) -> Maybe TypPrimName -> String -> SourceSpan -> Either TypeError (TypPrimName, Integer)
inferLiteral isNegated expectedPrimitive rawLiteralText sourceSpan = do
  let expectedLiteralType = do
        primitiveName <- expectedPrimitive
        _ <- literalBounds primitiveName
        pure primitiveName
  let literalType = fromMaybe (fromMaybe TypPrimI32 expectedLiteralType) (integerLiteralSuffixType rawLiteralText)
  case expectedPrimitive of
    Just expectedType =>
      if expectedType /= literalType
        then Left (TypeMismatch (LeafPrimitiveType expectedType) (LeafPrimitiveType literalType) sourceSpan)
        else Right ()
    Nothing => Right ()
  literalMagnitude <- case integerLiteralValue rawLiteralText of
    Nothing => Left (CannotInferType sourceSpan)
    Just digitsValue => Right (the Integer (cast digitsValue))
  if isNegated && not (isSignedInteger literalType)
    then Left (InvalidUnaryOperand (show UnaryNegate) (LeafPrimitiveType literalType) sourceSpan)
    else do
      let literalValue = if isNegated then negate literalMagnitude else literalMagnitude
      checkIntegerLiteralRange literalType literalValue sourceSpan
      Right (literalType, literalValue)

export
inferIntegerLiteral : Maybe TypPrimName -> String -> SourceSpan -> Either TypeError (TypPrimName, Integer)
inferIntegerLiteral = inferLiteral False

export
inferNegatedIntegerLiteral : Maybe TypPrimName -> String -> SourceSpan -> Either TypeError (TypPrimName, Integer)
inferNegatedIntegerLiteral = inferLiteral True

export
checkArrayLength : LeafType -> Integer -> SourceSpan -> Either TypeError Nat
checkArrayLength lengthType lengthValue sourceSpan =
  if lengthType /= LeafPrimitiveType TypPrimUsize
    then Left (IncorrectArrayLengthType lengthType sourceSpan)
    else if lengthValue < 0 || lengthValue > cast usizeMaximum
      then Left (ArrayLengthTooLarge lengthValue sourceSpan)
      else Right (cast lengthValue)

truncateAndInterpretInteger : TypPrimName -> Nat -> Integer -> Integer
truncateAndInterpretInteger integerType bitWidth value =
  let modulus = the Integer 1 `shiftL` bitWidth
      lowBits = value .&. (modulus - 1)
  in if isSignedInteger integerType && lowBits >= modulus `div` 2
       then lowBits - modulus
       else lowBits

checkedResult : TypPrimName -> Integer -> SourceSpan -> Either TypeError ConstValue
checkedResult resultType resultValue sourceSpan =
  if fitsInteger resultType resultValue
    then Right (ConstInteger resultValue)
    else Left (ArithmeticOverflow (LeafPrimitiveType resultType) sourceSpan)

export
evalIntegerUnary : UnaryOperator -> TypPrimName -> Integer -> SourceSpan -> Either TypeError ConstValue
evalIntegerUnary unaryOperator TypPrimBit operandValue sourceSpan =
  case unaryOperator of
    UnaryLogicalNot =>
      if fitsLiteral TypPrimBit operandValue
        then Right (ConstInteger (1 - operandValue))
        else invalidOperand
    _ => invalidOperand
  where
    invalidOperand : Either TypeError ConstValue
    invalidOperand = Left (InvalidUnaryOperand (show unaryOperator) (LeafPrimitiveType TypPrimBit) sourceSpan)
evalIntegerUnary unaryOperator operandType operandValue sourceSpan =
  case integerBitWidth operandType of
    Nothing => Left (InvalidUnaryOperand (show unaryOperator) (LeafPrimitiveType operandType) sourceSpan)
    Just bitWidth => case unaryOperator of
      UnaryNegate =>
        if isSignedInteger operandType
          then checkedResult operandType (negate operandValue) sourceSpan
          else Left (InvalidUnaryOperand (show unaryOperator) (LeafPrimitiveType operandType) sourceSpan)
      UnaryLogicalNot => Right (ConstInteger (truncateAndInterpretInteger operandType bitWidth (complement operandValue)))
      _ => Left (InvalidUnaryOperand (show unaryOperator) (LeafPrimitiveType operandType) sourceSpan)

-- Rust integer division truncates toward zero; remainder has the dividend's sign.
quotient : Integer -> Integer -> Integer
quotient dividend divisor =
  let magnitude = abs dividend `div` abs divisor
  in if (dividend < 0) /= (divisor < 0) then negate magnitude else magnitude

isShiftOperator : BinaryOperator -> Bool
isShiftOperator BinaryShiftLeft = True
isShiftOperator BinaryShiftRight = True
isShiftOperator _ = False

export
evalIntegerBinaryOperation : BinaryOperator -> TypPrimName -> Integer -> TypPrimName -> Integer -> SourceSpan -> Either TypeError ConstValue
evalIntegerBinaryOperation binaryOperator leftType leftValue rightType rightValue sourceSpan =
  case (integerBitWidth leftType, integerBitWidth rightType) of
    (Just leftBitWidth, Just _) =>
      if leftType /= rightType && not (isShiftOperator binaryOperator)
        then invalidOperands
        else evaluateOperation leftBitWidth
    _ => invalidOperands
  where
    invalidOperands : Either TypeError ConstValue
    invalidOperands = Left (InvalidBinaryOperands (show binaryOperator) (LeafPrimitiveType leftType) (LeafPrimitiveType rightType) sourceSpan)

    divideOrTakeRemainder : (isRemainder : Bool) -> Either TypeError ConstValue
    divideOrTakeRemainder isRemainder =
      if rightValue == 0 then Left (DivisionByZeroInConstant sourceSpan)
      else if not (fitsInteger leftType (quotient leftValue rightValue))
        then Left (ArithmeticOverflow (LeafPrimitiveType leftType) sourceSpan)
        else checkedResult leftType (if isRemainder then leftValue - quotient leftValue rightValue * rightValue else quotient leftValue rightValue) sourceSpan

    evaluateOperation : (leftBitWidth : Nat) -> Either TypeError ConstValue
    evaluateOperation leftBitWidth = case binaryOperator of
      BinaryAdd => checkedResult leftType (leftValue + rightValue) sourceSpan
      BinarySubtract => checkedResult leftType (leftValue - rightValue) sourceSpan
      BinaryMultiply => checkedResult leftType (leftValue * rightValue) sourceSpan
      BinaryDivide => divideOrTakeRemainder False
      BinaryRemainder => divideOrTakeRemainder True
      BinaryEqual => Right (ConstBool (leftValue == rightValue))
      BinaryNotEqual => Right (ConstBool (leftValue /= rightValue))
      BinaryGreater => Right (ConstBool (leftValue > rightValue))
      BinaryGreaterEqual => Right (ConstBool (leftValue >= rightValue))
      BinaryLess => Right (ConstBool (leftValue < rightValue))
      BinaryLessEqual => Right (ConstBool (leftValue <= rightValue))
      BinaryBitAnd => Right (ConstInteger (truncateAndInterpretInteger leftType leftBitWidth (leftValue .&. rightValue)))
      BinaryBitOr => Right (ConstInteger (truncateAndInterpretInteger leftType leftBitWidth (leftValue .|. rightValue)))
      BinaryBitXor => Right (ConstInteger (truncateAndInterpretInteger leftType leftBitWidth (leftValue `xor` rightValue)))
      BinaryShiftLeft =>
        if rightValue < 0 || rightValue >= cast leftBitWidth
          then Left (ArithmeticOverflow (LeafPrimitiveType leftType) sourceSpan)
          else Right (ConstInteger (truncateAndInterpretInteger leftType leftBitWidth (leftValue `shiftL` cast rightValue)))
      BinaryShiftRight =>
        if rightValue < 0 || rightValue >= cast leftBitWidth
          then Left (ArithmeticOverflow (LeafPrimitiveType leftType) sourceSpan)
          else Right (ConstInteger (leftValue `shiftR` cast rightValue))
      _ => invalidOperands

export
castInteger : TypPrimName -> TypPrimName -> Integer -> SourceSpan -> Either TypeError Integer
castInteger sourceType targetType integerValue sourceSpan =
  case (integerBitWidth sourceType, integerBitWidth targetType) of
    (Just _, Just targetBitWidth) => Right (truncateAndInterpretInteger targetType targetBitWidth integerValue)
    _ => Left (InvalidCast (LeafPrimitiveType sourceType) (LeafPrimitiveType targetType) sourceSpan)

||| Cast an already-rounded floating-point value to an integer: truncate toward
||| zero, saturate at the destination bounds, and convert NaN to zero. An f32
||| evaluator must round to f32 before calling this helper with its Double carrier.
export
castFloatToInteger : TypPrimName -> TypPrimName -> Double -> SourceSpan -> Either TypeError Integer
castFloatToInteger sourceType targetType floatValue sourceSpan =
  if sourceType /= TypPrimF32 && sourceType /= TypPrimF64
    then invalidCast
    else case integerBounds targetType of
      Nothing => invalidCast
      Just (targetMinimum, targetMaximum) =>
        if floatValue /= floatValue then Right 0
        else if floatValue <= cast targetMinimum then Right targetMinimum
        else if floatValue >= cast targetMaximum then Right targetMaximum
        else Right (cast (if floatValue < 0 then ceiling floatValue else floor floatValue))
  where
    invalidCast : Either TypeError Integer
    invalidCast = Left (InvalidCast (LeafPrimitiveType sourceType) (LeafPrimitiveType targetType) sourceSpan)

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
arrayLayoutSize elementSize elementCount =
  if elementCount > usizeMaximum then Left (LayoutCountTooLarge elementCount)
  else let byteSize = elementSize * elementCount in
    if byteSize > maxObjectSize then Left (LayoutSizeTooLarge byteSize)
    else Right byteSize
