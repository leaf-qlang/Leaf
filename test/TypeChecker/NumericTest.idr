module TypeChecker.NumericTest

import Data.Maybe
import Test.Simple

import Compiler.Prelude
import Compiler.TypeChecker.Data
import Compiler.TypeChecker.Numeric
import Compiler.TypeChecker.PreludeSignatures
import Compiler.TypeChecker.Type
import Frontend.Source
import Frontend.Syntax.Literal
import Frontend.Syntax.Operator
import Frontend.Token

%default total

location : SourceSpan
location = MkSourceSpan "numeric-test.rs" (MkSourcePos 1 1) (MkSourcePos 1 2)

reported : Either TypeError a -> Either String a
reported (Left err) = Left (show err)
reported (Right value) = Right value

integerResult : Either TypeError ConstValue -> Either String Integer
integerResult (Left err) = Left (show err)
integerResult (Right (ConstInteger value)) = Right value
integerResult (Right _) = Left "Expected integer constant"

booleanResult : Either TypeError ConstValue -> Either String Bool
booleanResult (Left err) = Left (show err)
booleanResult (Right (ConstBool value)) = Right value
booleanResult (Right _) = Left "Expected boolean constant"

usizeBinary : BinaryOperator -> Integer -> Integer -> Either String Integer
usizeBinary operator left right = integerResult (evalIntegerBinaryOperation operator TypPrimUsize left TypPrimUsize right location)

overflow : Either String Integer
overflow = Left (show (ArithmeticOverflow (LeafPrimitiveType TypPrimUsize) location))

mathClasses : String -> Maybe (List TypPrimName)
mathClasses name =
  case preludeSignature name of
    Just (MathSignature classes _) => Just (map numericClassPrimitive classes)
    _ => Nothing

layoutResult : Either ArrayLayoutError Nat -> Either String Nat
layoutResult (Left (LayoutCountTooLarge _)) = Left "count"
layoutResult (Left (LayoutSizeTooLarge _)) = Left "size"
layoutResult (Right bytes) = Right bytes

export
runNumericTests : IO ()
runNumericTests = runTests $ Test.do

  test "usize has the fixed 64-bit target range" $
    (integerBitWidth TypPrimUsize, integerBounds TypPrimUsize) `shouldBe`
      (Just 64, Just (0, 18446744073709551615))

  test "the usize maximum is the largest value of its bit width" $
    Just (the Integer (cast usizeMaximum)) `shouldBe` map snd (integerBounds TypPrimUsize)

  test "usize and u64 remain distinct types despite equal widths" $
    (LeafPrimitiveType TypPrimUsize == LeafPrimitiveType TypPrimU64) `shouldBe` False

  test "unconstrained integer literals keep the i32 default" $
    reported (inferIntegerLiteral Nothing "42" location) `shouldBe` Right (TypPrimI32, 42)

  test "an expected usize type accepts literals beyond i32 and u32" $
    reported (inferIntegerLiteral (Just TypPrimUsize) "4294967296" location) `shouldBe`
      Right (TypPrimUsize, 4294967296)

  test "a usize suffix accepts its maximum independently of context" $
    reported (inferIntegerLiteral Nothing "18446744073709551615usize" location) `shouldBe`
      Right (TypPrimUsize, 18446744073709551615)

  test "the same large unsuffixed literal overflows the default i32" $
    reported (inferIntegerLiteral Nothing "4294967296" location) `shouldBe`
      Left (show (IntegerLiteralOutOfRange 4294967296 (LeafPrimitiveType TypPrimI32) location))

  test "usize literal overflow identifies usize rather than object size" $
    reported (inferIntegerLiteral Nothing "18446744073709551616usize" location) `shouldBe`
      Left (show (IntegerLiteralOutOfRange 18446744073709551616 (LeafPrimitiveType TypPrimUsize) location))

  test "a u64 suffix cannot be implicitly changed by usize context" $
    reported (inferIntegerLiteral (Just TypPrimUsize) "3u64" location) `shouldBe`
      Left (show (TypeMismatch (LeafPrimitiveType TypPrimUsize) (LeafPrimitiveType TypPrimU64) location))

  test "a noninteger context does not become the integer literal type" $
    reported (inferIntegerLiteral (Just TypPrimBool) "1" location) `shouldBe`
      Left (show (TypeMismatch (LeafPrimitiveType TypPrimBool) (LeafPrimitiveType TypPrimI32) location))

  test "an unsuffixed literal takes the bit type from its context" $
    (reported (inferIntegerLiteral (Just TypPrimBit) "0" location),
     reported (inferIntegerLiteral (Just TypPrimBit) "1" location)) `shouldBe`
      (Right (TypPrimBit, 0), Right (TypPrimBit, 1))

  test "a bit literal other than 0 and 1 is out of range" $
    reported (inferIntegerLiteral (Just TypPrimBit) "2" location) `shouldBe`
      Left (show (IntegerLiteralOutOfRange 2 (LeafPrimitiveType TypPrimBit) location))

  test "an integer suffix does not become a bit" $
    reported (inferIntegerLiteral (Just TypPrimBit) "1u8" location) `shouldBe`
      Left (show (TypeMismatch (LeafPrimitiveType TypPrimBit) (LeafPrimitiveType TypPrimU8) location))

  test "a negated literal is one signed number, so -128i8 is in range" $
    reported (inferNegatedIntegerLiteral Nothing "128i8" location) `shouldBe` Right (TypPrimI8, -128)

  test "a negated literal in a signed context takes that type" $
    reported (inferNegatedIntegerLiteral (Just TypPrimI8) "128" location) `shouldBe` Right (TypPrimI8, -128)

  test "128i8 without negation is out of range" $
    reported (inferIntegerLiteral Nothing "128i8" location) `shouldBe`
      Left (show (IntegerLiteralOutOfRange 128 (LeafPrimitiveType TypPrimI8) location))

  test "a negated literal below the signed minimum is out of range" $
    reported (inferNegatedIntegerLiteral Nothing "129i8" location) `shouldBe`
      Left (show (IntegerLiteralOutOfRange (-129) (LeafPrimitiveType TypPrimI8) location))

  test "an unconstrained negated literal is an i32" $
    reported (inferNegatedIntegerLiteral Nothing "7" location) `shouldBe` Right (TypPrimI32, -7)

  test "negating an unsigned or bit literal is invalid even for zero" $
    (reported (inferNegatedIntegerLiteral (Just TypPrimUsize) "0" location),
     reported (inferNegatedIntegerLiteral Nothing "1u8" location),
     reported (inferNegatedIntegerLiteral (Just TypPrimBit) "1" location)) `shouldBe`
      (Left (show (InvalidUnaryOperand "-" (LeafPrimitiveType TypPrimUsize) location)),
       Left (show (InvalidUnaryOperand "-" (LeafPrimitiveType TypPrimU8) location)),
       Left (show (InvalidUnaryOperand "-" (LeafPrimitiveType TypPrimBit) location)))

  test "abs exists only for signed integers and floats" $
    mathClasses "abs" `shouldBe`
      Just [TypPrimI8, TypPrimI16, TypPrimI32, TypPrimI64, TypPrimI128, TypPrimF32, TypPrimF64]

  test "min and max include usize" $
    (map (elem TypPrimUsize) (mathClasses "min"), map (elem TypPrimUsize) (mathClasses "max")) `shouldBe`
      (Just True, Just True)

  test "the other math functions are overloaded over f32 and f64 only" $
    all (\name => mathClasses name == Just [TypPrimF32, TypPrimF64])
      ["sin", "cos", "tan", "asin", "acos", "atan", "exp", "ln", "log2", "log10", "sqrt", "floor", "ceil", "round"]
      `shouldBe` True

  test "turns accepts f32 and f64 and produces the angle of the same width" $
    (case preludeSignature "turns" of
       Just (TurnsSignature classes) => Just (map (\class => (numericClassPrimitive class, turnsAngleType class)) classes)
       _ => Nothing)
      `shouldBe` Just [(TypPrimF32, Just TypPrimAngle32), (TypPrimF64, Just TypPrimAngle64)]

  test "every prelude name has a signature except phase, which is excluded with qstate" $
    filter (isNothing . preludeSignature) preludeFunctionNames `shouldBe` ["phase"]

  test "a u64 constant is not a valid usize count" $
    reported (checkArrayLength (LeafPrimitiveType TypPrimU64) 3 location) `shouldBe`
      Left (show (IncorrectArrayLengthType (LeafPrimitiveType TypPrimU64) location))

  test "usize maximum is a valid count before object layout" $
    reported (checkArrayLength (LeafPrimitiveType TypPrimUsize) 18446744073709551615 location) `shouldBe`
      Right 18446744073709551615

  test "negative evaluated counts are rejected" $
    reported (checkArrayLength (LeafPrimitiveType TypPrimUsize) (-1) location) `shouldBe`
      Left (show (ArrayLengthTooLarge (-1) location))

  test "evaluated count overflow has a count diagnostic" $
    reported (checkArrayLength (LeafPrimitiveType TypPrimUsize) 18446744073709551616 location) `shouldBe`
      Left (show (ArrayLengthTooLarge 18446744073709551616 location))

  test "usize arithmetic keeps all 64 bits" $
    usizeBinary BinaryAdd 4294967296 1 `shouldBe` Right 4294967297

  test "constant usize addition overflow is rejected" $
    usizeBinary BinaryAdd 18446744073709551615 1 `shouldBe` overflow

  test "constant usize subtraction underflow is rejected" $
    usizeBinary BinarySubtract 0 1 `shouldBe` overflow

  test "constant usize multiplication overflow is rejected" $
    usizeBinary BinaryMultiply 9223372036854775808 2 `shouldBe` overflow

  test "usize division and remainder preserve unsigned values" $
    (usizeBinary BinaryDivide 18446744073709551615 2,
     usizeBinary BinaryRemainder 18446744073709551615 2) `shouldBe`
      (Right 9223372036854775807, Right 1)

  test "division by zero is reported" $
    usizeBinary BinaryDivide 5 0 `shouldBe` Left (show (DivisionByZeroInConstant location))

  test "remainder by zero is reported" $
    usizeBinary BinaryRemainder 5 0 `shouldBe` Left (show (DivisionByZeroInConstant location))

  test "signed division truncates toward zero and remainder retains dividend sign" $
    (integerResult (evalIntegerBinaryOperation BinaryDivide TypPrimI32 (-7) TypPrimI32 3 location),
     integerResult (evalIntegerBinaryOperation BinaryRemainder TypPrimI32 (-7) TypPrimI32 3 location)) `shouldBe`
      (Right (-2), Right (-1))

  test "signed minimum divided or remaindered by minus one overflows" $
    (integerResult (evalIntegerBinaryOperation BinaryDivide TypPrimI8 (-128) TypPrimI8 (-1) location),
     integerResult (evalIntegerBinaryOperation BinaryRemainder TypPrimI8 (-128) TypPrimI8 (-1) location)) `shouldBe`
      (Left (show (ArithmeticOverflow (LeafPrimitiveType TypPrimI8) location)),
       Left (show (ArithmeticOverflow (LeafPrimitiveType TypPrimI8) location)))

  test "usize unary negation is invalid even for zero" $
    integerResult (evalIntegerUnary UnaryNegate TypPrimUsize 0 location) `shouldBe`
      Left (show (InvalidUnaryOperand "-" (LeafPrimitiveType TypPrimUsize) location))

  test "usize complement is restricted to 64 bits" $
    integerResult (evalIntegerUnary UnaryLogicalNot TypPrimUsize 0 location) `shouldBe`
      Right 18446744073709551615

  test "logical not flips a bit" $
    (integerResult (evalIntegerUnary UnaryLogicalNot TypPrimBit 0 location),
     integerResult (evalIntegerUnary UnaryLogicalNot TypPrimBit 1 location)) `shouldBe`
      (Right 1, Right 0)

  test "logical not rejects a bit value outside 0 and 1" $
    integerResult (evalIntegerUnary UnaryLogicalNot TypPrimBit 2 location) `shouldBe`
      Left (show (InvalidUnaryOperand "!" (LeafPrimitiveType TypPrimBit) location))

  test "negating a bit is invalid" $
    integerResult (evalIntegerUnary UnaryNegate TypPrimBit 1 location) `shouldBe`
      Left (show (InvalidUnaryOperand "-" (LeafPrimitiveType TypPrimBit) location))

  test "usize bitwise operators retain the high bit" $
    (usizeBinary BinaryBitAnd 18446744073709551615 9223372036854775808,
     usizeBinary BinaryBitOr 9223372036854775808 1,
     usizeBinary BinaryBitXor 18446744073709551615 9223372036854775808) `shouldBe`
      (Right 9223372036854775808, Right 9223372036854775809, Right 9223372036854775807)

  test "usize right shift is logical and permits a differently typed shift count" $
    integerResult (evalIntegerBinaryOperation BinaryShiftRight TypPrimUsize 18446744073709551615 TypPrimI32 1 location) `shouldBe`
      Right 9223372036854775807

  test "left shifts discard high bits instead of overflowing on the result" $
    usizeBinary BinaryShiftLeft 9223372036854775808 1 `shouldBe` Right 0

  test "a shift by the target width overflows" $
    usizeBinary BinaryShiftLeft 1 64 `shouldBe` overflow

  test "negative shift counts are rejected" $
    integerResult (evalIntegerBinaryOperation BinaryShiftRight TypPrimUsize 1 TypPrimI32 (-1) location) `shouldBe` overflow

  test "ordinary usize arithmetic does not coerce u64 operands" $
    integerResult (evalIntegerBinaryOperation BinaryAdd TypPrimUsize 1 TypPrimU64 2 location) `shouldBe`
      Left (show (InvalidBinaryOperands "+" (LeafPrimitiveType TypPrimUsize) (LeafPrimitiveType TypPrimU64) location))

  test "usize ordering compares the full unsigned range" $
    booleanResult (evalIntegerBinaryOperation BinaryGreater TypPrimUsize 18446744073709551615 TypPrimUsize 9223372036854775807 location) `shouldBe`
      Right True

  test "narrowing usize casts truncate high bits" $
    reported (castInteger TypPrimUsize TypPrimU8 257 location) `shouldBe` Right 1

  test "widening unsigned casts zero extend" $
    reported (castInteger TypPrimU8 TypPrimUsize 255 location) `shouldBe` Right 255

  test "negative signed casts to usize sign extend before reinterpretation" $
    reported (castInteger TypPrimI8 TypPrimUsize (-1) location) `shouldBe` Right 18446744073709551615

  test "same-width signed casts reinterpret the high bit" $
    reported (castInteger TypPrimUsize TypPrimI64 18446744073709551615 location) `shouldBe` Right (-1)

  test "u128 to usize casts truncate to the target width" $
    reported (castInteger TypPrimU128 TypPrimUsize 18446744073709551617 location) `shouldBe` Right 1

  test "float casts truncate toward zero" $
    reported (castFloatToInteger TypPrimF64 TypPrimUsize 3.9 location) `shouldBe` Right 3

  test "negative floats saturate at usize minimum" $
    reported (castFloatToInteger TypPrimF64 TypPrimUsize (-3.9) location) `shouldBe` Right 0

  test "out-of-range floats saturate at usize maximum" $
    reported (castFloatToInteger TypPrimF64 TypPrimUsize 18446744073709551616.0 location) `shouldBe`
      Right 18446744073709551615

  test "the largest f64 below usize maximum is converted without saturation" $
    reported (castFloatToInteger TypPrimF64 TypPrimUsize 18446744073709549568.0 location) `shouldBe`
      Right 18446744073709549568

  test "NaN casts to zero" $
    reported (castFloatToInteger TypPrimF64 TypPrimUsize (0.0 / 0.0) location) `shouldBe` Right 0

  test "floating infinities saturate without host integer conversion" $
    (reported (castFloatToInteger TypPrimF64 TypPrimUsize (1.0 / 0.0) location),
     reported (castFloatToInteger TypPrimF64 TypPrimUsize (-1.0 / 0.0) location)) `shouldBe`
      (Right 18446744073709551615, Right 0)

  test "signed float casts truncate negative values toward zero" $
    reported (castFloatToInteger TypPrimF64 TypPrimI32 (-3.9) location) `shouldBe` Right (-3)

  test "nonzero array layout is bounded in bytes by signed pointer maximum" $
    layoutResult (arrayLayoutSize 1 9223372036854775807) `shouldBe` Right 9223372036854775807

  test "a representable count may still exceed the object size bound" $
    layoutResult (arrayLayoutSize 1 9223372036854775808) `shouldBe` Left "size"

  test "element byte size contributes to array layout overflow" $
    layoutResult (arrayLayoutSize 8 1152921504606846976) `shouldBe` Left "size"

  test "zero-sized element arrays may have usize maximum elements" $
    layoutResult (arrayLayoutSize 0 18446744073709551615) `shouldBe` Right 0

  test "zero-sized arrays still require a representable count" $
    layoutResult (arrayLayoutSize 0 18446744073709551616) `shouldBe` Left "count"
