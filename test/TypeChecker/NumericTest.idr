module TypeChecker.NumericTest

import Data.Maybe
import TestFramework

import Compiler.Frontend.Prelude
import Compiler.Frontend.TypeChecker.Data
import Compiler.Frontend.TypeChecker.Numeric
import Compiler.Frontend.TypeChecker.PreludeSignatures
import Compiler.Frontend.TypeChecker.Type
import Compiler.Frontend.Source
import Compiler.Frontend.Syntax.Literal
import Compiler.Frontend.Syntax.Operator
import Compiler.Frontend.Token

%default total

numericTestSpan : SourceSpan
numericTestSpan = MkSourceSpan "numeric-test.rs" (MkSourcePos 1 1) (MkSourcePos 1 2)

showingError : Either TypeError a -> Either String a
showingError (Left typeError) = Left (show typeError)
showingError (Right resultValue) = Right resultValue

integerResult : Either TypeError ConstValue -> Either String Integer
integerResult (Left typeError) = Left (show typeError)
integerResult (Right (ConstInteger resultValue)) = Right resultValue
integerResult (Right _) = Left "Expected integer constant"

booleanResult : Either TypeError ConstValue -> Either String Bool
booleanResult (Left typeError) = Left (show typeError)
booleanResult (Right (ConstBool resultValue)) = Right resultValue
booleanResult (Right _) = Left "Expected boolean constant"

usizeBinary : BinaryOperator -> Integer -> Integer -> Either String Integer
usizeBinary binaryOperator leftValue rightValue = integerResult (evalIntegerBinaryOperation binaryOperator TypPrimUsize leftValue TypPrimUsize rightValue numericTestSpan)

usizeOverflowError : Either String Integer
usizeOverflowError = Left (show (ArithmeticOverflow (LeafPrimitiveType TypPrimUsize) numericTestSpan))

mathClasses : String -> Maybe (List TypPrimName)
mathClasses mathFunctionName =
  case preludeSignature mathFunctionName of
    Just (MathSignature numericClasses _) => Just (map numericClassPrimitive numericClasses)
    _ => Nothing

layoutResult : Either ArrayLayoutError Nat -> Either String Nat
layoutResult (Left (LayoutCountTooLarge _)) = Left "count"
layoutResult (Left (LayoutSizeTooLarge _)) = Left "size"
layoutResult (Right byteSize) = Right byteSize

export
runNumericTests : IO Bool
runNumericTests = runTests $ Test.do

  test "usize has the fixed 64-bit target range" $
    (integerBitWidth TypPrimUsize, integerBounds TypPrimUsize) `shouldBe`
      (Just 64, Just (0, 18446744073709551615))

  test "the usize maximum is the largest value of its bit width" $
    Just (the Integer (cast usizeMaximum)) `shouldBe` map snd (integerBounds TypPrimUsize)

  test "usize and u64 remain distinct types despite equal widths" $
    (LeafPrimitiveType TypPrimUsize == LeafPrimitiveType TypPrimU64) `shouldBe` False

  test "unconstrained integer literals keep the i32 default" $
    showingError (inferIntegerLiteral Nothing "42" numericTestSpan) `shouldBe` Right (TypPrimI32, 42)

  test "an expected usize type accepts literals beyond i32 and u32" $
    showingError (inferIntegerLiteral (Just TypPrimUsize) "4294967296" numericTestSpan) `shouldBe`
      Right (TypPrimUsize, 4294967296)

  test "a usize suffix accepts its maximum independently of context" $
    showingError (inferIntegerLiteral Nothing "18446744073709551615usize" numericTestSpan) `shouldBe`
      Right (TypPrimUsize, 18446744073709551615)

  test "the same large unsuffixed literal overflows the default i32" $
    showingError (inferIntegerLiteral Nothing "4294967296" numericTestSpan) `shouldBe`
      Left (show (IntegerLiteralOutOfRange 4294967296 (LeafPrimitiveType TypPrimI32) numericTestSpan))

  test "usize literal overflow identifies usize rather than object size" $
    showingError (inferIntegerLiteral Nothing "18446744073709551616usize" numericTestSpan) `shouldBe`
      Left (show (IntegerLiteralOutOfRange 18446744073709551616 (LeafPrimitiveType TypPrimUsize) numericTestSpan))

  test "a u64 suffix cannot be implicitly changed by usize context" $
    showingError (inferIntegerLiteral (Just TypPrimUsize) "3u64" numericTestSpan) `shouldBe`
      Left (show (TypeMismatch (LeafPrimitiveType TypPrimUsize) (LeafPrimitiveType TypPrimU64) numericTestSpan))

  test "a noninteger context does not become the integer literal type" $
    showingError (inferIntegerLiteral (Just TypPrimBool) "1" numericTestSpan) `shouldBe`
      Left (show (TypeMismatch (LeafPrimitiveType TypPrimBool) (LeafPrimitiveType TypPrimI32) numericTestSpan))

  test "an unsuffixed literal takes the bit type from its context" $
    (showingError (inferIntegerLiteral (Just TypPrimBit) "0" numericTestSpan),
     showingError (inferIntegerLiteral (Just TypPrimBit) "1" numericTestSpan)) `shouldBe`
      (Right (TypPrimBit, 0), Right (TypPrimBit, 1))

  test "a bit literal other than 0 and 1 is out of range" $
    showingError (inferIntegerLiteral (Just TypPrimBit) "2" numericTestSpan) `shouldBe`
      Left (show (IntegerLiteralOutOfRange 2 (LeafPrimitiveType TypPrimBit) numericTestSpan))

  test "an integer suffix does not become a bit" $
    showingError (inferIntegerLiteral (Just TypPrimBit) "1u8" numericTestSpan) `shouldBe`
      Left (show (TypeMismatch (LeafPrimitiveType TypPrimBit) (LeafPrimitiveType TypPrimU8) numericTestSpan))

  test "a negated literal is one signed number, so -128i8 is in range" $
    showingError (inferNegatedIntegerLiteral Nothing "128i8" numericTestSpan) `shouldBe` Right (TypPrimI8, -128)

  test "a negated literal in a signed context takes that type" $
    showingError (inferNegatedIntegerLiteral (Just TypPrimI8) "128" numericTestSpan) `shouldBe` Right (TypPrimI8, -128)

  test "128i8 without negation is out of range" $
    showingError (inferIntegerLiteral Nothing "128i8" numericTestSpan) `shouldBe`
      Left (show (IntegerLiteralOutOfRange 128 (LeafPrimitiveType TypPrimI8) numericTestSpan))

  test "a negated literal below the signed minimum is out of range" $
    showingError (inferNegatedIntegerLiteral Nothing "129i8" numericTestSpan) `shouldBe`
      Left (show (IntegerLiteralOutOfRange (-129) (LeafPrimitiveType TypPrimI8) numericTestSpan))

  test "an unconstrained negated literal is an i32" $
    showingError (inferNegatedIntegerLiteral Nothing "7" numericTestSpan) `shouldBe` Right (TypPrimI32, -7)

  test "negating an unsigned or bit literal is invalid even for zero" $
    (showingError (inferNegatedIntegerLiteral (Just TypPrimUsize) "0" numericTestSpan),
     showingError (inferNegatedIntegerLiteral Nothing "1u8" numericTestSpan),
     showingError (inferNegatedIntegerLiteral (Just TypPrimBit) "1" numericTestSpan)) `shouldBe`
      (Left (show (InvalidUnaryOperand "-" (LeafPrimitiveType TypPrimUsize) numericTestSpan)),
       Left (show (InvalidUnaryOperand "-" (LeafPrimitiveType TypPrimU8) numericTestSpan)),
       Left (show (InvalidUnaryOperand "-" (LeafPrimitiveType TypPrimBit) numericTestSpan)))

  test "abs exists only for signed integers and floats" $
    mathClasses "abs" `shouldBe`
      Just [TypPrimI8, TypPrimI16, TypPrimI32, TypPrimI64, TypPrimI128, TypPrimF32, TypPrimF64]

  test "min and max include usize" $
    (map (elem TypPrimUsize) (mathClasses "min"), map (elem TypPrimUsize) (mathClasses "max")) `shouldBe`
      (Just True, Just True)

  test "the other math functions are overloaded over f32 and f64 only" $
    all (\mathFunctionName => mathClasses mathFunctionName == Just [TypPrimF32, TypPrimF64])
      ["sin", "cos", "tan", "asin", "acos", "atan", "exp", "ln", "log2", "log10", "sqrt", "floor", "ceil", "round"]
      `shouldBe` True

  test "turns accepts f32 and f64 and produces the angle of the same width" $
    (case preludeSignature "turns" of
       Just (TurnsSignature numericClasses) => Just (map (\numericClass => (numericClassPrimitive numericClass, turnsAngleType numericClass)) numericClasses)
       _ => Nothing)
      `shouldBe` Just [(TypPrimF32, Just TypPrimAngle32), (TypPrimF64, Just TypPrimAngle64)]

  test "every prelude name has a signature except phase, which is excluded with qstate" $
    filter (isNothing . preludeSignature) preludeFunctionNames `shouldBe` ["phase"]

  test "a u64 constant is not a valid usize count" $
    showingError (checkArrayLength (LeafPrimitiveType TypPrimU64) 3 numericTestSpan) `shouldBe`
      Left (show (IncorrectArrayLengthType (LeafPrimitiveType TypPrimU64) numericTestSpan))

  test "usize maximum is a valid count before object layout" $
    showingError (checkArrayLength (LeafPrimitiveType TypPrimUsize) 18446744073709551615 numericTestSpan) `shouldBe`
      Right 18446744073709551615

  test "negative evaluated counts are rejected" $
    showingError (checkArrayLength (LeafPrimitiveType TypPrimUsize) (-1) numericTestSpan) `shouldBe`
      Left (show (ArrayLengthTooLarge (-1) numericTestSpan))

  test "evaluated count overflow has a count diagnostic" $
    showingError (checkArrayLength (LeafPrimitiveType TypPrimUsize) 18446744073709551616 numericTestSpan) `shouldBe`
      Left (show (ArrayLengthTooLarge 18446744073709551616 numericTestSpan))

  test "usize arithmetic keeps all 64 bits" $
    usizeBinary BinaryAdd 4294967296 1 `shouldBe` Right 4294967297

  test "constant usize addition overflow is rejected" $
    usizeBinary BinaryAdd 18446744073709551615 1 `shouldBe` usizeOverflowError

  test "constant usize subtraction underflow is rejected" $
    usizeBinary BinarySubtract 0 1 `shouldBe` usizeOverflowError

  test "constant usize multiplication overflow is rejected" $
    usizeBinary BinaryMultiply 9223372036854775808 2 `shouldBe` usizeOverflowError

  test "usize division and remainder preserve unsigned values" $
    (usizeBinary BinaryDivide 18446744073709551615 2,
     usizeBinary BinaryRemainder 18446744073709551615 2) `shouldBe`
      (Right 9223372036854775807, Right 1)

  test "division by zero is reported" $
    usizeBinary BinaryDivide 5 0 `shouldBe` Left (show (DivisionByZeroInConstant numericTestSpan))

  test "remainder by zero is reported" $
    usizeBinary BinaryRemainder 5 0 `shouldBe` Left (show (DivisionByZeroInConstant numericTestSpan))

  test "signed division truncates toward zero and remainder retains dividend sign" $
    (integerResult (evalIntegerBinaryOperation BinaryDivide TypPrimI32 (-7) TypPrimI32 3 numericTestSpan),
     integerResult (evalIntegerBinaryOperation BinaryRemainder TypPrimI32 (-7) TypPrimI32 3 numericTestSpan)) `shouldBe`
      (Right (-2), Right (-1))

  test "signed minimum divided or remaindered by minus one overflows" $
    (integerResult (evalIntegerBinaryOperation BinaryDivide TypPrimI8 (-128) TypPrimI8 (-1) numericTestSpan),
     integerResult (evalIntegerBinaryOperation BinaryRemainder TypPrimI8 (-128) TypPrimI8 (-1) numericTestSpan)) `shouldBe`
      (Left (show (ArithmeticOverflow (LeafPrimitiveType TypPrimI8) numericTestSpan)),
       Left (show (ArithmeticOverflow (LeafPrimitiveType TypPrimI8) numericTestSpan)))

  test "usize unary negation is invalid even for zero" $
    integerResult (evalIntegerUnary UnaryNegate TypPrimUsize 0 numericTestSpan) `shouldBe`
      Left (show (InvalidUnaryOperand "-" (LeafPrimitiveType TypPrimUsize) numericTestSpan))

  test "usize complement is restricted to 64 bits" $
    integerResult (evalIntegerUnary UnaryLogicalNot TypPrimUsize 0 numericTestSpan) `shouldBe`
      Right 18446744073709551615

  test "logical not flips a bit" $
    (integerResult (evalIntegerUnary UnaryLogicalNot TypPrimBit 0 numericTestSpan),
     integerResult (evalIntegerUnary UnaryLogicalNot TypPrimBit 1 numericTestSpan)) `shouldBe`
      (Right 1, Right 0)

  test "logical not rejects a bit value outside 0 and 1" $
    integerResult (evalIntegerUnary UnaryLogicalNot TypPrimBit 2 numericTestSpan) `shouldBe`
      Left (show (InvalidUnaryOperand "!" (LeafPrimitiveType TypPrimBit) numericTestSpan))

  test "negating a bit is invalid" $
    integerResult (evalIntegerUnary UnaryNegate TypPrimBit 1 numericTestSpan) `shouldBe`
      Left (show (InvalidUnaryOperand "-" (LeafPrimitiveType TypPrimBit) numericTestSpan))

  test "usize bitwise operators retain the high bit" $
    (usizeBinary BinaryBitAnd 18446744073709551615 9223372036854775808,
     usizeBinary BinaryBitOr 9223372036854775808 1,
     usizeBinary BinaryBitXor 18446744073709551615 9223372036854775808) `shouldBe`
      (Right 9223372036854775808, Right 9223372036854775809, Right 9223372036854775807)

  test "usize right shift is logical and permits a differently typed shift count" $
    integerResult (evalIntegerBinaryOperation BinaryShiftRight TypPrimUsize 18446744073709551615 TypPrimI32 1 numericTestSpan) `shouldBe`
      Right 9223372036854775807

  test "left shifts discard high bits instead of overflowing on the result" $
    usizeBinary BinaryShiftLeft 9223372036854775808 1 `shouldBe` Right 0

  test "a shift by the target width overflows" $
    usizeBinary BinaryShiftLeft 1 64 `shouldBe` usizeOverflowError

  test "negative shift counts are rejected" $
    integerResult (evalIntegerBinaryOperation BinaryShiftRight TypPrimUsize 1 TypPrimI32 (-1) numericTestSpan) `shouldBe` usizeOverflowError

  test "ordinary usize arithmetic does not coerce u64 operands" $
    integerResult (evalIntegerBinaryOperation BinaryAdd TypPrimUsize 1 TypPrimU64 2 numericTestSpan) `shouldBe`
      Left (show (InvalidBinaryOperands "+" (LeafPrimitiveType TypPrimUsize) (LeafPrimitiveType TypPrimU64) numericTestSpan))

  test "usize ordering compares the full unsigned range" $
    booleanResult (evalIntegerBinaryOperation BinaryGreater TypPrimUsize 18446744073709551615 TypPrimUsize 9223372036854775807 numericTestSpan) `shouldBe`
      Right True

  test "narrowing usize casts truncate high bits" $
    showingError (castInteger TypPrimUsize TypPrimU8 257 numericTestSpan) `shouldBe` Right 1

  test "widening unsigned casts zero extend" $
    showingError (castInteger TypPrimU8 TypPrimUsize 255 numericTestSpan) `shouldBe` Right 255

  test "negative signed casts to usize sign extend before reinterpretation" $
    showingError (castInteger TypPrimI8 TypPrimUsize (-1) numericTestSpan) `shouldBe` Right 18446744073709551615

  test "same-width signed casts reinterpret the high bit" $
    showingError (castInteger TypPrimUsize TypPrimI64 18446744073709551615 numericTestSpan) `shouldBe` Right (-1)

  test "u128 to usize casts truncate to the target width" $
    showingError (castInteger TypPrimU128 TypPrimUsize 18446744073709551617 numericTestSpan) `shouldBe` Right 1

  test "float casts truncate toward zero" $
    showingError (castFloatToInteger TypPrimF64 TypPrimUsize 3.9 numericTestSpan) `shouldBe` Right 3

  test "negative floats saturate at usize minimum" $
    showingError (castFloatToInteger TypPrimF64 TypPrimUsize (-3.9) numericTestSpan) `shouldBe` Right 0

  test "out-of-range floats saturate at usize maximum" $
    showingError (castFloatToInteger TypPrimF64 TypPrimUsize 18446744073709551616.0 numericTestSpan) `shouldBe`
      Right 18446744073709551615

  test "the largest f64 below usize maximum is converted without saturation" $
    showingError (castFloatToInteger TypPrimF64 TypPrimUsize 18446744073709549568.0 numericTestSpan) `shouldBe`
      Right 18446744073709549568

  test "NaN casts to zero" $
    showingError (castFloatToInteger TypPrimF64 TypPrimUsize (0.0 / 0.0) numericTestSpan) `shouldBe` Right 0

  test "floating infinities saturate without host integer conversion" $
    (showingError (castFloatToInteger TypPrimF64 TypPrimUsize (1.0 / 0.0) numericTestSpan),
     showingError (castFloatToInteger TypPrimF64 TypPrimUsize (-1.0 / 0.0) numericTestSpan)) `shouldBe`
      (Right 18446744073709551615, Right 0)

  test "signed float casts truncate negative values toward zero" $
    showingError (castFloatToInteger TypPrimF64 TypPrimI32 (-3.9) numericTestSpan) `shouldBe` Right (-3)

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
