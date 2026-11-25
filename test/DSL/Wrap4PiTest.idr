module DSL.Wrap4PiTest

import DSL.AngleConstants
import DSL.Wrap4Pi
import TestFramework

%default total

export
runWrap4PiTests : IO Bool
runWrap4PiTests = runTests $ Test.do
  test "angles inside the signed range keep their value" $
    map reduceModuloFourPiIntoSignedTwoPiRange [negate twoPi, -6.0, negate pi, 0.0, pi, 6.0]
      `shouldBe` [negate twoPi, -6.0, negate pi, 0.0, pi, 6.0]

  test "the excluded upper endpoint wraps to the included lower endpoint" $
    reduceModuloFourPiIntoSignedTwoPiRange twoPi `shouldBe` negate twoPi

  let offset = 1.0e-9
  test "just above two pi wraps to just above minus two pi" $
    let result = reduceModuloFourPiIntoSignedTwoPiRange (twoPi + offset)
    in (abs (result - (negate twoPi + offset)) < 1.0e-14) `shouldBe` True

  test "just below minus two pi wraps to just below two pi" $
    let result = reduceModuloFourPiIntoSignedTwoPiRange (negate twoPi - offset)
    in (abs (result - (twoPi - offset)) < 1.0e-14) `shouldBe` True

  test "three times the stored two pi wraps to just below positive two pi" $
    -- Three times the stored twoPi is slightly below the mathematical 6π.
    let result = reduceModuloFourPiIntoSignedTwoPiRange (3 * twoPi)
    in (result < twoPi && twoPi - result < 1.0e-14) `shouldBe` True

  test "minus three times the stored two pi wraps to just above minus two pi" $
    -- The negative input is slightly above the mathematical -6π.
    let result = reduceModuloFourPiIntoSignedTwoPiRange (-3 * twoPi)
    in (negate twoPi < result && result - negate twoPi < 1.0e-14) `shouldBe` True

  test "adding a few periods of four pi does not change the reduced angle" $
    -- Small period counts keep rounding in the test inputs below the tolerance.
    let reductionIsPeriodic : Double -> Double -> Bool
        reductionIsPeriodic angle periodCount =
          abs (reduceModuloFourPiIntoSignedTwoPiRange (angle + periodCount * fourPi)
                 - reduceModuloFourPiIntoSignedTwoPiRange angle) < 1.0e-14
    in all (\angle => all (reductionIsPeriodic angle) [-3.0, -1.0, 1.0, 2.0, 3.0])
           [negate pi, -1.0, 0.5, pi, 6.0]
         `shouldBe` True

  test "NaN and infinite angles reduce to NaN" $
    let isNaN : Double -> Bool
        isNaN value = value /= value
    in map (isNaN . reduceModuloFourPiIntoSignedTwoPiRange) [0.0 / 0.0, 1.0 / 0.0, -1.0 / 0.0]
         `shouldBe` [True, True, True]

  -- To reproduce the reference values below, start with the exact value of each
  -- Double input and use 385 decimal digits of precision for π and the arithmetic.
  -- Subtract the nearest whole multiple of 4π from the input.
  test "angles up to the three-part split limit of 2^35 retain their signed remainder" $
    let billionResult = reduceModuloFourPiIntoSignedTwoPiRange 1.0e9
        negativeBillionResult = reduceModuloFourPiIntoSignedTwoPiRange (-1.0e9)
        justBelowSplitLimit = reduceModuloFourPiIntoSignedTwoPiRange 34359738367.999996
    in (abs (billionResult + 5.705789883678201) < 1.0e-14 &&
        abs (negativeBillionResult - 5.705789883678201) < 1.0e-14 &&
        abs (justBelowSplitLimit - 3.84186692069867) < 1.0e-14) `shouldBe` True

  test "angles from the three-part split limit of 2^35 upwards retain their signed remainder" $
    let atSplitLimit = reduceModuloFourPiIntoSignedTwoPiRange 34359738368.0
        tenTrillionResult = reduceModuloFourPiIntoSignedTwoPiRange 1.0e13
    in (abs (atSplitLimit - 3.841870735395936) < 1.0e-14 &&
        abs (tenTrillionResult - 5.990123022991308) < 1.0e-14) `shouldBe` True

  test "large finite angles retain their signed remainder" $
    let positiveResult = reduceModuloFourPiIntoSignedTwoPiRange 1.0e22
        negativeResult = reduceModuloFourPiIntoSignedTwoPiRange (-1.0e22)
        nearDoubleLimit = reduceModuloFourPiIntoSignedTwoPiRange 1.0e308
    in (abs (positiveResult - 5.2630079146204995) < 1.0e-14 &&
        abs (negativeResult + 5.2630079146204995) < 1.0e-14 &&
        abs (nearDoubleLimit + 3.6121649926171213) < 1.0e-14) `shouldBe` True
