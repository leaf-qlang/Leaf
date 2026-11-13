module Compiler.Frontend.TypeChecker.PreludeSignatures

import Data.List
import Data.List1

import Compiler.Frontend.TypeChecker.Data
import Compiler.Frontend.TypeChecker.Helper
import Compiler.Frontend.TypeChecker.Type
import Compiler.Frontend.Syntax.Common
import Compiler.Frontend.Token

%default total

-------------------------------------------------------------------------------------
-- Numeric overload classes
-------------------------------------------------------------------------------------
public export
data NumericClass
  = NumericI8   | NumericI16  | NumericI32  | NumericI64  | NumericI128
  | NumericU8   | NumericU16  | NumericU32  | NumericU64  | NumericU128 | NumericUsize
  | NumericF32  | NumericF64

export
numericClassPrimitive : NumericClass -> TypPrimName
numericClassPrimitive numericClass =
  case numericClass of
    NumericI8    => TypPrimI8
    NumericI16   => TypPrimI16
    NumericI32   => TypPrimI32
    NumericI64   => TypPrimI64
    NumericI128  => TypPrimI128
    NumericU8    => TypPrimU8
    NumericU16   => TypPrimU16
    NumericU32   => TypPrimU32
    NumericU64   => TypPrimU64
    NumericU128  => TypPrimU128
    NumericUsize => TypPrimUsize
    NumericF32   => TypPrimF32
    NumericF64   => TypPrimF64

export
signedNumericClasses : List NumericClass
signedNumericClasses =
  [ NumericI8, NumericI16, NumericI32, NumericI64, NumericI128
  , NumericF32, NumericF64
  ]

export
floatNumericClasses : List NumericClass
floatNumericClasses = [NumericF32, NumericF64]

export
turnsAngleType : NumericClass -> Maybe TypPrimName
turnsAngleType NumericF32 = Just TypPrimAngle32
turnsAngleType NumericF64 = Just TypPrimAngle64
turnsAngleType _          = Nothing

export
everyNumericClass : List NumericClass
everyNumericClass =
  [ NumericI8, NumericI16, NumericI32, NumericI64, NumericI128
  , NumericU8, NumericU16, NumericU32, NumericU64, NumericU128, NumericUsize
  , NumericF32, NumericF64
  ]

--------------------------------------------------------------------------------
-- The prelude signature table
--------------------------------------------------------------------------------

public export
data PreludeSignature
  = GateSignature Nat Nat                        -- angle arguments, then qbit arguments
  | MathSignature (List NumericClass) LeafType   -- abs: signed integers/floats; min/max: all numeric; the rest: f32 and f64
  | TurnsSignature (List NumericClass)           -- turns(0.25): f32 -> angle32 or f64 -> angle64, by argument width
  | ParamSignature                               -- Param("theta") : param, a direct call with one string literal

export
preludeSignature : String -> Maybe PreludeSignature
preludeSignature name =
  case name of
    -- 0 angle arguments, 1 qbit argument
    "I"    => Just (GateSignature 0 1)
    "X"    => Just (GateSignature 0 1)
    "Y"    => Just (GateSignature 0 1)
    "Z"    => Just (GateSignature 0 1)
    "H"    => Just (GateSignature 0 1)
    "S"    => Just (GateSignature 0 1)
    "SDG"  => Just (GateSignature 0 1)
    "T"    => Just (GateSignature 0 1)
    "TDG"  => Just (GateSignature 0 1)
    "SX"   => Just (GateSignature 0 1)
    "SXDG" => Just (GateSignature 0 1)
    -- 1 angle argument, 1 qbit argument
    "RX"   => Just (GateSignature 1 1)
    "RY"   => Just (GateSignature 1 1)
    "RZ"   => Just (GateSignature 1 1)
    "U1"   => Just (GateSignature 1 1)
    "GPI"  => Just (GateSignature 1 1)
    "GPI2" => Just (GateSignature 1 1)
    -- 2 and 3 angle arguments, 1 qbit argument
    "U2"   => Just (GateSignature 2 1)
    "U3"   => Just (GateSignature 3 1)
    -- 0 angle arguments, 2 qbit arguments
    "CNOT"  => Just (GateSignature 0 2)
    "CX"    => Just (GateSignature 0 2)
    "CY"    => Just (GateSignature 0 2)
    "CZ"    => Just (GateSignature 0 2)
    "CS"    => Just (GateSignature 0 2)
    "CSDG"  => Just (GateSignature 0 2)
    "CT"    => Just (GateSignature 0 2)
    "CTDG"  => Just (GateSignature 0 2)
    "CSX"   => Just (GateSignature 0 2)
    "CSXDG" => Just (GateSignature 0 2)
    "SWAP"  => Just (GateSignature 0 2)
    -- 1 angle argument, 2 qbit arguments
    "CRX" => Just (GateSignature 1 2)
    "CRY" => Just (GateSignature 1 2)
    "CRZ" => Just (GateSignature 1 2)
    "CU1" => Just (GateSignature 1 2)
    "RXX" => Just (GateSignature 1 2)
    "RYY" => Just (GateSignature 1 2)
    "RZZ" => Just (GateSignature 1 2)
    "ZZ"  => Just (GateSignature 1 2)
    -- 2 and 3 angle arguments, 2 qbit arguments
    "CU2" => Just (GateSignature 2 2)
    "MS"  => Just (GateSignature 2 2)
    "CU3" => Just (GateSignature 3 2)
    -- 0 angle arguments, 3 qbit arguments
    "CCX"   => Just (GateSignature 0 3)
    "CSWAP" => Just (GateSignature 0 3)
    -- math: abs accepts signed integers and floats; min/max accept every
    -- numeric primitive; every other math function accepts f32 and f64
    "abs" => Just (MathSignature signedNumericClasses (LeafPrimitiveType TypPrimF64))
    "min" => Just (MathSignature everyNumericClass (LeafPrimitiveType TypPrimF64))
    "max" => Just (MathSignature everyNumericClass (LeafPrimitiveType TypPrimF64))
    "acos"  => Just (MathSignature floatNumericClasses (LeafPrimitiveType TypPrimF64))
    "asin"  => Just (MathSignature floatNumericClasses (LeafPrimitiveType TypPrimF64))
    "atan"  => Just (MathSignature floatNumericClasses (LeafPrimitiveType TypPrimF64))
    "ceil"  => Just (MathSignature floatNumericClasses (LeafPrimitiveType TypPrimF64))
    "cos"   => Just (MathSignature floatNumericClasses (LeafPrimitiveType TypPrimF64))
    "exp"   => Just (MathSignature floatNumericClasses (LeafPrimitiveType TypPrimF64))
    "floor" => Just (MathSignature floatNumericClasses (LeafPrimitiveType TypPrimF64))
    "ln"    => Just (MathSignature floatNumericClasses (LeafPrimitiveType TypPrimF64))
    "log2"  => Just (MathSignature floatNumericClasses (LeafPrimitiveType TypPrimF64))
    "log10" => Just (MathSignature floatNumericClasses (LeafPrimitiveType TypPrimF64))
    "round" => Just (MathSignature floatNumericClasses (LeafPrimitiveType TypPrimF64))
    "sin"   => Just (MathSignature floatNumericClasses (LeafPrimitiveType TypPrimF64))
    "sqrt"  => Just (MathSignature floatNumericClasses (LeafPrimitiveType TypPrimF64))
    "tan"   => Just (MathSignature floatNumericClasses (LeafPrimitiveType TypPrimF64))
    "turns" => Just (TurnsSignature floatNumericClasses)
    "Param" => Just ParamSignature
    _ => Nothing

export
gateLeastEffect : String -> FunctionEffect
gateLeastEffect gateName =
  if gateName `elem` ["I", "X", "CX", "CNOT", "CCX", "SWAP", "CSWAP"]
    then EffectUncompsafe
    else EffectUnitary

export
gateCapabilities : List SupportKind
gateCapabilities = [SupportAdjoint, SupportCtrl]

--------------------------------------------------------------------------------
-- The value type a prelude name has when used as a value
--------------------------------------------------------------------------------

mathArity : String -> Nat
mathArity "min" = 2
mathArity "max" = 2
mathArity _     = 1

-- every Leaf gate returns the qbits it was given
gateReturnType : (qbitArgs : Nat) -> (qbitType : LeafType) -> LeafType
gateReturnType Z _ = unreachable {function = "gateReturnType"} {reason = "every prelude gate returns at least one qbit"}
gateReturnType (S Z) qbitType = qbitType
gateReturnType (S (S n)) qbitType = LeafTupleType (qbitType ::: replicate (S n) qbitType)

-- builds the function type of a prelude gate
gateFunctionType : (gateName : String) -> (angleArgs : Nat) -> (qbitArgs : Nat) -> LeafType
gateFunctionType gateName angleArgs qbitArgs =
  let angleType = LeafPrimitiveType TypPrimAngle64
      qbitType  = LeafQualifiedType QuantumMultiplicityLinear (LeafPrimitiveType TypPrimQbit)
      parameterTypes = replicate angleArgs angleType ++ replicate qbitArgs qbitType
  in LeafFunctionType (gateLeastEffect gateName) gateCapabilities parameterTypes
       (gateReturnType qbitArgs qbitType)

public export
preludeValueType : String -> InferredType
preludeValueType "Param" = NoValueType
preludeValueType "phase" = NoValueType
preludeValueType name =
  case preludeSignature name of
    Just (GateSignature angleArgs qbitArgs) =>
      ResolvedType (gateFunctionType name angleArgs qbitArgs)
    Just (MathSignature _ resultType) =>
      ResolvedType (LeafFunctionType EffectClassical [] (replicate (mathArity name) resultType) resultType)
    Just (TurnsSignature _) =>
      ResolvedType (LeafFunctionType EffectClassical [] [LeafPrimitiveType TypPrimF64] (LeafPrimitiveType TypPrimAngle64))
    Just ParamSignature =>
      unreachable {function = "preludeValueType"} {reason = "Param is handled above, as it has no value type"}
    Nothing =>
      unreachable {function = "preludeValueType"} {reason = "\{name} is not a prelude symbol"}
