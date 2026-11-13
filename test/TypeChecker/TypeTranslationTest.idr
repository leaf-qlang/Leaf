module TypeChecker.TypeTranslationTest

import Test.Simple

import Compiler.Frontend.TypeChecker.Data
import Compiler.Frontend.TypeChecker.Helper
import Compiler.Frontend.TypeChecker.Type
import Data.List1
import Desugarer.Helper
import Compiler.Frontend.ASTPhases
import Compiler.Frontend.Syntax.AST
import Compiler.Frontend.Syntax.Common
import Compiler.Frontend.Syntax.Type
import Compiler.Frontend.Token

%default total

-- The semantic type of a program's first parameter, once desugared.
firstParameterType : String -> Maybe InferredType
firstParameterType inputProgram = do
  MkAstNode _ _ (MkSourceFileNode _ items) <- lexParseThenDesugar "test-fixture.rs" inputProgram
  MkAstNode _ _ (ItemFunction declaration) :: _ <- Just items
    | _ => Nothing
  MkAstNode _ _ (NormalParameter _ _ _ parameterType) :: _ <- Just declaration.functionParameters
    | _ => Nothing
  Just (toInferredType parameterType)

firstParameterLeafType : String -> Maybe LeafType
firstParameterLeafType source =
  case firstParameterType source of
    Just (ResolvedType leafType) => Just leafType
    _ => Nothing

-- The array length in the type of a program's first parameter.
firstParameterArrayLength : String -> Maybe Nat
firstParameterArrayLength inputProgram =
  case firstParameterType inputProgram of
    Just (ResolvedType (LeafArrayType _ arrayLength)) => Just arrayLength
    _ => Nothing

-- Whether the referent of a program's first parameter, a reference, holds an
-- multiplicity qualifier at an owned position.
firstParameterReferentIsQualified : String -> Maybe Bool
firstParameterReferentIsQualified inputProgram =
  case firstParameterType inputProgram of
    Just (ResolvedType (LeafReferenceType _ referent)) => Just (qualified referent)
    _ => Nothing
  where
    qualified : LeafType -> Bool
    qualified (LeafQualifiedType _ _) = True
    qualified leafType@(LeafTupleType elementTypes) =
      any (\elementType => qualified (assert_smaller leafType elementType)) elementTypes
    qualified (LeafArrayType elementType _) = qualified elementType
    qualified (LeafSliceType elementType) = qualified elementType
    qualified _ = False

-- The multiplicity of the qbit elements of a program's first parameter array.
firstParameterElementMultiplicity : String -> Maybe QuantumMultiplicityQualifier
firstParameterElementMultiplicity inputProgram =
  case firstParameterType inputProgram of
    Just (ResolvedType (LeafArrayType (LeafQualifiedType multiplicity (LeafPrimitiveType TypPrimQbit)) _)) =>
      Just multiplicity
    _ => Nothing

export
runTypeTranslationTests : IO ()
runTypeTranslationTests = runTests $ Test.do

  test "a decimal array length with digit separators is evaluated" $
    firstParameterArrayLength "fn f(qs: [qbit; 1_0]) {}" `shouldBe` Just 10

  test "a lowercase hexadecimal array length is evaluated" $
    firstParameterArrayLength "fn f(qs: [qbit; 0x1f]) {}" `shouldBe` Just 31

  test "an uppercase hexadecimal prefix is accepted in an array length" $
    firstParameterArrayLength "fn f(qs: [qbit; 0X1F]) {}" `shouldBe` Just 31

  test "an uppercase octal prefix is accepted in an array length" $
    firstParameterArrayLength "fn f(qs: [qbit; 0O17]) {}" `shouldBe` Just 15

  test "an uppercase binary prefix is accepted in an array length" $
    firstParameterArrayLength "fn f(qs: [qbit; 0B101]) {}" `shouldBe` Just 5

  test "a decimal usize suffix is accepted in an array length" $
    firstParameterArrayLength "fn f(qs: [qbit; 31usize]) {}" `shouldBe` Just 31

  test "a usize suffix is accepted in an array length" $
    firstParameterArrayLength "fn f(qs: [qbit; 0x1f_usize]) {}" `shouldBe` Just 31

  test "a parenthesized array length is evaluated" $
    firstParameterArrayLength "fn f(qs: [qbit; ((3usize))]) {}" `shouldBe` Just 3

  test "usize remains distinct from u64 during type translation" $
    map show (firstParameterLeafType "fn f(n: usize) {}") `shouldBe` Just "usize"

  test "the largest usize count is preserved without narrowing to a host Int" $
    firstParameterArrayLength "fn f(xs: [(); 18446744073709551615usize]) {}" `shouldBe` Just 18446744073709551615

  test "an out-of-range unsuffixed count is deferred to typing" $
    firstParameterArrayLength "fn f(xs: [(); 18446744073709551616]) {}" `shouldBe` Nothing

  test "the qbit elements of an array are linear by default" $
    firstParameterElementMultiplicity "fn f(qs: [qbit; 2]) {}" `shouldBe` Just QuantumMultiplicityLinear

  test "the qbit elements of an array keep a written qualifier" $
    firstParameterElementMultiplicity "fn f(qs: [affine qbit; 2]) {}" `shouldBe` Just QuantumMultiplicityAffine

  test "a reference to qbits holds no multiplicity qualifier" $
    firstParameterReferentIsQualified "fn f(r: &(qbit, [qbit; 2])) {}" `shouldBe` Just False

  -- Validation rejects this annotation; translating it anyway shows that a
  -- reference type holds no multiplicity qualifier by construction.
  test "a multiplicity qualifier written behind a reference is not translated" $
    firstParameterReferentIsQualified "fn f(r: &(i32, [affine qbit; 2])) {}" `shouldBe` Just False
