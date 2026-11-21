module ScopeAndNameResolution.PreludeTest

import Compiler.Frontend.Prelude
import Compiler.Frontend.ScopeAndNameResolver.Data
import Compiler.Frontend.ScopeAndNameResolver.Validate
import Compiler.Frontend.ASTData
import Compiler.Frontend.Source
import ScopeAndNameResolution.Helper
import ScopeAndNameResolution.PreludeTestHelper

import Data.List
import Data.Maybe
import Data.SortedMap
import TestFramework

%default total

export
runPreludeFunctionsResolutionTests : IO Bool
runPreludeFunctionsResolutionTests = runTests $ Test.do
  test "prelude ownership, bindings and declaration order are complete" $
    (resolvedSource "fn f() { sin(0.0); }" >>= preludeLayout) `shouldBe` Just True

  test "every specified prelude name resolves as an ordinary value" $
    useOrigins "fn f() { abs; acos; asin; atan; ceil; cos; exp; floor; ln; log2; log10; max; min; Param; phase; round; sin; sqrt; tan; turns; I; X; Y; Z; H; S; SDG; T; TDG; SX; SXDG; RX; RY; RZ; U1; U2; U3; CNOT; CX; CY; CZ; CS; CSDG; CT; CTDG; CSX; CSXDG; CRX; CRY; CRZ; CU1; CU2; CU3; SWAP; RXX; RYY; RZZ; CCX; CSWAP; GPI; GPI2; MS; ZZ; }"
      `shouldBe` Just (map (\functionName => (functionName, "prelude")) preludeFunctionNames)

  test "source functions shadow the prelude even before their declaration" $
    useOrigins "fn f() { sin(0.0); } fn sin(x: f64) { x; }"
      `shouldBe` Just [("sin", "function"), ("x", "parameter")]

  test "parameter bindings shadow prelude functions" $
    useOrigins "fn f(sin: i32) { sin; }"
      `shouldBe` Just [("sin", "parameter")]

  test "local declarations can shadow prelude quantum gates" $
    useOrigins "fn f() { H; let H = 1; H; }"
      `shouldBe` Just [("H", "prelude"), ("H", "local")]

  test "a local initializer sees the prelude before the new binding" $
    useOrigins "fn f() { let sin = sin; sin; }"
      `shouldBe` Just [("sin", "prelude"), ("sin", "local")]

  test "block-local shadowing does not replace the prelude outside the block" $
    useOrigins "fn f() { sin; { let sin = 1; sin; } sin; }"
      `shouldBe` Just [("sin", "prelude"), ("sin", "local"), ("sin", "prelude")]

  test "prelude lookup still reports unknown names" $
    missingName "fn f() { unknown_function(); }" `shouldBe` Just "unknown_function"

  test "prelude registration does not suppress duplicate source declarations" $
    (case resolveSource "fn sin() {} fn sin() {}" of
       Left (ResolutionFailure (DuplicateDeclaration "sin" [_] current previous)) =>
         spanKey current == ("resolution-test.lf", 1, 16, 1, 19) &&
         spanKey previous == ("resolution-test.lf", 1, 4, 1, 7)
       _ => False) `shouldBe` True

  test "prelude registration creates no source occurrences or locals" $
    (do resolvedModule <- resolvedSource ""
        rootScope <- lookup resolvedModule.rootScopeId resolvedModule.tables.scopes
        pure (length (SortedMap.toList resolvedModule.tables.references),
              length (SortedMap.toList resolvedModule.tables.nodeScopes),
              length (SortedMap.toList resolvedModule.tables.localVarsMeta),
              length (SortedMap.toList rootScope.valueBindings),
              length (SortedMap.toList rootScope.typeBindings)))
      `shouldBe` Just (0, 1, 0, 0, 0)

  test "repeated prelude uses retain their symbol identity and use-site scopes" $
    (do resolvedModule <- resolvedSource "fn f() { sin; { sin; } }"
        [outerSinReference, innerSinReference] <- pure (valueReferences resolvedModule)
          | _ => Nothing
        pure (outerSinReference.target == innerSinReference.target &&
              outerSinReference.enclosingScope /= innerSinReference.enclosingScope &&
              lookup outerSinReference.occurrence.nodeId resolvedModule.tables.nodeScopes == Just outerSinReference.enclosingScope &&
              lookup innerSinReference.occurrence.nodeId resolvedModule.tables.nodeScopes == Just innerSinReference.enclosingScope))
      `shouldBe` Just True

  test "resolved prelude and shadowing tables pass invariant validation" $
    traverse (\sourceText => map (map show . validateResolvedModule) (resolvedSource sourceText))
      [ ""
      , "fn f() { sin(0.0); cos(0.0); }"
      , "fn f() { sin(0.0); } fn sin(x: f64) { x; }"
      , "fn f() { let sin = sin; sin; }"
      ] `shouldBe` Just [[], [], [], []]

  test "a later source constant shadows a Prelude function without changing its registration" $
    checkSource "fn f() { sin; } const sin: i32 = 1;" constantShadowsPrelude `shouldBe` Right True
