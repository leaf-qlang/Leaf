module ScopeAndNameResolution.ResolveTest

import Compiler.Frontend.ScopeAndNameResolver.Data
import Compiler.Frontend.ASTData
import Compiler.Frontend.ASTPhases
import Compiler.Frontend.Source
import Compiler.Frontend.Syntax.AST
import Compiler.Frontend.Syntax.Common
import Compiler.Frontend.Syntax.Name
import Compiler.Frontend.Syntax.Operator
import Compiler.Frontend.Syntax.Pattern
import Compiler.Frontend.Syntax.Type
import ScopeAndNameResolution.Helper
import ScopeAndNameResolution.ResolveTestHelper

import Data.List
import Data.List1
import Data.Maybe
import Data.SnocList
import Data.SortedMap
import TestFramework

%default total

export
runSymbolAndScopeResolutionTests : IO Bool
runSymbolAndScopeResolutionTests = runTests $ Test.do
  -- Rendered from real resolution, so the spans are the ones the resolver recorded.
  -- InaccessibleSymbol is not covered: visibility is not checked yet.
  test "resolution diagnostics report the recorded source positions" $
    map (\sourceText => either show (const "resolved") (resolveSource sourceText))
      [ "fn f() {}\nfn f() {}"
      , "const N: i32 = 1;\nfn f() { let mut N = 2; }"
      , "fn f(n: i32) {\n  [0; n];\n}"
      , "fn f(config: my_module::Config) {}"
      ] `shouldBe`
      [ "Resolution: A duplicate declaration for name: 'f' declared in 'resolution-test.lf:2:4' was found; the previous declaration is in 'resolution-test.lf:1:4'."
      , "Resolution: The mutable binding for name: 'N' in 'resolution-test.lf:2:18' cannot shadow the constant declared in 'resolution-test.lf:1:7'."
      , "Resolution: The local: 'n' used in 'resolution-test.lf:2:7' is not a constant and cannot be used in an array length, in a repeat count from an array declaration or in the qubits register size argument for qalloc; it is declared in 'resolution-test.lf:1:6'."
      , "Resolution: Could not find a type declaration for the type or type path: 'my_module::Config' in 'resolution-test.lf:1:14'. Leaf does not support named types yet!."
      ]

  test "declarations, reads and writes agree between AST and reference tables" $
    checkSource "fn f() { let mut x = 1; let y = x; x = y; x; }" (\resolvedModule => do
      (_, functionDeclaration) <- functionNamed "f" resolvedModule
      xBinding <- letAt 0 functionDeclaration.functionBody
      yBinding <- letAt 1 functionDeclaration.functionBody
      xName <- binder xBinding.letPattern
      yName <- binder yBinding.letPattern
      xRead <- initializer yBinding
      statement <- elementAt 2 functionDeclaration.functionBody.nodeValue.blockStatements
      StatementAssignment assignment <- pure statement.nodeValue | _ => Nothing
      AssignTargetName target <- pure assignment.assignmentTarget.nodeValue | _ => Nothing
      finalRead <- exprAt 3 functionDeclaration.functionBody
      readsX <- useMatches resolvedModule xName xRead
      readsY <- useMatches resolvedModule yName assignment.assignmentValue
      finalX <- useMatches resolvedModule xName finalRead
      scope <- scopeFor resolvedModule functionDeclaration.functionBody
      xRefs <- lookup (symbolId xName) resolvedModule.tables.references
      yRefs <- lookup (symbolId yName) resolvedModule.tables.references
      pure (symbolId xName /= symbolId yName && symbolId target == symbolId xName &&
            readsX && readsY && finalX &&
            referenceMatches resolvedModule DeclarationReference xBinding.letPattern.astInfo.nodeId xName &&
            referenceMatches resolvedModule DeclarationReference yBinding.letPattern.astInfo.nodeId yName &&
            referenceMatches resolvedModule AssignmentTarget assignment.assignmentTarget.astInfo.nodeId target &&
            length (xRefs <>> []) == 4 && length (yRefs <>> []) == 2 &&
            bindingMatches scope xName && bindingMatches scope yName &&
            all (\statement => lookup statement.astInfo.nodeId resolvedModule.tables.nodeScopes == Just scope.id)
              functionDeclaration.functionBody.nodeValue.blockStatements &&
            (scope.declaredSymbolsInOrder <>> []) == [symbolId xName, symbolId yName] &&
            symbolMatches resolvedModule xName scope.id "local" xName.astInfo &&
            symbolMatches resolvedModule yName scope.id "local" yName.astInfo &&
            localMatches resolvedModule xName True && localMatches resolvedModule yName False)) `shouldBe` Right True

  test "a declaration without an initializer has one mutable local and exact read/write references" $
    checkSource "fn f() { let mut x: i32; x = 1; x; }" (\resolvedModule => do
      (fnInfo, functionDeclaration) <- functionNamed "f" resolvedModule
      binding <- letAt 0 functionDeclaration.functionBody
      xName <- binder binding.letPattern
      annotation <- binding.letTypeAnnotation
      assignment <- assignmentAt 1 functionDeclaration.functionBody
      AssignTargetName target <- pure assignment.assignmentTarget.nodeValue | _ => Nothing
      final <- exprAt 2 functionDeclaration.functionBody
      ExprName read <- pure final.nodeValue | _ => Nothing
      scope <- scopeFor resolvedModule functionDeclaration.functionBody
      readOK <- usesInScope resolvedModule scope.id [(xName, final)]
      pure (isNothing binding.letInitializer && symbolId target == symbolId xName && readOK &&
            nodeHasScope resolvedModule scope.id annotation &&
            nodeHasScope resolvedModule scope.id assignment.assignmentTarget &&
            nodeHasScope resolvedModule scope.id assignment.assignmentValue &&
            bindingMatches scope xName && localMatches resolvedModule xName True &&
            symbolMatches resolvedModule xName scope.id "local" xName.astInfo &&
            (scope.declaredSymbolsInOrder <>> []) == [symbolId xName] &&
            map fst (SortedMap.toList resolvedModule.tables.localVarsMeta) == [symbolId xName] &&
            referenceInventory resolvedModule
              [(DeclarationReference, fnInfo.nodeId, functionDeclaration.functionName),
               (DeclarationReference, binding.letPattern.astInfo.nodeId, xName),
               (AssignmentTarget, assignment.assignmentTarget.astInfo.nodeId, target),
               (ValueReference, final.astInfo.nodeId, read)])) `shouldBe` Right True

  test "same-scope shadowing resolves initializer uses to the previous declaration" $
    checkSource "fn f() { let x = 1; let x = x + 1; x; }" (\resolvedModule => do
      (_, functionDeclaration) <- functionNamed "f" resolvedModule
      firstBinding <- letAt 0 functionDeclaration.functionBody
      secondBinding <- letAt 1 functionDeclaration.functionBody
      first <- binder firstBinding.letPattern
      second <- binder secondBinding.letPattern
      initializerExpression <- initializer secondBinding
      ExprBinary _ left _ <- pure initializerExpression.nodeValue | _ => Nothing
      usesFirst <- useMatches resolvedModule first left
      final <- exprAt 2 functionDeclaration.functionBody
      usesSecond <- useMatches resolvedModule second final
      scope <- scopeFor resolvedModule functionDeclaration.functionBody
      pure (symbolId first /= symbolId second && usesFirst && usesSecond &&
            bindingMatches scope second &&
            (scope.declaredSymbolsInOrder <>> []) == [symbolId first, symbolId second] &&
            isJust (lookup (symbolId first) resolvedModule.tables.symbols))) `shouldBe` Right True

  test "destructuring initializers use both old parameters before introducing shadowing locals" $
    checkSource "fn f(x: i32, y: i32) { let (x, y) = (y, x); x; y; }" (\resolvedModule => do
      (fnInfo, functionDeclaration) <- functionNamed "f" resolvedModule
      [xParameter, yParameter] <- pure functionDeclaration.functionParameters | _ => Nothing
      [xName, yName] <- parameterNames functionDeclaration | _ => Nothing
      binding <- letAt 0 functionDeclaration.functionBody
      [(xPattern, newX), (yPattern, newY)] <- pure (patternBinders binding.letPattern) | _ => Nothing
      initializerExpression <- initializer binding
      ExprTuple (oldYUse ::: [oldXUse]) <- pure initializerExpression.nodeValue | _ => Nothing
      ExprName oldY <- pure oldYUse.nodeValue | _ => Nothing
      ExprName oldX <- pure oldXUse.nodeValue | _ => Nothing
      finalX <- exprAt 1 functionDeclaration.functionBody
      finalY <- exprAt 2 functionDeclaration.functionBody
      ExprName readX <- pure finalX.nodeValue | _ => Nothing
      ExprName readY <- pure finalY.nodeValue | _ => Nothing
      functionScope <- scopeFor resolvedModule xParameter
      bodyScope <- scopeFor resolvedModule functionDeclaration.functionBody
      usesOK <- usesInScope resolvedModule bodyScope.id [(yName, oldYUse), (xName, oldXUse), (newX, finalX), (newY, finalY)]
      pure (usesOK && length (nub (map symbolId [xName, yName, newX, newY])) == 4 &&
            bodyScope.parent == Just functionScope.id &&
            all (bindingMatches functionScope) [xName, yName] && all (bindingMatches bodyScope) [newX, newY] &&
            all (\resolvedName => localMatches resolvedModule resolvedName False) [xName, yName, newX, newY] &&
            (functionScope.declaredSymbolsInOrder <>> []) == map symbolId [xName, yName] &&
            (bodyScope.declaredSymbolsInOrder <>> []) == map symbolId [newX, newY] &&
            referenceInventory resolvedModule
              [(DeclarationReference, fnInfo.nodeId, functionDeclaration.functionName),
               (DeclarationReference, xParameter.astInfo.nodeId, xName),
               (DeclarationReference, yParameter.astInfo.nodeId, yName),
               (DeclarationReference, xPattern.astInfo.nodeId, newX),
               (DeclarationReference, yPattern.astInfo.nodeId, newY),
               (ValueReference, oldYUse.astInfo.nodeId, oldY),
               (ValueReference, oldXUse.astInfo.nodeId, oldX),
               (ValueReference, finalX.astInfo.nodeId, readX),
               (ValueReference, finalY.astInfo.nodeId, readY)])) `shouldBe` Right True

  -- A function, unlike a constant, is not a pattern, so a local may shadow it.
  test "array-size annotations use the outer function before introducing a local" $
    checkSource "const fn n() -> i32 { 2 } fn f() { let n: [i32; n()] = [0, 0]; n; }" (\resolvedModule => do
      (_, size) <- functionNamed "n" resolvedModule
      (_, functionDeclaration) <- functionNamed "f" resolvedModule
      binding <- letAt 0 functionDeclaration.functionBody
      local <- binder binding.letPattern
      typeAnnotation <- binding.letTypeAnnotation
      TyArray _ count <- pure typeAnnotation.nodeValue | _ => Nothing
      ExprCall callee [] <- pure count.nodeValue | _ => Nothing
      sizeUsesFunction <- useMatches resolvedModule size.functionName callee
      final <- exprAt 1 functionDeclaration.functionBody
      finalUsesLocal <- useMatches resolvedModule local final
      pure (symbolId size.functionName /= symbolId local && sizeUsesFunction && finalUsesLocal)) `shouldBe` Right True

  test "nested block final expressions use inner bindings and restore the outer scope" $
    checkSource "fn f() { let x = 1; let y = { let x = 2; x }; x; }" (\resolvedModule => do
      (_, functionDeclaration) <- functionNamed "f" resolvedModule
      outerBinding <- letAt 0 functionDeclaration.functionBody
      outerName <- binder outerBinding.letPattern
      yName <- letAt 1 functionDeclaration.functionBody
      initializerExpression <- initializer yName
      block <- blockBody initializerExpression
      innerBinding <- letAt 0 block
      innerName <- binder innerBinding.letPattern
      final <- block.nodeValue.finalExpression
      innerUse <- useMatches resolvedModule innerName final
      after <- exprAt 2 functionDeclaration.functionBody
      outerUse <- useMatches resolvedModule outerName after
      outer <- scopeFor resolvedModule functionDeclaration.functionBody
      inner <- scopeFor resolvedModule block
      pure (symbolId innerName /= symbolId outerName && innerUse && outerUse &&
            isBlock inner && inner.parent == Just outer.id &&
            bindingMatches outer outerName && bindingMatches inner innerName)) `shouldBe` Right True

  test "forward calls, recursion and mutual recursion reuse function declaration IDs" $
    checkSource "fn first() { second(); first(); } fn second() { first(); }" (\resolvedModule => do
      (firstInfo, first) <- functionNamed "first" resolvedModule
      (secondInfo, second) <- functionNamed "second" resolvedModule
      forwardCall <- exprAt 0 first.functionBody
      recursiveCall <- exprAt 1 first.functionBody
      mutualCall <- exprAt 0 second.functionBody
      ExprCall forward [] <- pure forwardCall.nodeValue | _ => Nothing
      ExprCall recursive [] <- pure recursiveCall.nodeValue | _ => Nothing
      ExprCall mutualCallee [] <- pure mutualCall.nodeValue | _ => Nothing
      forwardOK <- useMatches resolvedModule second.functionName forward
      recursiveOK <- useMatches resolvedModule first.functionName recursive
      mutualOK <- useMatches resolvedModule first.functionName mutualCallee
      pure (forwardOK && recursiveOK && mutualOK &&
            symbolId first.functionName /= symbolId second.functionName &&
            referenceMatches resolvedModule DeclarationReference firstInfo.nodeId first.functionName &&
            referenceMatches resolvedModule DeclarationReference secondInfo.nodeId second.functionName)) `shouldBe` Right True

  test "parameter metadata and bindings are complete and isolated between functions" $
    checkSource "fn f(mut x: i32, y: i32) { let z = x; y; } fn g(x: i32) { x; }" (\resolvedModule => do
      (_, functionF) <- functionNamed "f" resolvedModule
      (_, functionG) <- functionNamed "g" resolvedModule
      [xParameter, yParameter] <- pure functionF.functionParameters | _ => Nothing
      [gParameter] <- pure functionG.functionParameters | _ => Nothing
      NormalParameter _ _ xName _ <- pure xParameter.nodeValue | _ => Nothing
      NormalParameter _ _ yName _ <- pure yParameter.nodeValue | _ => Nothing
      NormalParameter _ _ gxName _ <- pure gParameter.nodeValue | _ => Nothing
      fScope <- scopeFor resolvedModule xParameter
      gScope <- scopeFor resolvedModule gParameter
      fBody <- scopeFor resolvedModule functionF.functionBody
      zBinding <- letAt 0 functionF.functionBody
      zName <- binder zBinding.letPattern
      initializerExpression <- initializer zBinding
      xUseMatches <- useMatches resolvedModule xName initializerExpression
      yExpr <- exprAt 1 functionF.functionBody
      yUseMatches <- useMatches resolvedModule yName yExpr
      gxExpr <- exprAt 0 functionG.functionBody
      gxUseMatches <- useMatches resolvedModule gxName gxExpr
      pure (xUseMatches && yUseMatches && gxUseMatches && symbolId xName /= symbolId gxName &&
            fScope.id /= gScope.id && fBody.parent == Just fScope.id &&
            fScope.parent == Just resolvedModule.rootScopeId && gScope.parent == Just resolvedModule.rootScopeId &&
            (case fScope.kind of FunctionScope => True; _ => False) &&
            (case gScope.kind of FunctionScope => True; _ => False) &&
            bindingMatches fScope xName && bindingMatches fScope yName && bindingMatches gScope gxName &&
            (fScope.declaredSymbolsInOrder <>> []) == [symbolId xName, symbolId yName] &&
            localMatches resolvedModule xName True && localMatches resolvedModule yName False &&
            localMatches resolvedModule gxName False && localMatches resolvedModule zName False &&
            symbolMatches resolvedModule xName fScope.id "parameter" xName.astInfo &&
            referenceMatches resolvedModule DeclarationReference xParameter.astInfo.nodeId xName &&
            referenceMatches resolvedModule DeclarationReference yParameter.astInfo.nodeId yName &&
            referenceMatches resolvedModule DeclarationReference gParameter.astInfo.nodeId gxName)) `shouldBe` Right True

  test "destructuring registers each binder with its own mutability and ignores wildcards" $
    checkSource "fn f() { let (mut a, (_, b)) = (1, (2, 3)); let [mut c, _, d] = [4, 5, 6]; a; b; c; d; }" (\resolvedModule => do
      (_, functionDeclaration) <- functionNamed "f" resolvedModule
      tuple <- letAt 0 functionDeclaration.functionBody
      array <- letAt 1 functionDeclaration.functionBody
      let binders = patternBinders tuple.letPattern ++ patternBinders array.letPattern
      let names = map snd binders
      uses <- traverse (\statementIndex => exprAt statementIndex functionDeclaration.functionBody) [2, 3, 4, 5]
      matches <- traverse (\(resolvedName, useExpression) => useMatches resolvedModule resolvedName useExpression) (zip names uses)
      scope <- scopeFor resolvedModule functionDeclaration.functionBody
      pure (map (\resolvedName => resolvedName.nodeValue.nameNodeText) names == ["a", "b", "c", "d"] &&
            length (nub (map symbolId names)) == 4 && all id matches &&
            all (\(resolvedName, mutable) => localMatches resolvedModule resolvedName mutable) (zip names [True, False, True, False]) &&
            all (\(pattern, resolvedName) => referenceMatches resolvedModule DeclarationReference pattern.astInfo.nodeId resolvedName) binders &&
            all (bindingMatches scope) names &&
            (scope.declaredSymbolsInOrder <>> []) == map symbolId names &&
            isNothing (lookup "_" scope.valueBindings))) `shouldBe` Right True

  test "for iterator and trailing uses resolve outside the loop binder's scope" $
    checkSource "fn f() { let x = [1]; for x in x { x; } x; }" (\resolvedModule => do
      (_, functionDeclaration) <- functionNamed "f" resolvedModule
      binding <- letAt 0 functionDeclaration.functionBody
      outerName <- binder binding.letPattern
      loopExpression <- exprAt 1 functionDeclaration.functionBody
      ExprFor pattern iterator body <- pure loopExpression.nodeValue | _ => Nothing
      loopName <- binder pattern
      outer <- scopeFor resolvedModule functionDeclaration.functionBody
      loopScope <- scopeFor resolvedModule pattern
      bodyScope <- scopeFor resolvedModule body
      iteratorOK <- useMatches resolvedModule outerName iterator
      bodyUse <- exprAt 0 body
      bodyOK <- useMatches resolvedModule loopName bodyUse
      after <- exprAt 2 functionDeclaration.functionBody
      afterOK <- useMatches resolvedModule outerName after
      pure (iteratorOK && bodyOK && afterOK && symbolId outerName /= symbolId loopName &&
            (case loopScope.kind of ForScope => True; _ => False) &&
            loopScope.parent == Just outer.id && bodyScope.parent == Just loopScope.id && isBlock bodyScope &&
            (case loopScope.origin of SourceScope originInfo => originInfo.nodeId == loopExpression.astInfo.nodeId; _ => False) &&
            (case bodyScope.origin of SourceScope originInfo => originInfo.nodeId == body.astInfo.nodeId; _ => False) &&
            bindingMatches outer outerName && bindingMatches loopScope loopName &&
            lookup loopExpression.astInfo.nodeId resolvedModule.tables.nodeScopes == Just outer.id &&
            referenceMatches resolvedModule DeclarationReference pattern.astInfo.nodeId loopName &&
            localMatches resolvedModule loopName False)) `shouldBe` Right True

  test "nested for loops restore each shadowed binding and keep their iterator scopes separate" $
    checkSource "fn f(i: i32) { for i in [i] { for i in [i] { i; } i; } i; }" (\resolvedModule => do
      (fnInfo, functionDeclaration) <- functionNamed "f" resolvedModule
      [parameter] <- pure functionDeclaration.functionParameters | _ => Nothing
      [original] <- parameterNames functionDeclaration | _ => Nothing
      outerLoop <- exprAt 0 functionDeclaration.functionBody
      ExprFor outerPattern outerIterator outerBody <- pure outerLoop.nodeValue | _ => Nothing
      ExprArray [originalIteratorUse] <- pure outerIterator.nodeValue | _ => Nothing
      outer <- binder outerPattern
      innerLoop <- exprAt 0 outerBody
      ExprFor innerPattern innerIterator innerBody <- pure innerLoop.nodeValue | _ => Nothing
      ExprArray [outerIteratorUse] <- pure innerIterator.nodeValue | _ => Nothing
      inner <- binder innerPattern
      innerUse <- exprAt 0 innerBody
      afterInner <- exprAt 1 outerBody
      afterOuter <- exprAt 1 functionDeclaration.functionBody
      ExprName originalIteratorName <- pure originalIteratorUse.nodeValue | _ => Nothing
      ExprName outerIteratorName <- pure outerIteratorUse.nodeValue | _ => Nothing
      ExprName innerRead <- pure innerUse.nodeValue | _ => Nothing
      ExprName outerRead <- pure afterInner.nodeValue | _ => Nothing
      ExprName originalRead <- pure afterOuter.nodeValue | _ => Nothing
      functionScope <- scopeFor resolvedModule parameter
      bodyScope <- scopeFor resolvedModule functionDeclaration.functionBody
      outerScope <- scopeFor resolvedModule outerPattern
      outerBodyScope <- scopeFor resolvedModule outerBody
      innerScope <- scopeFor resolvedModule innerPattern
      innerBodyScope <- scopeFor resolvedModule innerBody
      originalUsesOK <- usesInScope resolvedModule bodyScope.id [(original, originalIteratorUse), (original, afterOuter)]
      outerUsesOK <- usesInScope resolvedModule outerBodyScope.id [(outer, outerIteratorUse), (outer, afterInner)]
      innerUseOK <- usesInScope resolvedModule innerBodyScope.id [(inner, innerUse)]
      pure (originalUsesOK && outerUsesOK && innerUseOK &&
            length (nub (map symbolId [original, outer, inner])) == 3 &&
            (case (outerScope.kind, innerScope.kind) of (ForScope, ForScope) => True; _ => False) &&
            outerScope.parent == Just bodyScope.id && outerBodyScope.parent == Just outerScope.id &&
            innerScope.parent == Just outerBodyScope.id && innerBodyScope.parent == Just innerScope.id &&
            isBlock outerBodyScope && isBlock innerBodyScope &&
            all (nodeHasScope resolvedModule bodyScope.id) [outerLoop, outerIterator] &&
            all (nodeHasScope resolvedModule outerBodyScope.id) [innerLoop, innerIterator] &&
            bindingMatches functionScope original && bindingMatches outerScope outer && bindingMatches innerScope inner &&
            all (\resolvedName => localMatches resolvedModule resolvedName False) [original, outer, inner] &&
            (functionScope.declaredSymbolsInOrder <>> []) == [symbolId original] &&
            (outerScope.declaredSymbolsInOrder <>> []) == [symbolId outer] &&
            (innerScope.declaredSymbolsInOrder <>> []) == [symbolId inner] &&
            referenceInventory resolvedModule
              [(DeclarationReference, fnInfo.nodeId, functionDeclaration.functionName),
               (DeclarationReference, parameter.astInfo.nodeId, original),
               (DeclarationReference, outerPattern.astInfo.nodeId, outer),
               (DeclarationReference, innerPattern.astInfo.nodeId, inner),
               (ValueReference, originalIteratorUse.astInfo.nodeId, originalIteratorName),
               (ValueReference, outerIteratorUse.astInfo.nodeId, outerIteratorName),
               (ValueReference, innerUse.astInfo.nodeId, innerRead),
               (ValueReference, afterInner.astInfo.nodeId, outerRead),
               (ValueReference, afterOuter.astInfo.nodeId, originalRead)])) `shouldBe` Right True

  test "if and else-if branch scopes are siblings and chained-if nodes retain the enclosing scope" $
    checkSource "fn f(flag: bool) { if flag { let x = 1; x; } else if flag { let x = 2; x; } else { let x = 3; x; } flag; }" (\resolvedModule => do
      (_, functionDeclaration) <- functionNamed "f" resolvedModule
      [MkAstNode _ _ (NormalParameter _ _ flag _)] <- pure functionDeclaration.functionParameters | _ => Nothing
      expression <- exprAt 0 functionDeclaration.functionBody
      ExprIf first <- pure expression.nodeValue | _ => Nothing
      ElseChainedIf chained <- first.ifElseBranch | _ => Nothing
      ElseBlock last <- chained.nodeValue.ifElseBranch | _ => Nothing
      let blocks = [first.ifThenBlock, chained.nodeValue.ifThenBlock, last]
      scopes <- traverse (scopeFor resolvedModule) blocks
      bindings <- traverse (letAt 0) blocks
      names <- traverse (binder . (.letPattern)) bindings
      uses <- traverse (exprAt 1) blocks
      matches <- traverse (\(resolvedName, useExpression) => useMatches resolvedModule resolvedName useExpression) (zip names uses)
      firstCondition <- useMatches resolvedModule flag first.ifCondition
      secondCondition <- useMatches resolvedModule flag chained.nodeValue.ifCondition
      outer <- scopeFor resolvedModule functionDeclaration.functionBody
      after <- exprAt 1 functionDeclaration.functionBody
      afterOK <- useMatches resolvedModule flag after
      pure (firstCondition && secondCondition && afterOK && all id matches &&
            length (nub (map (.id) scopes)) == 3 && length (nub (map symbolId names)) == 3 &&
            all (\scope => isBlock scope && scope.parent == Just outer.id) scopes &&
            all (\(scope, resolvedName) => bindingMatches scope resolvedName) (zip scopes names) &&
            lookup chained.astInfo.nodeId resolvedModule.tables.nodeScopes == Just outer.id &&
            isNothing (lookup "x" outer.valueBindings))) `shouldBe` Right True

  test "plain blocks isolate declarations" $ blockIsolation "" `shouldBe` Right True
  test "loop blocks isolate declarations" $ blockIsolation "loop" `shouldBe` Right True
  test "while blocks isolate declarations" $ blockIsolation "while true" `shouldBe` Right True
  test "controlled blocks isolate declarations" $ blockIsolation "ctrl(&q)" `shouldBe` Right True
  test "adjoint blocks isolate declarations" $ blockIsolation "adjoint" `shouldBe` Right True

  test "controlled and adjoint callables resolve their controls and function names" $
    checkSource "unitary fn g(q: &qbit) {} unitary fn f(q: &qbit) { ctrl(q).apply(g); adjoint(g); }" (\resolvedModule => do
      (_, functionG) <- functionNamed "g" resolvedModule
      (_, functionF) <- functionNamed "f" resolvedModule
      [MkAstNode _ _ (NormalParameter _ _ qName _)] <- pure functionF.functionParameters | _ => Nothing
      controlled <- exprAt 0 functionF.functionBody
      adjointed <- exprAt 1 functionF.functionBody
      ExprCtrl (ControlledCallable (control ::: []) _ callable) <- pure controlled.nodeValue | _ => Nothing
      ExprAdjoint (AdjointOfCallable adjointCallable) <- pure adjointed.nodeValue | _ => Nothing
      controlOK <- useMatches resolvedModule qName control
      callableOK <- useMatches resolvedModule functionG.functionName callable
      adjointOK <- useMatches resolvedModule functionG.functionName adjointCallable
      bodyScope <- scopeFor resolvedModule functionF.functionBody
      pure (controlOK && callableOK && adjointOK &&
            lookup controlled.astInfo.nodeId resolvedModule.tables.nodeScopes == Just bodyScope.id &&
            lookup adjointed.astInfo.nodeId resolvedModule.tables.nodeScopes == Just bodyScope.id)) `shouldBe` Right True

  test "controlled blocks resolve every operand before entering the child scope" $
    checkSource "fn f(q: qbit, r: qbit) { ctrl(&q, &r) { let q = 1; q; r; } q; r; }" (\resolvedModule => do
      (fnInfo, functionDeclaration) <- functionNamed "f" resolvedModule
      [qParameter, rParameter] <- pure functionDeclaration.functionParameters | _ => Nothing
      [qName, rName] <- parameterNames functionDeclaration | _ => Nothing
      controlled <- exprAt 0 functionDeclaration.functionBody
      ExprCtrl (ControlledBlock (firstControl ::: [secondControl]) _ block) <- pure controlled.nodeValue
        | _ => Nothing
      ExprUnary _ firstOperand <- pure firstControl.nodeValue | _ => Nothing
      ExprUnary _ secondOperand <- pure secondControl.nodeValue | _ => Nothing
      innerBinding <- letAt 0 block
      innerQ <- binder innerBinding.letPattern
      innerQUse <- exprAt 1 block
      innerRUse <- exprAt 2 block
      afterQ <- exprAt 1 functionDeclaration.functionBody
      afterR <- exprAt 2 functionDeclaration.functionBody
      outer <- scopeFor resolvedModule functionDeclaration.functionBody
      inner <- scopeFor resolvedModule block
      outerUses <- usesInScope resolvedModule outer.id
        [(qName, firstOperand), (rName, secondOperand), (qName, afterQ), (rName, afterR)]
      innerUses <- usesInScope resolvedModule inner.id [(innerQ, innerQUse), (rName, innerRUse)]
      valueOccurrences <- traverse valueReferenceOccurrence
        [firstOperand, secondOperand, innerQUse, innerRUse, afterQ, afterR]
      pure (outerUses && innerUses && length (nub (map symbolId [qName, rName, innerQ])) == 3 &&
            all (nodeHasScope resolvedModule outer.id) [controlled, firstControl, secondControl] &&
            inner.id /= outer.id && inner.parent == Just outer.id && isBlock inner &&
            bindingMatches inner innerQ && localMatches resolvedModule innerQ False &&
            symbolMatches resolvedModule innerQ inner.id "local" innerQ.astInfo &&
            (inner.declaredSymbolsInOrder <>> []) == [symbolId innerQ] &&
            isNothing (lookup "q" outer.valueBindings) && isNothing (lookup "r" inner.valueBindings) &&
            referenceInventory resolvedModule
              ([(DeclarationReference, fnInfo.nodeId, functionDeclaration.functionName),
                (DeclarationReference, qParameter.astInfo.nodeId, qName),
                (DeclarationReference, rParameter.astInfo.nodeId, rName),
                (DeclarationReference, innerBinding.letPattern.astInfo.nodeId, innerQ)] ++
               valueOccurrences))) `shouldBe` Right True

  test "controlled callables resolve every control and the callable in the enclosing scope" $
    checkSource "unitary fn g(target: &qbit) {} unitary fn f(q: &qbit, r: &qbit) { ctrl(q, r).apply(g); }" (\resolvedModule => do
      (gInfo, functionG) <- functionNamed "g" resolvedModule
      (fInfo, functionF) <- functionNamed "f" resolvedModule
      [targetParameter] <- pure functionG.functionParameters | _ => Nothing
      [target] <- parameterNames functionG | _ => Nothing
      [qParameter, rParameter] <- pure functionF.functionParameters | _ => Nothing
      [qName, rName] <- parameterNames functionF | _ => Nothing
      controlled <- exprAt 0 functionF.functionBody
      ExprCtrl (ControlledCallable (firstControl ::: [secondControl]) _ callable) <- pure controlled.nodeValue
        | _ => Nothing
      body <- scopeFor resolvedModule functionF.functionBody
      reads <- usesInScope resolvedModule body.id [(qName, firstControl), (rName, secondControl), (functionG.functionName, callable)]
      valueOccurrences <- traverse valueReferenceOccurrence [firstControl, secondControl, callable]
      pure (reads && symbolId qName /= symbolId rName && nodeHasScope resolvedModule body.id controlled &&
            (body.declaredSymbolsInOrder <>> []) == [] &&
            referenceInventory resolvedModule
              ([(DeclarationReference, gInfo.nodeId, functionG.functionName),
                (DeclarationReference, targetParameter.astInfo.nodeId, target),
                (DeclarationReference, fInfo.nodeId, functionF.functionName),
                (DeclarationReference, qParameter.astInfo.nodeId, qName),
                (DeclarationReference, rParameter.astInfo.nodeId, rName)] ++
               valueOccurrences))) `shouldBe` Right True

  test "controlled blocks reject an unresolved second control operand" $
    unresolved "fn f(q: qbit) { ctrl(&q, &missing) {} }" "missing" `shouldBe` Right True

  test "controlled callables reject an unresolved second control operand" $
    unresolved "unitary fn g(target: &qbit) {} unitary fn f(q: &qbit) { ctrl(q, missing).apply(g); }" "missing" `shouldBe` Right True

  test "parameter and return annotations see module functions" $
    checkSource "const fn n() -> i32 { 2 } fn f(m: i32, values: [i32; n()]) -> [i32; n()] { values }" (\resolvedModule => do
      (_, size) <- functionNamed "n" resolvedModule
      (_, functionDeclaration) <- functionNamed "f" resolvedModule
      [_, MkAstNode _ _ (NormalParameter _ _ _ arrayType)] <- pure functionDeclaration.functionParameters | _ => Nothing
      resultType <- functionDeclaration.returnType
      TyArray _ parameterSize <- pure arrayType.nodeValue | _ => Nothing
      TyArray _ resultSize <- pure resultType.nodeValue | _ => Nothing
      ExprCall parameterCallee [] <- pure parameterSize.nodeValue | _ => Nothing
      ExprCall resultCallee [] <- pure resultSize.nodeValue | _ => Nothing
      parameterOK <- useMatches resolvedModule size.functionName parameterCallee
      resultOK <- useMatches resolvedModule size.functionName resultCallee
      pure (parameterOK && resultOK)) `shouldBe` Right True

  test "functions and constants have module ownership and no local-variable metadata" $
    checkSource "pub const n: i32 = 1; pub fn f() { n; } fn g() {}" (\resolvedModule => do
      (constInfo, constDeclaration) <- constantNamed "n" resolvedModule
      (fnInfo, functionDeclaration) <- functionNamed "f" resolvedModule
      (_, privateFn) <- functionNamed "g" resolvedModule
      constantSymbol <- lookup (symbolId constDeclaration.constName) resolvedModule.tables.symbols
      functionSymbol <- lookup (symbolId functionDeclaration.functionName) resolvedModule.tables.symbols
      privateSymbol <- lookup (symbolId privateFn.functionName) resolvedModule.tables.symbols
      useExpression <- exprAt 0 functionDeclaration.functionBody
      useOK <- useMatches resolvedModule constDeclaration.constName useExpression
      pure (useOK && symbolMatches resolvedModule constDeclaration.constName resolvedModule.rootScopeId "constant" constInfo &&
            symbolMatches resolvedModule functionDeclaration.functionName resolvedModule.rootScopeId "function" fnInfo &&
            (case constantSymbol.visibility of PublicVisibility => True; _ => False) &&
            (case functionSymbol.visibility of PublicVisibility => True; _ => False) &&
            (case privateSymbol.visibility of ModuleVisibility => True; _ => False) &&
            all (\resolvedName => isNothing (lookup (symbolId resolvedName) resolvedModule.tables.localVarsMeta))
              [constDeclaration.constName, functionDeclaration.functionName, privateFn.functionName] &&
            resolvedModule.tables.currentScopeId == resolvedModule.rootScopeId &&
            resolvedModule.tables.currentModuleSymbolId == resolvedModule.rootSymbolId &&
            (case resolvedModule.tables.currentScopeKind of ModuleScope => True; _ => False))) `shouldBe` Right True

  test "self-initialization without an outer binding is unresolved" $
    unresolved "fn f() { let x = x; }" "x" `shouldBe` Right True
  test "a use before a later local declaration is unresolved" $
    unresolved "fn f() { x; let x = 1; }" "x" `shouldBe` Right True
  test "a block local cannot escape its block" $
    unresolved "fn f() { { let x = 1; } x; }" "x" `shouldBe` Right True
  test "a then-branch local is unavailable in the else branch" $
    unresolved "fn f() { if true { let x = 1; } else { x; } }" "x" `shouldBe` Right True
  test "a for binder cannot escape its loop" $
    unresolved "fn f() { for x in [1] {} x; }" "x" `shouldBe` Right True
  test "a parameter is unavailable in another function" $
    unresolved "fn f(x: i32) {} fn g() { x; }" "x" `shouldBe` Right True
  test "a local from an earlier function is unavailable in a later function" $
    unresolved "fn f() { let x = 1; } fn g() { x; }" "x" `shouldBe` Right True
  test "a local in a later function is unavailable in an earlier function" $
    unresolved "fn f() { x; } fn g() { let x = 1; }" "x" `shouldBe` Right True
  test "controlled block locals cannot escape" $
    unresolved "fn f(q: qbit) { ctrl(&q) { let x = 1; } x; }" "x" `shouldBe` Right True
  test "adjoint block locals cannot escape" $
    unresolved "fn f() { adjoint { let x = 1; } x; }" "x" `shouldBe` Right True

  test "unresolved-name diagnostics identify the exact source occurrence" $
    (case resolveSource "fn f() {\n  missing;\n}" of
       Left (ResolutionFailure (UnresolvedName resolvedName span)) =>
         Right (resolvedName, coordinates span)
       Left fixtureError => Left (show fixtureError)
       Right _ => Left "Expected UnresolvedName")
      `shouldBe` Right ("missing", (2, 3, 2, 10))

  test "duplicate function diagnostics identify both declarations" $
    (case resolveSource "fn f() {}\nfn f() {}" of
       Left (ResolutionFailure (DuplicateDeclaration resolvedName [_] span previousSpan)) =>
         Right (resolvedName, spanKey span, spanKey previousSpan)
       Left fixtureError => Left (show fixtureError)
       Right _ => Left "Expected DuplicateDeclaration")
      `shouldBe` Right ("f", ("resolution-test.lf", 2, 4, 2, 5), ("resolution-test.lf", 1, 4, 1, 5))

  test "constants and functions conflict in the same value namespace" $
    (case resolveSource "const f: i32 = 1;\nfn f() {}" of
       Left (ResolutionFailure (DuplicateDeclaration resolvedName [_] span previousSpan)) =>
         Right (resolvedName, spanKey span, spanKey previousSpan)
       Left fixtureError => Left (show fixtureError)
       Right _ => Left "Expected DuplicateDeclaration")
      `shouldBe` Right ("f", ("resolution-test.lf", 2, 4, 2, 5), ("resolution-test.lf", 1, 7, 1, 8))

  test "call callee and every argument have value references in the body scope" $
    expressionUses "g(x, n)" ["g", "x", "n"] (\expression => case expression.nodeValue of
      ExprCall callee arguments => Just (callee :: arguments)
      _ => Nothing) `shouldBe` Right True

  test "tuple elements resolve each name occurrence" $
    expressionUses "(x, n)" ["x", "n"] (\expression => case expression.nodeValue of
      ExprTuple elements => Just (forget elements)
      _ => Nothing) `shouldBe` Right True

  test "array elements resolve each name occurrence" $
    expressionUses "[x, n]" ["x", "n"] (\expression => case expression.nodeValue of
      ExprArray elements => Just elements
      _ => Nothing) `shouldBe` Right True

  test "repeated arrays resolve both their element and count" $
    expressionUses "[x; N]" ["x", "N"] (\expression => case expression.nodeValue of
      ExprRepeatedArray element count => Just [element, count]
      _ => Nothing) `shouldBe` Right True

  test "indexing resolves the object and the index" $
    expressionUses "a[i]" ["a", "i"] (\expression => case expression.nodeValue of
      ExprIndex object index => Just [object, index]
      _ => Nothing) `shouldBe` Right True

  test "ranges resolve both endpoints" $
    expressionUses "i..n" ["i", "n"] (\expression => case expression.nodeValue of
      ExprRange (Just rangeStart) _ (Just rangeEnd) => Just [rangeStart, rangeEnd]
      _ => Nothing) `shouldBe` Right True

  test "ranges without an upper bound resolve their start" $
    expressionUses "i.." ["i"] (\expression => case expression.nodeValue of
      ExprRange (Just rangeStart) _ Nothing => Just [rangeStart]
      _ => Nothing) `shouldBe` Right True

  test "ranges without a lower bound resolve their end" $
    expressionUses "..n" ["n"] (\expression => case expression.nodeValue of
      ExprRange Nothing _ (Just rangeEnd) => Just [rangeEnd]
      _ => Nothing) `shouldBe` Right True

  test "unary operands retain their reference and enclosing scope" $
    expressionUses "-x" ["x"] (\expression => case expression.nodeValue of
      ExprUnary _ operand => Just [operand]
      _ => Nothing) `shouldBe` Right True

  test "both binary operands retain their references and enclosing scope" $
    expressionUses "x + n" ["x", "n"] (\expression => case expression.nodeValue of
      ExprBinary _ left right => Just [left, right]
      _ => Nothing) `shouldBe` Right True

  test "casts resolve their operand and expressions in the target type" $
    expressionUses "a as [i32; N]" ["a", "N"] (\expression => do
      ExprCast operand target <- pure expression.nodeValue | _ => Nothing
      TyArray _ size <- pure target.nodeValue | _ => Nothing
      pure [operand, size]) `shouldBe` Right True

  test "tuple indexing resolves its base expression" $
    expressionUses "pair.0" ["pair"] (\expression => case expression.nodeValue of
      ExprTupleIndex tuple "0" => Just [tuple]
      _ => Nothing) `shouldBe` Right True

  test "indexed assignment records reads of the base, index and value" $
    checkSource "fn f(mut a: [i32; 2], i: i32, x: i32) { a[i] = x; }" (\resolvedModule => do
      (_, functionDeclaration) <- functionNamed "f" resolvedModule
      [aName, iName, xName] <- parameterNames functionDeclaration | _ => Nothing
      assignment <- assignmentAt 0 functionDeclaration.functionBody
      AssignTargetIndex object index <- pure assignment.assignmentTarget.nodeValue | _ => Nothing
      scope <- scopeFor resolvedModule functionDeclaration.functionBody
      reads <- usesInScope resolvedModule scope.id [(aName, object), (iName, index), (xName, assignment.assignmentValue)]
      pure (reads && nodeHasScope resolvedModule scope.id assignment.assignmentTarget &&
            length (valueReferences resolvedModule) == 3 && length (allReferences resolvedModule) == 7)) `shouldBe` Right True

  test "tuple-index assignment records reads without inventing a symbol for the index" $
    checkSource "fn f(mut pair: (i32, i32), x: i32) { pair.0 = x; }" (\resolvedModule => do
      (_, functionDeclaration) <- functionNamed "f" resolvedModule
      [pair, xName] <- parameterNames functionDeclaration | _ => Nothing
      assignment <- assignmentAt 0 functionDeclaration.functionBody
      AssignTargetTupleIndex object "0" <- pure assignment.assignmentTarget.nodeValue | _ => Nothing
      scope <- scopeFor resolvedModule functionDeclaration.functionBody
      reads <- usesInScope resolvedModule scope.id [(pair, object), (xName, assignment.assignmentValue)]
      pure (reads && nodeHasScope resolvedModule scope.id assignment.assignmentTarget &&
            length (valueReferences resolvedModule) == 2 && length (allReferences resolvedModule) == 5)) `shouldBe` Right True

  -- Member validity is deferred to typechecking; resolution still visits the
  -- base and value and records the textual selector's lexical scope.
  test "field assignment records the selector scope while deferring member lookup" $
    checkSource "fn f(mut pair: (i32, i32), x: i32) { pair.field = x; }" (\resolvedModule => do
      (_, functionDeclaration) <- functionNamed "f" resolvedModule
      [pair, xName] <- parameterNames functionDeclaration | _ => Nothing
      assignment <- assignmentAt 0 functionDeclaration.functionBody
      AssignTargetField object field <- pure assignment.assignmentTarget.nodeValue | _ => Nothing
      scope <- scopeFor resolvedModule functionDeclaration.functionBody
      reads <- usesInScope resolvedModule scope.id [(pair, object), (xName, assignment.assignmentValue)]
      pure (reads && nodeHasScope resolvedModule scope.id assignment.assignmentTarget &&
            nodeHasScope resolvedModule scope.id field &&
            all (\reference => reference.occurrence.nodeId /= field.astInfo.nodeId) (allReferences resolvedModule) &&
            not (elem "field" (map (.declaredName) (sourceSymbols resolvedModule))) &&
            length (allReferences resolvedModule) == 5)) `shouldBe` Right True

  test "compound assignment preserves its operator and resolves each written name once" $
    checkSource "fn f(mut x: i32, y: i32) { x += y; }" (\resolvedModule => do
      (fnInfo, functionDeclaration) <- functionNamed "f" resolvedModule
      [xParameter, yParameter] <- pure functionDeclaration.functionParameters | _ => Nothing
      [xName, yName] <- parameterNames functionDeclaration | _ => Nothing
      assignment <- assignmentAt 0 functionDeclaration.functionBody
      AssignTargetName target <- pure assignment.assignmentTarget.nodeValue | _ => Nothing
      ExprName yRead <- pure assignment.assignmentValue.nodeValue | _ => Nothing
      scope <- scopeFor resolvedModule functionDeclaration.functionBody
      reads <- usesInScope resolvedModule scope.id [(yName, assignment.assignmentValue)]
      pure (reads && symbolId target == symbolId xName && assignment.assignmentOperator.nodeValue == AssignAdd &&
            nodeHasScope resolvedModule scope.id assignment.assignmentValue &&
            nodeHasScope resolvedModule scope.id assignment.assignmentTarget &&
            nodeHasScope resolvedModule scope.id target &&
            referenceInventory resolvedModule
              [(DeclarationReference, fnInfo.nodeId, functionDeclaration.functionName),
               (DeclarationReference, xParameter.astInfo.nodeId, xName),
               (DeclarationReference, yParameter.astInfo.nodeId, yName),
               (AssignmentTarget, assignment.assignmentTarget.astInfo.nodeId, target),
               (ValueReference, assignment.assignmentValue.astInfo.nodeId, yRead)])) `shouldBe` Right True

  test "a compound index block has one scope and its local does not escape" $
    checkSource "fn f(mut a: [i32; 2], i: i32) { a[{ let i = 0; i }] += 1; i; }" (\resolvedModule => do
      (fnInfo, functionDeclaration) <- functionNamed "f" resolvedModule
      [aParameter, iParameter] <- pure functionDeclaration.functionParameters | _ => Nothing
      [aName, iName] <- parameterNames functionDeclaration | _ => Nothing
      assignment <- assignmentAt 0 functionDeclaration.functionBody
      AssignTargetIndex object index <- pure assignment.assignmentTarget.nodeValue | _ => Nothing
      ExprName aRead <- pure object.nodeValue | _ => Nothing
      block <- blockBody index
      localBinding <- letAt 0 block
      local <- binder localBinding.letPattern
      final <- block.nodeValue.finalExpression
      ExprName localRead <- pure final.nodeValue | _ => Nothing
      after <- exprAt 1 functionDeclaration.functionBody
      ExprName outerRead <- pure after.nodeValue | _ => Nothing
      bodyScope <- scopeFor resolvedModule functionDeclaration.functionBody
      indexScope <- scopeFor resolvedModule block
      objectOK <- useMatches resolvedModule aName object
      localOK <- useMatches resolvedModule local final
      afterOK <- useMatches resolvedModule iName after
      pure (assignment.assignmentOperator.nodeValue == AssignAdd &&
            objectOK && localOK && afterOK && symbolId local /= symbolId iName &&
            indexScope.parent == Just bodyScope.id &&
            blockScopesMatchNodes resolvedModule && bindingMatches indexScope local &&
            localMatches resolvedModule local False &&
            (indexScope.declaredSymbolsInOrder <>> []) == [symbolId local] &&
            referenceInventory resolvedModule
              [(DeclarationReference, fnInfo.nodeId, functionDeclaration.functionName),
               (DeclarationReference, aParameter.astInfo.nodeId, aName),
               (DeclarationReference, iParameter.astInfo.nodeId, iName),
               (ValueReference, object.astInfo.nodeId, aRead),
               (DeclarationReference, localBinding.letPattern.astInfo.nodeId, local),
               (ValueReference, final.astInfo.nodeId, localRead),
               (ValueReference, after.astInfo.nodeId, outerRead)])) `shouldBe` Right True

  test "a compound index block without references still has exactly one scope" $
    checkSource "fn f(mut a: [i32; 2]) { a[{ 0 }] += 1; }" (\resolvedModule => do
      (_, functionDeclaration) <- functionNamed "f" resolvedModule
      assignment <- assignmentAt 0 functionDeclaration.functionBody
      AssignTargetIndex _ index <- pure assignment.assignmentTarget.nodeValue | _ => Nothing
      block <- blockBody index
      indexScope <- scopeFor resolvedModule block
      pure (blockScopesMatchNodes resolvedModule && isBlock indexScope &&
            null (indexScope.declaredSymbolsInOrder <>> []) &&
            length (filter (isBlock . snd) (SortedMap.toList resolvedModule.tables.scopes)) == 2))
      `shouldBe` Right True

  test "nested compound targets retain consistent block scopes" $
    checkSource "fn f(mut a: [i32; 2]) { a[{ let i = 0; let mut b = [0]; b[{ i }] += 1; i }] += 1; }"
      (\resolvedModule => Just (blockScopesMatchNodes resolvedModule &&
        length (filter (isBlock . snd) (SortedMap.toList resolvedModule.tables.scopes)) == 3))
      `shouldBe` Right True

  test "nested signature and local types have scopes on every visited type node" $
    checkSource "const n: i32 = 2; fn f(value: &([i32; n], &[i32])) -> [i32; n] { let local: [i32; n] = [0; n]; }" (\resolvedModule => do
      (_, constDeclaration) <- constantNamed "n" resolvedModule
      (_, functionDeclaration) <- functionNamed "f" resolvedModule
      [parameter] <- pure functionDeclaration.functionParameters | _ => Nothing
      NormalParameter _ _ _ referenceType <- pure parameter.nodeValue | _ => Nothing
      TyReference _ tupleType <- pure referenceType.nodeValue | _ => Nothing
      TyTuple (arrayType ::: [sliceReference]) <- pure tupleType.nodeValue | _ => Nothing
      TyArray elementType parameterSize <- pure arrayType.nodeValue | _ => Nothing
      TyReference _ sliceType <- pure sliceReference.nodeValue | _ => Nothing
      TySlice sliceElement <- pure sliceType.nodeValue | _ => Nothing
      returnType <- functionDeclaration.returnType
      TyArray returnElement returnSize <- pure returnType.nodeValue | _ => Nothing
      local <- letAt 0 functionDeclaration.functionBody
      localType <- local.letTypeAnnotation
      TyArray localElement localSize <- pure localType.nodeValue | _ => Nothing
      initializerExpression <- initializer local
      ExprRepeatedArray zero count <- pure initializerExpression.nodeValue | _ => Nothing
      functionScope <- scopeFor resolvedModule parameter
      bodyScope <- scopeFor resolvedModule functionDeclaration.functionBody
      signatureUses <- usesInScope resolvedModule functionScope.id [(constDeclaration.constName, parameterSize), (constDeclaration.constName, returnSize)]
      bodyUses <- usesInScope resolvedModule bodyScope.id [(constDeclaration.constName, localSize), (constDeclaration.constName, count)]
      pure (signatureUses && bodyUses && functionScope.id /= bodyScope.id &&
            all (nodeHasScope resolvedModule functionScope.id)
              [referenceType, tupleType, arrayType, elementType, sliceReference, sliceType, sliceElement, returnType, returnElement] &&
            all (nodeHasScope resolvedModule bodyScope.id) [localType, localElement] &&
            all (nodeHasScope resolvedModule bodyScope.id) [initializerExpression, zero] &&
            nodeHasScope resolvedModule resolvedModule.rootScopeId constDeclaration.constType)) `shouldBe` Right True

  test "cast target type nodes have the enclosing expression scope" $
    checkSource "const N: i32 = 2; fn f(a: [i32; 2]) { a as [i32; N]; }" (\resolvedModule => do
      (_, functionDeclaration) <- functionNamed "f" resolvedModule
      expression <- exprAt 0 functionDeclaration.functionBody
      ExprCast _ target <- pure expression.nodeValue | _ => Nothing
      TyArray element _ <- pure target.nodeValue | _ => Nothing
      scope <- scopeFor resolvedModule functionDeclaration.functionBody
      pure (nodeHasScope resolvedModule scope.id expression &&
            all (nodeHasScope resolvedModule scope.id) [target, element])) `shouldBe` Right True

  test "nested pattern containers and wildcards have scopes but introduce only named binders" $
    checkSource "fn f() { let (a, [_, b]) = (1, [2, 3]); }" (\resolvedModule => do
      (_, functionDeclaration) <- functionNamed "f" resolvedModule
      binding <- letAt 0 functionDeclaration.functionBody
      PatternTuple (aPattern ::: [arrayPattern]) <- pure binding.letPattern.nodeValue | _ => Nothing
      PatternArray [wildcard, bPattern] <- pure arrayPattern.nodeValue | _ => Nothing
      PatternWildcard <- pure wildcard.nodeValue | _ => Nothing
      aName <- binder aPattern
      bName <- binder bPattern
      scope <- scopeFor resolvedModule functionDeclaration.functionBody
      initializerExpression <- initializer binding
      ExprTuple (oneLiteral ::: [arrayExpression]) <- pure initializerExpression.nodeValue | _ => Nothing
      ExprArray [twoLiteral, threeLiteral] <- pure arrayExpression.nodeValue | _ => Nothing
      pure (all (nodeHasScope resolvedModule scope.id) [binding.letPattern, aPattern, arrayPattern, wildcard, bPattern] &&
            all (nodeHasScope resolvedModule scope.id) [initializerExpression, oneLiteral, arrayExpression, twoLiteral, threeLiteral] &&
            (scope.declaredSymbolsInOrder <>> []) == [symbolId aName, symbolId bName] &&
            sort (map fst (SortedMap.toList resolvedModule.tables.localVarsMeta)) == sort [symbolId aName, symbolId bName] &&
            sort (map (.declaredName) (sourceSymbols resolvedModule)) == ["", "a", "b", "f"] &&
            length (allReferences resolvedModule) == 3 &&
            all (\reference => not (elem reference.occurrence.nodeId
                 [binding.letPattern.astInfo.nodeId, arrayPattern.astInfo.nodeId, wildcard.astInfo.nodeId]))
              (allReferences resolvedModule))) `shouldBe` Right True

  test "small shadowing fixtures have exact symbol, binding, declaration and reference inventories" $
    checkSource "const n: i32 = 1; fn f(x: i32) { let y = x; let y = y; y; }" (\resolvedModule => do
      (constInfo, constDeclaration) <- constantNamed "n" resolvedModule
      (fnInfo, functionDeclaration) <- functionNamed "f" resolvedModule
      [parameter] <- pure functionDeclaration.functionParameters | _ => Nothing
      [xName] <- parameterNames functionDeclaration | _ => Nothing
      first <- letAt 0 functionDeclaration.functionBody
      second <- letAt 1 functionDeclaration.functionBody
      firstYName <- binder first.letPattern
      secondYName <- binder second.letPattern
      xUseExpr <- initializer first
      y1UseExpr <- initializer second
      y2UseExpr <- exprAt 2 functionDeclaration.functionBody
      ExprName xUse <- pure xUseExpr.nodeValue | _ => Nothing
      ExprName y1Use <- pure y1UseExpr.nodeValue | _ => Nothing
      ExprName y2Use <- pure y2UseExpr.nodeValue | _ => Nothing
      root <- lookup resolvedModule.rootScopeId resolvedModule.tables.scopes
      functionScope <- scopeFor resolvedModule parameter
      bodyScope <- scopeFor resolvedModule functionDeclaration.functionBody
      orderedRoot <- traverse (\declaredSymbolId => lookup declaredSymbolId resolvedModule.tables.symbols) (root.declaredSymbolsInOrder <>> [])
      pure (sort (map (.symbolId) (sourceSymbols resolvedModule)) ==
              sort [resolvedModule.rootSymbolId, symbolId constDeclaration.constName, symbolId functionDeclaration.functionName, symbolId xName, symbolId firstYName, symbolId secondYName] &&
            sort (map fst (SortedMap.toList resolvedModule.tables.localVarsMeta)) == sort [symbolId xName, symbolId firstYName, symbolId secondYName] &&
            map (.declaredName) orderedRoot == ["<prelude>", "n", "f"] &&
            map (\(resolvedName, binding) => (resolvedName, binding.target)) (SortedMap.toList root.valueBindings) ==
              [("f", symbolId functionDeclaration.functionName), ("n", symbolId constDeclaration.constName)] &&
            map (\(resolvedName, binding) => (resolvedName, binding.target)) (SortedMap.toList functionScope.valueBindings) == [("x", symbolId xName)] &&
            map (\(resolvedName, binding) => (resolvedName, binding.target)) (SortedMap.toList bodyScope.valueBindings) == [("y", symbolId secondYName)] &&
            (functionScope.declaredSymbolsInOrder <>> []) == [symbolId xName] &&
            (bodyScope.declaredSymbolsInOrder <>> []) == [symbolId firstYName, symbolId secondYName] &&
            symbolId xUse == symbolId xName && symbolId y1Use == symbolId firstYName && symbolId y2Use == symbolId secondYName &&
            referenceInventory resolvedModule
              [(DeclarationReference, constInfo.nodeId, constDeclaration.constName),
               (DeclarationReference, fnInfo.nodeId, functionDeclaration.functionName),
               (DeclarationReference, parameter.astInfo.nodeId, xName),
               (DeclarationReference, first.letPattern.astInfo.nodeId, firstYName),
               (ValueReference, xUseExpr.astInfo.nodeId, xUse),
               (DeclarationReference, second.letPattern.astInfo.nodeId, secondYName),
               (ValueReference, y1UseExpr.astInfo.nodeId, y1Use),
               (ValueReference, y2UseExpr.astInfo.nodeId, y2Use)])) `shouldBe` Right True

  test "constant initializers can reference later constants with module scope and identity" $
    checkSource "const first: i32 = later; const later: i32 = 2; fn f() { first; later; }" (\resolvedModule => do
      (firstInfo, first) <- constantNamed "first" resolvedModule
      (laterInfo, later) <- constantNamed "later" resolvedModule
      (fnInfo, functionDeclaration) <- functionNamed "f" resolvedModule
      ExprName forward <- pure first.constValue.nodeValue | _ => Nothing
      firstUse <- exprAt 0 functionDeclaration.functionBody
      laterUse <- exprAt 1 functionDeclaration.functionBody
      body <- scopeFor resolvedModule functionDeclaration.functionBody
      forwardOK <- usesInScope resolvedModule resolvedModule.rootScopeId [(later.constName, first.constValue)]
      bodyOK <- usesInScope resolvedModule body.id [(first.constName, firstUse), (later.constName, laterUse)]
      pure (forwardOK && bodyOK && symbolId first.constName /= symbolId later.constName &&
            referenceMatches resolvedModule DeclarationReference firstInfo.nodeId first.constName &&
            referenceMatches resolvedModule DeclarationReference laterInfo.nodeId later.constName &&
            length (allReferences resolvedModule) == 6)) `shouldBe` Right True

  test "duplicate constants identify the original symbol and both declaration spans" $
    duplicateDeclaration "const n: i32 = 1;" "const n: i32 = 2;" "n" (2, 7, 2, 8) `shouldBe` Right True

  test "a constant conflicting with an earlier function reports that function" $
    duplicateDeclaration "fn f() {}" "const f: i32 = 1;" "f" (2, 7, 2, 8) `shouldBe` Right True

  test "an immutable bare constant pattern reuses the constant without creating a local" $
    checkSource "const U: () = (); fn f() { let U = (); U; }" (\resolvedModule => do
      (_, constDeclaration) <- constantNamed "U" resolvedModule
      (_, functionDeclaration) <- functionNamed "f" resolvedModule
      binding <- letAt 0 functionDeclaration.functionBody
      final <- exprAt 1 functionDeclaration.functionBody
      useOK <- useMatches resolvedModule constDeclaration.constName final
      pure (constantPatternMatches resolvedModule constDeclaration.constName binding.letPattern && useOK &&
            null (SortedMap.toList resolvedModule.tables.localVarsMeta))) `shouldBe` Right True

  test "a mutable let binder cannot shadow a module constant" $
    constantShadowing "const N: i32 = 1;\nfn f() { let mut N = 2; }"
      `shouldBe` Right ("N", (2, 18, 2, 19), (1, 7, 1, 8))

  test "a tuple can contain a local binder and repeated constant patterns" $
    checkSource "const U: () = (); fn f() { let (x, U, U) = (1, (), ()); x; }" (\resolvedModule => do
      (_, constDeclaration) <- constantNamed "U" resolvedModule
      (_, functionDeclaration) <- functionNamed "f" resolvedModule
      binding <- letAt 0 functionDeclaration.functionBody
      PatternTuple patterns <- pure binding.letPattern.nodeValue | _ => Nothing
      [xPattern, first, second] <- pure (forget patterns) | _ => Nothing
      xName <- binder xPattern
      final <- exprAt 1 functionDeclaration.functionBody
      useOK <- useMatches resolvedModule xName final
      scope <- scopeFor resolvedModule binding.letPattern
      pure (constantPatternMatches resolvedModule constDeclaration.constName first &&
            constantPatternMatches resolvedModule constDeclaration.constName second &&
            localMatches resolvedModule xName False && bindingMatches scope xName && useOK &&
            (scope.declaredSymbolsInOrder <>> []) == [symbolId xName] &&
            length (SortedMap.toList resolvedModule.tables.localVarsMeta) == 1)) `shouldBe` Right True

  test "an array can contain repeated constant patterns without introducing bindings" $
    checkSource "const U: () = (); fn f() { let [U, U] = [(), ()]; }" (\resolvedModule => do
      (_, constDeclaration) <- constantNamed "U" resolvedModule
      (_, functionDeclaration) <- functionNamed "f" resolvedModule
      binding <- letAt 0 functionDeclaration.functionBody
      PatternArray [first, second] <- pure binding.letPattern.nodeValue | _ => Nothing
      pure (constantPatternMatches resolvedModule constDeclaration.constName first &&
            constantPatternMatches resolvedModule constDeclaration.constName second &&
            null (SortedMap.toList resolvedModule.tables.localVarsMeta))) `shouldBe` Right True

  test "constant patterns remain references in nested blocks" $
    checkSource "const U: () = (); fn f() { { let U = (); } }" (\resolvedModule => do
      (_, constDeclaration) <- constantNamed "U" resolvedModule
      (_, functionDeclaration) <- functionNamed "f" resolvedModule
      inner <- returnedAt 0 functionDeclaration.functionBody >>= blockBody
      binding <- letAt 0 inner
      pure (constantPatternMatches resolvedModule constDeclaration.constName binding.letPattern &&
            null (SortedMap.toList resolvedModule.tables.localVarsMeta))) `shouldBe` Right True

  test "repeated constant parameters are pattern references and introduce no parameters" $
    checkSource "const U: () = (); fn f(U: (), U: ()) { U; }" (\resolvedModule => do
      (_, constDeclaration) <- constantNamed "U" resolvedModule
      (_, functionDeclaration) <- functionNamed "f" resolvedModule
      [first, second] <- pure functionDeclaration.functionParameters | _ => Nothing
      [firstName, secondName] <- parameterNames functionDeclaration | _ => Nothing
      useExpression <- exprAt 0 functionDeclaration.functionBody
      useOK <- useMatches resolvedModule constDeclaration.constName useExpression
      pure (constantOccurrenceMatches resolvedModule constDeclaration.constName first.astInfo.nodeId firstName &&
            constantOccurrenceMatches resolvedModule constDeclaration.constName second.astInfo.nodeId secondName && useOK &&
            null (SortedMap.toList resolvedModule.tables.localVarsMeta))) `shouldBe` Right True

  test "for constant patterns introduce no loop binding" $
    checkSource "const U: () = (); fn f() { for U in [()] { U; } }" (\resolvedModule => do
      (_, constDeclaration) <- constantNamed "U" resolvedModule
      (_, functionDeclaration) <- functionNamed "f" resolvedModule
      loopExpression <- returnedAt 0 functionDeclaration.functionBody
      ExprFor pattern _ body <- pure loopExpression.nodeValue | _ => Nothing
      useExpression <- exprAt 0 body
      useOK <- useMatches resolvedModule constDeclaration.constName useExpression
      pure (constantPatternMatches resolvedModule constDeclaration.constName pattern && useOK &&
            null (SortedMap.toList resolvedModule.tables.localVarsMeta))) `shouldBe` Right True

  test "repeated constant tuple patterns introduce no for-loop bindings" $
    checkForPattern "const U: () = (); fn f() { let (U, U) = ((), ()); for unused in [((), ())] { U; } }" (\resolvedModule => do
      (_, constDeclaration) <- constantNamed "U" resolvedModule
      (_, functionDeclaration) <- functionNamed "f" resolvedModule
      loopExpression <- returnedAt 0 functionDeclaration.functionBody
      ExprFor pattern _ body <- pure loopExpression.nodeValue | _ => Nothing
      PatternTuple patterns <- pure pattern.nodeValue | _ => Nothing
      [first, second] <- pure (forget patterns) | _ => Nothing
      loopScope <- scopeFor resolvedModule pattern
      useExpression <- exprAt 0 body
      useOK <- useMatches resolvedModule constDeclaration.constName useExpression
      pure (constantPatternMatches resolvedModule constDeclaration.constName first &&
            constantPatternMatches resolvedModule constDeclaration.constName second && useOK &&
            (case loopScope.kind of ForScope => True; _ => False) &&
            null (SortedMap.toList loopScope.valueBindings) &&
            null (SortedMap.toList resolvedModule.tables.localVarsMeta))) `shouldBe` Right True

  test "a constant declared later in the module is still a constant pattern" $
    checkSource "fn f() { let U = (); } const U: () = ();" (\resolvedModule => do
      (_, constDeclaration) <- constantNamed "U" resolvedModule
      (_, functionDeclaration) <- functionNamed "f" resolvedModule
      binding <- letAt 0 functionDeclaration.functionBody
      pure (constantPatternMatches resolvedModule constDeclaration.constName binding.letPattern &&
            null (SortedMap.toList resolvedModule.tables.localVarsMeta))) `shouldBe` Right True

  test "a constant shadowing a prelude function is interpreted as a pattern" $
    checkSource "const sin: () = (); fn f() { let sin = (); }" (\resolvedModule => do
      (_, constDeclaration) <- constantNamed "sin" resolvedModule
      (_, functionDeclaration) <- functionNamed "f" resolvedModule
      binding <- letAt 0 functionDeclaration.functionBody
      pure (constantPatternMatches resolvedModule constDeclaration.constName binding.letPattern &&
            null (SortedMap.toList resolvedModule.tables.localVarsMeta))) `shouldBe` Right True

  -- Resolving a constant pattern does not decide whether it is irrefutable.
  test "integer constant patterns defer refutability checking" $
    checkSource "const N: i32 = 1; fn f() { let N = 2; }" (\resolvedModule => do
      (_, constDeclaration) <- constantNamed "N" resolvedModule
      (_, functionDeclaration) <- functionNamed "f" resolvedModule
      binding <- letAt 0 functionDeclaration.functionBody
      pure (constantPatternMatches resolvedModule constDeclaration.constName binding.letPattern)) `shouldBe` Right True

  test "a mutable binder nested in a destructuring pattern cannot shadow a constant" $
    constantShadowing "const N: i32 = 1;\nfn f() { let (a, mut N) = (1, 2); }"
      `shouldBe` Right ("N", (2, 22, 2, 23), (1, 7, 1, 8))

  test "a mutable function parameter cannot shadow a constant" $
    constantShadowing "const N: i32 = 1;\nfn f(mut N: i32) {}"
      `shouldBe` Right ("N", (2, 10, 2, 11), (1, 7, 1, 8))

  test "a mutable for binder cannot shadow a constant" $
    forConstantShadowing "const N: i32 = 1;\nfn f() { let mut N = 1; for unused in [1] {} }"
      `shouldBe` Right ("N", (2, 18, 2, 19), (1, 7, 1, 8))

  test "constant-shadowing diagnostics identify the constant's symbol" $
    (do expectedSymbol <- checkSource "const N: i32 = 1;" (\resolvedModule =>
          map (\(_, constDeclaration) => symbolId constDeclaration.constName) (constantNamed "N" resolvedModule))
        case resolveSource "const N: i32 = 1;\nfn f() { let mut N = 2; }" of
          Left (ResolutionFailure (BindingShadowsConstant _ reportedSymbol _ _)) => Right (reportedSymbol == expectedSymbol)
          Left fixtureError => Left (show fixtureError)
          Right _ => Left "Expected BindingShadowsConstant, but resolution succeeded") `shouldBe` Right True

  test "a repeated tuple binder reports both occurrences" $
    duplicateBinder "fn f() { let (x, x) = (1, 2); }"
      `shouldBe` Right ("x", (1, 18, 1, 19), (1, 15, 1, 16))

  test "a repeated nested array binder reports both occurrences" $
    duplicateBinder "fn f() { let (x, [x]) = (1, [2]); }"
      `shouldBe` Right ("x", (1, 19, 1, 20), (1, 15, 1, 16))

  test "a repeated for binder reports both occurrences" $
    duplicateForBinder "fn f() { let (x, x) = (1, 2); for unused in [(1, 2)] {} }"
      `shouldBe` Right ("x", (1, 18, 1, 19), (1, 15, 1, 16))

  test "a repeated function parameter reports both occurrences" $
    duplicateBinder "fn f(x: i32, x: i32) {}"
      `shouldBe` Right ("x", (1, 14, 1, 15), (1, 6, 1, 7))

  test "parameters and locals may still shadow module functions" $
    checkSource "fn g() {} fn f(g: i32) { let g = g; g; }" (\resolvedModule => do
      (_, functionF) <- functionNamed "f" resolvedModule
      [parameter] <- parameterNames functionF | _ => Nothing
      binding <- letAt 0 functionF.functionBody
      local <- binder binding.letPattern
      initializerExpression <- initializer binding
      final <- exprAt 1 functionF.functionBody
      initUsesParameter <- useMatches resolvedModule parameter initializerExpression
      finalUsesLocal <- useMatches resolvedModule local final
      pure (initUsesParameter && finalUsesLocal)) `shouldBe` Right True

  test "a repeat count cannot use a parameter" $
    nonConstantUse "fn f(n: i32) { [0; n]; }"
      `shouldBe` Right ("n", (1, 20, 1, 21), (1, 6, 1, 7))

  test "an array length in a let annotation cannot use an earlier local" $
    nonConstantUse "fn f() { let n = 2; let a: [i32; n] = [0, 0]; }"
      `shouldBe` Right ("n", (1, 34, 1, 35), (1, 14, 1, 15))

  test "an array length in a cast target cannot use a parameter" $
    nonConstantUse "fn f(n: i32, a: [i32; 2]) { a as [i32; n]; }"
      `shouldBe` Right ("n", (1, 40, 1, 41), (1, 6, 1, 7))

  test "a repeat count in a nested block cannot use an enclosing local" $
    nonConstantUse "fn f() { let n = 2; { [0; n]; } }"
      `shouldBe` Right ("n", (1, 27, 1, 28), (1, 14, 1, 15))

  test "a repeat count cannot use a for binder" $
    nonConstantUse "fn f() { for i in [1] { [0; i]; } }"
      `shouldBe` Right ("i", (1, 29, 1, 30), (1, 14, 1, 15))

  test "a nested constant expression cannot use locals of its enclosing constant expression" $
    nonConstantUse "fn f() { [0; { let k = 2; [0; k]; 2 }]; }"
      `shouldBe` Right ("k", (1, 31, 1, 32), (1, 20, 1, 21))

  test "nested constant contexts restore outer constant locals and then ordinary parameter access" $
    checkSource "fn f(x: i32) { [0; { let n = 2; [0; { let m = 1; m }]; n }]; x; }" (\resolvedModule => do
      (fnInfo, functionDeclaration) <- functionNamed "f" resolvedModule
      [parameter] <- pure functionDeclaration.functionParameters | _ => Nothing
      [xName] <- parameterNames functionDeclaration | _ => Nothing
      repeated <- exprAt 0 functionDeclaration.functionBody
      ExprRepeatedArray _ outerCount <- pure repeated.nodeValue | _ => Nothing
      outerBlock <- blockBody outerCount
      nBinding <- letAt 0 outerBlock
      nName <- binder nBinding.letPattern
      innerRepeated <- exprAt 1 outerBlock
      ExprRepeatedArray _ innerCount <- pure innerRepeated.nodeValue | _ => Nothing
      innerBlock <- blockBody innerCount
      mBinding <- letAt 0 innerBlock
      mName <- binder mBinding.letPattern
      mUse <- innerBlock.nodeValue.finalExpression
      nUse <- outerBlock.nodeValue.finalExpression
      xUse <- exprAt 1 functionDeclaration.functionBody
      ExprName mRead <- pure mUse.nodeValue | _ => Nothing
      ExprName nRead <- pure nUse.nodeValue | _ => Nothing
      ExprName xRead <- pure xUse.nodeValue | _ => Nothing
      bodyScope <- scopeFor resolvedModule functionDeclaration.functionBody
      outerScope <- scopeFor resolvedModule outerBlock
      innerScope <- scopeFor resolvedModule innerBlock
      mUseMatches <- usesInScope resolvedModule innerScope.id [(mName, mUse)]
      nUseMatches <- usesInScope resolvedModule outerScope.id [(nName, nUse)]
      xUseMatches <- usesInScope resolvedModule bodyScope.id [(xName, xUse)]
      pure (mUseMatches && nUseMatches && xUseMatches && isNothing resolvedModule.tables.constContextBoundary &&
            outerScope.parent == Just bodyScope.id && innerScope.parent == Just outerScope.id &&
            bindingMatches outerScope nName && bindingMatches innerScope mName &&
            (outerScope.declaredSymbolsInOrder <>> []) == [symbolId nName] &&
            (innerScope.declaredSymbolsInOrder <>> []) == [symbolId mName] &&
            referenceInventory resolvedModule
              [(DeclarationReference, fnInfo.nodeId, functionDeclaration.functionName),
               (DeclarationReference, parameter.astInfo.nodeId, xName),
               (DeclarationReference, nBinding.letPattern.astInfo.nodeId, nName),
               (DeclarationReference, mBinding.letPattern.astInfo.nodeId, mName),
               (ValueReference, mUse.astInfo.nodeId, mRead),
               (ValueReference, nUse.astInfo.nodeId, nRead),
               (ValueReference, xUse.astInfo.nodeId, xRead)])) `shouldBe` Right True

  test "leaving a nested constant context still forbids parameters in the outer count" $
    nonConstantUse "fn f(x: i32) { [0; { [0; 2]; x }]; }"
      `shouldBe` Right ("x", (1, 30, 1, 31), (1, 6, 1, 7))

  test "constant expressions may use locals they declare themselves" $
    checkSource "fn f() { let a: [i32; { let k = 2; k }] = [0; { let m = 2; m }]; }" valueReferenceKinds
      `shouldBe` Right [("k", "local"), ("m", "local")]

  test "constant expressions may use constants, functions and prelude functions" $
    checkSource "const N: i32 = 2; const fn g() -> i32 { 2 } fn f() { [0; N]; [0; g()]; [0; abs(2)]; }" valueReferenceKinds
      `shouldBe` Right [("N", "constant"), ("g", "function"), ("abs", "function")]

  test "repeated-array elements and later uses still see locals" $
    checkSource "fn f(x: i32) { [x; 2]; let a: [i32; 2] = [x, x]; x; }" valueReferenceKinds
      `shouldBe` Right [("x", "parameter"), ("x", "parameter"), ("x", "parameter"), ("x", "parameter")]

  test "method calls resolve the receiver and arguments but not the method name" $
    expressionUses "x.missing(n)" ["x", "n"] (\expression => case expression.nodeValue of
      ExprMethodCall receiver _ arguments => Just (receiver :: arguments)
      _ => Nothing) `shouldBe` Right True

  test "field reads resolve the object but not the field name" $
    expressionUses "pair.missing" ["pair"] (\expression => case expression.nodeValue of
      ExprField object _ => Just [object]
      _ => Nothing) `shouldBe` Right True

  test "return values are resolved" $
    expressionUses "return x" ["x"] (\expression => case expression.nodeValue of
      ExprReturn (Just returnValue) => Just [returnValue]
      _ => Nothing) `shouldBe` Right True

  test "break values are resolved inside the loop body" $
    checkSource "fn f(x: i32) { loop { break x; } }" valueReferenceKinds
      `shouldBe` Right [("x", "parameter")]

  test "a while condition cannot see locals of its body" $
    unresolved "fn f() { while c { let c = true; } }" "c" `shouldBe` Right True

  test "locals declared in an if condition block do not reach the branches" $
    unresolved "fn f() { if { let c = true; c } { c; } }" "c" `shouldBe` Right True

  test "a parameter shadows its own function's name" $
    checkSource "fn f(f: i32) { f; }" valueReferenceKinds `shouldBe` Right [("f", "parameter")]

  test "a for binder cannot escape an enclosing block" $
    unresolved "fn f() { { for i in [1] {} } i; }" "i" `shouldBe` Right True

  test "leaving a for loop nested in a block restores the outer binding" $
    checkSource "fn f() { let i = 0; { for i in [1] { i; } } i; }" (\resolvedModule => do
      (_, functionDeclaration) <- functionNamed "f" resolvedModule
      outerBinding <- letAt 0 functionDeclaration.functionBody
      outer <- binder outerBinding.letPattern
      after <- exprAt 2 functionDeclaration.functionBody
      block <- exprAt 1 functionDeclaration.functionBody >>= blockBody
      loopExpression <- block.nodeValue.finalExpression
      ExprFor pattern _ body <- pure loopExpression.nodeValue | _ => Nothing
      loopName <- binder pattern
      inner <- exprAt 0 body
      innerOK <- useMatches resolvedModule loopName inner
      afterOK <- useMatches resolvedModule outer after
      pure (innerOK && afterOK && symbolId loopName /= symbolId outer)) `shouldBe` Right True

  test "a constant initializer cannot see function parameters" $
    unresolved "fn f(x: i32) {} const C: i32 = x;" "x" `shouldBe` Right True

  test "an unresolved assignment target is reported" $
    unresolved "fn f() { y = 1; }" "y" `shouldBe` Right True

  test "function-type parameter names are not bindings" $
    unresolved "fn f(g: fn(x: i32) -> i32) { x; }" "x" `shouldBe` Right True

  test "an array length inside a function type cannot use a local" $
    nonConstantUse "fn f() { let n = 2; let g: fn(a: [i32; n]); }"
      `shouldBe` Right ("n", (1, 40, 1, 41), (1, 14, 1, 15))

  test "an assignment inside a constant expression cannot target an enclosing local" $
    nonConstantUse "fn f() { let mut x = 1; [0; { x = 2; 2 }]; }"
      `shouldBe` Right ("x", (1, 31, 1, 32), (1, 18, 1, 19))

  test "a parameter named like a prelude function is still a local in a constant expression" $
    nonConstantUse "fn f(abs: i32) { [0; abs]; }"
      `shouldBe` Right ("abs", (1, 22, 1, 25), (1, 6, 1, 9))

  test "constant item types and initializers may use constants as array lengths" $
    checkSource "const N: i32 = 2; const A: [i32; N] = [0; N];" valueReferenceKinds
      `shouldBe` Right [("N", "constant"), ("N", "constant")]

  test "a parameter type cannot use an earlier parameter as an array length" $
    nonConstantUse "fn f(n: i32, a: [i32; n]) {}"
      `shouldBe` Right ("n", (1, 23, 1, 24), (1, 6, 1, 7))

  test "a return type cannot use a parameter as an array length" $
    nonConstantUse "fn f(n: i32) -> [i32; n] {}"
      `shouldBe` Right ("n", (1, 23, 1, 24), (1, 6, 1, 7))

  test "a parameter type cannot use its own parameter as an array length" $
    nonConstantUse "fn f(n: [i32; n]) {}"
      `shouldBe` Right ("n", (1, 15, 1, 16), (1, 6, 1, 7))

  test "a parameter shadows a module function inside later signature types" $
    nonConstantUse "const fn n() -> i32 { 2 } fn f(n: i32, values: [i32; n()]) {}"
      `shouldBe` Right ("n", (1, 54, 1, 55), (1, 32, 1, 33))

  test "a parameter type sees a later parameter and rejects it as a constant" $
    nonConstantUse "fn f(a: [i32; n], n: i32) {}"
      `shouldBe` Right ("n", (1, 15, 1, 16), (1, 19, 1, 20))

  test "a later parameter shadows a module function in an earlier signature type" $
    nonConstantUse "const fn n() -> i32 { 2 } fn f(values: [i32; n()], n: i32) {}"
      `shouldBe` Right ("n", (1, 46, 1, 47), (1, 52, 1, 53))

  test "a later parameter shadows a prelude function in an earlier signature type" $
    nonConstantUse "fn f(values: [i32; abs(2)], abs: i32) {}"
      `shouldBe` Right ("abs", (1, 20, 1, 23), (1, 29, 1, 32))

  test "a local in a signature length block shadows an already registered later parameter" $
    checkSource "fn f(values: [i32; { let n = 2; n }], n: i32) { n; }" valueReferenceKinds
      `shouldBe` Right [("n", "local"), ("n", "parameter")]

  test "constant parameter patterns keep signature types and the body bound to the constant" $
    checkSource "const N: i32 = 2; fn f(values: [i32; N], N: i32) -> [i32; N] { N; }" (\resolvedModule => do
      (_, constDeclaration) <- constantNamed "N" resolvedModule
      (_, functionDeclaration) <- functionNamed "f" resolvedModule
      [_, parameter] <- pure functionDeclaration.functionParameters | _ => Nothing
      [_, resolvedName] <- parameterNames functionDeclaration | _ => Nothing
      uses <- valueReferenceKinds resolvedModule
      pure (constantOccurrenceMatches resolvedModule constDeclaration.constName parameter.astInfo.nodeId resolvedName &&
            uses == [("N", "constant"), ("N", "constant"), ("N", "constant")] &&
            length (SortedMap.toList resolvedModule.tables.localVarsMeta) == 1)) `shouldBe` Right True

  test "signature array lengths may use module constants alongside parameters" $
    checkSource "const N: i32 = 2; fn f(n: i32, a: [i32; N]) -> [i32; N] {}" valueReferenceKinds
      `shouldBe` Right [("N", "constant"), ("N", "constant")]

  test "a mutable let binder cannot shadow a constant declared later in the module" $
    constantShadowing "fn f() { let mut N = 1; }\nconst N: i32 = 2;"
      `shouldBe` Right ("N", (1, 18, 1, 19), (2, 7, 2, 8))

  -- Only constants are protected: mutable binders may shadow functions.
  test "mutable binders may shadow module and prelude functions" $
    checkSource "fn g() {} fn f() { let mut g = 1; let mut sin = 2; g; sin; }" valueReferenceKinds
      `shouldBe` Right [("g", "local"), ("sin", "local")]

  test "an immutable parameter named like a later constant is a constant pattern" $
    checkSource "fn f(U: ()) { U; } const U: () = ();" (\resolvedModule => do
      (_, constDeclaration) <- constantNamed "U" resolvedModule
      (_, functionDeclaration) <- functionNamed "f" resolvedModule
      [parameter] <- pure functionDeclaration.functionParameters | _ => Nothing
      [resolvedName] <- parameterNames functionDeclaration | _ => Nothing
      useExpression <- exprAt 0 functionDeclaration.functionBody
      useOK <- useMatches resolvedModule constDeclaration.constName useExpression
      pure (constantOccurrenceMatches resolvedModule constDeclaration.constName parameter.astInfo.nodeId resolvedName && useOK &&
            null (SortedMap.toList resolvedModule.tables.localVarsMeta))) `shouldBe` Right True

  test "a constant parameter pattern does not hide later duplicate parameters" $
    duplicateBinder "const U: () = (); fn f(U: (), x: i32, x: i32) {}"
      `shouldBe` Right ("x", (1, 39, 1, 40), (1, 31, 1, 32))

  test "a constant pattern between duplicate binders does not hide the duplicate" $
    duplicateBinder "const U: () = (); fn f() { let (x, U, x) = (1, (), 2); }"
      `shouldBe` Right ("x", (1, 39, 1, 40), (1, 33, 1, 34))

  test "a binder repeated three times reports the first repetition" $
    duplicateBinder "fn f() { let (x, x, x) = (1, 2, 3); }"
      `shouldBe` Right ("x", (1, 18, 1, 19), (1, 15, 1, 16))

  test "a repeat count in a constant initializer cannot use the initializer's local" $
    nonConstantUse "const C: i32 = { let x = 1; [0; x]; 2 };"
      `shouldBe` Right ("x", (1, 33, 1, 34), (1, 22, 1, 23))

  test "a constant initializer block may use its own locals" $
    checkSource "const C: i32 = { let x = 1; x };" valueReferenceKinds
      `shouldBe` Right [("x", "local")]

  test "a local inside a repeat count may shadow an outer parameter" $
    checkSource "fn f(n: i32) { [0; { let n = 1; n }]; }" valueReferenceKinds
      `shouldBe` Right [("n", "local")]

  test "a local initializer inside a repeat count cannot use an outer parameter" $
    nonConstantUse "fn f(n: i32) { [0; { let k = n; k }]; }"
      `shouldBe` Right ("n", (1, 30, 1, 31), (1, 6, 1, 7))

  test "a parameter shadows a module function inside the return type" $
    nonConstantUse "const fn n() -> i32 { 2 }\nfn f(n: i32) -> [i32; n()] {}"
      `shouldBe` Right ("n", (2, 23, 2, 24), (2, 6, 2, 7))

  -- A qalloc count is a constant context, like an array length or repeat count.
  test "a qalloc count cannot use an outer parameter" $
    nonConstantUse "fn f(n: usize) { let qs = qalloc(n); }"
      `shouldBe` Right ("n", (1, 34, 1, 35), (1, 6, 1, 7))

  test "a qalloc count may use a top-level constant" $
    checkSource "const N: usize = 2; fn f() { let qs = qalloc(N); }" valueReferenceKinds
      `shouldBe` Right [("N", "constant")]

  test "a qalloc count may use a local it declares itself" $
    checkSource "fn f() { let qs = qalloc({ let k = 2; k }); }" valueReferenceKinds
      `shouldBe` Right [("k", "local")]

  test "a local initializer inside a qalloc count cannot use an outer parameter" $
    nonConstantUse "fn f(n: usize) { let qs = qalloc({ let k = n; k }); }"
      `shouldBe` Right ("n", (1, 44, 1, 45), (1, 6, 1, 7))

  test "a local inside a qalloc count may shadow an outer parameter" $
    checkSource "fn f(n: usize) { let qs = qalloc({ let n = 2; n }); }" valueReferenceKinds
      `shouldBe` Right [("n", "local")]

  test "a parameter shadows a module function inside a qalloc count" $
    nonConstantUse "const fn n() -> usize { 2 } fn f(n: usize) { let qs = qalloc(n()); }"
      `shouldBe` Right ("n", (1, 62, 1, 63), (1, 34, 1, 35))

  test "leaving a qalloc count restores ordinary parameter access" $
    checkSource "fn g(qs: [qbit; 2], n: usize) {} fn f(n: usize) { g(qalloc(2), n); n; }" (\resolvedModule => do
      kinds <- valueReferenceKinds resolvedModule
      pure (kinds, isNothing resolvedModule.tables.constContextBoundary))
      `shouldBe` Right ([("g", "function"), ("n", "parameter"), ("n", "parameter")], True)

  -- Leaf has no type declarations yet, so every written type path is unresolved.
  test "a simple type path in a parameter type is unresolved" $
    unresolvedTypePath "fn f(person: Person) {}"
      `shouldBe` Right ("Person", (1, 14, 1, 20))

  test "a simple type path in a return type is unresolved" $
    unresolvedTypePath "fn f() -> Person {}"
      `shouldBe` Right ("Person", (1, 11, 1, 17))

  test "a simple type path in a local annotation is unresolved" $
    unresolvedTypePath "fn f() { let person: Person; }"
      `shouldBe` Right ("Person", (1, 22, 1, 28))

  test "a simple type path in a cast target is unresolved" $
    unresolvedTypePath "fn f(x: i32) { x as Person; }"
      `shouldBe` Right ("Person", (1, 21, 1, 27))

  test "a qualified type path in a parameter type is unresolved" $
    unresolvedTypePath "fn f(person: my_module::Config) {}"
      `shouldBe` Right ("my_module::Config", (1, 14, 1, 31))

  test "a qualified type path in a return type is unresolved" $
    unresolvedTypePath "fn f() -> my_module::Config {}"
      `shouldBe` Right ("my_module::Config", (1, 11, 1, 28))

  test "a qualified type path in a local annotation is unresolved" $
    unresolvedTypePath "fn f() { let person: my_module::Config; }"
      `shouldBe` Right ("my_module::Config", (1, 22, 1, 39))

  test "a qualified type path in a cast target is unresolved" $
    unresolvedTypePath "fn f(x: i32) { x as my_module::Config; }"
      `shouldBe` Right ("my_module::Config", (1, 21, 1, 38))

  -- As in Rust (E0070), assigning to a constant or function is a type error,
  -- not a resolution error: the target resolves to that item.
  test "assignment targets may resolve to constants and functions" $
    checkSource "const N: i32 = 1; fn g() {} fn f() { N = 2; g = 3; }" (\resolvedModule => do
      (_, constDeclaration) <- constantNamed "N" resolvedModule
      (_, functionG) <- functionNamed "g" resolvedModule
      (_, functionF) <- functionNamed "f" resolvedModule
      constantAssignment <- assignmentAt 0 functionF.functionBody
      functionAssignment <- assignmentAt 1 functionF.functionBody
      AssignTargetName constantTarget <- pure constantAssignment.assignmentTarget.nodeValue | _ => Nothing
      AssignTargetName functionTarget <- pure functionAssignment.assignmentTarget.nodeValue | _ => Nothing
      pure (symbolId constantTarget == symbolId constDeclaration.constName &&
            symbolId functionTarget == symbolId functionG.functionName &&
            referenceMatches resolvedModule AssignmentTarget constantAssignment.assignmentTarget.astInfo.nodeId constantTarget &&
            referenceMatches resolvedModule AssignmentTarget functionAssignment.assignmentTarget.astInfo.nodeId functionTarget &&
            null (SortedMap.toList resolvedModule.tables.localVarsMeta))) `shouldBe` Right True
