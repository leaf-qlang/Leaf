module ScopeAndNameResolution.ResolveTestHelper

import Compiler.Frontend.ScopeAndNameResolver.Data
import Compiler.Frontend.ASTData
import Compiler.Frontend.ASTPhases
import Compiler.Frontend.Source
import Compiler.Frontend.Syntax.AST
import Compiler.Frontend.Syntax.Attribute
import Compiler.Frontend.Syntax.Common
import Compiler.Frontend.Syntax.Contract
import Compiler.Frontend.Syntax.Doc
import Compiler.Frontend.Syntax.Name
import Compiler.Frontend.Syntax.Pattern
import Compiler.Frontend.Syntax.Type
import ScopeAndNameResolution.Helper

import Data.List
import Data.List1
import Data.Maybe
import Data.SnocList
import Data.SortedMap

%default total

export
elementAt : Nat -> List a -> Maybe a
elementAt _ [] = Nothing
elementAt Z (element :: _) = Just element
elementAt (S remainingIndex) (_ :: remainingElements) = elementAt remainingIndex remainingElements

export
functionNamed : String -> ResolvedModule -> Maybe (AstInfo, FunctionDeclarationNode ResolvedAstPhase)
functionNamed functionNameText resolvedModule =
  let MkSourceFileNode _ sourceFileItems = resolvedModule.ast.nodeValue
  in head' (mapMaybe matchingFunction sourceFileItems)
  where
    matchingFunction : ResolvedItem -> Maybe (AstInfo, FunctionDeclarationNode ResolvedAstPhase)
    matchingFunction (MkAstNode itemInfo _ (ItemFunction functionDeclaration)) =
      if functionDeclaration.functionName.nodeValue.nameNodeText == functionNameText then Just (itemInfo, functionDeclaration) else Nothing
    matchingFunction _ = Nothing

export
constantNamed : String -> ResolvedModule -> Maybe (AstInfo, ConstDeclarationNode ResolvedAstPhase)
constantNamed constantNameText resolvedModule =
  let MkSourceFileNode _ sourceFileItems = resolvedModule.ast.nodeValue
  in head' (mapMaybe matchingConstant sourceFileItems)
  where
    matchingConstant : ResolvedItem -> Maybe (AstInfo, ConstDeclarationNode ResolvedAstPhase)
    matchingConstant (MkAstNode itemInfo _ (ItemConst constDeclaration)) =
      if constDeclaration.constName.nodeValue.nameNodeText == constantNameText then Just (itemInfo, constDeclaration) else Nothing
    matchingConstant _ = Nothing

export
letAt : Nat -> ResolvedBlock -> Maybe (LetBindingNode ResolvedAstPhase)
letAt index block = do
  statement <- elementAt index block.nodeValue.blockStatements
  case statement.nodeValue of
    StatementLet binding => Just binding
    _ => Nothing

export
exprAt : Nat -> ResolvedBlock -> Maybe ResolvedExpr
exprAt index block = do
  statement <- elementAt index block.nodeValue.blockStatements
  case statement.nodeValue of
    StatementSemiExpression expression => Just expression
    StatementExpression expression => Just expression
    _ => Nothing

-- The value returned by the statement at `index`. Desugaring turns a function
-- body's final expression into such a `return` statement.
export
returnedAt : Nat -> ResolvedBlock -> Maybe ResolvedExpr
returnedAt index block = do
  MkAstNode _ _ (ExprReturn (Just returnValue)) <- exprAt index block
    | _ => Nothing
  Just returnValue

export
binder : ResolvedPattern -> Maybe ResolvedName
binder (MkAstNode _ _ (PatternName _ binderName)) = Just binderName
binder _ = Nothing

nameUse : ResolvedExpr -> Maybe ResolvedName
nameUse (MkAstNode _ _ (ExprName usedName)) = Just usedName
nameUse _ = Nothing

export
initializer : LetBindingNode ResolvedAstPhase -> Maybe ResolvedExpr
initializer binding = map (.initializerValue) binding.letInitializer

export
symbolId : ResolvedName -> SymbolId
symbolId resolvedName = resolvedName.nodeValue.nameNodeSymbolId

export
scopeFor : ResolvedModule -> AstNode ResolvedAstPhase a -> Maybe ScopeInfo
scopeFor resolvedModule astNode = do
  scopeId <- lookup astNode.astInfo.nodeId resolvedModule.scopeTables.nodeScopes
  lookup scopeId resolvedModule.scopeTables.scopes

sameRole : ReferenceRole -> ReferenceRole -> Bool
sameRole DeclarationReference DeclarationReference = True
sameRole ValueReference ValueReference = True
sameRole AssignmentTarget AssignmentTarget = True
sameRole PatternReference PatternReference = True
sameRole _ _ = False

-- Compare each occurrence, role and context with its unique reference entry.
-- A compound assignment retains its operator and has one target occurrence;
-- its read-modify-write behavior is represented by the operator, not a copied name.
-- This catches missing references, wrong targets/roles/contexts and lost spans.
export
referenceMatches : ResolvedModule -> ReferenceRole -> NodeId -> ResolvedName -> Bool
referenceMatches resolvedModule expectedRole contextNode occurrenceName =
  case filter (\reference => reference.occurrence.nodeId == occurrenceName.astInfo.nodeId &&
                       sameRole reference.role expectedRole && reference.contextNode == contextNode) (allReferences resolvedModule) of
    [reference] => reference.target == symbolId occurrenceName && sameRole reference.role expectedRole &&
             reference.contextNode == contextNode && reference.writtenName == occurrenceName.nodeValue.nameNodeText &&
             spanKey reference.occurrence.span == spanKey occurrenceName.astInfo.span &&
             lookup occurrenceName.astInfo.nodeId resolvedModule.scopeTables.nodeScopes == Just reference.enclosingScope &&
             lookup contextNode resolvedModule.scopeTables.nodeScopes == Just reference.enclosingScope
    _ => False

-- Constants in patterns reference an existing symbol and introduce neither a
-- local binding nor local-variable metadata in the occurrence's scope.
export
constantOccurrenceMatches : ResolvedModule -> ResolvedName -> NodeId -> ResolvedName -> Bool
constantOccurrenceMatches resolvedModule constantName contextNode occurrenceName =
  case scopeFor resolvedModule occurrenceName of
    Nothing => False
    Just occurrenceScope =>
      symbolId occurrenceName == symbolId constantName &&
      referenceMatches resolvedModule PatternReference contextNode occurrenceName &&
      isNothing (lookup (symbolId occurrenceName) resolvedModule.scopeTables.localVarsMeta) &&
      isNothing (lookup occurrenceName.nodeValue.nameNodeText occurrenceScope.valueBindings) &&
      not (elem (symbolId occurrenceName) (occurrenceScope.declaredSymbolsInOrder <>> []))

export
constantPatternMatches : ResolvedModule -> ResolvedName -> ResolvedPattern -> Bool
constantPatternMatches resolvedModule constantName pattern = case pattern.nodeValue of
  PatternPath constantPath =>
    let occurrenceName = MkAstNode constantPath.astInfo constantPath.metadata
                 (MkResolvedNameNode constantPath.nodeValue.firstPathSegmentText constantPath.nodeValue.referencedSymbolId)
    in constantPath.nodeValue.remainingPathSegmentTexts == [] &&
       constantPath.nodeValue.firstPathSegmentText == constantName.nodeValue.nameNodeText &&
       constantOccurrenceMatches resolvedModule constantName pattern.astInfo.nodeId occurrenceName
  _ => False

export
useMatches : ResolvedModule -> ResolvedName -> ResolvedExpr -> Maybe Bool
useMatches resolvedModule declaredName expression = do
  usedName <- nameUse expression
  pure (symbolId usedName == symbolId declaredName &&
        referenceMatches resolvedModule ValueReference expression.astInfo.nodeId usedName)

export
bindingMatches : ScopeInfo -> ResolvedName -> Bool
bindingMatches scopeInfo declaredName = case lookup declaredName.nodeValue.nameNodeText scopeInfo.valueBindings of
  Nothing => False
  Just scopeBinding => scopeBinding.target == symbolId declaredName &&
    scopeBinding.writtenName == declaredName.nodeValue.nameNodeText &&
    map spanKey scopeBinding.introducedAt == Just (spanKey declaredName.astInfo.span) &&
    (case scopeBinding.bindingKind of DeclaredBinding => True; _ => False) &&
    (case scopeBinding.bindingVisibility of LexicalVisibility => True; _ => False)

export
localMatches : ResolvedModule -> ResolvedName -> Bool -> Bool
localMatches resolvedModule localName expectedMutable = case lookup (symbolId localName) resolvedModule.scopeTables.localVarsMeta of
  Just (MkLocalVarQualifiers actualMutability ()) =>
    case actualMutability of
      MutableVariable => expectedMutable
      ImmutableVariable => not expectedMutable
  _ => False

export
symbolMatches : ResolvedModule -> ResolvedName -> ScopeId -> String -> AstInfo -> Bool
symbolMatches resolvedModule declaredName expectedScope expectedKindText expectedOrigin =
  case lookup (symbolId declaredName) resolvedModule.scopeTables.symbols of
    Nothing => False
    Just symbolInfo => symbolInfo.symbolId == symbolId declaredName &&
      symbolInfo.declaredName == declaredName.nodeValue.nameNodeText &&
      symbolInfo.declaringScope == expectedScope && symbolInfo.declaringModule == resolvedModule.rootSymbolId &&
      kindText symbolInfo.symbolKind == expectedKindText &&
      (case symbolInfo.origin of
         SourceSymbol originInfo => originInfo.nodeId == expectedOrigin.nodeId && spanKey originInfo.span == spanKey expectedOrigin.span
         _ => False)

export
isBlock : ScopeInfo -> Bool
isBlock scopeInfo = case scopeInfo.kind of BlockScope => True; _ => False

-- Every block scope must be the scope recorded for its own AST node. This
-- also detects duplicated scope creation for blocks that contain no names.
export
blockScopesMatchNodes : ResolvedModule -> Bool
blockScopesMatchNodes resolvedModule = all blockScopeMatchesNode (SortedMap.toList resolvedModule.scopeTables.scopes)
  where
    blockScopeMatchesNode : (ScopeId, ScopeInfo) -> Bool
    blockScopeMatchesNode (scopeId, scopeInfo) = case (scopeInfo.kind, scopeInfo.origin) of
      (BlockScope, SourceScope originInfo) =>
        lookup originInfo.nodeId resolvedModule.scopeTables.nodeScopes == Just scopeId
      _ => True

export
patternBinders : ResolvedPattern -> List (ResolvedPattern, ResolvedName)
patternBinders pattern@(MkAstNode _ _ patternNode) = case patternNode of
  PatternName _ binderName => [(pattern, binderName)]
  PatternTuple elementPatterns => concatMap recur (forget elementPatterns)
  PatternArray elementPatterns => concatMap recur elementPatterns
  _ => []
  where
    recur : ResolvedPattern -> List (ResolvedPattern, ResolvedName)
    recur nestedPattern = patternBinders (assert_smaller patternNode nestedPattern)

export
blockBody : ResolvedExpr -> Maybe ResolvedBlock
blockBody (MkAstNode _ _ expressionNode) = case expressionNode of
  ExprBlock block => Just block
  ExprLoop block => Just block
  ExprWhile _ block => Just block
  ExprCtrl (ControlledBlock _ _ block) => Just block
  ExprAdjoint (AdjointBlock block) => Just block
  _ => Nothing

-- Shared semantic assertion for constructs that introduce an ordinary block.
export
blockIsolation : String -> Either String Bool
blockIsolation blockConstruct = checkSource
  ("fn f(q: qbit) { " ++ blockConstruct ++ " { let inner = 1; inner; } q; }") $ \resolvedModule => do
    (_, functionDeclaration) <- functionNamed "f" resolvedModule
    [MkAstNode _ _ (NormalParameter _ _ qbitParameter _)] <- pure functionDeclaration.functionParameters
      | _ => Nothing
    outerScope <- scopeFor resolvedModule functionDeclaration.functionBody
    constructExpression <- exprAt 0 functionDeclaration.functionBody
    constructScope <- scopeFor resolvedModule constructExpression
    constructBlock <- blockBody constructExpression
    innerScope <- scopeFor resolvedModule constructBlock
    innerBinding <- letAt 0 constructBlock
    innerName <- binder innerBinding.letPattern
    innerUse <- exprAt 1 constructBlock
    afterExpression <- exprAt 1 functionDeclaration.functionBody
    innerUse <- useMatches resolvedModule innerName innerUse
    afterUse <- useMatches resolvedModule qbitParameter afterExpression
    pure (isBlock innerScope && innerScope.id /= outerScope.id && innerScope.parent == Just outerScope.id &&
          constructScope.id == outerScope.id && bindingMatches innerScope innerName &&
          isNothing (lookup "inner" outerScope.valueBindings) && innerUse && afterUse)

-- The parser currently sets the filename on the source-file node only.
-- Check diagnostic coordinates independently; referenceMatches above checks
-- that the full incoming AST span is preserved in the reference table.
export
coordinates : SourceSpan -> (Nat, Nat, Nat, Nat)
coordinates sourceSpan = (sourceSpan.start.line, sourceSpan.start.column, sourceSpan.end.line, sourceSpan.end.column)

export
unresolved : String -> String -> Either String Bool
unresolved sourceText expectedName = map (== expectedName) (expectUnresolvedName sourceText)

export
nodeHasScope : ResolvedModule -> ScopeId -> AstNode ResolvedAstPhase a -> Bool
nodeHasScope resolvedModule expectedScope astNode = lookup astNode.astInfo.nodeId resolvedModule.scopeTables.nodeScopes == Just expectedScope

export
parameterNames : FunctionDeclarationNode ResolvedAstPhase -> Maybe (List ResolvedName)
parameterNames functionDeclaration = traverse normalParameterName functionDeclaration.functionParameters
  where
    normalParameterName : AstNode ResolvedAstPhase (FunctionParameterNode ResolvedAstPhase) -> Maybe ResolvedName
    normalParameterName (MkAstNode _ _ (NormalParameter _ _ parameterNameNode _)) = Just parameterNameNode
    normalParameterName _ = Nothing

export
assignmentAt : Nat -> ResolvedBlock -> Maybe (AssignmentNode ResolvedAstPhase)
assignmentAt index block = do
  statement <- elementAt index block.nodeValue.blockStatements
  case statement.nodeValue of
    StatementAssignment assignment => Just assignment
    _ => Nothing

export
usesInScope : ResolvedModule -> ScopeId -> List (ResolvedName, ResolvedExpr) -> Maybe Bool
usesInScope resolvedModule expectedScope expectedUses = do
  useMatchResults <- traverse (\(declaredName, expression) => useMatches resolvedModule declaredName expression) expectedUses
  pure (all id useMatchResults && all (\(_, expression) => nodeHasScope resolvedModule expectedScope expression) expectedUses)

-- The test supplies the expected name occurrences explicitly; this helper
-- does not discover them by traversing the same expression cases as Resolve.
export
expressionUses : String -> List String -> (ResolvedExpr -> Maybe (List ResolvedExpr)) -> Either String Bool
expressionUses expressionText expectedNameTexts selectUses = checkSource
  ("const N: i32 = 2; fn g(x: i32, n: i32) {} fn f(a: [i32; 2], i: i32, x: i32, n: i32, pair: (i32, i32)) { " ++
   expressionText ++ "; }") $ \resolvedModule => do
    (_, constDeclaration) <- constantNamed "N" resolvedModule
    (_, functionG) <- functionNamed "g" resolvedModule
    (_, functionF) <- functionNamed "f" resolvedModule
    parameterNameNodes <- parameterNames functionF
    let declarations = SortedMap.fromList $ map (\nameNode => (nameNode.nodeValue.nameNodeText, nameNode))
                                     (constDeclaration.constName :: functionG.functionName :: parameterNameNodes)
    expectedDeclarations <- traverse (\nameText => SortedMap.lookup nameText declarations) expectedNameTexts
    bodyExpression <- exprAt 0 functionF.functionBody
    uses <- selectUses bodyExpression
    usedNames <- traverse nameUse uses
    bodyScope <- scopeFor resolvedModule functionF.functionBody
    usesMatch <- usesInScope resolvedModule bodyScope.id (zip expectedDeclarations uses)
    pure (length uses == length expectedNameTexts && usesMatch && nodeHasScope resolvedModule bodyScope.id bodyExpression &&
          map (\reference => reference.occurrence.nodeId) (valueReferences resolvedModule) == map (\nameNode => nameNode.astInfo.nodeId) usedNames)

-- Compare the complete occurrence inventory as well as each reference's
-- contents, so omitted entries and additional entries both fail the assertion.
export
referenceInventory : ResolvedModule -> List (ReferenceRole, NodeId, ResolvedName) -> Bool
referenceInventory resolvedModule expectedReferences =
  let buckets = SortedMap.toList resolvedModule.scopeTables.references
      actualOccurrences = concatMap (\(bucketKey, bucketReferences) => map (\reference => (bucketKey, reference.occurrence.nodeId)) (bucketReferences <>> [])) buckets
  in map fst buckets == sort (nub (map (\(_, _, occurrenceName) => symbolId occurrenceName) expectedReferences)) &&
     sort actualOccurrences == sort (map (\(_, _, occurrenceName) => (symbolId occurrenceName, occurrenceName.astInfo.nodeId)) expectedReferences) &&
     all (\(expectedRole, contextNode, occurrenceName) => referenceMatches resolvedModule expectedRole contextNode occurrenceName) expectedReferences

export
valueReferenceOccurrence : ResolvedExpr -> Maybe (ReferenceRole, NodeId, ResolvedName)
valueReferenceOccurrence nameExpression = do
  usedName <- nameUse nameExpression
  pure (ValueReference, nameExpression.astInfo.nodeId, usedName)

export
sourceSymbols : ResolvedModule -> List ResolvedSymbolInfo
sourceSymbols resolvedModule = filter fromSource (map snd (SortedMap.toList resolvedModule.scopeTables.symbols))
  where
    fromSource : ResolvedSymbolInfo -> Bool
    fromSource symbolInfo = case symbolInfo.origin of SourceSymbol _ => True; _ => False

-- The parser currently accepts only a bare identifier after `for`. For richer
-- resolver fixtures, move the first let's already parsed pattern into the
-- following loop, then remove that let. Its node IDs and diagnostic positions
-- are retained, and the resulting AST contains each node only once.
moveLetPatternToFor : SourceFile CanonicalAstPhase -> Maybe (SourceFile CanonicalAstPhase)
moveLetPatternToFor sourceFile = do
  let MkSourceFileNode fileDocs sourceFileItems = sourceFile.nodeValue
  adjustedItems <- traverse moveInFunction sourceFileItems
  pure ({ nodeValue := MkSourceFileNode fileDocs adjustedItems } sourceFile)
  where
    replaceLoopPattern : CanonicalPattern -> CanonicalExpr -> Maybe CanonicalExpr
    replaceLoopPattern pattern expression = case expression.nodeValue of
      ExprFor _ iterable loopBody => Just ({ nodeValue := ExprFor pattern iterable loopBody } expression)
      _ => Nothing

    -- A loop that ends the function body was desugared into its `return` statement.
    replaceExpression : CanonicalPattern -> CanonicalExpr -> Maybe CanonicalExpr
    replaceExpression pattern expression = case expression.nodeValue of
      ExprReturn (Just returnValue) => do
        returnValue <- replaceLoopPattern pattern returnValue
        pure ({ nodeValue := ExprReturn (Just returnValue) } expression)
      _ => replaceLoopPattern pattern expression

    replaceStatement : CanonicalPattern -> Statement CanonicalAstPhase -> Maybe (Statement CanonicalAstPhase)
    replaceStatement pattern statement = case statement.nodeValue of
      StatementExpression expression => do
        expression <- replaceExpression pattern expression
        pure ({ nodeValue := StatementExpression expression } statement)
      StatementSemiExpression expression => do
        expression <- replaceExpression pattern expression
        pure ({ nodeValue := StatementSemiExpression expression } statement)
      _ => Nothing

    moveInFunction : Item CanonicalAstPhase -> Maybe (Item CanonicalAstPhase)
    moveInFunction item = case item.nodeValue of
      ItemFunction functionDeclaration => do
        letStatement :: loopStatement :: remainingStatements <- pure functionDeclaration.functionBody.nodeValue.blockStatements | _ => Nothing
        StatementLet letBinding <- pure letStatement.nodeValue | _ => Nothing
        adjustedLoopStatement <- replaceStatement letBinding.letPattern loopStatement
        let adjustedFunctionBody : CanonicalBlock =
              { nodeValue := { blockStatements := adjustedLoopStatement :: remainingStatements } functionDeclaration.functionBody.nodeValue } functionDeclaration.functionBody
        pure ({ nodeValue := ItemFunction ({ functionBody := adjustedFunctionBody } functionDeclaration) } item)
      _ => Just item

withForPattern : String -> (Either FixtureError ResolvedModule -> Either String a) -> Either String a
withForPattern sourceText inspect = do
  canonicalSourceFile <- either (Left . show) Right (canonicalSource sourceText)
  adjustedSourceFile <- case moveLetPatternToFor canonicalSourceFile of
    Nothing => Left "Expected a let pattern followed by a for loop in the canonical fixture"
    Just adjustedSourceFile => Right adjustedSourceFile
  inspect (resolveCanonicalSource adjustedSourceFile)

export
checkForPattern : String -> (ResolvedModule -> Maybe a) -> Either String a
checkForPattern sourceText inspect = withForPattern sourceText $ \resolutionResult => case resolutionResult of
  Left fixtureError => Left (show fixtureError)
  Right resolvedModule => case inspect resolvedModule of
    Nothing => Left "Unexpected resolved for-pattern fixture or missing table entry"
    Just inspectedValue => Right inspectedValue

-- Resolve a matching single declaration to obtain the expected conflicting
-- SymbolId without depending on how many synthetic Prelude symbols exist.
export
duplicateDeclaration : String -> String -> String -> (Nat, Nat, Nat, Nat) -> Either String Bool
duplicateDeclaration firstSource secondSource declaredName expectedSpan = do
  expectedConflict <- checkSource firstSource $ \resolvedModule => do
    rootScope <- lookup resolvedModule.rootScopeId resolvedModule.scopeTables.scopes
    rootBinding <- lookup declaredName rootScope.valueBindings
    previousSpan <- rootBinding.introducedAt
    pure (rootBinding.target, spanKey previousSpan)
  case resolveSource (firstSource ++ "\n" ++ secondSource) of
    Left (ResolutionFailure (DuplicateDeclaration reportedName conflictingSymbols duplicateSpan previousSpan)) =>
      Right (reportedName == declaredName && conflictingSymbols == [fst expectedConflict] && coordinates duplicateSpan == expectedSpan &&
             duplicateSpan.file == previousSpan.file && spanKey previousSpan == snd expectedConflict)
    Left fixtureError => Left (show fixtureError)
    Right _ => Left "Expected DuplicateDeclaration, but resolution succeeded"

-- Duplicate binders are a resolution error, whereas repeated constant pattern
-- occurrences are legal and must not be rejected by post-parse validation.
export
duplicateBinder : String -> Either String (String, (Nat, Nat, Nat, Nat), (Nat, Nat, Nat, Nat))
duplicateBinder sourceText = case resolveSource sourceText of
  Left (ResolutionFailure (DuplicateDeclaration reportedName [_] currentSpan previousSpan)) =>
    Right (reportedName, coordinates currentSpan, coordinates previousSpan)
  Left fixtureError => Left (show fixtureError)
  Right _ => Left "Expected DuplicateDeclaration, but resolution succeeded"

export
duplicateForBinder : String -> Either String (String, (Nat, Nat, Nat, Nat), (Nat, Nat, Nat, Nat))
duplicateForBinder sourceText = withForPattern sourceText $ \resolutionResult => case resolutionResult of
  Left (ResolutionFailure (DuplicateDeclaration reportedName [_] currentSpan previousSpan)) =>
    Right (reportedName, coordinates currentSpan, coordinates previousSpan)
  Left fixtureError => Left (show fixtureError)
  Right _ => Left "Expected DuplicateDeclaration, but resolution succeeded"

-- Returns the name and the binder and constant coordinates of the expected
-- BindingShadowsConstant diagnostic.
export
constantShadowing : String -> Either String (String, (Nat, Nat, Nat, Nat), (Nat, Nat, Nat, Nat))
constantShadowing sourceText = case resolveSource sourceText of
  Left (ResolutionFailure (BindingShadowsConstant reportedName _ binderSpan constantSpan)) =>
    Right (reportedName, coordinates binderSpan, coordinates constantSpan)
  Left fixtureError => Left (show fixtureError)
  Right _ => Left "Expected BindingShadowsConstant, but resolution succeeded"

export
forConstantShadowing : String -> Either String (String, (Nat, Nat, Nat, Nat), (Nat, Nat, Nat, Nat))
forConstantShadowing sourceText = withForPattern sourceText $ \resolutionResult => case resolutionResult of
  Left (ResolutionFailure (BindingShadowsConstant reportedName _ binderSpan constantSpan)) =>
    Right (reportedName, coordinates binderSpan, coordinates constantSpan)
  Left fixtureError => Left (show fixtureError)
  Right _ => Left "Expected BindingShadowsConstant, but resolution succeeded"

-- Returns the name and the use and local declaration coordinates of the
-- expected LocalValueUsedAsConstant diagnostic.
export
nonConstantUse : String -> Either String (String, (Nat, Nat, Nat, Nat), (Nat, Nat, Nat, Nat))
nonConstantUse sourceText = case resolveSource sourceText of
  Left (ResolutionFailure (LocalValueUsedAsConstant reportedName _ useSpan localSpan)) =>
    Right (reportedName, coordinates useSpan, coordinates localSpan)
  Left fixtureError => Left (show fixtureError)
  Right _ => Left "Expected LocalValueUsedAsConstant, but resolution succeeded"

-- Returns the written type path and coordinates of the expected
-- UnresolvedTypePath diagnostic.
export
unresolvedTypePath : String -> Either String (String, (Nat, Nat, Nat, Nat))
unresolvedTypePath sourceText = case resolveSource sourceText of
  Left (ResolutionFailure (UnresolvedTypePath typePathText typePathSpan)) =>
    Right (typePathText, coordinates typePathSpan)
  Left fixtureError => Left (show fixtureError)
  Right _ => Left "Expected UnresolvedTypePath, but resolution succeeded"

-- Every value reference resolves to a symbol with the given kind, in source order.
export
valueReferenceKinds : ResolvedModule -> Maybe (List (String, String))
valueReferenceKinds resolvedModule = traverse describeReferenceTarget (valueReferences resolvedModule)
  where
    describeReferenceTarget : SymbolReference -> Maybe (String, String)
    describeReferenceTarget reference = do
      targetSymbol <- lookup reference.target resolvedModule.scopeTables.symbols
      pure (reference.writtenName, kindText targetSymbol.symbolKind)
