module Compiler.Frontend.ScopeAndNameResolver.Resolve

import Compiler.Helper
import Control.Monad.State
import Compiler.Frontend.Prelude
import Compiler.Frontend.TypeChecker.Data
import Compiler.Frontend.ScopeAndNameResolver.Data
import Compiler.Frontend.ScopeAndNameResolver.Helper
import Data.List
import Data.List1
import Data.Maybe
import Data.SnocList
import Data.SortedMap
import Compiler.Frontend.ASTData
import Compiler.Frontend.ASTPhases
import Compiler.Frontend.Source
import Compiler.Frontend.Syntax.Attribute
import Compiler.Frontend.Syntax.AST
import Compiler.Frontend.Syntax.Contract
import Compiler.Frontend.Syntax.Common
import Compiler.Frontend.Syntax.Doc
import Compiler.Frontend.Syntax.Literal
import Compiler.Frontend.Syntax.Name
import Compiler.Frontend.Syntax.Operator
import Compiler.Frontend.Syntax.Pattern
import Compiler.Frontend.Syntax.Type
import Compiler.Frontend.Token

%default total

resolveNode : AstInfo -> ProvenanceMetadata -> a -> ResolvedAstNode a
resolveNode astInfo (MkProvenanceMetadata provenance) = resolvedAstNode astInfo provenance

resolveAstNode : {a : Type} -> AstNode CanonicalAstPhase a -> AstNode ResolvedAstPhase a
resolveAstNode (MkAstNode astInfo metadata nodeValue) = resolveNode astInfo metadata nodeValue

visibleConstantBinding : String -> ScopeTables -> Maybe ScopeBinding
visibleConstantBinding nameText scopeTables =
  case retrieveSymbolBinding nameText scopeTables of
    Binding scopeBinding => case map (.symbolKind) (lookup scopeBinding.target scopeTables.symbols) of
      Just SymbolConstant => Just scopeBinding
      _ => Nothing
    _ => Nothing

rejectConstantShadowing : String -> SourceSpan -> StateT ScopeTables (Either ResolutionError) ()
rejectConstantShadowing nameText binderSpan = do
  scopeTables <- get
  case visibleConstantBinding nameText scopeTables of
    Just constantBinding => case constantBinding.introducedAt of
      Just constantDeclarationSpan =>
        lift $ Left $ BindingShadowsConstant nameText constantBinding.target binderSpan constantDeclarationSpan
      -- Constants are only declared from source, which always records the name span.
      Nothing => unreachable __FILE__ {function = "rejectConstantShadowing"} {reason = "constant binding has no introduction span"}
    Nothing => pure ()

rejectLocalNameUsedInConstantRole : String -> SourceSpan -> ScopeBinding -> StateT ScopeTables (Either ResolutionError) ()
rejectLocalNameUsedInConstantRole nameText useSpan nameBinding = do
  scopeTables <- get
  case (scopeTables.constContextBoundary, lookup nameBinding.target scopeTables.symbols) of
    (Just constContextBoundary, Just boundSymbolInfo) =>
      if isLocalSymbolKind boundSymbolInfo.symbolKind && isScopeOrAncestor boundSymbolInfo.declaringScope constContextBoundary scopeTables
        then case nameBinding.introducedAt of
          Just localDeclarationSpan =>
            lift $ Left $ LocalValueUsedAsConstant nameText nameBinding.target useSpan localDeclarationSpan
          -- Locals and parameters are only declared from source, which always records the name span.
          Nothing => unreachable __FILE__ {function = "rejectLocalNameUsedInConstantRole"} {reason = "local binding has no introduction span"}
        else pure ()
    _ => pure ()

-- Resolves an (array length/array repeat count/qalloc register allocation size) argument with restoring any enclosing context afterwards.
withConstContext : StateT ScopeTables (Either ResolutionError) a -> StateT ScopeTables (Either ResolutionError) a
withConstContext resolveConstant = do
  scopeTables <- get
  let enclosingConstContextBoundary = scopeTables.constContextBoundary
  put $ { constContextBoundary := Just scopeTables.currentScopeId } scopeTables
  resolvedConstant <- resolveConstant
  modify $ \tablesAfterConstant => { constContextBoundary := enclosingConstContextBoundary } tablesAfterConstant
  pure resolvedConstant

-- Runs an action inside a new child scope of the current scope, restoring the
-- enclosing scope and scope kind afterwards.
withChildScope : ScopeKind -> ScopeOrigin -> StateT ScopeTables (Either ResolutionError) a -> StateT ScopeTables (Either ResolutionError) a
withChildScope childScopeKind childScopeOrigin resolveInChildScope = do
  scopeTables <- get
  let enclosingScopeId = scopeTables.currentScopeId
  let enclosingScopeKind = scopeTables.currentScopeKind
  let childScopeId = scopeTables.nextScopeId
  let childScopeInfo = MkScopeInfo
        childScopeId
        childScopeKind
        (Just enclosingScopeId)
        childScopeOrigin
        empty empty empty [<]
  put $
    {
      currentScopeId := childScopeId,
      currentScopeKind := childScopeKind,
      scopes := insert childScopeId childScopeInfo scopeTables.scopes
    } scopeTables
  childScopeResult <- resolveInChildScope
  modify $ \tablesAfterChildScope =>
    {
      currentScopeId := enclosingScopeId,
      currentScopeKind := enclosingScopeKind
    } tablesAfterChildScope
  pure childScopeResult

-- Declares a let/for binder or a function parameter in the current scope.
-- Callers must first go through resolveConstantPatternName: an immutable bare
-- constant name is a constant pattern, not a declaration. Reaching this with a
-- visible constant is therefore always an error.
declareLocalName : SymbolKind
  -> (contextNode : NodeId)
  -> (bindingMutability : Maybe Mutability)
  -> CanonicalName
  -> StateT ScopeTables (Either ResolutionError) ResolvedName
declareLocalName symbolKind contextNode bindingMutability
    (MkAstNode nameInfo metadata (MkNameNode nameText)) = do
  rejectConstantShadowing nameText nameInfo.span
  recordNodeScope nameInfo.nodeId
  scopeTables <- get
  let symbolId = scopeTables.nextSymbolId
  let symbolInfo = MkSymbolInfo
        symbolId
        symbolKind
        ()
        nameText
        scopeTables.currentScopeId
        scopeTables.currentModuleSymbolId
        LexicalVisibility
        (SourceSymbol nameInfo)
  let variableMutability = case bindingMutability of
        Nothing => ImmutableVariable
        Just Mutable => MutableVariable
  let localVarQualifiers = MkLocalVarQualifiers variableMutability ()
  let scopeBinding = MkScopeBinding
        nameText
        (Just nameInfo.span)
        symbolId
        DeclaredBinding
        LexicalVisibility
  let symbolReference = MkSymbolReference
        symbolId
        nameInfo
        scopeTables.currentScopeId
        contextNode
        DeclarationReference
        nameText
  let bindInCurrentScope : ScopeInfo -> ScopeInfo
      bindInCurrentScope scopeInfo =
        {
          valueBindings := insert nameText scopeBinding scopeInfo.valueBindings,
          declaredSymbolsInOrder := scopeInfo.declaredSymbolsInOrder :< symbolId
        } scopeInfo
  modify $ \currentTables =>
    {
      symbols := insert symbolId symbolInfo currentTables.symbols,
      localVarsMeta := insert symbolId localVarQualifiers currentTables.localVarsMeta,
      references := insert symbolId [< symbolReference] currentTables.references,
      scopes := updateExisting bindInCurrentScope currentTables.currentScopeId currentTables.scopes
    } currentTables
  pure $ resolveNode nameInfo metadata $
    MkResolvedNameNode nameText symbolId

-- Resolves a use of an already visible name and records the reference.
-- Declarations go through declareLocalName or declareValueSymbol instead.
resolveName : (contextNode : NodeId)
  -> (referenceRole : ReferenceRole)
  -> CanonicalName
  -> StateT ScopeTables (Either ResolutionError) ResolvedName
resolveName contextNode referenceRole
    (MkAstNode nameInfo metadata (MkNameNode nameText)) = do
  recordNodeScope nameInfo.nodeId
  scopeTables <- get
  nameScopeBinding <- case retrieveSymbolBinding nameText scopeTables of
    UnresolvedBinding =>
      lift $ Left $ UnresolvedName nameText nameInfo.span
    InaccessibleBinding symbolId =>
      lift $ Left $ InaccessibleSymbol nameText symbolId nameInfo.span
    Binding scopeBinding => pure scopeBinding
  rejectLocalNameUsedInConstantRole nameText nameInfo.span nameScopeBinding
  let boundSymbolId = nameScopeBinding.target
  let symbolReference = MkSymbolReference
        boundSymbolId
        nameInfo
        scopeTables.currentScopeId
        contextNode
        referenceRole
        nameText
  modify $ \currentTables =>
    let existingReferences = fromMaybe [<] (lookup boundSymbolId currentTables.references)
    in {
       references := insert boundSymbolId (existingReferences :< symbolReference) currentTables.references
    } currentTables
  pure $ resolveNode nameInfo metadata $
    MkResolvedNameNode nameText boundSymbolId

-- Bare immutable constant names are patterns referring to that constant.
-- Explicit `mut` requests a binding and may not shadow a constant.
resolveConstantPatternName : NodeId -> Maybe Mutability -> CanonicalName ->
                            StateT ScopeTables (Either ResolutionError) (Maybe ResolvedName)
resolveConstantPatternName contextNode bindingMutability binderName = do
  case bindingMutability of
    Just Mutable => rejectConstantShadowing binderName.nodeValue.nameNodeText binderName.astInfo.span
    Nothing => pure ()
  scopeTables <- get
  case visibleConstantBinding binderName.nodeValue.nameNodeText scopeTables of
    Just _ => map Just (resolveName contextNode PatternReference binderName)
    Nothing => pure Nothing

resolveParameterName : NodeId -> Maybe Mutability -> CanonicalName ->
                       StateT ScopeTables (Either ResolutionError) ResolvedName
resolveParameterName contextNode bindingMutability parameterName = do
  constantPatternName <- resolveConstantPatternName contextNode bindingMutability parameterName
  case constantPatternName of
    Just resolvedConstantName => pure resolvedConstantName
    Nothing => declareLocalName SymbolFunctionParameter contextNode bindingMutability parameterName

resolveAttribute : CanonicalAttribute -> ResolvedAttribute
resolveAttribute (MkAstNode attributeInfo metadata (MkAttributeNode attributeName attributeArguments)) =
  resolveNode attributeInfo metadata $
    MkAttributeNode
      (resolveAstNode attributeName)
      (map (map resolveAstNode) attributeArguments)

resolvePath : CanonicalPath -> StateT ScopeTables (Either ResolutionError) ResolvedPath
resolvePath (MkAstNode pathAstInfo metadata (MkPathNode firstSegment remainingSegments)) = do
  recordNodeScope pathAstInfo.nodeId
  notImplemented __FILE__ {function = "resolvePath"} {feature = "paths"}
  --pure $ resolveNode pathAstInfo metadata $
  --  MkResolvedPathNode
  --    (pathSegmentText firstSegment)
  --    (map pathSegmentText remainingSegments)
  --    (MkSymbolId pathAstInfo.nodeId.surfaceId)
  --where
  --  pathSegmentText : CanonicalPathSegment -> String
  --  pathSegmentText (MkAstNode _ _ (PathSegmentName text)) = text
  --  pathSegmentText (MkAstNode _ _ PathSegmentSelf) = "self"

resolvePatternUnchecked : CanonicalPattern -> StateT ScopeTables (Either ResolutionError) ResolvedPattern
resolvePatternUnchecked (MkAstNode patternInfo metadata patternNode) = do
  recordNodeScope patternInfo.nodeId
  resolvedPatternNode <- case patternNode of
    PatternWildcard =>
      pure PatternWildcard
    PatternName bindingMutability binderName => do
      constantPatternName <- resolveConstantPatternName patternInfo.nodeId bindingMutability binderName
      case constantPatternName of
        Just constantName =>
          pure $ PatternPath $ resolveNode constantName.astInfo constantName.metadata $
            MkResolvedPathNode constantName.nodeValue.nameNodeText [] constantName.nodeValue.nameNodeSymbolId
        Nothing => do
          resolvedBinderName <- declareLocalName SymbolLocalBinding patternInfo.nodeId bindingMutability binderName
          pure $ PatternName bindingMutability resolvedBinderName
    PatternPath valuePath =>
      notImplemented __FILE__ {function = "resolvePatternUnchecked"} {feature = "path patterns (needed for modules)"}
      --pure $ PatternPath (resolvePath valuePath)
    PatternLiteral literal =>
      pure $ PatternLiteral (resolveAstNode literal)
    PatternParenthesized innerPattern =>
      unreachable __FILE__ {function = "resolvePatternUnchecked"} {reason = "parenthesized patterns should have been removed during desugaring"}
    PatternTuple elementPatterns => do
      resolvedElementPatterns <- traverse recur elementPatterns
      pure $ PatternTuple resolvedElementPatterns
    PatternArray elementPatterns => do
      resolvedElementPatterns <- traverse recur elementPatterns
      pure $ PatternArray resolvedElementPatterns
    PatternStruct structPath fieldPatterns => do
      notImplemented __FILE__ {function = "resolvePatternUnchecked"} {feature = "struct patterns"}
      --resolvedFields <- traverse resolveStructPatternField fieldPatterns
      --pure $ PatternStruct (resolvePath structPath) resolvedFields
    PatternEnumTuple variantPath argumentPatterns => do
      notImplemented __FILE__ {function = "resolvePatternUnchecked"} {feature = "tuple-like enum variant patterns"}
      --resolvedArguments <- traverse recur argumentPatterns
      --pure $ PatternEnumTuple (resolvePath variantPath) resolvedArguments
  pure $ resolveNode patternInfo metadata resolvedPatternNode
  where
    recur : CanonicalPattern -> StateT ScopeTables (Either ResolutionError) ResolvedPattern
    recur nestedPattern =
      resolvePatternUnchecked (assert_smaller patternNode nestedPattern)

    --resolveStructPatternField : CanonicalStructPatternField -> StateT ScopeTables (Either ResolutionError) ResolvedStructPatternField
    --resolveStructPatternField (MkAstNode fieldInfo metadata fieldNode) = do
    --  recordNodeScope fieldInfo.nodeId
    --  resolvedFieldNode <- case fieldNode of
    --    -- Desugaring rewrites `{ x }` to `{ x: x }` with a PatternName binder, so
    --    -- `recur` below classifies it: `Point { N }` with a visible constant N is
    --    -- a constant pattern, as in Rust. Never declare it via declareLocalName directly.
    --    StructPatternFieldShorthand _ _ =>
    --      unreachable __FILE__ {function = "resolveStructPatternField"} {reason = "struct pattern field shorthands should have been removed during desugaring"}
    --    StructPatternFieldExplicit fieldName fieldPattern => do
    --      resolvedFieldName <- resolveName fieldInfo.nodeId FieldReference fieldName
    --      resolvedFieldPattern <- recur fieldPattern
    --      pure $ StructPatternFieldExplicit resolvedFieldName resolvedFieldPattern
    --  pure $ resolveNode fieldInfo metadata resolvedFieldNode

-- Check a complete pattern/parameter list after classifying names. Repeated
-- constant references are legal; only local/parameter declarations are binders.
rejectDuplicateBindings : List ResolvedName -> StateT ScopeTables (Either ResolutionError) ()
rejectDuplicateBindings binderNames = do
  scopeTables <- get
  lift $ checkBinderNames scopeTables empty binderNames
  where
    -- `firstBinderByName` maps each binder name seen so far to its first occurrence.
    checkBinderNames : ScopeTables -> (firstBinderByName : SortedMap String ResolvedName) -> List ResolvedName -> Either ResolutionError ()
    checkBinderNames _ _ [] = Right ()
    checkBinderNames scopeTables firstBinderByName (binderName :: remainingBinderNames) =
      case lookup binderName.nodeValue.nameNodeSymbolId scopeTables.symbols of
        Just binderSymbolInfo => if isLocalSymbolKind binderSymbolInfo.symbolKind
          then case lookup binderName.nodeValue.nameNodeText firstBinderByName of
            Just firstBinder => Left $ DuplicateDeclaration binderName.nodeValue.nameNodeText
              [firstBinder.nodeValue.nameNodeSymbolId] binderName.astInfo.span firstBinder.astInfo.span
            Nothing => checkBinderNames scopeTables (insert binderName.nodeValue.nameNodeText binderName firstBinderByName) remainingBinderNames
          else checkBinderNames scopeTables firstBinderByName remainingBinderNames
        Nothing => checkBinderNames scopeTables firstBinderByName remainingBinderNames

resolvePattern : CanonicalPattern -> StateT ScopeTables (Either ResolutionError) ResolvedPattern
resolvePattern canonicalPattern = do
  resolvedPattern <- resolvePatternUnchecked canonicalPattern
  rejectDuplicateBindings (bindingNames resolvedPattern)
  pure resolvedPattern
  where
    -- TODO: when struct and enum patterns are implemented, collect their binders
    -- here too (struct shorthand fields, explicit field patterns, enum tuple
    -- arguments); the `_ => []` case would otherwise skip their duplicates.
    -- Duplicate parameters of impl methods must also be checked once ItemImpl is
    -- resolved, since Compiler.Frontend.Validator.PostParseValidation no longer reports them.
    bindingNames : ResolvedPattern -> List ResolvedName
    bindingNames (MkAstNode _ _ patternNode) = case patternNode of
      PatternName _ binderName => [binderName]
      PatternTuple elementPatterns => concatMap (\nestedPattern => bindingNames (assert_smaller patternNode nestedPattern)) (forget elementPatterns)
      PatternArray elementPatterns => concatMap (\nestedPattern => bindingNames (assert_smaller patternNode nestedPattern)) elementPatterns
      _ => []

-- Establish all signature names before resolving any parameter types, so a
-- later parameter also receives a non-constant-use diagnostic in array lengths.
resolveFunctionParameterName : CanonicalFunctionParameter -> StateT ScopeTables (Either ResolutionError) ResolvedName
resolveFunctionParameterName (MkAstNode parameterInfo _ (NormalParameter _ parameterMutability parameterName _)) = do
  recordNodeScope parameterInfo.nodeId
  resolveParameterName parameterInfo.nodeId (map (.nodeValue) parameterMutability) parameterName
resolveFunctionParameterName (MkAstNode _ _ (ReceiverParameter _ _)) =
  notImplemented __FILE__ {function = "resolveFunctionParameterName"} {feature = "receiver parameters (self, &self, &mut self)"}

mutual
  resolveExpressionNode : AstInfo -> ExpressionNode CanonicalAstPhase -> StateT ScopeTables (Either ResolutionError) (ExpressionNode ResolvedAstPhase)
  resolveExpressionNode expressionInfo expressionNode =
    case expressionNode of
      ExprLiteral literal => pure $ ExprLiteral (resolveAstNode literal)
      ExprName valueName => do
        resolvedName <- resolveName expressionInfo.nodeId ValueReference valueName
        pure $ ExprName resolvedName
      ExprPath valuePath => do
        resolvedPath <- resolvePath valuePath
        pure $ ExprPath resolvedPath
      ExprBuiltin builtin => pure $ ExprBuiltin builtin
      ExprSelf () => notImplemented __FILE__ {function = "resolveExpressionNode"} {feature = "self expressions"}
      ExprParenthesized _ => unreachable __FILE__ {function = "resolveExpressionNode"} {reason = "parenthesized expressions should have been removed during desugaring"}
      ExprTuple elementExpressions => do
        resolvedElementExpressions <- traverse resolveNestedExpression elementExpressions
        pure $ ExprTuple resolvedElementExpressions
      ExprArray elementExpressions => do
        resolvedElementExpressions <- traverse resolveNestedExpression elementExpressions
        pure $ ExprArray resolvedElementExpressions
      ExprRepeatedArray repeatedElement repeatCount => do
        resolvedRepeatedElement <- resolveNestedExpression repeatedElement
        resolvedRepeatCount <- withConstContext (resolveNestedExpression repeatCount)
        pure $ ExprRepeatedArray resolvedRepeatedElement resolvedRepeatCount
      ExprStructLiteral _ _ => notImplemented __FILE__ {function = "resolveExpressionNode"} {feature = "struct literals (ExprStructLiteral)"}
      ExprCall callee arguments => do
        resolvedCallee <- resolveNestedExpression callee
        resolvedArguments <- case callee.nodeValue of
             ExprBuiltin BuiltinQAlloc => withConstContext (traverse resolveNestedExpression arguments)
             _ => traverse resolveNestedExpression arguments
        pure $ ExprCall resolvedCallee resolvedArguments
      ExprMethodCall receiver methodName arguments => do
        let MkAstNode methodNameInfo _ _ = methodName
        recordNodeScope methodNameInfo.nodeId
        resolvedReceiver <- resolveNestedExpression receiver
        resolvedArguments <- traverse resolveNestedExpression arguments
        pure $ ExprMethodCall resolvedReceiver (resolveAstNode methodName) resolvedArguments
      ExprField accessedObject fieldName => do
        let MkAstNode fieldNameInfo _ _ = fieldName
        recordNodeScope fieldNameInfo.nodeId
        resolvedAccessedObject <- resolveNestedExpression accessedObject
        pure $ ExprField resolvedAccessedObject (resolveAstNode fieldName)
      ExprTupleIndex tuple indexText => do
        resolvedTuple <- resolveNestedExpression tuple
        pure $ ExprTupleIndex resolvedTuple indexText
      ExprIndex indexedObject index => do
        resolvedIndexedObject <- resolveNestedExpression indexedObject
        resolvedIndex <- resolveNestedExpression index
        pure $ ExprIndex resolvedIndexedObject resolvedIndex
      ExprUnary unaryOperator operand => do
        resolvedOperand <- resolveNestedExpression operand
        pure $ ExprUnary (resolveAstNode unaryOperator) resolvedOperand
      ExprBinary binaryOperator leftOperand rightOperand => do
        resolvedLeftOperand <- resolveNestedExpression leftOperand
        resolvedRightOperand <- resolveNestedExpression rightOperand
        pure $ ExprBinary (resolveAstNode binaryOperator) resolvedLeftOperand resolvedRightOperand
      ExprRange rangeStart rangeOperator rangeEnd => do
        resolvedRangeStart <- traverse resolveNestedExpression rangeStart
        resolvedRangeEnd <- traverse resolveNestedExpression rangeEnd
        pure $ ExprRange resolvedRangeStart (resolveAstNode rangeOperator) resolvedRangeEnd
      ExprCast castOperand castTargetType => do
        resolvedCastOperand <- resolveNestedExpression castOperand
        resolvedCastTargetType <- resolveType castTargetType
        pure $ ExprCast resolvedCastOperand resolvedCastTargetType
      ExprBlock block => do
        resolvedBlock <- resolveBlockExpression block
        pure $ ExprBlock resolvedBlock
      ExprIf ifNode => do
        resolvedIfNode <- resolveIfNode ifNode
        pure $ ExprIf resolvedIfNode
      ExprQIf ifNode => notImplemented __FILE__ {function = "resolveExpressionNode"} {feature = "ExprQIf"}
      ExprSIf ifNode => notImplemented __FILE__ {function = "resolveExpressionNode"} {feature = "ExprSIf"}
      ExprMatch matchNode => notImplemented __FILE__ {function = "resolveExpressionNode"} {feature = "ExprMatch"}
      ExprQMatch matchNode => notImplemented __FILE__ {function = "resolveExpressionNode"} {feature = "ExprQMatch"}
      ExprSMatch matchNode => notImplemented __FILE__ {function = "resolveExpressionNode"} {feature = "ExprSMatch"}
      ExprLoop loopBody => do
        resolvedLoopBody <- resolveBlockExpression loopBody
        pure $ ExprLoop resolvedLoopBody
      ExprWhile loopCondition loopBody => do
        resolvedLoopCondition <- resolveNestedExpression loopCondition
        resolvedLoopBody <- resolveBlockExpression loopBody
        pure $ ExprWhile resolvedLoopCondition resolvedLoopBody
      ExprFor binderPattern iterable loopBody => do
        resolvedIterable <- resolveNestedExpression iterable
        -- The pattern scope originates from the for expression; its body block
        -- gets its own BlockScope originating from the block node.
        (resolvedBinderPattern, resolvedLoopBody) <- withChildScope ForScope (SourceScope expressionInfo) $ do
          resolvedBinderPattern <- resolvePattern binderPattern
          resolvedLoopBody <- resolveBlockExpression loopBody
          pure (resolvedBinderPattern, resolvedLoopBody)
        pure $ ExprFor resolvedBinderPattern resolvedIterable resolvedLoopBody
      ExprBreak breakValue => do
        resolvedBreakValue <- traverse resolveNestedExpression breakValue
        pure $ ExprBreak resolvedBreakValue
      ExprContinue => pure ExprContinue
      ExprReturn returnValue => do
        resolvedReturnValue <- traverse resolveNestedExpression returnValue
        pure $ ExprReturn resolvedReturnValue
      ExprCtrl control => do
        resolvedControl <- resolveControlExpressionNode control
        pure $ ExprCtrl resolvedControl
      ExprAdjoint adjoint => do
        resolvedAdjoint <- resolveAdjointExpressionNode adjoint
        pure $ ExprAdjoint resolvedAdjoint
    where
      resolveNestedExpression : CanonicalExpr -> StateT ScopeTables (Either ResolutionError) ResolvedExpr
      resolveNestedExpression nestedExpression = resolveExpression (assert_smaller expressionNode nestedExpression)

      resolveBlockExpression : CanonicalBlock -> StateT ScopeTables (Either ResolutionError) ResolvedBlock
      resolveBlockExpression
        (MkAstNode blockAstInfo metadata (MkBlockNode blockInnerDocs blockStatements finalExpression)) = do
        (resolvedStatements, resolvedFinalExpression) <- withChildScope BlockScope (SourceScope blockAstInfo) $ do
          recordNodeScope blockAstInfo.nodeId
          resolvedStatements <- traverse (\statement => resolveStatement (assert_smaller expressionNode statement)) blockStatements
          resolvedFinalExpression <- traverse resolveNestedExpression finalExpression
          pure (resolvedStatements, resolvedFinalExpression)
        pure $ resolveNode blockAstInfo metadata $
          MkBlockNode
            (map resolveAstNode blockInnerDocs)
            resolvedStatements
            resolvedFinalExpression

      resolveIfNode : ClassicalIfNode CanonicalAstPhase -> StateT ScopeTables (Either ResolutionError) (ClassicalIfNode ResolvedAstPhase)
      resolveIfNode ifNode@(MkClassicalIfNode ifCondition ifThenBlock ifElseBranch) = do
        resolvedCondition <- resolveNestedExpression ifCondition
        resolvedThenBlock <- resolveBlockExpression ifThenBlock
        resolvedElseBranch <- traverse resolveElseNode ifElseBranch
        pure $ MkClassicalIfNode resolvedCondition resolvedThenBlock resolvedElseBranch
        where
          resolveElseNode : ClassicalElseNode CanonicalAstPhase -> StateT ScopeTables (Either ResolutionError) (ClassicalElseNode ResolvedAstPhase)
          resolveElseNode (ElseBlock elseBlock) = do
            resolvedElseBlock <- resolveBlockExpression elseBlock
            pure $ ElseBlock resolvedElseBlock
          resolveElseNode (ElseChainedIf (MkAstNode chainedIfInfo metadata chainedIfNode)) = do
            recordNodeScope chainedIfInfo.nodeId
            resolvedIfNode <- resolveIfNode (assert_smaller ifNode chainedIfNode)
            pure $ ElseChainedIf $
              resolveNode chainedIfInfo metadata resolvedIfNode

      resolveControlExpressionNode : ControlExpressionNode CanonicalAstPhase -> StateT ScopeTables (Either ResolutionError) (ControlExpressionNode ResolvedAstPhase)
      resolveControlExpressionNode (ControlledCallable controlQbits onBasisRaw controlledCallable) = do
        resolvedControlQbits <- traverse resolveNestedExpression controlQbits
        resolvedCallable <- resolveNestedExpression controlledCallable
        pure $ ControlledCallable
          resolvedControlQbits
          (map resolveAstNode onBasisRaw)
          resolvedCallable
      resolveControlExpressionNode (ControlledBlock controlQbits onBasisRaw controlledBlock) = do
        resolvedControlQbits <- traverse resolveNestedExpression controlQbits
        resolvedBlock <- resolveBlockExpression controlledBlock
        pure $ ControlledBlock
          resolvedControlQbits
          (map resolveAstNode onBasisRaw)
          resolvedBlock

      resolveAdjointExpressionNode : AdjointExpressionNode CanonicalAstPhase -> StateT ScopeTables (Either ResolutionError) (AdjointExpressionNode ResolvedAstPhase)
      resolveAdjointExpressionNode (AdjointOfCallable adjointedCallable) = do
        resolvedCallable <- resolveNestedExpression adjointedCallable
        pure $ AdjointOfCallable resolvedCallable
      resolveAdjointExpressionNode (AdjointBlock adjointedBlock) = do
        resolvedBlock <- resolveBlockExpression adjointedBlock
        pure $ AdjointBlock resolvedBlock

  resolveExpression : CanonicalExpr -> StateT ScopeTables (Either ResolutionError) ResolvedExpr
  resolveExpression (MkAstNode expressionInfo metadata expressionNode) = do
    recordNodeScope expressionInfo.nodeId
    resolvedExpressionNode <- resolveExpressionNode expressionInfo expressionNode
    pure $ resolveNode expressionInfo metadata resolvedExpressionNode

  resolveType : Ty CanonicalAstPhase (Expr CanonicalAstPhase) -> StateT ScopeTables (Either ResolutionError) (Ty ResolvedAstPhase (Expr ResolvedAstPhase))
  resolveType (MkAstNode typeAstInfo metadata typeNode) = do
    recordNodeScope typeAstInfo.nodeId
    resolvedTypeNode <- case typeNode of
        TyPrimitive primitiveName => do
          pure $ TyPrimitive primitiveName
        TyPath typePath => do
          resolvedPath <- resolveTypePath typePath
          pure $ TyPath resolvedPath
        TyUnit => do
          pure TyUnit
        TyParenthesized _ => do
          unreachable __FILE__ {function = "resolveType"} {reason = "parenthesized types should have been removed during desugaring"}
        TyTuple elementTypes => do
          resolvedElementTypes <- traverse resolveNestedType elementTypes
          pure $ TyTuple resolvedElementTypes
        TyArray elementType sizeExpression => do
          resolvedElementType <- resolveNestedType elementType
          resolvedSizeExpression <- withConstContext (resolveExpression sizeExpression)
          pure $ TyArray
            resolvedElementType
            resolvedSizeExpression
        TySlice elementType => do
          resolvedElementType <- resolveNestedType elementType
          pure $ TySlice resolvedElementType
        TyReference borrowKind referencedType => do
          resolvedReferencedType <- resolveNestedType referencedType
          pure $ TyReference
            (resolveAstNode borrowKind)
            resolvedReferencedType
        TyQualified quantumUsageQualifier qualifiedType => do
          resolvedQualifiedType <- resolveNestedType qualifiedType
          pure $ TyQualified
            (resolveAstNode quantumUsageQualifier)
            resolvedQualifiedType
        TyFunction functionEffect functionParameters returnType => do
          resolvedFunctionParameters <- traverse resolveFunctionTypeParameter functionParameters
          resolvedReturnType <- traverse resolveNestedType returnType
          pure $ TyFunction
            (map resolveAstNode functionEffect)
            resolvedFunctionParameters
            resolvedReturnType
    pure $ resolveNode typeAstInfo metadata resolvedTypeNode
      where
        resolveTypePath : AstNode CanonicalAstPhase (PathNode CanonicalAstPhase) ->
                            StateT ScopeTables (Either ResolutionError) (AstNode ResolvedAstPhase ResolvedPathNode)
        resolveTypePath (MkAstNode pathInfo _ (MkPathNode firstSegment remainingSegments)) = do
          recordNodeScope pathInfo.nodeId
          -- Leaf has no type declarations or modules yet, so no type path can name a type.
          let writtenTypePathText = concat (intersperse "::" (map pathSegmentText (firstSegment :: remainingSegments)))
          lift $ Left $ UnresolvedTypePath writtenTypePathText pathInfo.span
          where
            pathSegmentText : CanonicalPathSegment -> String
            pathSegmentText (MkAstNode _ _ (PathSegmentName segmentText)) = segmentText
            pathSegmentText (MkAstNode _ _ PathSegmentSelf) = "self"
        resolveNestedType : CanonicalTy -> StateT ScopeTables (Either ResolutionError) ResolvedTy
        resolveNestedType nestedType = resolveType (assert_smaller typeNode nestedType)
        resolveFunctionTypeParameter : CanonicalAstNode (FunctionTypeParameterNode CanonicalAstPhase (CanonicalAstNode (ExpressionNode CanonicalAstPhase))) ->
           StateT ScopeTables (Either ResolutionError) $ ResolvedAstNode (FunctionTypeParameterNode ResolvedAstPhase (ResolvedAstNode (ExpressionNode ResolvedAstPhase)))
        resolveFunctionTypeParameter (MkAstNode parameterAstInfo metadata (MkFunctionTypeParameterNode parameterName parameterType)) = do
          recordNodeScope parameterAstInfo.nodeId
          resolvedParameterType <- resolveNestedType parameterType
          pure $ resolveNode parameterAstInfo metadata $
            -- Not resolveName: a function-type parameter name is never a
            -- symbol (see the comment on FunctionTypeParameterNode in
            -- Syntax/Type.idr), so only its AstNode wrapping is updated.
            MkFunctionTypeParameterNode (resolveAstNode parameterName) resolvedParameterType

  resolveLetInitializer : LetInitializerNode CanonicalAstPhase -> StateT ScopeTables (Either ResolutionError) (LetInitializerNode ResolvedAstPhase)
  resolveLetInitializer (MkLetInitializerNode initializerMarker initializerValue) = do
    resolvedInitializerValue <- resolveExpression initializerValue
    pure $ MkLetInitializerNode (resolveAstNode initializerMarker) resolvedInitializerValue

  resolveAssignmentTarget : CanonicalAstNode (AssignmentTargetNode CanonicalAstPhase) -> StateT ScopeTables (Either ResolutionError) (ResolvedAstNode (AssignmentTargetNode ResolvedAstPhase))
  resolveAssignmentTarget (MkAstNode assignmentTargetAstInfo metadata assignmentTargetNode) = do
    recordNodeScope assignmentTargetAstInfo.nodeId
    resolvedAssignmentTarget <- case assignmentTargetNode of
      AssignTargetName targetName => do
        resolvedTargetName <- resolveName assignmentTargetAstInfo.nodeId AssignmentTarget targetName
        pure $ AssignTargetName resolvedTargetName
      AssignTargetIndex targetObject indexExpression => do
        resolvedTargetObject <- resolveExpression targetObject
        resolvedIndexExpression <- resolveExpression indexExpression
        pure $ AssignTargetIndex
          resolvedTargetObject
          resolvedIndexExpression
      AssignTargetField targetObject fieldName => do
        let MkAstNode fieldInfo _ _ = fieldName
        recordNodeScope fieldInfo.nodeId
        resolvedTargetObject <- resolveExpression targetObject
        pure $ AssignTargetField
          resolvedTargetObject
          (resolveAstNode fieldName)
      AssignTargetTupleIndex targetObject tupleIndexRawText => do
        resolvedTargetObject <- resolveExpression targetObject
        pure $ AssignTargetTupleIndex
          resolvedTargetObject
          tupleIndexRawText
    pure (resolveNode assignmentTargetAstInfo metadata resolvedAssignmentTarget)

  resolveStatement : Statement CanonicalAstPhase -> StateT ScopeTables (Either ResolutionError) (Statement ResolvedAstPhase)
  resolveStatement (MkAstNode statementAstInfo metadata statementNode) = do
    recordNodeScope statementAstInfo.nodeId
    resolvedStatementNode <- case statementNode of
        StatementLet (MkLetBindingNode letQualifiers letPattern typeAnnotation letInitializer) => do
          resolvedTypeAnnotation <- traverse (\annotationType => resolveType (assert_smaller statementNode annotationType)) typeAnnotation
          resolvedInitializer <- traverse (\initializer => resolveLetInitializer (assert_smaller statementNode initializer)) letInitializer
          -- New bindings are visible only after their annotation and initializer.
          resolvedPattern <- resolvePattern letPattern
          pure $ StatementLet $
            MkLetBindingNode
              (map resolveAstNode letQualifiers)
              resolvedPattern
              resolvedTypeAnnotation
              resolvedInitializer
        StatementAssignment (MkAssignmentNode assignmentTarget assignmentOperator assignmentValue) => do
          resolvedAssignmentTarget <- resolveAssignmentTarget assignmentTarget
          resolvedAssignmentValue <- resolveExpression assignmentValue
          pure $ StatementAssignment $
            MkAssignmentNode
              resolvedAssignmentTarget
              (resolveAstNode assignmentOperator)
              resolvedAssignmentValue
        StatementSemiExpression statementExpression => do
          resolvedExpression <- resolveExpression statementExpression
          pure $ StatementSemiExpression resolvedExpression
        StatementExpression statementExpression => do
          resolvedExpression <- resolveExpression statementExpression
          pure $ StatementExpression resolvedExpression
    pure (resolveNode statementAstInfo metadata resolvedStatementNode)

resolveFunctionParameter : ResolvedName -> AstNode CanonicalAstPhase (FunctionParameterNode CanonicalAstPhase) ->
                           StateT ScopeTables (Either ResolutionError) (AstNode ResolvedAstPhase (FunctionParameterNode ResolvedAstPhase))
resolveFunctionParameter resolvedParameterName
  (MkAstNode parameterInfo metadata (NormalParameter parameterDocs parameterMutability parameterName parameterType)) = do
    resolvedParameterType <- resolveType parameterType
    pure $ resolveNode parameterInfo metadata $
      NormalParameter
        (map resolveAstNode parameterDocs)
        (map resolveAstNode parameterMutability)
        resolvedParameterName
        resolvedParameterType
resolveFunctionParameter _ (MkAstNode _ _ (ReceiverParameter _ _)) =
  notImplemented __FILE__ {function = "resolveFunctionParameter"} {feature = "receiver parameters (self, &self, &mut self)"}

resolveSignedPauliTerm : SignedPauliTerm CanonicalAstPhase -> StateT ScopeTables (Either ResolutionError) (SignedPauliTerm ResolvedAstPhase)
resolveSignedPauliTerm (MkAstNode termInfo metadata (MkSignedPauliTermNode sign pauliString)) = do
  recordNodeScope termInfo.nodeId
  pure $ resolveNode termInfo metadata $
    MkSignedPauliTermNode sign (resolveAstNode pauliString)

resolveContractPredicate : CanonicalContractPredicate -> StateT ScopeTables (Either ResolutionError) ResolvedContractPredicate
resolveContractPredicate (MkAstNode predicateInfo metadata predicateNode) = do
  recordNodeScope predicateInfo.nodeId
  resolvedPredicateNode <- case predicateNode of
    ContractClean qbitArgument => do
      resolvedQbitArgument <- resolveExpression qbitArgument
      pure $ ContractClean resolvedQbitArgument
    ContractBasis qbitArgument pauliString => do
      resolvedQbitArgument <- resolveExpression qbitArgument
      pure $ ContractBasis
        resolvedQbitArgument
        (resolveAstNode pauliString)
    ContractSeparable qbitArgument => do
      resolvedQbitArgument <- resolveExpression qbitArgument
      pure $ ContractSeparable resolvedQbitArgument
    ContractIsolated qbitArgument => do
      resolvedQbitArgument <- resolveExpression qbitArgument
      pure $ ContractIsolated resolvedQbitArgument
    ContractProduct firstQbitSet otherQbitSets => do
      resolvedFirstQbitSet <- resolveExpression firstQbitSet
      resolvedOtherQbitSets <- traverse resolveExpression otherQbitSets
      pure $ ContractProduct
        resolvedFirstQbitSet
        resolvedOtherQbitSets
    ContractStabilized qbitArgument stabilizerTerms => do
      resolvedQbitArgument <- resolveExpression qbitArgument
      resolvedStabilizerTerms <- traverse resolveSignedPauliTerm stabilizerTerms
      pure $ ContractStabilized
        resolvedQbitArgument
        resolvedStabilizerTerms
  pure $ resolveNode predicateInfo metadata resolvedPredicateNode

resolveContractClause : ContractClause CanonicalAstPhase (Expr CanonicalAstPhase) -> StateT ScopeTables (Either ResolutionError) (ContractClause ResolvedAstPhase (Expr ResolvedAstPhase))
resolveContractClause (MkAstNode contractAstInfo metadata contractClauseNode) = do
  recordNodeScope contractAstInfo.nodeId
  resolvedClauseNode <- case contractClauseNode of
      RequiresClause predicate => do
        resolvedContractPredicate <- resolveContractPredicate predicate
        pure $ RequiresClause resolvedContractPredicate
      EnsuresClause predicate => do
        resolvedContractPredicate <- resolveContractPredicate predicate
        pure $ EnsuresClause resolvedContractPredicate
  pure $ resolveNode contractAstInfo metadata resolvedClauseNode

resolveFunctionBody : Block CanonicalAstPhase -> StateT ScopeTables (Either ResolutionError) (Block ResolvedAstPhase)
resolveFunctionBody (MkAstNode _ _ (MkBlockNode _ _ (Just _))) =
  unreachable __FILE__ {function = "resolveFunctionBody"} {reason = "the final expression of a function body should have been desugared to a statement"}
resolveFunctionBody (MkAstNode functionBodyAstInfo metadata (MkBlockNode blockInnerDocs blockStatements Nothing)) = do
  resolvedBlockStatements <- withChildScope BlockScope (SourceScope functionBodyAstInfo) $ do
    recordNodeScope functionBodyAstInfo.nodeId
    traverse resolveStatement blockStatements
  pure $ resolveNode functionBodyAstInfo metadata $ MkBlockNode
      (map resolveAstNode blockInnerDocs)
      resolvedBlockStatements
      Nothing

-- Adds a value-namespace declaration to the current scope.
-- Fails with DuplicateDeclaration if the scope already declares the same name.
declareValueSymbol : AstInfo -> SymbolKind -> SymbolVisibility -> CanonicalName -> StateT ScopeTables (Either ResolutionError) ()
declareValueSymbol itemInfo symbolKind declaredVisibility (MkAstNode nameInfo _ (MkNameNode nameText)) = do
  recordNodeScope itemInfo.nodeId
  scopeTables <- get
  let symbolId = scopeTables.nextSymbolId
  let currentScopeId = scopeTables.currentScopeId
  let existingBinding = lookup currentScopeId scopeTables.scopes >>= \scopeInfo => lookup nameText scopeInfo.valueBindings
  case existingBinding of
    Just previousBinding => case previousBinding.introducedAt of
      Just previousDeclarationSpan =>
        lift $ Left $ DuplicateDeclaration nameText [previousBinding.target] nameInfo.span previousDeclarationSpan
      -- Source declarations always record their name span. Prelude bindings
      -- live in the parent scope and cannot be a same-scope conflict here.
      Nothing => unreachable __FILE__ {function = "declareValueSymbol"} {reason = "existing source declaration has no introduction span"}
    Nothing => pure ()
  let symbolInfo = MkSymbolInfo
        symbolId
        symbolKind
        ()
        nameText
        currentScopeId
        scopeTables.currentModuleSymbolId
        declaredVisibility
        (SourceSymbol itemInfo)
  let symbolReference = MkSymbolReference symbolId nameInfo currentScopeId itemInfo.nodeId DeclarationReference nameText
  let scopeBinding = MkScopeBinding nameText (Just nameInfo.span) symbolId DeclaredBinding declaredVisibility
  let bindInCurrentScope : ScopeInfo -> ScopeInfo
      bindInCurrentScope scopeInfo =
        {
          valueBindings := insert nameText scopeBinding scopeInfo.valueBindings,
          declaredSymbolsInOrder := scopeInfo.declaredSymbolsInOrder :< symbolId
        } scopeInfo
  modify $ \currentTables =>
    {
      symbols := insert symbolId symbolInfo currentTables.symbols,
      references := insert symbolId [< symbolReference] currentTables.references,
      scopes := updateExisting bindInCurrentScope currentScopeId currentTables.scopes
    } currentTables

-- First pass over a scope's items: declares every item name before any item body
-- is resolved, so items can refer to each other regardless of declaration order.
declareItem : CanonicalItem -> StateT ScopeTables (Either ResolutionError) ()
declareItem (MkAstNode itemInfo _ itemNode) =
  case itemNode of
    ItemModule declaration => notImplemented __FILE__ {function = "declareItem"} {feature = "ItemModule"}
    ItemUse declaration => notImplemented __FILE__ {function = "declareItem"} {feature = "ItemUse"}
    ItemConst (MkConstDeclarationNode _ constVisibility constName _ _) =>
      declareValueSymbol itemInfo SymbolConstant (symbolVisibility constVisibility) constName
    ItemEnum declaration => notImplemented __FILE__ {function = "declareItem"} {feature = "ItemEnum"}
    ItemQEnum declaration => notImplemented __FILE__ {function = "declareItem"} {feature = "ItemQEnum"}
    ItemStruct declaration => notImplemented __FILE__ {function = "declareItem"} {feature = "ItemStruct"}
    ItemImpl declaration => notImplemented __FILE__ {function = "declareItem"} {feature = "ItemImpl"}
    ItemFunction (MkFunctionDeclarationNode _ _ functionVisibility _ _ functionName _ _ _ _ _) =>
      declareValueSymbol itemInfo SymbolFunction (symbolVisibility functionVisibility) functionName

-- Resolves the name of an item that declareItem has already declared in the
-- current scope to that declaration's SymbolId.
resolveDeclaredValueName : CanonicalName -> StateT ScopeTables (Either ResolutionError) ResolvedName
resolveDeclaredValueName (MkAstNode nameInfo metadata (MkNameNode nameText)) = do
  recordNodeScope nameInfo.nodeId
  scopeTables <- get
  let declaredBinding = lookup scopeTables.currentScopeId scopeTables.scopes >>= \scopeInfo => lookup nameText scopeInfo.valueBindings
  case declaredBinding of
    Just itemBinding => pure $ resolveNode nameInfo metadata $ MkResolvedNameNode nameText itemBinding.target
    Nothing => unreachable __FILE__ {function = "resolveDeclaredValueName"} {reason = "item name was not declared by declareItem"}

-- Second pass over a scope's items: resolves each item against the scope that
-- declareItem has already populated with all item names.
resolveItem : CanonicalItem -> StateT ScopeTables (Either ResolutionError) ResolvedItem
resolveItem (MkAstNode itemInfo metadata itemNode) = do
  resolvedItemNode <- case itemNode of
    ItemModule declaration => notImplemented __FILE__ {function = "resolveItem"} {feature = "ItemModule"}
    ItemUse declaration => notImplemented __FILE__ {function = "resolveItem"} {feature = "ItemUse"}
    ItemConst constDeclaration => do
      resolvedConstDeclaration <- resolveConstDeclaration constDeclaration
      pure $ ItemConst resolvedConstDeclaration
    ItemEnum declaration => notImplemented __FILE__ {function = "resolveItem"} {feature = "ItemEnum"}
    ItemQEnum declaration => notImplemented __FILE__ {function = "resolveItem"} {feature = "ItemQEnum"}
    ItemStruct declaration => notImplemented __FILE__ {function = "resolveItem"} {feature = "ItemStruct"}
    ItemImpl declaration => notImplemented __FILE__ {function = "resolveItem"} {feature = "ItemImpl"}
    ItemFunction functionDeclaration => do
      resolvedFunctionDeclaration <- resolveFunctionDeclaration functionDeclaration
      pure $ ItemFunction resolvedFunctionDeclaration
  pure $ resolveNode itemInfo metadata resolvedItemNode
  where
    resolveConstDeclaration : ConstDeclarationNode CanonicalAstPhase -> StateT ScopeTables (Either ResolutionError) (ConstDeclarationNode ResolvedAstPhase)
    resolveConstDeclaration (MkConstDeclarationNode constDocs constVisibility constName constType constValue) = do
      resolvedConstName <- resolveDeclaredValueName constName
      resolvedConstType <- resolveType constType
      resolvedConstValue <- resolveExpression constValue
      pure $ MkConstDeclarationNode
        (map resolveAstNode constDocs)
        (map resolveAstNode constVisibility)
        resolvedConstName
        resolvedConstType
        resolvedConstValue

    resolveFunctionDeclaration : FunctionDeclarationNode CanonicalAstPhase -> StateT ScopeTables (Either ResolutionError) (FunctionDeclarationNode ResolvedAstPhase)
    resolveFunctionDeclaration
        (MkFunctionDeclarationNode
          functionDocs
          functionAttributes
          functionVisibility
          functionConstness
          functionEffect
          functionName
          functionParameters
          returnType
          supportClause
          contractClauses
          functionBody) = do
      resolvedFunctionName <- resolveDeclaredValueName functionName
      (resolvedParameters, resolvedReturnType, resolvedContracts, resolvedBody) <-
        withChildScope FunctionScope (SourceScope itemInfo) $ do
          resolvedParameterNames <- traverse resolveFunctionParameterName functionParameters
          rejectDuplicateBindings resolvedParameterNames
          resolvedParameters <- traverse (\(resolvedParameterName, parameter) => resolveFunctionParameter resolvedParameterName parameter)
                                         (zip resolvedParameterNames functionParameters)
          resolvedReturnType <- traverse resolveType returnType
          resolvedContracts <- traverse resolveContractClause contractClauses
          resolvedBody <- resolveFunctionBody functionBody
          pure (resolvedParameters, resolvedReturnType, resolvedContracts, resolvedBody)
      pure $ MkFunctionDeclarationNode
        (map resolveAstNode functionDocs)
        (map resolveAttribute functionAttributes)
        (map resolveAstNode functionVisibility)
        (map resolveAstNode functionConstness)
        (map resolveAstNode functionEffect)
        resolvedFunctionName
        resolvedParameters
        resolvedReturnType
        (map resolveAstNode supportClause)
        resolvedContracts
        resolvedBody

registerPrelude : StateT ScopeTables (Either ResolutionError) ()
registerPrelude = do
  scopeTables <- get
  let preludeScopeId = scopeTables.nextScopeId
  let preludeModuleId = scopeTables.nextSymbolId
  let preludeModuleInfo = MkSymbolInfo
        preludeModuleId
        SymbolModule
        ()
        "<prelude>"
        scopeTables.currentScopeId
        scopeTables.currentModuleSymbolId
        PublicVisibility
        PreludeSymbol
  let preludeScopeInfo = MkScopeInfo
        preludeScopeId
        ModuleScope
        Nothing
        PreludeScope
        empty
        empty
        empty
        [<]
  let attachPreludeAsParent : ScopeInfo -> ScopeInfo
      attachPreludeAsParent scopeInfo =
        {
          parent := Just preludeScopeId,
          declaredSymbolsInOrder := scopeInfo.declaredSymbolsInOrder :< preludeModuleId
        } scopeInfo
  modify $ \currentTables =>
    {
      symbols := insert preludeModuleId preludeModuleInfo currentTables.symbols,
      scopes := insert preludeScopeId preludeScopeInfo $
        updateExisting attachPreludeAsParent currentTables.currentScopeId currentTables.scopes,
      memberScopes := insert preludeModuleId preludeScopeId currentTables.memberScopes
    } currentTables
  traverse_ (declarePreludeFunction preludeScopeId preludeModuleId) preludeFunctionNames
  where
    declarePreludeFunction : ScopeId -> SymbolId -> String -> StateT ScopeTables (Either ResolutionError) ()
    declarePreludeFunction preludeScopeId preludeModuleId preludeFunctionName = do
      scopeTables <- get
      let symbolId = scopeTables.nextSymbolId
      let symbolInfo = MkSymbolInfo
            symbolId
            SymbolFunction
            ()
            preludeFunctionName
            preludeScopeId
            preludeModuleId
            PublicVisibility
            PreludeSymbol
      let scopeBinding = MkScopeBinding
            preludeFunctionName
            Nothing
            symbolId
            PreludeBinding
            PublicVisibility
      let bindInPreludeScope : ScopeInfo -> ScopeInfo
          bindInPreludeScope scopeInfo =
            {
              valueBindings := insert preludeFunctionName scopeBinding scopeInfo.valueBindings,
              declaredSymbolsInOrder := scopeInfo.declaredSymbolsInOrder :< symbolId
            } scopeInfo
      modify $ \currentTables =>
        {
          symbols := insert symbolId symbolInfo currentTables.symbols,
          scopes := updateExisting bindInPreludeScope preludeScopeId currentTables.scopes
        } currentTables

||| Perform symbol and scope resolution over the canonical AST of
||| a source file, starting from the scope of the root module.
export
resolveCanonicalSyntax : CanonicalSourceFile -> Either ResolutionError ResolvedModule
resolveCanonicalSyntax (MkAstNode fileInfo metadata (MkSourceFileNode fileDocs sourceFileItems)) = do
  (finalScopeTables, resolvedItems) <- runStateT initialScopeTables $ do
    registerPrelude
    traverse_ declareItem sourceFileItems
    traverse resolveItem sourceFileItems
  pure $ MkResolvedModule
    moduleSymbolId
    moduleScopeId
    (resolveNode fileInfo metadata $ MkSourceFileNode (map resolveAstNode fileDocs) resolvedItems)
    finalScopeTables
  where
    moduleScopeId = MkScopeId 0
    moduleSymbolId = MkSymbolId 0
    moduleScopeInfo = MkScopeInfo moduleScopeId ModuleScope Nothing (SourceScope fileInfo) empty empty empty [<]
    -- The root module has no enclosing scope or module, so it declares itself in its own scope and module
    moduleSymbolInfo = MkSymbolInfo moduleSymbolId SymbolModule () "" moduleScopeId moduleSymbolId PublicVisibility (SourceSymbol fileInfo)
    initialScopeTables =
      MkScopeTables
        (singleton moduleScopeId moduleScopeInfo)
        (singleton fileInfo.nodeId moduleScopeId)
        (singleton moduleSymbolId moduleSymbolInfo)
        empty
        (singleton moduleSymbolId moduleScopeId)
        empty
        moduleScopeId
        ModuleScope
        moduleSymbolId
        Nothing
