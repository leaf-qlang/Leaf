module ScopeAndNameResolution.PreludeTestHelper

import Compiler.Frontend.Prelude
import Compiler.Frontend.ScopeAndNameResolver.Data
import Compiler.Frontend.ASTData
import Compiler.Frontend.ASTPhases
import Compiler.Frontend.Source
import Compiler.Frontend.Syntax.AST
import Compiler.Frontend.Syntax.Name
import ScopeAndNameResolution.Helper

import Data.List
import Data.Maybe
import Data.SnocList
import Data.SortedMap

%default total

isPrelude : SymbolOrigin -> Bool
isPrelude PreludeSymbol = True
isPrelude _ = False

isPublic : SymbolVisibility -> Bool
isPublic PublicVisibility = True
isPublic _ = False

isModuleScope : ScopeKind -> Bool
isModuleScope ModuleScope = True
isModuleScope _ = False

isPreludeModule : ResolvedSymbolInfo -> Bool
isPreludeModule symbolInfo = case symbolInfo.symbolKind of
  SymbolModule => isPrelude symbolInfo.origin
  _ => False

-- Check ownership, lexical ancestry and declaration order independently of
-- the general validator, which deliberately does not require complete tables.
export
preludeLayout : ResolvedModule -> Maybe Bool
preludeLayout resolvedModule = do
  let scopeTables = resolvedModule.scopeTables
  rootScope <- lookup resolvedModule.rootScopeId scopeTables.scopes
  preludeScopeId <- rootScope.parent
  preludeScope <- lookup preludeScopeId scopeTables.scopes
  [preludeModuleSymbol] <- pure (filter isPreludeModule (map snd (SortedMap.toList scopeTables.symbols)))
    | _ => Nothing
  let preludeBindings = map snd (SortedMap.toList preludeScope.valueBindings)
  pure $
    scopeTables.currentScopeId == resolvedModule.rootScopeId &&
    isModuleScope scopeTables.currentScopeKind &&
    scopeTables.currentModuleSymbolId == resolvedModule.rootSymbolId &&
    isModuleScope rootScope.kind && isModuleScope preludeScope.kind &&
    (case preludeScope.origin of PreludeScope => True; _ => False) &&
    isNothing preludeScope.parent &&
    preludeModuleSymbol.declaringScope == resolvedModule.rootScopeId &&
    preludeModuleSymbol.declaringModule == resolvedModule.rootSymbolId &&
    lookup preludeModuleSymbol.symbolId scopeTables.memberScopes == Just preludeScopeId &&
    lookup resolvedModule.rootSymbolId scopeTables.memberScopes == Just resolvedModule.rootScopeId &&
    elem preludeModuleSymbol.symbolId (rootScope.declaredSymbolsInOrder <>> []) &&
    sort (map (.writtenName) preludeBindings) == sort preludeFunctionNames &&
    sort (preludeScope.declaredSymbolsInOrder <>> []) == sort (map (.target) preludeBindings) &&
    all (validBinding scopeTables preludeScopeId preludeModuleSymbol.symbolId) preludeBindings
  where
    validBinding : ScopeTables -> ScopeId -> SymbolId -> ScopeBinding -> Bool
    validBinding scopeTables preludeScopeId preludeModuleId preludeBinding =
      case lookup preludeBinding.target scopeTables.symbols of
        Nothing => False
        Just functionSymbol =>
          (case preludeBinding.bindingKind of PreludeBinding => True; _ => False) &&
          isNothing preludeBinding.introducedAt && isPublic preludeBinding.bindingVisibility &&
          (case functionSymbol.symbolKind of SymbolFunction => True; _ => False) &&
          isPrelude functionSymbol.origin && isPublic functionSymbol.visibility &&
          functionSymbol.symbolId == preludeBinding.target && functionSymbol.declaredName == preludeBinding.writtenName &&
          functionSymbol.declaringScope == preludeScopeId && functionSymbol.declaringModule == preludeModuleId &&
          isNothing (lookup functionSymbol.symbolId scopeTables.localVarsMeta)

export
useOrigins : String -> Maybe (List (String, String))
useOrigins sourceText = do
  resolvedModule <- resolvedSource sourceText
  traverse (describeReferenceOrigin resolvedModule.scopeTables) (valueReferences resolvedModule)
  where
    describeReferenceOrigin : ScopeTables -> SymbolReference -> Maybe (String, String)
    describeReferenceOrigin scopeTables reference = do
      targetSymbol <- lookup reference.target scopeTables.symbols
      let originDescription = if isPrelude targetSymbol.origin then "prelude" else
            case targetSymbol.symbolKind of
              SymbolConstant => "other"
              symbolKind => kindText symbolKind
      pure (reference.writtenName, originDescription)

export
missingName : String -> Maybe String
missingName sourceText = case expectUnresolvedName sourceText of
  Right unresolvedName => Just unresolvedName
  Left _ => Nothing

export
constantShadowsPrelude : ResolvedModule -> Maybe Bool
constantShadowsPrelude resolvedModule = do
  MkSourceFileNode _ [MkAstNode _ _ (ItemFunction functionDeclaration), MkAstNode _ _ (ItemConst constDeclaration)] <- pure resolvedModule.ast.nodeValue
    | _ => Nothing
  MkAstNode _ _ (StatementSemiExpression sinExpression) :: _ <- pure functionDeclaration.functionBody.nodeValue.blockStatements
    | _ => Nothing
  ExprName sinName <- pure sinExpression.nodeValue | _ => Nothing
  rootScope <- lookup resolvedModule.rootScopeId resolvedModule.scopeTables.scopes
  preludeScopeId <- rootScope.parent
  preludeScope <- lookup preludeScopeId resolvedModule.scopeTables.scopes
  sourceBinding <- lookup "sin" rootScope.valueBindings
  preludeBinding <- lookup "sin" preludeScope.valueBindings
  sourceSymbol <- lookup sourceBinding.target resolvedModule.scopeTables.symbols
  preludeSymbol <- lookup preludeBinding.target resolvedModule.scopeTables.symbols
  bodyScope <- lookup functionDeclaration.functionBody.astInfo.nodeId resolvedModule.scopeTables.nodeScopes
  [sinReference] <- pure (valueReferences resolvedModule) | _ => Nothing
  preludeLayoutIsValid <- preludeLayout resolvedModule
  pure (preludeLayoutIsValid && sourceBinding.target /= preludeBinding.target &&
        sourceBinding.target == constDeclaration.constName.nodeValue.nameNodeSymbolId &&
        sinName.nodeValue.nameNodeSymbolId == sourceBinding.target &&
        (case sourceBinding.bindingKind of DeclaredBinding => True; _ => False) &&
        (case sourceBinding.bindingVisibility of ModuleVisibility => True; _ => False) &&
        (case sourceSymbol.symbolKind of SymbolConstant => True; _ => False) &&
        (case sourceSymbol.origin of SourceSymbol _ => True; _ => False) &&
        sourceSymbol.declaringScope == resolvedModule.rootScopeId && sourceSymbol.declaringModule == resolvedModule.rootSymbolId &&
        isPrelude preludeSymbol.origin && preludeSymbol.declaringScope == preludeScopeId &&
        (case preludeBinding.bindingKind of PreludeBinding => True; _ => False) &&
        isPublic preludeBinding.bindingVisibility &&
        sinReference.target == sourceBinding.target && sinReference.writtenName == "sin" &&
        sinReference.occurrence.nodeId == sinName.astInfo.nodeId &&
        spanKey sinReference.occurrence.span == spanKey sinName.astInfo.span &&
        sinReference.contextNode == sinExpression.astInfo.nodeId && sinReference.enclosingScope == bodyScope &&
        lookup sinExpression.astInfo.nodeId resolvedModule.scopeTables.nodeScopes == Just bodyScope &&
        lookup sinName.astInfo.nodeId resolvedModule.scopeTables.nodeScopes == Just bodyScope &&
        isNothing (lookup preludeBinding.target resolvedModule.scopeTables.references) &&
        length (allReferences resolvedModule) == 3)
