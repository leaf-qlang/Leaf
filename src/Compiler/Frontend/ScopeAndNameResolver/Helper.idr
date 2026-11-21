module Compiler.Frontend.ScopeAndNameResolver.Helper

import Control.Monad.State
import Compiler.Frontend.ScopeAndNameResolver.Data
import Data.SortedMap
import Compiler.Frontend.ASTData
import Compiler.Frontend.ASTPhases
import Compiler.Frontend.Syntax.Common

%default total

export
recordNodeScope : NodeId -> StateT ScopeTables (Either ResolutionError) ()
recordNodeScope nodeId = modify $ \scopeTables =>
  { nodeScopes := insert nodeId scopeTables.currentScopeId scopeTables.nodeScopes } scopeTables

export
symbolVisibility : Maybe (AstNode CanonicalAstPhase VisibilityQualifier) -> SymbolVisibility
symbolVisibility (Just (MkAstNode _ _ VisibilityPublic)) = PublicVisibility
symbolVisibility Nothing = ModuleVisibility

public export
data BindingRetrievalResult
  = UnresolvedBinding
  | InaccessibleBinding SymbolId
  | Binding ScopeBinding

export
retrieveSymbolBinding : String -> ScopeTables -> BindingRetrievalResult
retrieveSymbolBinding symbolName scopeTables =
  searchScopeAndAncestors (length (SortedMap.toList scopeTables.scopes)) scopeTables.currentScopeId
  where
    -- `remainingScopeCount` bounds the walk, so it terminates even on a malformed parent chain.
    searchScopeAndAncestors : (remainingScopeCount : Nat) -> ScopeId -> BindingRetrievalResult
    searchScopeAndAncestors Z _ = UnresolvedBinding
    searchScopeAndAncestors (S remainingScopeCount) scopeId =
      case lookup scopeId scopeTables.scopes of
        Nothing => UnresolvedBinding
        Just scopeInfo =>
          case lookup symbolName scopeInfo.valueBindings of
            Just scopeBinding => Binding scopeBinding
            Nothing =>
              case scopeInfo.parent of
                Nothing => UnresolvedBinding
                Just parentScopeId => searchScopeAndAncestors remainingScopeCount parentScopeId

export
isLocalSymbolKind : SymbolKind -> Bool
isLocalSymbolKind SymbolLocalBinding = True
isLocalSymbolKind SymbolFunctionParameter = True
isLocalSymbolKind SymbolSelfReceiverParameter = True
isLocalSymbolKind _ = False

||| True when `candidateScopeId` is `startScopeId` or one of its parent scopes.
export
isScopeOrAncestor : ScopeId -> ScopeId -> ScopeTables -> Bool
isScopeOrAncestor candidateScopeId startScopeId scopeTables =
  isCandidateOnPathToRoot (length (SortedMap.toList scopeTables.scopes)) startScopeId
  where
    -- `remainingScopeCount` bounds the walk, so it terminates even on a malformed parent chain.
    isCandidateOnPathToRoot : (remainingScopeCount : Nat) -> ScopeId -> Bool
    isCandidateOnPathToRoot Z _ = False
    isCandidateOnPathToRoot (S remainingScopeCount) scopeId =
      scopeId == candidateScopeId ||
        case lookup scopeId scopeTables.scopes >>= (.parent) of
          Nothing => False
          Just parentScopeId => isCandidateOnPathToRoot remainingScopeCount parentScopeId
