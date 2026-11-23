module Compiler.Frontend.ScopeAndNameResolver.Validate

import Compiler.Frontend.ScopeAndNameResolver.Data
import Compiler.Frontend.ASTData
import Compiler.Frontend.Source

import Data.List
import Data.Maybe
import Data.SnocList
import Data.SortedMap

%default total

-- These diagnostics describe inconsistent compiler output, not invalid Leaf
-- source. Keep them separate from ResolutionError and out of ASTData.
public export
data BindingNamespace = TypeNamespace | ValueNamespace | FieldNamespace

public export
Show BindingNamespace where
  show TypeNamespace = "type"
  show ValueNamespace = "value"
  show FieldNamespace = "field"

public export
data ResolutionInvariantError
  = MissingRootModule SymbolId
  | InvalidRootModule SymbolId
  | MissingRootScope ScopeId
  | InvalidRootScope ScopeId
  | SymbolKeyMismatch SymbolId SymbolId
  | MissingDeclaringScope SymbolId ScopeId
  | MissingDeclaringModule SymbolId SymbolId
  | InvalidDeclaringModule SymbolId SymbolId
  | SelfDeclaringModule SymbolId
  | ScopeKeyMismatch ScopeId ScopeId
  | MissingParentScope ScopeId ScopeId
  | ScopeParentCycle ScopeId
  | BindingNameMismatch ScopeId BindingNamespace String String
  | MissingBindingTarget ScopeId BindingNamespace String SymbolId
  | MissingDeclaredSymbol ScopeId SymbolId
  | DuplicateDeclaredSymbol ScopeId SymbolId
  | WrongDeclarationScope ScopeId SymbolId ScopeId
  | MissingDeclarationOrderEntry ScopeId SymbolId
  | MissingReferenceSymbol SymbolId
  | ReferenceKeyMismatch SymbolId SymbolId NodeId
  | MissingReferenceScope NodeId ScopeId
  | MissingNodeScope NodeId ScopeId
  | MissingLocalSymbol SymbolId
  | InvalidLocalSymbolKind SymbolId
  | MissingMemberOwner SymbolId
  | InvalidMemberOwner SymbolId
  | MissingMemberScope SymbolId ScopeId
  | InvalidMemberScopeKind SymbolId ScopeId
  | UnrestoredCurrentScope ScopeId ScopeId
  | UnrestoredCurrentModule SymbolId SymbolId
  | InvalidCurrentScopeKind ScopeId
  | UnrestoredConstContext ScopeId
  | MissingLocalVarQualifiers SymbolId
  | DeclaredBindingNameMismatch ScopeId BindingNamespace String SymbolId String
  | MissingReferenceNodeScope NodeId ScopeId
  | ReferenceNodeScopeMismatch NodeId ScopeId ScopeId
  | ConflictingReference NodeId NodeId ReferenceRole
  | DeclarationReferenceNameMismatch SymbolId NodeId String String
  | DeclarationReferenceScopeMismatch SymbolId NodeId ScopeId ScopeId

symbolLabel : SymbolId -> String
symbolLabel (MkSymbolId symbolNumber) = "symbol #" ++ show symbolNumber

scopeLabel : ScopeId -> String
scopeLabel (MkScopeId scopeNumber) = "scope #" ++ show scopeNumber

nodeLabel : NodeId -> String
nodeLabel (MkNodeId surfaceId desugarId) =
  "node #" ++ show surfaceId ++ "." ++ show desugarId

referenceRoleLabel : ReferenceRole -> String
referenceRoleLabel ValueReference = "value"
referenceRoleLabel AssignmentTarget = "assignment target"
referenceRoleLabel DeclarationReference = "declaration"
referenceRoleLabel TypeReference = "type"
referenceRoleLabel QualifierReference = "qualifier"
referenceRoleLabel ImportReference = "import"
referenceRoleLabel ConstructorReference = "constructor"
referenceRoleLabel PatternReference = "pattern"
referenceRoleLabel FieldReference = "field"
referenceRoleLabel MethodReference = "method"

public export
Show ResolutionInvariantError where
  show (MissingRootModule rootSymbolId) = "Root module is missing: " ++ symbolLabel rootSymbolId
  show (InvalidRootModule rootSymbolId) = "Root module is not a module: " ++ symbolLabel rootSymbolId
  show (MissingRootScope rootScopeId) = "Root scope is missing: " ++ scopeLabel rootScopeId
  show (InvalidRootScope rootScopeId) = "Root scope is not a ModuleScope: " ++ scopeLabel rootScopeId
  show (SymbolKeyMismatch tableKey storedSymbolId) =
    "Symbol table key " ++ symbolLabel tableKey ++ " contains " ++ symbolLabel storedSymbolId
  show (MissingDeclaringScope symbolId declaringScopeId) =
    symbolLabel symbolId ++ " has missing declaring " ++ scopeLabel declaringScopeId
  show (MissingDeclaringModule symbolId declaringModuleId) =
    symbolLabel symbolId ++ " has missing declaring module " ++ symbolLabel declaringModuleId
  show (InvalidDeclaringModule symbolId declaringModuleId) =
    symbolLabel symbolId ++ " has non-module declaring symbol " ++ symbolLabel declaringModuleId
  show (SelfDeclaringModule symbolId) =
    symbolLabel symbolId ++ " declares itself but is not the root module"
  show (ScopeKeyMismatch tableKey storedScopeId) =
    "Scope table key " ++ scopeLabel tableKey ++ " contains " ++ scopeLabel storedScopeId
  show (MissingParentScope scopeId parentScopeId) =
    scopeLabel scopeId ++ " has missing parent " ++ scopeLabel parentScopeId
  show (ScopeParentCycle scopeId) = "Scope parent cycle through " ++ scopeLabel scopeId
  show (BindingNameMismatch scopeId bindingNamespace bindingKey writtenName) =
    scopeLabel scopeId ++ " has " ++ show bindingNamespace ++ " binding key " ++ show bindingKey ++
      " with written name " ++ show writtenName
  show (MissingBindingTarget scopeId bindingNamespace bindingName targetSymbolId) =
    scopeLabel scopeId ++ " has " ++ show bindingNamespace ++ " binding " ++ show bindingName ++
      " targeting missing " ++ symbolLabel targetSymbolId
  show (MissingDeclaredSymbol scopeId symbolId) =
    scopeLabel scopeId ++ " lists missing declaration " ++ symbolLabel symbolId
  show (DuplicateDeclaredSymbol scopeId symbolId) =
    scopeLabel scopeId ++ " lists declaration twice: " ++ symbolLabel symbolId
  show (WrongDeclarationScope scopeId symbolId declaringScopeId) =
    scopeLabel scopeId ++ " lists " ++ symbolLabel symbolId ++ " declared in " ++ scopeLabel declaringScopeId
  show (MissingDeclarationOrderEntry scopeId symbolId) =
    scopeLabel scopeId ++ " omits declared symbol " ++ symbolLabel symbolId ++ " from declaration order"
  show (MissingReferenceSymbol symbolId) =
    "Reference table mentions missing " ++ symbolLabel symbolId
  show (ReferenceKeyMismatch bucketKey targetSymbolId occurrenceNodeId) =
    "Reference bucket " ++ symbolLabel bucketKey ++ " contains target " ++ symbolLabel targetSymbolId ++
      " at " ++ nodeLabel occurrenceNodeId
  show (MissingReferenceScope occurrenceNodeId enclosingScopeId) =
    "Reference at " ++ nodeLabel occurrenceNodeId ++ " has missing enclosing " ++ scopeLabel enclosingScopeId
  show (MissingNodeScope nodeId scopeId) =
    nodeLabel nodeId ++ " is mapped to missing " ++ scopeLabel scopeId
  show (MissingLocalSymbol symbolId) =
    "Local-variable metadata targets missing " ++ symbolLabel symbolId
  show (InvalidLocalSymbolKind symbolId) =
    "Local-variable metadata targets a non-local/non-parameter " ++ symbolLabel symbolId
  show (MissingMemberOwner ownerSymbolId) = "Member-scope owner is missing: " ++ symbolLabel ownerSymbolId
  show (InvalidMemberOwner ownerSymbolId) = "Symbol cannot own a member scope: " ++ symbolLabel ownerSymbolId
  show (MissingMemberScope ownerSymbolId memberScopeId) =
    symbolLabel ownerSymbolId ++ " has missing member " ++ scopeLabel memberScopeId
  show (InvalidMemberScopeKind ownerSymbolId memberScopeId) =
    symbolLabel ownerSymbolId ++ " has incompatible member scope kind at " ++ scopeLabel memberScopeId
  show (UnrestoredCurrentScope rootScopeId finalScopeId) =
    "Resolution ended in " ++ scopeLabel finalScopeId ++ " instead of root " ++ scopeLabel rootScopeId
  show (UnrestoredCurrentModule rootModuleId finalModuleId) =
    "Resolution ended in module " ++ symbolLabel finalModuleId ++ " instead of root " ++ symbolLabel rootModuleId
  show (InvalidCurrentScopeKind rootScopeId) =
    "Resolution did not restore ModuleScope for root " ++ scopeLabel rootScopeId
  show (UnrestoredConstContext constContextBoundary) =
    "Resolution ended inside a constant context bounded by " ++ scopeLabel constContextBoundary
  show (MissingLocalVarQualifiers symbolId) =
    "Local or parameter " ++ symbolLabel symbolId ++ " has no local-variable metadata"
  show (DeclaredBindingNameMismatch scopeId bindingNamespace writtenName targetSymbolId declaredName) =
    scopeLabel scopeId ++ " has " ++ show bindingNamespace ++ " declaration binding " ++ show writtenName ++
      " targeting " ++ symbolLabel targetSymbolId ++ " declared as " ++ show declaredName
  show (MissingReferenceNodeScope nodeId expectedScopeId) =
    "Reference node " ++ nodeLabel nodeId ++ " has no scope mapping; expected " ++ scopeLabel expectedScopeId
  show (ReferenceNodeScopeMismatch nodeId expectedScopeId actualScopeId) =
    "Reference node " ++ nodeLabel nodeId ++ " maps to " ++ scopeLabel actualScopeId ++
      " instead of its enclosing " ++ scopeLabel expectedScopeId
  show (ConflictingReference occurrenceNodeId contextNodeId referenceRole) =
    "Conflicting " ++ referenceRoleLabel referenceRole ++ " reference at " ++ nodeLabel occurrenceNodeId ++
      " in context " ++ nodeLabel contextNodeId
  show (DeclarationReferenceNameMismatch targetSymbolId occurrenceNodeId writtenName declaredName) =
    "Declaration reference at " ++ nodeLabel occurrenceNodeId ++ " spells " ++ show writtenName ++
      " but " ++ symbolLabel targetSymbolId ++ " is declared as " ++ show declaredName
  show (DeclarationReferenceScopeMismatch targetSymbolId occurrenceNodeId declaringScopeId referenceScopeId) =
    "Declaration reference at " ++ nodeLabel occurrenceNodeId ++ " is in " ++ scopeLabel referenceScopeId ++
      " but " ++ symbolLabel targetSymbolId ++ " is declared in " ++ scopeLabel declaringScopeId

public export
Interpolation ResolutionInvariantError where
  interpolate invariantError = show invariantError

hasKey : Ord k => k -> SortedMap k v -> Bool
hasKey key entries = isJust (lookup key entries)

check : Bool -> ResolutionInvariantError -> List ResolutionInvariantError
check True _ = []
check False invariantError = [invariantError]

isModule : SymbolKind -> Bool
isModule SymbolModule = True
isModule _ = False

isLocal : SymbolKind -> Bool
isLocal SymbolLocalBinding = True
isLocal SymbolFunctionParameter = True
isLocal SymbolSelfReceiverParameter = True
isLocal _ = False

canOwnMembers : SymbolKind -> Bool
canOwnMembers SymbolModule = True
canOwnMembers SymbolStruct = True
canOwnMembers SymbolEnum = True
canOwnMembers SymbolQEnum = True
canOwnMembers SymbolEnumVariant = True
canOwnMembers _ = False

-- Modules may reuse ModuleScope instead of allocating a separate MemberScope.
-- SymbolKind alone cannot distinguish a struct-like variant from a tuple variant.
memberScopeMatches : SymbolKind -> ScopeKind -> Bool
memberScopeMatches SymbolModule ModuleScope = True
memberScopeMatches _ MemberScope = True
memberScopeMatches _ _ = False

validateRoots : ResolvedModule -> List ResolutionInvariantError
validateRoots resolvedModule =
  let symbolErrors = case lookup resolvedModule.rootSymbolId resolvedModule.scopeTables.symbols of
        Nothing => [MissingRootModule resolvedModule.rootSymbolId]
        Just rootSymbolInfo => check (isModule rootSymbolInfo.symbolKind) (InvalidRootModule resolvedModule.rootSymbolId)
      scopeErrors = case lookup resolvedModule.rootScopeId resolvedModule.scopeTables.scopes of
        Nothing => [MissingRootScope resolvedModule.rootScopeId]
        Just rootScopeInfo => case rootScopeInfo.kind of
          ModuleScope => []
          _ => [InvalidRootScope resolvedModule.rootScopeId]
  in symbolErrors ++ scopeErrors

-- Check the final StateT cursor, without cascading when a root is already invalid.
validateFinalState : ResolvedModule -> List ResolutionInvariantError
validateFinalState resolvedModule =
  let scopeErrors = case lookup resolvedModule.rootScopeId resolvedModule.scopeTables.scopes of
        Just rootScopeInfo => case rootScopeInfo.kind of
          ModuleScope =>
            check (resolvedModule.scopeTables.currentScopeId == resolvedModule.rootScopeId)
                  (UnrestoredCurrentScope resolvedModule.rootScopeId resolvedModule.scopeTables.currentScopeId) ++
            (case resolvedModule.scopeTables.currentScopeKind of
               ModuleScope => []
               _ => [InvalidCurrentScopeKind resolvedModule.rootScopeId])
          _ => []
        Nothing => []
      moduleErrors = case lookup resolvedModule.rootSymbolId resolvedModule.scopeTables.symbols of
        Just rootSymbolInfo => if isModule rootSymbolInfo.symbolKind
          then check (resolvedModule.scopeTables.currentModuleSymbolId == resolvedModule.rootSymbolId)
                     (UnrestoredCurrentModule resolvedModule.rootSymbolId resolvedModule.scopeTables.currentModuleSymbolId)
          else []
        Nothing => []
      constContextErrors = case resolvedModule.scopeTables.constContextBoundary of
        Nothing => []
        Just constContextBoundary => [UnrestoredConstContext constContextBoundary]
  in scopeErrors ++ moduleErrors ++ constContextErrors

-- Index declaration order once: checking historical shadowed symbols must not
-- repeatedly scan a large scope's declaration list for every symbol.
declarationIndex : ResolvedModule -> SortedMap (ScopeId, SymbolId) ()
declarationIndex resolvedModule = fromList $
  concatMap (\(scopeId, scopeInfo) => map (\declaredSymbolId => ((scopeId, declaredSymbolId), ())) (scopeInfo.declaredSymbolsInOrder <>> []))
            (SortedMap.toList resolvedModule.scopeTables.scopes)

validateSymbol : ResolvedModule -> SortedMap (ScopeId, SymbolId) () ->
                 (SymbolId, ResolvedSymbolInfo) -> List ResolutionInvariantError
validateSymbol resolvedModule declarationOrderIndex (symbolKey, symbolInfo) =
  check (symbolKey == symbolInfo.symbolId) (SymbolKeyMismatch symbolKey symbolInfo.symbolId) ++
  check (hasKey symbolInfo.declaringScope resolvedModule.scopeTables.scopes) (MissingDeclaringScope symbolKey symbolInfo.declaringScope) ++
  -- Only the root module may be its own declaring module; see SymbolInfo.
  check (symbolInfo.declaringModule /= symbolKey || symbolKey == resolvedModule.rootSymbolId) (SelfDeclaringModule symbolKey) ++
  -- The root is implicit. Invalid self-declarations and missing scopes already
  -- have diagnostics above. Every other symbol, including shadowed and Prelude
  -- declarations, must occur in its lexical declaring scope's order list.
  (if symbolKey == resolvedModule.rootSymbolId || symbolInfo.declaringModule == symbolKey ||
      not (hasKey symbolInfo.declaringScope resolvedModule.scopeTables.scopes)
     then []
     else check (hasKey (symbolInfo.declaringScope, symbolKey) declarationOrderIndex)
                (MissingDeclarationOrderEntry symbolInfo.declaringScope symbolKey)) ++
  (if isLocal symbolInfo.symbolKind
     then check (hasKey symbolKey resolvedModule.scopeTables.localVarsMeta) (MissingLocalVarQualifiers symbolKey)
     else []) ++
  case lookup symbolInfo.declaringModule resolvedModule.scopeTables.symbols of
    Nothing => [MissingDeclaringModule symbolKey symbolInfo.declaringModule]
    Just declaringModuleInfo =>
      check (isModule declaringModuleInfo.symbolKind) (InvalidDeclaringModule symbolKey symbolInfo.declaringModule)

validateBinding : ResolvedModule -> ScopeId -> BindingNamespace ->
                  (String, ScopeBinding) -> List ResolutionInvariantError
validateBinding resolvedModule scopeId bindingNamespace (bindingKey, scopeBinding) =
  check (bindingKey == scopeBinding.writtenName) (BindingNameMismatch scopeId bindingNamespace bindingKey scopeBinding.writtenName) ++
  case lookup scopeBinding.target resolvedModule.scopeTables.symbols of
    Nothing => [MissingBindingTarget scopeId bindingNamespace bindingKey scopeBinding.target]
    Just targetSymbolInfo => case scopeBinding.bindingKind of
      DeclaredBinding =>
        check (scopeBinding.writtenName == targetSymbolInfo.declaredName)
              (DeclaredBindingNameMismatch scopeId bindingNamespace scopeBinding.writtenName scopeBinding.target targetSymbolInfo.declaredName)
      -- Imports and implicitly supplied Prelude aliases can use another spelling.
      _ => []

validateDeclarationOrder : ResolvedModule -> ScopeId -> (alreadyListedSymbols : SortedMap SymbolId ()) ->
                           List SymbolId -> List ResolutionInvariantError
validateDeclarationOrder _ _ _ [] = []
validateDeclarationOrder resolvedModule scopeId alreadyListedSymbols (symbolId :: remainingSymbolIds) =
  let duplicateErrors = check (not (hasKey symbolId alreadyListedSymbols)) (DuplicateDeclaredSymbol scopeId symbolId)
      symbolErrors = case lookup symbolId resolvedModule.scopeTables.symbols of
        Nothing => [MissingDeclaredSymbol scopeId symbolId]
        Just symbolInfo => check (symbolInfo.declaringScope == scopeId)
                                 (WrongDeclarationScope scopeId symbolId symbolInfo.declaringScope)
  in duplicateErrors ++ symbolErrors ++
     validateDeclarationOrder resolvedModule scopeId (insert symbolId () alreadyListedSymbols) remainingSymbolIds

validateScope : ResolvedModule -> (ScopeId, ScopeInfo) -> List ResolutionInvariantError
validateScope resolvedModule (scopeKey, scopeInfo) =
  let declaredSymbolIds = scopeInfo.declaredSymbolsInOrder <>> []
      parentErrors = case scopeInfo.parent of
        Nothing => []
        Just parentScopeId => check (hasKey parentScopeId resolvedModule.scopeTables.scopes) (MissingParentScope scopeKey parentScopeId)
  in check (scopeKey == scopeInfo.id) (ScopeKeyMismatch scopeKey scopeInfo.id) ++ parentErrors ++
     concatMap (validateBinding resolvedModule scopeKey TypeNamespace) (SortedMap.toList scopeInfo.typeBindings) ++
     concatMap (validateBinding resolvedModule scopeKey ValueNamespace) (SortedMap.toList scopeInfo.valueBindings) ++
     concatMap (validateBinding resolvedModule scopeKey FieldNamespace) (SortedMap.toList scopeInfo.fieldBindings) ++
     validateDeclarationOrder resolvedModule scopeKey empty declaredSymbolIds

-- A parent walk visits at most the number of scopes before stopping or repeating
-- a scope. Explicit fuel makes this total even on cyclic input. Completed walks
-- are memoized so shared parent chains are not retraversed for every scope.
-- `completedScopes` holds the scopes whose whole parent chain has been walked;
-- `scopesOnCurrentWalk` holds the scopes visited by the walk in progress.
walkParents : (remainingSteps : Nat) -> SortedMap ScopeId ScopeInfo -> (completedScopes : SortedMap ScopeId ()) ->
              (scopesOnCurrentWalk : SortedMap ScopeId ()) -> ScopeId -> (SortedMap ScopeId (), List ResolutionInvariantError)
walkParents Z _ completedScopes _ _ = (completedScopes, [])
walkParents (S remainingSteps) scopes completedScopes scopesOnCurrentWalk currentScopeId =
  if hasKey currentScopeId scopesOnCurrentWalk then (completedScopes, [ScopeParentCycle currentScopeId])
  else if hasKey currentScopeId completedScopes then (completedScopes, [])
  else case lookup currentScopeId scopes of
    Nothing => (completedScopes, []) -- Missing parents are reported by validateScope.
    Just currentScopeInfo =>
      let (completedAfterParentWalk, cycleErrors) = case currentScopeInfo.parent of
            Nothing => (completedScopes, [])
            Just parentScopeId => walkParents remainingSteps scopes completedScopes (insert currentScopeId () scopesOnCurrentWalk) parentScopeId
      in (insert currentScopeId () completedAfterParentWalk, cycleErrors)

validateParentCycles : SortedMap ScopeId ScopeInfo -> List ResolutionInvariantError
validateParentCycles scopes =
  let scopeEntries = SortedMap.toList scopes
      walkStepLimit = S (List.length scopeEntries)
      (_, cycleErrors) = foldl (walkParentsFromScope walkStepLimit) (empty, []) scopeEntries
  in cycleErrors
  where
    walkParentsFromScope : Nat -> (SortedMap ScopeId (), List ResolutionInvariantError) ->
                           (ScopeId, ScopeInfo) -> (SortedMap ScopeId (), List ResolutionInvariantError)
    walkParentsFromScope walkStepLimit (completedScopes, cycleErrors) (startScopeId, _) =
      let (completedAfterWalk, newCycleErrors) = walkParents walkStepLimit scopes completedScopes empty startScopeId
      in (completedAfterWalk, newCycleErrors ++ cycleErrors)

-- resolveName maps both its name occurrence and its context. Collapsed path
-- qualifiers may keep source occurrences without individual nodeScopes entries;
-- any mapping retained for them must still agree with the reference scope.
validateReferenceNodes : ResolvedModule -> SymbolReference -> List ResolutionInvariantError
validateReferenceNodes resolvedModule symbolReference =
  if not (hasKey symbolReference.enclosingScope resolvedModule.scopeTables.scopes) then []
  else concatMap checkNodeScope (nub [symbolReference.occurrence.nodeId, symbolReference.contextNode])
  where
    checkNodeScope : NodeId -> List ResolutionInvariantError
    checkNodeScope nodeId = case lookup nodeId resolvedModule.scopeTables.nodeScopes of
      Nothing => case symbolReference.role of
        QualifierReference =>
          if nodeId == symbolReference.contextNode then [MissingReferenceNodeScope nodeId symbolReference.enclosingScope] else []
        _ => [MissingReferenceNodeScope nodeId symbolReference.enclosingScope]
      Just mappedScopeId =>
        if hasKey mappedScopeId resolvedModule.scopeTables.scopes
          then check (mappedScopeId == symbolReference.enclosingScope)
                     (ReferenceNodeScopeMismatch nodeId symbolReference.enclosingScope mappedScopeId)
          else [] -- validateResolvedModule reports the dangling nodeScopes entry.

validateDeclarationReference : ResolvedModule -> SymbolReference -> List ResolutionInvariantError
validateDeclarationReference resolvedModule symbolReference = case symbolReference.role of
  DeclarationReference => case lookup symbolReference.target resolvedModule.scopeTables.symbols of
    Nothing => []
    Just targetSymbolInfo =>
      check (symbolReference.writtenName == targetSymbolInfo.declaredName)
            (DeclarationReferenceNameMismatch symbolReference.target symbolReference.occurrence.nodeId
                                              symbolReference.writtenName targetSymbolInfo.declaredName) ++
      (if hasKey targetSymbolInfo.declaringScope resolvedModule.scopeTables.scopes &&
          hasKey symbolReference.enclosingScope resolvedModule.scopeTables.scopes
         then check (symbolReference.enclosingScope == targetSymbolInfo.declaringScope)
                    (DeclarationReferenceScopeMismatch symbolReference.target symbolReference.occurrence.nodeId
                                                       targetSymbolInfo.declaringScope symbolReference.enclosingScope)
         else [])
  _ => []

validateReference : ResolvedModule -> SymbolId -> SymbolReference -> List ResolutionInvariantError
validateReference resolvedModule bucketKey symbolReference =
  let targetErrors = if symbolReference.target == bucketKey then [] else
        ReferenceKeyMismatch bucketKey symbolReference.target symbolReference.occurrence.nodeId ::
          check (hasKey symbolReference.target resolvedModule.scopeTables.symbols) (MissingReferenceSymbol symbolReference.target)
  in targetErrors ++ check (hasKey symbolReference.enclosingScope resolvedModule.scopeTables.scopes)
                          (MissingReferenceScope symbolReference.occurrence.nodeId symbolReference.enclosingScope) ++
     validateReferenceNodes resolvedModule symbolReference ++ validateDeclarationReference resolvedModule symbolReference

validateReferences : ResolvedModule -> (SymbolId, SnocList SymbolReference) -> List ResolutionInvariantError
validateReferences resolvedModule (bucketKey, bucketReferences) =
  check (hasKey bucketKey resolvedModule.scopeTables.symbols) (MissingReferenceSymbol bucketKey) ++
  concatMap (validateReference resolvedModule bucketKey) (bucketReferences <>> [])

sameReferenceData : SymbolReference -> SymbolReference -> Bool
sameReferenceData firstReference secondReference =
  firstReference.target == secondReference.target && firstReference.enclosingScope == secondReference.enclosingScope &&
  firstReference.writtenName == secondReference.writtenName &&
  spanKey firstReference.occurrence.span == spanKey secondReference.occurrence.span
  where
    spanKey : SourceSpan -> (String, Nat, Nat, Nat, Nat)
    spanKey sourceSpan = (sourceSpan.file, sourceSpan.start.line, sourceSpan.start.column, sourceSpan.end.line, sourceSpan.end.column)

-- Repeated records for the same occurrence/context/role are tolerated if their
-- data agrees; resolution currently visits each occurrence once, so none are
-- expected. Different roles or contexts are also valid; conflicting copies are not.
validateReferenceConsistency : ResolvedModule -> List ResolutionInvariantError
validateReferenceConsistency resolvedModule =
  let allReferences = concatMap (\(_, bucketReferences) => bucketReferences <>> []) (SortedMap.toList resolvedModule.scopeTables.references)
      (_, conflictErrors) = foldl recordReference (empty, []) allReferences
  in reverse conflictErrors
  where
    -- `referenceByOccurrence` maps each occurrence, context and role seen so far to its first reference.
    recordReference : (SortedMap (NodeId, NodeId, String) SymbolReference, List ResolutionInvariantError) ->
                      SymbolReference -> (SortedMap (NodeId, NodeId, String) SymbolReference, List ResolutionInvariantError)
    recordReference (referenceByOccurrence, conflictErrors) symbolReference =
      let occurrenceKey = (symbolReference.occurrence.nodeId, symbolReference.contextNode, referenceRoleLabel symbolReference.role)
      in case lookup occurrenceKey referenceByOccurrence of
        Nothing => (insert occurrenceKey symbolReference referenceByOccurrence, conflictErrors)
        Just previousReference =>
          (referenceByOccurrence, if sameReferenceData previousReference symbolReference then conflictErrors else
            ConflictingReference symbolReference.occurrence.nodeId symbolReference.contextNode symbolReference.role :: conflictErrors)

validateLocal : ResolvedModule -> (SymbolId, ResolvedLocalVarQualifiers) -> List ResolutionInvariantError
validateLocal resolvedModule (localSymbolId, _) =
  case lookup localSymbolId resolvedModule.scopeTables.symbols of
    Nothing => [MissingLocalSymbol localSymbolId]
    Just localSymbolInfo => check (isLocal localSymbolInfo.symbolKind) (InvalidLocalSymbolKind localSymbolId)

validateMembers : ResolvedModule -> (SymbolId, ScopeId) -> List ResolutionInvariantError
validateMembers resolvedModule (ownerSymbolId, memberScopeId) =
  let ownerErrors = case lookup ownerSymbolId resolvedModule.scopeTables.symbols of
        Nothing => [MissingMemberOwner ownerSymbolId]
        Just ownerSymbolInfo => check (canOwnMembers ownerSymbolInfo.symbolKind) (InvalidMemberOwner ownerSymbolId)
      scopeErrors = case lookup memberScopeId resolvedModule.scopeTables.scopes of
        Nothing => [MissingMemberScope ownerSymbolId memberScopeId]
        Just memberScopeInfo => case lookup ownerSymbolId resolvedModule.scopeTables.symbols of
          Nothing => []
          Just ownerSymbolInfo =>
            check (memberScopeMatches ownerSymbolInfo.symbolKind memberScopeInfo.kind) (InvalidMemberScopeKind ownerSymbolId memberScopeId)
  in ownerErrors ++ scopeErrors

||| Check the stored resolution tables; an empty list means these invariants hold.
||| Requires the final module cursor, metadata for local/parameter symbols,
||| declaration order for non-root symbols, and consistent stored references.
||| This does not re-resolve names, check access visibility, or walk the AST to
||| require a scope/reference entry for every relevant node. Member references may
||| still be deferred to typechecking. Qualifier occurrences may retain NodeIds
||| absent from the collapsed resolved AST and nodeScopes. Identical repeated
||| reference records are tolerated, conflicting ones are not.
||| Historical shadowed declarations are valid even when no current name-map
||| entry points to them. Declaration order
||| is checked for membership/duplicates, not reconstructed from source spans.
public export
validateResolvedModule : ResolvedModule -> List ResolutionInvariantError
validateResolvedModule resolvedModule =
  validateRoots resolvedModule ++ validateFinalState resolvedModule ++
  concatMap (validateSymbol resolvedModule (declarationIndex resolvedModule)) (SortedMap.toList resolvedModule.scopeTables.symbols) ++
  concatMap (validateScope resolvedModule) (SortedMap.toList resolvedModule.scopeTables.scopes) ++
  validateParentCycles resolvedModule.scopeTables.scopes ++
  concatMap (validateReferences resolvedModule) (SortedMap.toList resolvedModule.scopeTables.references) ++
  validateReferenceConsistency resolvedModule ++
  concatMap (\(nodeId, scopeId) => check (hasKey scopeId resolvedModule.scopeTables.scopes) (MissingNodeScope nodeId scopeId))
            (SortedMap.toList resolvedModule.scopeTables.nodeScopes) ++
  concatMap (validateLocal resolvedModule) (SortedMap.toList resolvedModule.scopeTables.localVarsMeta) ++
  concatMap (validateMembers resolvedModule) (SortedMap.toList resolvedModule.scopeTables.memberScopes)
