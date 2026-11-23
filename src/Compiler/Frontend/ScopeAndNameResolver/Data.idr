module Compiler.Frontend.ScopeAndNameResolver.Data

import Compiler.Frontend.ASTData
import Compiler.Frontend.ASTPhases
import Compiler.Frontend.Helper
import Compiler.Frontend.QuantumAnnotations
import Compiler.Frontend.Source
import Compiler.Frontend.Syntax.AST

import Data.SortedMap

%default total

public export
ResolvedSymbolInfo : Type
ResolvedSymbolInfo = SymbolInfo ()

public export
data VariableMutability
  = ImmutableVariable
  | MutableVariable

public export
record LocalVarQualifiers (storage: Type) where
  constructor MkLocalVarQualifiers
  mutability     : VariableMutability
  quantumStorage : storage

public export
ResolvedLocalVarQualifiers : Type
ResolvedLocalVarQualifiers = LocalVarQualifiers ()

public export
record ScopeTables where
  constructor MkScopeTables
  -- Scope structure and lexical environments.
  scopes           : SortedMap ScopeId ScopeInfo
  nodeScopes       : SortedMap NodeId ScopeId                      -- lexical environment used to resolve a node
  -- Symbols, declaration metadata, and uses.
  symbols          : SortedMap SymbolId ResolvedSymbolInfo
  localVarsMeta    : SortedMap SymbolId ResolvedLocalVarQualifiers -- Local/parameter declaration metadata, keyed by the corresponding SymbolId.
  memberScopes     : SortedMap SymbolId ScopeId                    -- Given a symbol, which scope contains its members? Member example: const and functions inside a module
  references       : SortedMap SymbolId (SnocList SymbolReference)
  -- Resolver traversal state.
  currentScopeId        : ScopeId                                  -- current scope while threading ScopeTables through the State monad
  currentScopeKind      : ScopeKind
  currentModuleSymbolId : SymbolId                                 -- module enclosing the current scope
  constContextBoundary  : Maybe ScopeId                            -- while resolving the innermost array length, a repeat count in array declaration syntax or qalloc() 
                                                                   -- allocation register size, the scope enclosing it; locals and parameters declared in this outer scope 
                                                                   -- or its ancestors cannot be used here:
                                                                   -- ex: let a = [0; n];  is rejected because n is declared outside the boundary
                                                                   -- ex: let b = [0; { let k = 2; k }]; is allowed by this check because k is declared inside the expression
public export
(.nextSymbolId) : ScopeTables -> SymbolId
(.nextSymbolId) scopeTables =
  case maxKey scopeTables.symbols of
       Nothing => MkSymbolId 0
       Just (MkSymbolId largestSymbolNumber) => MkSymbolId (S largestSymbolNumber)

public export
(.nextScopeId) : ScopeTables-> ScopeId
(.nextScopeId) scopeTables =
  case maxKey scopeTables.scopes of
       Nothing => MkScopeId 0
       Just (MkScopeId largestScopeNumber) => MkScopeId (S largestScopeNumber)

public export
record ResolvedModule where
  constructor MkResolvedModule
  rootSymbolId : SymbolId
  rootScopeId  : ScopeId
  ast          : ResolvedSourceFile
  scopeTables  : ScopeTables

public export
data ResolutionError
  = UnresolvedName String SourceSpan                                    -- No matching declaration is visible at the use site
  | UnresolvedTypePath String SourceSpan                                -- Written type path: `Person`, `my_module::Config`. Leaf has no named types yet.
  | DuplicateDeclaration String (List SymbolId) SourceSpan SourceSpan   -- Current name span, then the previous declaration name span.
                                                                        -- Declarations conflict in the same scope and namespace,
  | InaccessibleSymbol String SymbolId SourceSpan                       -- Declaration exists but visibility rules prohibit access,
                                                                        -- example: accessing a private function from a sibling module.
  | BindingShadowsConstant String SymbolId SourceSpan SourceSpan        -- An explicit mutable binder cannot shadow a visible constant.
                                                                        -- Immutable bare names instead resolve to constant patterns.
  | LocalValueUsedAsConstant String SymbolId SourceSpan SourceSpan      -- Use span, then the local's declaration name span. As in Rust (E0435),
                                                                        -- array lengths, repeat counts in array declaration syntax, qalloc() allocation register size 
                                                                        -- cannot use local variables declared in enclosing scope (upstream).

-- Guide for future extensions:
-- IllegalCapture String SourceSpan                         -- Nested functions are forbidden from capturing enclosing locals,
                                                             -- example: `fn outer() { let x = 1; fn inner() -> i32 { x } }`
-- IllegalShadowing String SymbolId SourceSpan SourceSpan   -- A declaration shadows a protected name,
-- AmbiguousName String (List SymbolId) SourceSpan          -- Lookup finds multiple candidates without a rule selecting one.
-- UnresolvedPathSegment, when a component of a qualified path cannot be found, example: `my_library::missing::helper`.
-- InvalidPathQualifier, when a resolved symbol cannot qualify another path component, example: `count::helper` where `count` is an integer variable.
-- ConflictingImports, when imports introduce different symbols under the same name where forbidden, example: `use a::helper; use b::helper;`.
-- WrongNamespace, when a name exists only in a namespace incompatible with its use, example: `let y: x = 0;` where `x` names only a variable.
-- UseBeforeDeclaration, optionally when a local variable is referenced before its declaration, example: `let y = x; let x = 1;` with no earlier `x` in scope.
-- ModuleNotFound, during module loading when an external module cannot be located, example: `mod my_library;` with no corresponding module source.
-- CyclicImport, when an import cycle prevents resolution or violates Leaf’s rules, example: `a::helper` re-exports `b::helper`, which re-exports `a::helper`, with no actual definition.

export
showResolutionError : ResolutionError -> String
showResolutionError (UnresolvedName unresolvedName sourceSpan) =
  "Could not find a matching declaration for this name: '\{unresolvedName}' in '\{sourceSpan}'."
showResolutionError (UnresolvedTypePath typePathText sourceSpan) =
  "Could not find a type declaration for the type or type path: '\{typePathText}' in '\{sourceSpan}'. Leaf does not support named types yet!."
showResolutionError (DuplicateDeclaration declaredName _ sourceSpan previousDeclarationSpan) =
  "A duplicate declaration for name: '\{declaredName}' declared in '\{sourceSpan}' was found; the previous declaration is in '\{previousDeclarationSpan}'."
showResolutionError (InaccessibleSymbol inaccessibleName _ sourceSpan) =
  "At current location '\{sourceSpan}' the name: '\{inaccessibleName}' is not publicly accessible."
showResolutionError (BindingShadowsConstant bindingName _ sourceSpan constantDeclarationSpan) =
  "The mutable binding for name: '\{bindingName}' in '\{sourceSpan}' cannot shadow the constant declared in '\{constantDeclarationSpan}'."
showResolutionError (LocalValueUsedAsConstant localName _ sourceSpan localDeclarationSpan) =
  "The local: '\{localName}' used in '\{sourceSpan}' is not a constant and cannot be used in an array length, in a repeat count from an array declaration or in the qubits register size argument for qalloc; it is declared in '\{localDeclarationSpan}'."

export
implementation Show ResolutionError where
  show = showResolutionError
