module Compiler.Frontend.TypeChecker.State

import Compiler.Helper
import Control.Monad.State
import Data.SortedMap
import Data.SortedSet

import Compiler.Frontend.ScopeAndNameResolver.Data
import Compiler.Frontend.TypeChecker.Data
import Compiler.Frontend.TypeChecker.TcType
import Compiler.Frontend.TypeChecker.Type
import Compiler.Frontend.Syntax.AST
import Compiler.Frontend.ASTData
import Compiler.Frontend.ASTPhases
import Compiler.Frontend.QuantumAnnotations
import Compiler.Frontend.Syntax.Common

%default total

--------------------------------------------------------------------------------
-- Type checker state
--------------------------------------------------------------------------------
-- Threaded through the checker in a State monad and dropped when checking
-- ends: later passes read only the TypeTables it builds.
--------------------------------------------------------------------------------

public export
data LoopContext
  = ValueLoop (Maybe TcType)                      -- `loop`: the type its break values combine to so far
  | UnitLoop                                      -- while / for: break takes no value

public export
record FunctionContext where
  constructor MkFunctionContext
  returnType     : LeafType

public export
record InferenceState where                       -- per function or const initializer, emptied by writeback
  constructor MkInferenceState
  nextVariable     : Nat                          -- number of the next fresh inference variable
  variables        : SortedMap Nat VariableState
  expressionTypes  : SortedMap NodeId TcType
  patternTypes     : SortedMap NodeId TcType
  binderTypes      : SortedMap SymbolId TcType    -- locals of the function being checked
  scratchBinders   : List SymbolId
  uncomputeBinders : List SymbolId                -- bound with :=
  integerLiterals  : List (NodeId, Integer)       -- range-checked at writeback
  loops            : List LoopContext             -- innermost first

public export
emptyInferenceState : InferenceState
emptyInferenceState = MkInferenceState 0 empty empty empty empty [] [] [] []

public export
record TypeCheckerState where
  constructor MkTypeCheckerState
  tables          : TypeTables
  functionContext : Maybe FunctionContext            -- tells pass B (BodyCheck) which function it is operating inside, if any.
  inferenceState  : InferenceState                   -- pass B's (BodyCheck) scratch space for the one body it is checking right now
  declarations    : SortedMap SymbolId ResolvedItem  -- maps each top-level item's symbol to that item's resolved AST node
  checkedBodies   : SortedSet SymbolId               -- set of functions whose bodies pass B (BodyCheck) has already finished
  constExprs      : SortedMap NodeId Nat

public export
data CheckFailure
  = Blocked SymbolId                               -- needs this symbol's signature, value or checked body first
  | Failed TypeError

export
typeError : TypeError -> StateT TypeCheckerState (Either CheckFailure) a
typeError diagnostic = lift (Left (Failed diagnostic))

export
blocked : SymbolId -> StateT TypeCheckerState (Either CheckFailure) a
blocked awaitedSymbol = do
  checkerState <- get
  case lookup awaitedSymbol checkerState.declarations of
    Just _  => lift (Left (Blocked awaitedSymbol))
    Nothing => unreachable __FILE__ {function = "blocked"} {reason = "symbol cannot be found in checker state top level declarations"}

--------------------------------------------------------------------------------
-- Recording results
--------------------------------------------------------------------------------

updatedTypedSymbolInfo : TypedSymbolInfo -> InferredType -> TypedSymbolInfo
updatedTypedSymbolInfo symbolInfo inferredType = { symbolType := inferredType } symbolInfo

export
recordSymbolType : SymbolId -> LeafType -> StateT TypeCheckerState (Either CheckFailure) ()
recordSymbolType symbolId leafType = do
  checkerState <- get
  case lookup symbolId checkerState.tables.symbols of
    Nothing => unreachable __FILE__ {function = "recordSymbolType"} {reason = "symbol cannot be found in the symbol table"}
    Just symbolInfo => do
      let updatedSymbolInfo = updatedTypedSymbolInfo symbolInfo (ResolvedType leafType)
      modify $ \currentState => { tables.symbols := insert symbolId updatedSymbolInfo currentState.tables.symbols } currentState

typedLocalVarQualifiers : TypedLocalVarQualifiers -> LeafType -> TypedLocalVarQualifiers
typedLocalVarQualifiers localVarQualifiers leafType =
  if hasOwnedQbit leafType
    then { quantumStorage := AssignedQbitStorage (MkQuantumStorageProperties NoAutomaticCleanup) } localVarQualifiers
    else { quantumStorage := NotQbitLocal } localVarQualifiers

export
recordParameterStorage : SymbolId -> LeafType -> StateT TypeCheckerState (Either CheckFailure) ()
recordParameterStorage symbolId leafType = do
  checkerState <- get
  case lookup symbolId checkerState.tables.localVarsMeta of
    Nothing => unreachable __FILE__ {function = "recordParameterStorage"} {reason = "symbol cannot be found in the local variable metadata"}
    Just localVariableQualifiers => do
      let classifiedQualifiers = typedLocalVarQualifiers localVariableQualifiers leafType
      modify $ \currentState => { tables.localVarsMeta := insert symbolId classifiedQualifiers currentState.tables.localVarsMeta } currentState

export
recordConstValue : SymbolId -> ConstValue -> StateT TypeCheckerState (Either CheckFailure) ()
recordConstValue symbolId constValue =
  modify $ \currentState => { tables.constValues := insert symbolId constValue currentState.tables.constValues } currentState
