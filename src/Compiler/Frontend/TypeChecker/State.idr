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
  = ValueLoop (Maybe TcType)     -- `loop`: the type its break values combine to so far
  | UnitLoop                     -- while / for: break takes no value

public export
record InferenceState where                                       -- per function or const initializer, emptied by writeback
  constructor MkInferenceState
  nextInferenceVariableId : Nat                                   -- identifier of the next fresh inference variable
  inferenceVariables      : SortedMap Nat InferenceVariableState  -- inference variables by their Nat identifier: placeholders for something the type checker doesn't know yet.
  expressionTypes         : SortedMap NodeId TcType               -- type of every expression in the body being checked
  patternTypes            : SortedMap NodeId TcType               -- type of each pattern node in the body being checked
  binderTypes             : SortedMap SymbolId TcType             -- locals of the function being checked
  scratchBinders          : List SymbolId                         -- list of the local bindings in the current body that were declared with let scratch
  uncomputeModeBinders    : List SymbolId                         -- list of the variables in the current function that were declared with :=
  integerLiterals         : List (NodeId, Integer)                -- list of the integer literals in the current body whose range can't be checked yet
  enclosingLoops          : List LoopContext                      -- stack of loops surrounding the code that pass B is checking right now, innermost first

public export
emptyInferenceState : InferenceState
emptyInferenceState = MkInferenceState 0 empty empty empty empty [] [] [] []

public export
record TypeCheckerState where
  constructor MkTypeCheckerState
  typeTables                  : TypeTables
  enclosingFunctionReturnType : Maybe LeafType                    -- declared return type of the function whose body pass B is checking; Nothing for a const initializer
  inferenceState              : InferenceState                    -- pass B's (BodyCheck) scratch space for the one body it is checking right now
  topLevelItems               : SortedMap SymbolId ResolvedItem   -- maps each top-level item's symbol (const and fn for now) to that item's resolved AST node
  checkedBodies               : SortedSet SymbolId                -- set of functions whose bodies pass B (BodyCheck) has already finished
  constExprs                  : SortedMap NodeId Nat              -- memo table for evaluated length expressions

public export
data CheckFailure
  = Blocked SymbolId        -- needs this symbol's signature, value or checked body first
  | Failed TypeError

export
liftTypeError : TypeError -> StateT TypeCheckerState (Either CheckFailure) a
liftTypeError typeError = lift (Left (Failed typeError))

export
blocked : SymbolId -> StateT TypeCheckerState (Either CheckFailure) a
blocked awaitedSymbol = do
  checkerState <- get
  case lookup awaitedSymbol checkerState.topLevelItems of
    Just _  => lift (Left (Blocked awaitedSymbol))
    Nothing => unreachable __FILE__ {function = "blocked"} {reason = "symbol cannot be found in the checker state top-level items"}

--------------------------------------------------------------------------------
-- Recording results
--------------------------------------------------------------------------------

updatedTypedSymbolInfo : TypedSymbolInfo -> InferredType -> TypedSymbolInfo
updatedTypedSymbolInfo symbolInfo inferredType = { symbolType := inferredType } symbolInfo

export
recordSymbolType : SymbolId -> LeafType -> StateT TypeCheckerState (Either CheckFailure) ()
recordSymbolType symbolId leafType = do
  checkerState <- get
  case lookup symbolId checkerState.typeTables.symbols of
    Nothing => unreachable __FILE__ {function = "recordSymbolType"} {reason = "symbol cannot be found in the symbol table"}
    Just symbolInfo => do
      let updatedSymbolInfo = updatedTypedSymbolInfo symbolInfo (ResolvedType leafType)
      modify $ \currentState => { typeTables.symbols := insert symbolId updatedSymbolInfo currentState.typeTables.symbols } currentState

typedLocalVarQualifiers : TypedLocalVarQualifiers -> LeafType -> TypedLocalVarQualifiers
typedLocalVarQualifiers localVarQualifiers leafType =
  if hasOwnedQbit leafType
    then { quantumStorage := AssignedQbitStorage (MkQuantumStorageProperties NoAutomaticCleanup) } localVarQualifiers
    else { quantumStorage := NotQbitLocal } localVarQualifiers

export
recordParameterStorage : SymbolId -> LeafType -> StateT TypeCheckerState (Either CheckFailure) ()
recordParameterStorage symbolId leafType = do
  checkerState <- get
  case lookup symbolId checkerState.typeTables.localVarsMeta of
    Nothing => unreachable __FILE__ {function = "recordParameterStorage"} {reason = "symbol cannot be found in the local variable metadata"}
    Just localVariableQualifiers => do
      let classifiedQualifiers = typedLocalVarQualifiers localVariableQualifiers leafType
      modify $ \currentState => { typeTables.localVarsMeta := insert symbolId classifiedQualifiers currentState.typeTables.localVarsMeta } currentState

export
recordConstValue : SymbolId -> ConstValue -> StateT TypeCheckerState (Either CheckFailure) ()
recordConstValue symbolId constValue =
  modify $ \currentState => { typeTables.constValues := insert symbolId constValue currentState.typeTables.constValues } currentState
