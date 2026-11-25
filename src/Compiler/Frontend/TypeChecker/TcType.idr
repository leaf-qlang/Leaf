module Compiler.Frontend.TypeChecker.TcType

import Data.List1

import Compiler.Frontend.TypeChecker.Type
import Compiler.Frontend.ASTData
import Compiler.Frontend.Token
import Compiler.Frontend.Syntax.Common
import Compiler.Frontend.Syntax.Operator

%default total

--------------------------------------------------------------------------------
-- Checker-internal types
--------------------------------------------------------------------------------
-- TcType mirrors LeafType constructor for constructor, but may still contain
-- unknowns while a function body or const initializer is still being checked:
-- an unknown type (TcVariable), such as the type of an unsuffixed literal,
-- of the elements of an empty array, or of an unannotated, uninitialized local;
-- and the quantum usage of a `qalloc` qbit (UnknownQuantumUsage).
--------------------------------------------------------------------------------

public export
data TcQuantumUsage
  = KnownQuantumUsage QuantumUsageQualifier
  | UnknownQuantumUsage Nat                  -- Nat identifies an entry in InferenceState.inferenceVariables.

public export
data TcType
  = TcPrimitiveType TypPrimName
  | TcNamedType SymbolId
  | TcUnitType
  | TcTupleType (List1 TcType)
  | TcArrayType TcType Nat
  | TcSliceType TcType
  | TcRangeType RangeShape TcType
  | TcReferenceType BorrowKind TcType
  | TcFunctionType FunctionEffect (List SupportKind) (List TcType) TcType
  | TcQuantumQualifiedType TcQuantumUsage TcType
  | TcNeverType
  | TcStringLiteralType
  | TcVariable Nat                           -- an unknown type; Nat identifies an entry in InferenceState.inferenceVariables

-- The set of types that an unknown type (TcVariable) may still turn out to be.
public export
data TypeVariableDomain
  = AnyTypeDomain                            -- any type: type of the elements of an empty array or of an unannotated, uninitialized local; has no default
  | IntegerLiteralDomain                     -- any integer type or bit, defaults to i32
  | FloatLiteralDomain                       -- f32, f64, angle32 or angle64, defaults to f64

-- Unified variables form union-find trees: each variable links to a parent,
-- and the root at the top holds the state of the whole tree. An open root's
-- rank is an upper bound on its tree's height. Linking two roots puts the
-- lower-ranked one under the other, which keeps trees shallow; equal ranks
-- link either way and raise the surviving root's rank by one.
public export
data InferenceVariableState                         -- An inference variable is a placeholder for something the type checker may not know yet. 
  = OpenTypeVariable TypeVariableDomain Nat         -- root; Nat is its union-find rank
  | FixedTypeVariable TcType                        -- root, solved
  | OpenQuantumUsage Nat                            -- root; Nat is its union-find rank
  | FixedQuantumUsage QuantumUsageQualifier         -- root, solved
  | LinkedVariable Nat                              -- not a root: Nat identifies its parent, of the same sort
                                                    -- Entry for an inference variable that was unified with another one, it no longer holds 
                                                    -- its own state; it says "I'm the same unknown as variable #n, so look there 

