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

-- Merged variables form union-find trees: each non-root variable stores its
-- parent's ID, and the root holds the shared inference state. An open root's
-- rank is an upper bound on its tree's height. Merging two roots puts the
-- lower-ranked one under the other, which keeps trees shallow; equal ranks
-- allow either root to survive and raise its rank by one.
public export
data InferenceVariableState                         -- An inference variable is a placeholder for something the type checker may not know yet. 
  = OpenTypeVariable TypeVariableDomain Nat         -- unknown type; stores allowed types and tree rank
  | FixedTypeVariable TcType                        -- stores the inferred type
  | OpenQuantumUsage Nat                            -- unknown linear/affine qualifier; Nat is the tree rank
  | FixedQuantumUsage QuantumUsageQualifier         -- stores the inferred linear/affine qualifier
  | ParentReference Nat                             -- parent variable ID; follow it to the shared inference state
                                                    -- Both variables represent types, or both quantum usage qualifiers.

