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
-- unknowns while a function body or const initializer is being checked: the
-- type of an unsuffixed literal (TcVariable) and the quantum usage of a
-- `qalloc` qbit (QuantumUsageVariable). Writeback replaces every unknown,
-- by what unification fixed it to or by its default, and turns the TcType
-- into a LeafType.
--------------------------------------------------------------------------------

public export
data TcQuantumUsage
  = KnownQuantumUsage QuantumUsageQualifier
  | QuantumUsageVariable Nat          -- Nat identifies an entry in InferenceState.variables.
                                      -- If its quantum usage qualifier remains unknown when inference finishes,
                                      -- will default that qualifier to linear.


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
  | TcVariable Nat                     -- an unsuffixed literal's type, {integer} or {float}, Nat identifies an entry in InferenceState.variables.

public export
data TypeVariableKind
  = GeneralTypeKind                    -- type for elements of an empty array or type an unannotated, uninitialized local.
  | IntegerLiteral                     -- {integer}: any integer type or bit, defaults to i32
  | FloatLiteral                       -- {float}: f32, f64, angle32 or angle64, defaults to f64

public export
data VariableState
  = OpenTypeVariable TypeVariableKind Nat           -- root; Nat is its rank
  | FixedTypeVariable TcType                        -- root, solved
  | OpenQuantumUsage Nat                            -- root; rank
  | FixedQuantumUsage QuantumUsageQualifier         -- root, solved
  | LinkedVariable Nat                              -- not a root: same sort as its target

