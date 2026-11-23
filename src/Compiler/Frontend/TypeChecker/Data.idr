module Compiler.Frontend.TypeChecker.Data

import Data.List1
import Data.SortedMap
import Data.String

import Compiler.Frontend.ScopeAndNameResolver.Data
import Compiler.Frontend.TypeChecker.Type
import Compiler.Frontend.ASTData
import Compiler.Frontend.ASTPhases
import Compiler.Frontend.QuantumAnnotations
import Compiler.Frontend.Source
import Compiler.Frontend.Syntax.AST
import Compiler.Frontend.Syntax.Common
import Compiler.Frontend.Token

%default total

public export
data InferredType
  = TypeNotYetResolved
  | ResolvedType LeafType
  | NoValueType                                              -- the symbol names a namespace or a type, so it has no value type

public export
TypedSymbolInfo : Type
TypedSymbolInfo = SymbolInfo InferredType

public export
data QbitStorageStatus
  = PendingQbitClassification
  | NotQbitLocal
  | AssignedQbitStorage QuantumStorageProperties

public export
TypedLocalVarQualifiers : Type
TypedLocalVarQualifiers = LocalVarQualifiers QbitStorageStatus

public export
data ConstValue
  = ConstInteger Integer
  | ConstFloat Double
  | ConstBool Bool
  | ConstUnit
  | ConstTuple (List1 ConstValue)
  | ConstArray (List ConstValue)

public export
data Coercion
  = FloatToAngle TypPrimName               -- an f32/f64 gate angle argument becomes this angle32/angle64
  | ArrayToSlice Nat                       -- &[T; N] passed as &[T]; N kept so lowering can specialize
  | BitToBool                              -- a bit condition: `if b` means `if b == 1`

public export
data BuiltinForm                           -- which documented overload of a builtin was chosen
  = SingleQbit                             -- measr(q), qalloc(), barrier()
  | SelectedQbits Nat                      -- measr(q1, q2, q3), barrier(q1, q2, q3)
  | QbitArray Nat                          -- measr(qs), qalloc(3)
  | NoOverload                             -- len(a), rev(0..n)

public export
data Callee
  = FunctionCall SymbolId                  -- declared, prelude or associated function named at the call
  | MethodCall SymbolId                    -- resolved method
  | ValueCall                              -- a function-typed value: parameter, adjoint(f), ctrl(..).apply(f)
  | BuiltinCall Builtin BuiltinForm

public export
data ArgumentPassing
  = ByValue                                -- copied (classical) or moved (quantum)
  | Threaded                               -- &q, &qs[1..], &mut x, or a qbit reference: the place is updated

public export
record CallResolution where
  constructor MkCallResolution
  callee          : Callee
  argumentPassing : List ArgumentPassing   -- one per argument, in order

public export
record TypeTables where
  constructor MkTypeTables
  -- Scope structure and lexical environments.
  scopes           : SortedMap ScopeId ScopeInfo
  nodeScopes       : SortedMap NodeId ScopeId                       -- lexical environment used to resolve a node
  -- Symbols, declaration metadata, and uses.
  symbols          : SortedMap SymbolId TypedSymbolInfo
  localVarsMeta    : SortedMap SymbolId TypedLocalVarQualifiers     -- Local/parameter declaration metadata, keyed by the corresponding SymbolId.
  memberScopes     : SortedMap SymbolId ScopeId                     -- Given a symbol, which scope contains its members? Member example: const and functions inside a module
  references       : SortedMap SymbolId (SnocList SymbolReference)  -- records where each symbol appears in the program
  -- Evaluated constant values.
  constValues      : SortedMap SymbolId ConstValue
  -- Types assigned to expression and pattern nodes.
  expressionTypes  : SortedMap NodeId LeafType                      -- every Expr node, type before any coercion
  patternTypes     : SortedMap NodeId LeafType                      -- patterns describe how to match or unpack a value and bind names to its parts.
  -- Typing decisions used by later compiler stages.
  coercions        : SortedMap NodeId Coercion                      -- Expr nodes whose value is implicitly converted
  calls            : SortedMap NodeId CallResolution                -- every ExprCall / ExprMethodCall node

--------------------------------------------------------------------------------
-- Ownership
--------------------------------------------------------------------------------
-- Filled by the OwnershipCheck pass from the typed AST. An access event records
-- what an operation does to a place; whether that is legal, and whether it is
-- the place's last use, is decided by the ownership analysis over control flow.
--------------------------------------------------------------------------------

public export
data AccessKind
  = ReadAccess          -- Observe/copy a value without transferring ownership.
  | WriteAccess         -- Initialize or replace a value.
  | MoveAccess          -- Transfer ownership elsewhere.
  | SharedBorrowAccess  -- Borrow without allowing mutation through this borrow.
  | MutableBorrowAccess -- Borrow with permission to mutate through this borrow.
  | ConsumeAccess       -- Consume a resource without transferring it onward.

public export
data PlaceRoot
  = LocalRoot SymbolId   -- A local variable or parameter, including a generated local.
  | TemporaryRoot NodeId -- Temporary storage produced by an expression, such as f() in f().x.

-- Projections are applied from left to right, starting at the place's root.
public export
data PlaceProjection
  = FieldProjection SymbolId -- The resolved field declaration, not its written spelling.
  | TupleProjection Nat      -- A zero-based tuple element index.
  | IndexProjection NodeId   -- The expression computing an array/slice index or range.
  | DereferenceProjection    -- The storage reached through a reference.

-- A field SymbolId alone identifies a declaration, not a particular value's
-- storage. For p.x, retain LocalRoot p and [FieldProjection x].
-- Different index-expression IDs or reference roots do not prove disjointness:
-- ownership analysis must account for dynamic indices and reference aliasing.
public export
record Place where
  constructor MkPlace
  root        : PlaceRoot
  projections : List PlaceProjection

public export
record AccessEvent where
  constructor MkAccessEvent
  kind       : AccessKind -- Classified using types and the operation's semantics.
  place      : Place      -- The affected local, temporary, field, element or referent.
  occurrence : AstInfo    -- The access's AST occurrence and diagnostic source span.

-- What a loop, adjoint or ctrl body touches from outside it. Lowering turns
-- `updated` into letrec parameters and results, or into a unitary's inputs
-- and outputs, and passes `readOnly` in unchanged.
public export
record Footprint where
  constructor MkFootprint
  updated  : List Place
  readOnly : List Place

public export
data CleanupAction
  = ResetScratch SymbolId                 -- `scratch` local: reset at scope exit
  | UncomputeLocal SymbolId               -- `:=` local: uncompute at scope exit

public export
record OwnershipTables where
  constructor MkOwnershipTables
  -- Events directly attributed to an expression/statement, in local evaluation
  -- order; accesses recorded on child nodes must not be duplicated here.
  -- Compile-time-only references (e.g. path qualifiers) produce no access event.
  -- SortedMap key order is NOT execution order.
  accesses       : SortedMap NodeId (List AccessEvent)
  footprints     : SortedMap NodeId Footprint             -- loop / while / for / adjoint { } / ctrl(..) { } nodes
  cleanups       : SortedMap NodeId (List CleanupAction)  -- scope exits: block ends, return, break, continue
  borrowedPlaces : SortedMap SymbolId Place               -- reference locals: `let qv = &qs[1..]` gives qv ↦ qs[1..]

public export
record TypedModule where
  constructor MkTypedModule
  rootSymbolId    : SymbolId
  rootScopeId     : ScopeId
  ast             : TypedSourceFile
  typeTables      : TypeTables
  ownershipTables : OwnershipTables

public export
data TypeError
  = TypeMismatch LeafType LeafType SourceSpan                  -- expected type, actual type
  | CannotInferType SourceSpan                                 -- insufficient information to determine a type
  | NotCallable LeafType SourceSpan                            -- attempted to call a value whose type is not callable
  | WrongArgumentCount Nat Nat SourceSpan                      -- expected count, actual count
  | InvalidUnaryOperand String LeafType SourceSpan             -- operator, operand type
  | InvalidBinaryOperands String LeafType LeafType SourceSpan  -- operator, left type, right type
  | NotIndexable LeafType SourceSpan                           -- attempted indexing on an unsupported type
  | IntegerLiteralOutOfRange Integer LeafType SourceSpan       -- literal value, target type
  | InvalidCast LeafType LeafType SourceSpan                   -- source type, target type
  | InvalidQuantumQualifier String LeafType SourceSpan         -- qualifier, annotated type, ex: let scratch n: i32 = 5;
  | InvalidQbitReference SourceSpan                           -- explicit 'mut' on a qbit reference, ex: &mut qbit or &mut [qbit]
  | InvalidConditionType String LeafType SourceSpan            -- construct if/qif/sif/etc., actual type, ex: if q { ... } where q: qbit
  | QuantumWidthMismatch String Nat Nat SourceSpan             -- context, expected width, actual width. ex: ctrl(&q0, &q1).on(bs"1").apply(H)(&target);
  | EffectViolation FunctionEffect FunctionEffect SourceSpan   -- enclosing effect restriction, offending operation's effect, ex: measr(&q) inside a unitary function,
  | MissingCapability String SourceSpan                        -- required capability (adjoint or ctrl), ex: adjoint(f) when f has no established adjoint support
  | InvalidQuantumPattern String SourceSpan               -- explanation of the invalid pattern, ex: mixing integer and basis-string patterns in one qmatch, or using _ in smatch.
  | CyclicDeclaration (List String) SourceSpan                 -- symbols involved in a declaration dependency cycle
  -- Constant evaluation
  | NotAConstantExpression SourceSpan                          -- non-const or indirect call, for loop or quantum operation in a const context
  | IncorrectArrayLengthType LeafType SourceSpan               -- type of a length, repeat count or qalloc count that is not usize
  | ArrayLengthTooLarge Integer SourceSpan                     -- count outside 0..usize::MAX; defensive, since a typed usize value and an in-range literal cannot cause it
  | ArithmeticOverflow LeafType SourceSpan                     -- type of the overflowing operation, ex: 255u8 + 1 or 1u8 << 8
  | DivisionByZeroInConstant SourceSpan
  | ConstEvaluationLimitExceeded SourceSpan                    -- constant evaluation ran out of steps
  | InvalidConstantControlFlow String SourceSpan               -- jump keyword leaving a constant expression, ex: [0; { break; 3 }]
  -- Expressions, patterns and places
  | UnknownMember String SourceSpan                            -- member name; no supported type has named fields or methods
  | InvalidBuiltinContext String SourceSpan                    -- builtin used outside a call or a valid position, ex: let m = measr;
  | UnsupportedFeature String SourceSpan                       -- excluded construct, ex: string literal outside Param or function attributes
  | IndexOutOfBounds Integer Nat SourceSpan                    -- index, length
  | UnsizedValue LeafType SourceSpan                           -- unsized type used by value, ex: let s = a[1..3];
  | MissingRangeEndpoint String SourceSpan                     -- construct needing the endpoint (rev or for), ex: rev(1..)
  | ReversedRange Integer Integer SourceSpan                   -- start, end, ex: &a[3..1]
  | WrongPatternArity Nat Nat SourceSpan                       -- value's element count, pattern's element count
  | RefutableBindingPattern SourceSpan                         -- ex: let ZERO = 0; where ZERO is a constant
  | QuantumUsageMismatch QuantumUsageQualifier QuantumUsageQualifier SourceSpan  -- required, actual, ex: let affine r = H(q); with q linear
  | BreakValueInUnitLoop SourceSpan                            -- break with a value inside while or for
  | AssignmentThroughSharedReference SourceSpan                -- ex: r[0] = 0; where r: &[i32]
  -- Effects and attributes
  | InvalidAttributeEffect String FunctionEffect SourceSpan    -- attribute, function effect, ex: #[qasm_gate] general fn
  | JumpOutOfQuantumBlock String SourceSpan                    -- jump keyword leaving a ctrl or adjoint block
  -- Ownership, initialization and cleanup
  | LinearQbitNotConsumed SourceSpan                           -- binding or temporary holding a linear qbit that is never consumed
  | UseAfterMove String SourceSpan                             -- local used after it was moved
  | UntrackedElementMove SourceSpan                            -- move out of an array through a dynamic index
  | MoveOutOfBorrow SourceSpan                                 -- move of an owned qbit out through a reference
  | OverlappingBorrow SourceSpan                               -- access conflicting with a live exclusive loan
  | MutableBorrowOfImmutable String SourceSpan                 -- local borrowed with &mut but not declared mut
  | ImmutableAssignment String SourceSpan                      -- local written again without mut
  | UninitializedPlace String SourceSpan                       -- local read before it is definitely initialized
  | EscapingReference SourceSpan                               -- reference that outlives its referent
  | UnprovableCleanup SourceSpan                               -- scratch, := or uncompute without a valid inverse and release
  | UnprovableTransformation String SourceSpan                 -- adjoint or ctrl region that cannot be transformed

export
showTypeError : TypeError -> String
showTypeError typeError =
  case typeError of
    TypeMismatch expectedType actualType sourceSpan =>
      at sourceSpan $ "Expected type '" ++ show expectedType ++ "', but found '" ++ show actualType ++ "'."
    CannotInferType sourceSpan =>
      at sourceSpan "Cannot infer the type; add a type annotation."
    NotCallable calleeType sourceSpan =>
      at sourceSpan $ "Cannot call a value of type '" ++ show calleeType ++ "'."
    WrongArgumentCount expectedCount actualCount sourceSpan =>
      at sourceSpan $ "Expected " ++ show expectedCount ++ " argument(s), but received " ++ show actualCount ++ "."
    InvalidUnaryOperand operatorName operandType sourceSpan =>
      at sourceSpan $ "Operator '" ++ operatorName ++ "' cannot be applied to type '" ++ show operandType ++ "'."
    InvalidBinaryOperands operatorName leftType rightType sourceSpan =>
      at sourceSpan $ "Operator '" ++ operatorName ++ "' cannot be applied to types '" ++ show leftType ++ "' and '" ++ show rightType ++ "'."
    NotIndexable indexedType sourceSpan =>
      at sourceSpan $ "Cannot index a value of type '" ++ show indexedType ++ "'."
    IntegerLiteralOutOfRange literalValue targetType sourceSpan =>
      at sourceSpan $ "Integer literal " ++ show literalValue ++ " is out of range for type '" ++ show targetType ++ "'."
    InvalidCast sourceType targetType sourceSpan =>
      at sourceSpan $ "Cannot cast type '" ++ show sourceType ++ "' to '" ++ show targetType ++ "'."
    InvalidQuantumQualifier qualifierName annotatedType sourceSpan =>
      at sourceSpan $ "Quantum qualifier '" ++ qualifierName ++ "' is not valid for type '" ++ show annotatedType ++ "'."
    InvalidQbitReference sourceSpan =>
      at sourceSpan "Qbit references are mutable by default; omit 'mut' from the reference."
    InvalidConditionType constructName conditionType sourceSpan =>
      at sourceSpan $ "Type '" ++ show conditionType ++ "' is not a valid condition type for '" ++ constructName ++ "'."
    QuantumWidthMismatch widthContext expectedWidth actualWidth sourceSpan =>
      at sourceSpan $ "Quantum width mismatch in " ++ widthContext ++ ": expected " ++ show expectedWidth ++ ", but found " ++ show actualWidth ++ "."
    EffectViolation enclosingEffect operationEffect sourceSpan =>
      at sourceSpan $ "An operation with effect '" ++ show operationEffect ++ "' is not permitted in a function with effect '" ++ show enclosingEffect ++ "'."
    MissingCapability capabilityName sourceSpan =>
      at sourceSpan $ "The callable does not have established support for '" ++ capabilityName ++ "'."
    InvalidQuantumPattern explanation sourceSpan =>
      at sourceSpan $ "Invalid quantum pattern: " ++ explanation
    CyclicDeclaration cycleSymbolNames sourceSpan =>
      at sourceSpan $ "Cyclic declaration dependency involving symbols " ++ (joinBy ", " $ map (\symbolName => "'" ++ symbolName ++ "'") cycleSymbolNames) ++ "."
    NotAConstantExpression sourceSpan =>
      at sourceSpan "This expression cannot be evaluated at compile time."
    IncorrectArrayLengthType lengthType sourceSpan =>
      at sourceSpan $ "An array length, repeat count or qubit count must have type 'usize', but has type '" ++ show lengthType ++ "'."
    ArrayLengthTooLarge lengthValue sourceSpan =>
      at sourceSpan $ "The length " ++ show lengthValue ++ " does not fit in 'usize'."
    ArithmeticOverflow operationType sourceSpan =>
      at sourceSpan $ "Arithmetic overflow in a constant of type '" ++ show operationType ++ "'."
    DivisionByZeroInConstant sourceSpan =>
      at sourceSpan "Division by zero in a constant expression."
    ConstEvaluationLimitExceeded sourceSpan =>
      at sourceSpan "Constant evaluation exceeded its step limit."
    InvalidConstantControlFlow jumpKeyword sourceSpan =>
      at sourceSpan $ "'" ++ jumpKeyword ++ "' cannot leave a constant expression."
    UnknownMember memberName sourceSpan =>
      at sourceSpan $ "No member '" ++ memberName ++ "' exists on this value."
    InvalidBuiltinContext builtinName sourceSpan =>
      at sourceSpan $ "The builtin '" ++ builtinName ++ "' cannot be used here."
    UnsupportedFeature featureName sourceSpan =>
      at sourceSpan $ "'" ++ featureName ++ "' is not supported."
    IndexOutOfBounds index valueLength sourceSpan =>
      at sourceSpan $ "Index " ++ show index ++ " is out of bounds for length " ++ show valueLength ++ "."
    UnsizedValue unsizedType sourceSpan =>
      at sourceSpan $ "A value of unsized type '" ++ show unsizedType ++ "' must be used through a reference."
    MissingRangeEndpoint constructName sourceSpan =>
      at sourceSpan $ "The range is missing an endpoint that '" ++ constructName ++ "' needs."
    ReversedRange rangeStart rangeEnd sourceSpan =>
      at sourceSpan $ "The range " ++ show rangeStart ++ ".." ++ show rangeEnd ++ " runs backwards."
    WrongPatternArity valueElementCount patternElementCount sourceSpan =>
      at sourceSpan $ "The value has " ++ show valueElementCount ++ " element(s), but the pattern has " ++ show patternElementCount ++ "."
    RefutableBindingPattern sourceSpan =>
      at sourceSpan "This pattern does not match every value; a binding needs an irrefutable pattern."
    QuantumUsageMismatch requiredUsage actualUsage sourceSpan =>
      at sourceSpan $ "Expected a '" ++ show requiredUsage ++ "' qbit, but found a '" ++ show actualUsage ++ "' qbit; use weaken to make a linear qbit affine."
    BreakValueInUnitLoop sourceSpan =>
      at sourceSpan "A 'while' or 'for' loop cannot break with a value."
    AssignmentThroughSharedReference sourceSpan =>
      at sourceSpan "Cannot assign through a shared reference."
    InvalidAttributeEffect attributeName functionEffect sourceSpan =>
      at sourceSpan $ "The attribute '" ++ attributeName ++ "' is not allowed on a function with effect '" ++ show functionEffect ++ "'."
    JumpOutOfQuantumBlock jumpKeyword sourceSpan =>
      at sourceSpan $ "'" ++ jumpKeyword ++ "' cannot leave a ctrl or adjoint block."
    LinearQbitNotConsumed sourceSpan =>
      at sourceSpan "A linear qbit is never consumed; measure, discard or return it."
    UseAfterMove localName sourceSpan =>
      at sourceSpan $ "Use of '" ++ localName ++ "' after it was moved."
    UntrackedElementMove sourceSpan =>
      at sourceSpan "Cannot move an array element out through a dynamic index."
    MoveOutOfBorrow sourceSpan =>
      at sourceSpan "Cannot move a qbit out through a reference."
    OverlappingBorrow sourceSpan =>
      at sourceSpan "This access conflicts with a live exclusive borrow."
    MutableBorrowOfImmutable localName sourceSpan =>
      at sourceSpan $ "Cannot borrow '" ++ localName ++ "' mutably; declare it with 'mut'."
    ImmutableAssignment localName sourceSpan =>
      at sourceSpan $ "Cannot assign twice to immutable '" ++ localName ++ "'; declare it with 'mut'."
    UninitializedPlace localName sourceSpan =>
      at sourceSpan $ "'" ++ localName ++ "' is used before it is initialized."
    EscapingReference sourceSpan =>
      at sourceSpan "This reference outlives the value it refers to."
    UnprovableCleanup sourceSpan =>
      at sourceSpan "Cannot prove that these qubits can be uncomputed and released."
    UnprovableTransformation transformationName sourceSpan =>
      at sourceSpan $ "Cannot construct the '" ++ transformationName ++ "' transformation of this code."
  where
    at : SourceSpan -> String -> String
    at sourceSpan message = "Type error at \{sourceSpan}: \{message}"

public export
implementation Show TypeError where
  show = showTypeError

