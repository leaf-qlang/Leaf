module Compiler.Frontend.Validator.PostParseValidation

import Data.List
import Data.List1
import Compiler.Frontend.ASTData
import Compiler.Frontend.ASTPhases
import Compiler.Frontend.Source
import Compiler.Frontend.Token
import Compiler.Frontend.Syntax.AST
import Compiler.Frontend.Syntax.Attribute
import Compiler.Frontend.Syntax.Common
import Compiler.Frontend.Syntax.Literal
import Compiler.Frontend.Syntax.Name
import Compiler.Frontend.Syntax.Operator
import Compiler.Frontend.Syntax.Type

%default total

--------------------------------------------------------------------------------
-- Post-parse syntactic validation
--------------------------------------------------------------------------------
-- The pass that owns every check which is (a) NOT enforced by the AST's
-- shape, (b) NOT a parser rejection, and (c) decidable on the SURFACE TREE
-- ALONE -- no name resolution, no types. It runs immediately after parsing
-- and reports against the spans the AST preserved for exactly this purpose.
--
-- CHECKS OWNED HERE:
--   * unknown attribute names: only `qasm_gate` and `qasm_def` are
--       recognized
--   * duplicate attributes on one item: a repeated name is rejected at its
--       second occurrence
--   * conflicting attributes on one item: `qasm_gate` and `qasm_def` are
--       mutually exclusive and are rejected when applied together
--   * `&mut` on a SYNTACTICALLY-qbit type (`&mut qbit`, `&mut [qbit]`,
--       `&mut [qbit; 2]`, through parens/qualifiers), wherever a type occurs;
--   * `break` outside a loop, while still walking and validating its optional
--       value expression
--   * `continue` outside a loop
--   * `return` outside a function body (for example in a const initializer),
--       while still walking and validating its optional value expression
--   * a quantum usage qualifier written both on a `let` and inside its type
--       annotation (`let linear q: affine qbit = ...`); reported at every
--       qualifier at an owned position of the annotation (see "Owned
--       positions" in Compiler.Frontend.Syntax.Type), so qualifiers inside function
--       types are not repeats
--   * a quantum usage qualifier behind a reference, nested in its referent
--       (`&[linear qbit]`, `&(i32, affine qbit)`): a reference borrows its
--       referent without owning it; the parser already rejects one directly
--       after `&` (`&affine qbit`)
--   * an array length written as a (possibly parenthesized) integer literal
--       with a suffix other than usize (`[qbit; 3i8]`, `[0; (3u64)]`) or
--       a suffixed usize value that exceeds the target range: an array length
--       has type usize, so only a usize suffix or none is accepted
--
-- Duplicate bindings are checked by name resolution: an immutable bare
-- pattern name may denote a constant rather than introduce a binding.
-- This applies to function parameters as well as let and for patterns.
--
-- Shape of the pass: a plain structural walk accumulating a List of errors
-- (empty list = valid). No early exit -- diagnostics improve when the user
-- sees every independent problem at once.
--
-- TOTALITY DISCIPLINE:
-- Idris 2's size-change checker credits CONSTRUCTOR PATTERNS ONLY. A record
-- dot-projection feeding a recursive argument (`validateBlock context
-- functionDeclaration.functionBody`) is size-unknown, and one unknown edge poisons the whole
-- SCC -- and this walk is ONE SCC, because expressions and types are mutual
-- (casts contain types; array sizes contain expressions). So: destructure
-- every record in the pattern head or in a constructor pattern; never
-- project in a recursive position. Projections remain fine on non-recursive
-- data (ValidationContext, SourceSpan).
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- Validation errors
--------------------------------------------------------------------------------

public export
data ValidationError : Type where

  UnknownAttribute :
       (errorSpan : SourceSpan)
    -> (attributeNameText : String)
    -> ValidationError

  -- Same attribute name written twice on one item, e.g.
  -- `#[qasm_gate] #[qasm_gate] fn f() {}`. `errorSpan` points at the
  -- repeated (second) occurrence.
  DuplicateAttribute :
       (errorSpan : SourceSpan)
    -> (attributeNameText : String)
    -> ValidationError

  -- Two distinct KNOWN attributes on one item, e.g.
  -- `#[qasm_gate] #[qasm_def] fn f() {}`. Today's only known attributes,
  -- qasm_gate and qasm_def, name mutually exclusive compilation targets, so
  -- any two distinct known attributes together are a conflict; `errorSpan`
  -- points at the second one.
  ConflictingAttributes :
       (errorSpan : SourceSpan)
    -> (attributeNameText : String)
    -> ValidationError

  MutableBorrowOfQbit :
       (errorSpan : SourceSpan)
    -> ValidationError

  BreakOutsideLoop :
       (errorSpan : SourceSpan)
    -> ValidationError

  ContinueOutsideLoop :
       (errorSpan : SourceSpan)
    -> ValidationError

  ReturnOutsideFunction :
       (errorSpan : SourceSpan)
    -> ValidationError

  ControlBasisLengthMismatch :
       (errorSpan : SourceSpan)
    -> (controlCount : Nat)
    -> (basisLength : Nat)
    -> ValidationError

  -- A quantum usage qualifier written both on a `let` and inside its type
  -- annotation, e.g. `let linear q: affine qbit = qalloc();`. `errorSpan`
  -- points at the qualifier inside the annotation.
  QuantumUsageQualifierInLetAndType :
       (errorSpan : SourceSpan)
    -> (letQualifier : QuantumUsageQualifier)
    -> (typeQualifier : QuantumUsageQualifier)
    -> ValidationError

  -- A quantum usage qualifier at an owned position of a reference's referent,
  -- e.g. `&[linear qbit]`. `errorSpan` points at the qualifier.
  QuantumUsageQualifierBehindReference :
       (errorSpan : SourceSpan)
    -> (qualifier : QuantumUsageQualifier)
    -> ValidationError

  -- An array length written as an integer literal with a non-usize type
  -- suffix, e.g. `[qbit; 3u64]`. `errorSpan` points at the literal.
  NonUsizeArrayLength :
       (errorSpan : SourceSpan)
    -> (suffixType : TypPrimName)
    -> ValidationError

  -- An array length written as an integer literal whose value does not fit
  -- usize, e.g. `[qbit; 18446744073709551616usize]`. `errorSpan` points at the literal.
  ArrayLengthOutOfRange :
       (errorSpan : SourceSpan)
    -> (literalText : String)
    -> (suffixType : TypPrimName)
    -> (suffixMaximum : Nat)
    -> ValidationError

-- The span a renderer should point at.
public export
validationErrorSpan : ValidationError -> SourceSpan
validationErrorSpan validationError =
  case validationError of
    UnknownAttribute errorSpan _                    => errorSpan
    DuplicateAttribute errorSpan _                  => errorSpan
    ConflictingAttributes errorSpan _               => errorSpan
    MutableBorrowOfQbit errorSpan                   => errorSpan
    BreakOutsideLoop errorSpan                      => errorSpan
    ContinueOutsideLoop errorSpan                   => errorSpan
    ReturnOutsideFunction errorSpan                 => errorSpan
    ControlBasisLengthMismatch errorSpan _ _        => errorSpan
    QuantumUsageQualifierInLetAndType errorSpan _ _ => errorSpan
    QuantumUsageQualifierBehindReference errorSpan _ => errorSpan
    NonUsizeArrayLength errorSpan _                 => errorSpan
    ArrayLengthOutOfRange errorSpan _ _ _           => errorSpan

public export
Interpolation ValidationError where
  interpolate validationError =
    "\{validationErrorSpan validationError}: " ++
      case validationError of
        UnknownAttribute _ attributeNameText =>
          "unknown attribute `" ++ attributeNameText ++
          "` (supported: qasm_gate, qasm_def)"
        DuplicateAttribute _ attributeNameText =>
          "attribute `" ++ attributeNameText ++
          "` is already applied to this item"
        ConflictingAttributes _ attributeNameText =>
          "attribute `" ++ attributeNameText ++
          "` conflicts with another attribute already applied to this item " ++
          "(qasm_gate and qasm_def are mutually exclusive)"
        MutableBorrowOfQbit _ =>
          "`mut` should never be written on a qbit reference; qbit references are mutable by default"
        BreakOutsideLoop _ =>
          "`break` found outside of a loop"
        ContinueOutsideLoop _ =>
          "`continue` found outside of a loop"
        ReturnOutsideFunction _ =>
          "`return` found outside of a function body"
        ControlBasisLengthMismatch _ controlCount basisLength =>
          "control basis contains " ++ show basisLength ++
          " states, but the control expression has " ++ show controlCount ++
          " control qbits"
        QuantumUsageQualifierInLetAndType _ letQualifier typeQualifier =>
          "`" ++ show typeQualifier ++ "` cannot be written in the type " ++
          "annotation because the `let` already has the `" ++ show letQualifier ++
          "` qualifier; write the quantum usage qualifier in one place only"
        QuantumUsageQualifierBehindReference _ qualifier =>
          "`" ++ show qualifier ++ "` cannot be written behind a reference; " ++
          "a reference borrows its referent without owning it"
        NonUsizeArrayLength _ suffixType =>
          "an array length must have type `usize`, but the suffix gives it type `" ++
          show suffixType ++ "`; write a `usize` suffix, or none"
        ArrayLengthOutOfRange _ literalText suffixType suffixMaximum =>
          "the array length `" ++ literalText ++ "` does not fit in `" ++
          show suffixType ++ "`, whose largest value is " ++ show suffixMaximum

--------------------------------------------------------------------------------
-- Validation context
--------------------------------------------------------------------------------
-- The little positional state the walk threads. Note the Rust rule encoded
-- at the while/for sites below: the CONDITION of a while and the ITERATOR
-- expression of a for are validated with insideLoop = False -- a break
-- there does not target the loop it syntactically sits in.
--------------------------------------------------------------------------------

record ValidationContext where
  constructor MkValidationContext
  insideLoop         : Bool
  insideFunctionBody : Bool

-- Top level / signatures / const initializers.
topLevelContext : ValidationContext
topLevelContext = MkValidationContext False False

-- Entering a function body.
functionBodyContext : ValidationContext
functionBodyContext = MkValidationContext False True

--------------------------------------------------------------------------------
-- Leaf checks (no traversal needed)
--------------------------------------------------------------------------------

-- Do two known attribute kinds conflict when both are written on one item?
-- The only known kinds today, qasm_gate and qasm_def, name mutually
-- exclusive OpenQASM compilation targets and the spec never shows more than
-- one of them on the same function -- so any two DISTINCT known kinds
-- conflict.
knownAttributeKindsConflict : KnownAttributeKind -> KnownAttributeKind -> Bool
knownAttributeKindsConflict KnownQasmGate KnownQasmGate = False
knownAttributeKindsConflict KnownQasmDef  KnownQasmDef  = False
knownAttributeKindsConflict _             _             = True

-- Known attributes: unknown names are errors for now. Argument shape is not
-- checked here: `parseAttribute` already accepts nothing but `#[name]` or
-- `#[name("string")]`, so every attribute reaching this pass is already
-- well-shaped.
--
-- Walks the list left-to-right threading the (name, known-kind) pairs
-- already seen on THIS item, so a name repeated verbatim is
-- DuplicateAttribute and two distinct known kinds together (currently just
-- qasm_gate + qasm_def) is ConflictingAttributes.
validateAttributesAfterEarlierOnes :
     (earlierAttributes : List (String, Maybe KnownAttributeKind))
  -> List SurfaceAttribute
  -> List ValidationError
validateAttributesAfterEarlierOnes _ [] = []
validateAttributesAfterEarlierOnes earlierAttributes (MkAstNode attributeInfo _ (MkAttributeNode attributeNameNode _) :: remainingAttributes) =
  let MkAstNode _ _ (MkNameNode attributeNameText) = attributeNameNode
      attributeKind = recognizeKnownAttribute attributeNameText
      unknownError =
        case attributeKind of
          Nothing => [UnknownAttribute attributeInfo.span attributeNameText]
          Just _  => []
      duplicateError =
        if any (\earlierAttribute => fst earlierAttribute == attributeNameText) earlierAttributes
          then [DuplicateAttribute attributeInfo.span attributeNameText]
          else []
      conflictError =
        case attributeKind of
          Nothing => []
          Just knownKind =>
            if any (\earlierAttribute => maybe False (knownAttributeKindsConflict knownKind) (snd earlierAttribute)) earlierAttributes
              then [ConflictingAttributes attributeInfo.span attributeNameText]
              else []
  in unknownError ++ duplicateError ++ conflictError
       ++ validateAttributesAfterEarlierOnes ((attributeNameText, attributeKind) :: earlierAttributes) remainingAttributes

validateAttributeList : List SurfaceAttribute -> List ValidationError
validateAttributeList = validateAttributesAfterEarlierOnes []

-- Is this type SYNTACTICALLY a qbit-carrying type? Only the cases visible
-- without resolution: qbit itself, arrays/slices of it, through parens and
-- qualifiers. Path types that CONTAIN qbits are typing's problem.
isSyntacticallyQbitType : TyNode SurfaceAstPhase SurfaceExpr -> Bool
isSyntacticallyQbitType typeNode =
  case typeNode of
    TyPrimitive TypPrimQbit                     => True
    TyParenthesized (MkAstNode _ _ innerType)   => isSyntacticallyQbitType innerType
    TyQualified _ (MkAstNode _ _ qualifiedType) => isSyntacticallyQbitType qualifiedType
    TySlice (MkAstNode _ _ elementType)         => isSyntacticallyQbitType elementType
    TyArray (MkAstNode _ _ elementType) _       => isSyntacticallyQbitType elementType
    _                                           => False

-- Quantum usage qualifiers written at the owned positions of a type.
ownedPositionQualifiers : SurfaceTy -> List (SurfaceAstNode QuantumUsageQualifier)
ownedPositionQualifiers = mapMaybe positionQualifier . ownedPositions

-- A `let` carrying `linear` or `affine` must not repeat a quantum usage qualifier
-- inside its type annotation. `scratch` on the `let` is unaffected.
letQuantumUsageConflicts :
     List (AstNode SurfaceAstPhase QuantumStorageQualifier)
  -> Maybe SurfaceTy
  -> List ValidationError
letQuantumUsageConflicts _ Nothing = []
letQuantumUsageConflicts letQualifiers (Just typeAnnotation) =
  case mapMaybe (storageQuantumUsage . (.nodeValue)) letQualifiers of
    [] => []
    letQualifier :: _ =>
      map (\(MkAstNode qualifierInfo _ typeQualifier) =>
             QuantumUsageQualifierInLetAndType qualifierInfo.span letQualifier typeQualifier)
          (ownedPositionQualifiers typeAnnotation)

-- A reference's referent holds no quantum usage qualifier at an owned position.
-- Qualifiers behind a nested reference are reported when the walk reaches
-- that reference, since owned positions do not enter references.
qualifiersBehindReference : SurfaceTy -> List ValidationError
qualifiersBehindReference referencedType =
  map (\(MkAstNode qualifierInfo _ qualifier) =>
         QuantumUsageQualifierBehindReference qualifierInfo.span qualifier)
      (ownedPositionQualifiers referencedType)

-- An array length literal may carry only a usize suffix, and its value
-- must fit that type. Parentheses are looked
-- through because desugaring removes them, leaving the bare literal for
-- typing. Lengths computed by other expressions are left to typing.
arrayLengthErrors : SurfaceExpr -> List ValidationError
arrayLengthErrors (MkAstNode _ _ (ExprParenthesized innerLength)) =
  arrayLengthErrors innerLength
arrayLengthErrors
    (MkAstNode lengthInfo _ (ExprLiteral (MkAstNode _ _ (LiteralIntegerRaw rawLiteralText)))) =
  case arrayLengthProblem rawLiteralText of
    Just (NonUsizeLengthSuffix suffixType) =>
      [NonUsizeArrayLength lengthInfo.span suffixType]
    Just (LengthExceedsSuffixType suffixType suffixMaximum) =>
      [ArrayLengthOutOfRange lengthInfo.span rawLiteralText suffixType suffixMaximum]
    Nothing => []
arrayLengthErrors _ = []

--------------------------------------------------------------------------------
-- The traversal
--------------------------------------------------------------------------------
-- Every function here destructures records with constructor patterns, per
-- the totality discipline in the header. Unused fields are wildcards; the
-- field ORDER in each pattern must track the record declarations in AST.idr.
--------------------------------------------------------------------------------

mutual

  -- Entry point: validate one parsed source file.
  public export
  validateSourceFile : SurfaceSourceFile -> List ValidationError
  validateSourceFile (MkAstNode _ _ (MkSourceFileNode _ sourceFileItems)) =
    validateItemList sourceFileItems

  ------------------------------------------------------------------
  -- Items and declarations
  ------------------------------------------------------------------

  validateItemList : List SurfaceItem -> List ValidationError
  validateItemList [] = []
  validateItemList (item :: remainingItems) = validateItem item ++ validateItemList remainingItems

  validateItem : SurfaceItem -> List ValidationError
  validateItem (MkAstNode _ _ itemNode) =
    case itemNode of
      ItemFunction functionDeclaration => validateFunctionDeclaration functionDeclaration
      ItemStruct structDeclaration     => validateStructDeclaration structDeclaration
      ItemEnum enumDeclaration         => validateEnumDeclaration enumDeclaration
      ItemQEnum qenumDeclaration       => validateQEnumDeclaration qenumDeclaration
      ItemImpl implDeclaration         => validateImplDeclaration implDeclaration
      ItemConst constDeclaration       => validateConstDeclaration constDeclaration
      -- `use` has no attributes, types, or expressions to walk.
      ItemUse _                        => []
      ItemModule moduleDeclaration     => validateModuleDeclaration moduleDeclaration

  -- Fields (in declaration order): docs, attributes, visibility, constness,
  -- effect, name, parameters, returnType, supports, contracts, body.
  -- `supports` and `contracts` are not walked here: the parser rejects
  -- `supports` and `requires`/`ensures` outright, so those fields are
  -- always empty by construction.
  validateFunctionDeclaration : FunctionDeclarationNode SurfaceAstPhase -> List ValidationError
  validateFunctionDeclaration
    (MkFunctionDeclarationNode _ functionAttributes _ _ _ _ functionParameters returnType _ _ functionBody) =
       validateAttributeList functionAttributes
    ++ validateParameterList functionParameters
    ++ validateOptionalType topLevelContext returnType
    ++ validateBlock functionBodyContext functionBody

  -- Parameter names require resolution, but every type still needs the
  -- syntactic and contextual checks performed by this pass.
  validateParameterList : List SurfaceFunctionParameter -> List ValidationError
  validateParameterList [] = []
  validateParameterList (MkAstNode _ _ parameterNode :: remainingParameters) =
    case parameterNode of
      NormalParameter _ _ _ parameterType =>
        validateType topLevelContext parameterType ++ validateParameterList remainingParameters
      ReceiverParameter _ _ =>
        validateParameterList remainingParameters

  validateStructDeclaration : StructDeclarationNode SurfaceAstPhase -> List ValidationError
  validateStructDeclaration (MkStructDeclarationNode _ structAttributes _ _ structFields) =
       validateAttributeList structAttributes
    ++ validateStructFieldList structFields

  validateStructFieldList :
       List (AstNode SurfaceAstPhase (StructFieldNode SurfaceAstPhase))
    -> List ValidationError
  validateStructFieldList [] = []
  validateStructFieldList
    (MkAstNode _ _ (MkStructFieldNode _ _ fieldType) :: remainingFields) =
    validateType topLevelContext fieldType ++ validateStructFieldList remainingFields

  validateEnumDeclaration : EnumDeclarationNode SurfaceAstPhase -> List ValidationError
  validateEnumDeclaration (MkEnumDeclarationNode _ enumAttributes _ _ enumVariants) =
       validateAttributeList enumAttributes
    ++ validateEnumVariantList enumVariants

  validateEnumVariantList :
       List (AstNode SurfaceAstPhase (EnumVariantNode SurfaceAstPhase))
    -> List ValidationError
  validateEnumVariantList [] = []
  validateEnumVariantList
    (MkAstNode _ _ (MkEnumVariantNode _ _ variantBody) :: remainingVariants) =
    (case variantBody of
       VariantUnit                => []
       VariantTuple payloadTypes  => validateTypeList1 topLevelContext payloadTypes
       VariantStruct payloadFields => validateStructFieldList payloadFields)
      ++ validateEnumVariantList remainingVariants

  validateQEnumDeclaration : QEnumDeclarationNode SurfaceAstPhase -> List ValidationError
  validateQEnumDeclaration (MkQEnumDeclarationNode _ qenumAttributes _ _ qenumVariants) =
       validateAttributeList qenumAttributes
    ++ validateQEnumVariantList qenumVariants

  validateQEnumVariantList :
       List (AstNode SurfaceAstPhase (QEnumVariantNode SurfaceAstPhase))
    -> List ValidationError
  validateQEnumVariantList [] = []
  validateQEnumVariantList
    (MkAstNode _ _ (MkQEnumVariantNode _ _ payloadTypes) :: remainingVariants) =
    validateTypeList1 topLevelContext payloadTypes
      ++ validateQEnumVariantList remainingVariants

  validateImplDeclaration : ImplDeclarationNode SurfaceAstPhase -> List ValidationError
  validateImplDeclaration (MkImplDeclarationNode _ _ implFunctions) =
    validateImplFunctionList implFunctions

  validateImplFunctionList :
       List SurfaceFunctionDeclaration
    -> List ValidationError
  validateImplFunctionList [] = []
  validateImplFunctionList (MkAstNode _ _ functionDeclaration :: remainingFunctions) =
    validateFunctionDeclaration functionDeclaration ++ validateImplFunctionList remainingFunctions

  -- Const initializers are NOT function bodies: `return` inside one is an
  -- error, which topLevelContext encodes.
  validateConstDeclaration : ConstDeclarationNode SurfaceAstPhase -> List ValidationError
  validateConstDeclaration (MkConstDeclarationNode _ _ _ constType constValue) =
       validateType topLevelContext constType
    ++ validateExpression topLevelContext constValue

  validateModuleDeclaration : ModuleDeclarationNode SurfaceAstPhase -> List ValidationError
  validateModuleDeclaration (MkModuleDeclarationNode _ _ _ moduleBody) =
    case moduleBody of
      ModuleInline _ moduleItems => validateItemList moduleItems
      ModuleExternal             => []

  ------------------------------------------------------------------
  -- Blocks and statements
  ------------------------------------------------------------------

  validateBlock : ValidationContext -> SurfaceBlock -> List ValidationError
  validateBlock context (MkAstNode _ _ (MkBlockNode _ blockStatements finalExpression)) =
       validateStatementList context blockStatements
    ++ validateOptionalExpression context finalExpression

  validateStatementList : ValidationContext -> List SurfaceStatement -> List ValidationError
  validateStatementList context [] = []
  validateStatementList context (statement :: remainingStatements) =
    validateStatement context statement ++ validateStatementList context remainingStatements

  validateStatement : ValidationContext -> SurfaceStatement -> List ValidationError
  validateStatement context (MkAstNode _ _ statementNode) =
    case statementNode of
      StatementLet (MkLetBindingNode letQualifiers _ typeAnnotation letInitializer) =>
           letQuantumUsageConflicts letQualifiers typeAnnotation
        ++ validateOptionalType context typeAnnotation
        ++ (case letInitializer of
              Nothing => []
              Just (MkLetInitializerNode _ initializerValue) =>
                validateExpression context initializerValue)
      StatementAssignment (MkAssignmentNode assignmentTarget _ assignmentValue) =>
           validateAssignmentTarget context assignmentTarget
        ++ validateExpression context assignmentValue
      StatementSemiExpression statementExpression => validateExpression context statementExpression
      StatementExpression statementExpression     => validateExpression context statementExpression

  validateAssignmentTarget : ValidationContext -> SurfaceAssignmentTarget -> List ValidationError
  validateAssignmentTarget context (MkAstNode _ _ targetNode) =
    case targetNode of
      AssignTargetName _                          => []
      AssignTargetIndex targetObject index        =>
        validateExpression context targetObject ++ validateExpression context index
      AssignTargetField targetObject _            => validateExpression context targetObject
      AssignTargetTupleIndex targetObject _       => validateExpression context targetObject

  ------------------------------------------------------------------
  -- Expressions
  ------------------------------------------------------------------

  validateExpressionList :
       ValidationContext -> List SurfaceExpr -> List ValidationError
  validateExpressionList context [] = []
  validateExpressionList context (expression :: remainingExpressions) =
    validateExpression context expression ++ validateExpressionList context remainingExpressions

  validateExpressionList1 :
       ValidationContext -> List1 SurfaceExpr -> List ValidationError
  validateExpressionList1 context (firstExpression ::: remainingExpressions) =
    validateExpression context firstExpression ++ validateExpressionList context remainingExpressions

  validateOptionalExpression :
       ValidationContext -> Maybe SurfaceExpr -> List ValidationError
  validateOptionalExpression context Nothing           = []
  validateOptionalExpression context (Just expression) = validateExpression context expression

  validateExpression : ValidationContext -> SurfaceExpr -> List ValidationError
  validateExpression context (MkAstNode expressionInfo _ expressionNode) =
    case expressionNode of
      ExprLiteral _  => []
      ExprName _     => []
      ExprBuiltin _  => []

      ExprParenthesized innerExpression => validateExpression context innerExpression
      ExprTuple elementExpressions      => validateExpressionList1 context elementExpressions
      ExprArray elementExpressions      => validateExpressionList context elementExpressions
      ExprRepeatedArray repeatedElement repeatCount =>
        validateExpression context repeatedElement ++ arrayLengthErrors repeatCount ++ validateExpression context repeatCount

      ExprCall callee arguments =>
        validateExpression context callee ++ validateExpressionList context arguments
      ExprMethodCall receiver _ arguments =>
        validateExpression context receiver ++ validateExpressionList context arguments
      ExprField accessedObject _          => validateExpression context accessedObject
      ExprTupleIndex indexedTuple _       => validateExpression context indexedTuple
      ExprIndex indexedObject index       => validateExpression context indexedObject ++ validateExpression context index

      ExprUnary _ operand                 => validateExpression context operand
      ExprBinary _ leftOperand rightOperand =>
        validateExpression context leftOperand ++ validateExpression context rightOperand
      ExprRange rangeStart _ rangeEnd     =>
        validateOptionalExpression context rangeStart ++ validateOptionalExpression context rangeEnd
      ExprCast castOperand castTargetType =>
        validateExpression context castOperand ++ validateType context castTargetType

      ExprBlock block                     => validateBlock context block

      ExprIf ifNode                       => validateClassicalIf context ifNode

      -- Loop bodies set insideLoop; while conditions and for iterator
      -- expressions do NOT count as inside the loop they head.
      ExprLoop loopBody =>
        validateBlock (MkValidationContext True context.insideFunctionBody) loopBody
      ExprWhile loopCondition loopBody =>
           validateExpression (MkValidationContext False context.insideFunctionBody) loopCondition
        ++ validateBlock (MkValidationContext True context.insideFunctionBody) loopBody
      ExprFor _ iterable loopBody =>
           validateExpression (MkValidationContext False context.insideFunctionBody) iterable
        ++ validateBlock (MkValidationContext True context.insideFunctionBody) loopBody

      ExprBreak breakValue =>
        (if context.insideLoop then [] else [BreakOutsideLoop expressionInfo.span])
          ++ validateOptionalExpression context breakValue
      ExprContinue =>
        if context.insideLoop then [] else [ContinueOutsideLoop expressionInfo.span]
      ExprReturn returnValue =>
        (if context.insideFunctionBody then [] else [ReturnOutsideFunction expressionInfo.span])
          ++ validateOptionalExpression context returnValue

      ExprCtrl controlExpression     => validateControlExpression context controlExpression
      ExprAdjoint adjointExpression  => validateAdjointExpression context adjointExpression

      ExprStructLiteral _ fieldInitializers => validateFieldInitializerList context fieldInitializers

      ExprQIf (MkQuantumIfNode qifCondition thenBranch elseBranch) =>
           validateExpression context qifCondition
        ++ validateQuantumBranch context thenBranch
        ++ (case elseBranch of
              Nothing => []
              Just quantumElseBranch => validateQuantumBranch context quantumElseBranch)
      ExprSIf (MkStateIfNode sifCondition thenExpression elseExpression) =>
           validateExpression context sifCondition
        ++ validateExpression context thenExpression
        ++ validateExpression context elseExpression

      ExprMatch (MkClassicalMatchNode scrutinee matchArms) =>
           validateExpression context scrutinee
        ++ validateClassicalArmList context matchArms
      ExprQMatch (MkQuantumMatchNode scrutinee matchArms) =>
           validateExpression context scrutinee
        ++ validateQuantumArmBodies context matchArms
      ExprSMatch (MkStateMatchNode scrutinee matchArms) =>
           validateExpression context scrutinee
        ++ validateQuantumArmBodies context matchArms

      -- ExprPath/ExprSelf carry no sub-expressions to walk. All eight forms
      -- above are also rejected as unsupported by the current parser, so a
      -- parsed source file cannot contain them yet -- but walking them now
      -- costs nothing and means nothing needs revisiting once the parser
      -- catches up. Their own semantic checks (qmatch/smatch pattern
      -- homogeneity, contract ordering, duplicate supports) stay out until
      -- that syntax exists to check.
      ExprPath _ => []
      ExprSelf _ => []

  validateFieldInitializerList :
       ValidationContext
    -> List (AstNode SurfaceAstPhase (FieldInitializerNode SurfaceAstPhase))
    -> List ValidationError
  validateFieldInitializerList context [] = []
  validateFieldInitializerList context (MkAstNode _ _ fieldInitializer :: remainingInitializers) =
    (case fieldInitializer of
       FieldInitShorthand _            => []
       FieldInitExplicit _ fieldValue  => validateExpression context fieldValue)
      ++ validateFieldInitializerList context remainingInitializers

  validateClassicalIf :
       ValidationContext -> ClassicalIfNode SurfaceAstPhase -> List ValidationError
  validateClassicalIf context (MkClassicalIfNode ifCondition thenBlock elseBranch) =
       validateExpression context ifCondition
    ++ validateBlock context thenBlock
    ++ (case elseBranch of
          Nothing                     => []
          Just (ElseBlock elseBlock)  => validateBlock context elseBlock
          Just (ElseChainedIf (MkAstNode _ _ chainedIfNode)) =>
            validateClassicalIf context chainedIfNode)

  validateQuantumBranch :
       ValidationContext -> QuantumBranchNode SurfaceAstPhase -> List ValidationError
  validateQuantumBranch context quantumBranch =
    case quantumBranch of
      QuantumBranchBlock branchBlock           => validateBlock context branchBlock
      QuantumBranchExpression branchExpression => validateExpression context branchExpression

  validateClassicalArmList :
       ValidationContext
    -> List SurfaceClassicalMatchArm
    -> List ValidationError
  validateClassicalArmList context [] = []
  validateClassicalArmList context
    (MkAstNode _ _ (MkClassicalMatchArmNode _ armGuard armBody) :: remainingArms) =
       validateOptionalExpression context armGuard
    ++ validateExpression context armBody
    ++ validateClassicalArmList context remainingArms

  validateQuantumArmBodies :
       ValidationContext
    -> List SurfaceQuantumMatchArm
    -> List ValidationError
  validateQuantumArmBodies context [] = []
  validateQuantumArmBodies context
    (MkAstNode _ _ (MkQuantumMatchArmNode _ armBody) :: remainingArms) =
    validateExpression context armBody ++ validateQuantumArmBodies context remainingArms

  -- `rawBasis` is the selector as written, `bs"…"`: four characters are the
  -- `bs` prefix and the quotes, the rest are one state per control.
  validateControlBasis :
      List1 SurfaceExpr -> Maybe (SurfaceAstNode String) -> List ValidationError
  validateControlBasis _ Nothing = []
  validateControlBasis controlQbits
      (Just (MkAstNode basisInfo _ rawBasis)) =
    let controlCount = length controlQbits
        basisLength = length (unpack rawBasis) `minus` 4
    in if controlCount == basisLength
        then []
        else [ControlBasisLengthMismatch basisInfo.span controlCount basisLength]

  validateControlExpression :
       ValidationContext -> ControlExpressionNode SurfaceAstPhase -> List ValidationError
  validateControlExpression context controlExpression =
    case controlExpression of
      ControlledCallable controlQbits onBasisRaw controlledCallable =>
          validateControlBasis controlQbits onBasisRaw
        ++ validateExpressionList1 context controlQbits
        ++ validateExpression context controlledCallable

      ControlledBlock controlQbits onBasisRaw controlledBlock =>
          validateControlBasis controlQbits onBasisRaw
        ++ validateExpressionList1 context controlQbits
        ++ validateBlock context controlledBlock

  validateAdjointExpression :
       ValidationContext -> AdjointExpressionNode SurfaceAstPhase -> List ValidationError
  validateAdjointExpression context adjointExpression =
    case adjointExpression of
      AdjointOfCallable adjointedCallable => validateExpression context adjointedCallable
      AdjointBlock adjointedBlock         => validateBlock context adjointedBlock

  ------------------------------------------------------------------
  -- Types: the &mut-qbit check, the qualifier-behind-reference check, the
  -- array-length literal check, and recursion into array-size expressions
  -- (which are full surface expressions).
  ------------------------------------------------------------------

  validateTypeList :
       ValidationContext -> List SurfaceTy -> List ValidationError
  validateTypeList context [] = []
  validateTypeList context (writtenType :: remainingTypes) =
    validateType context writtenType ++ validateTypeList context remainingTypes

  validateTypeList1 :
       ValidationContext -> List1 SurfaceTy -> List ValidationError
  validateTypeList1 context (firstType ::: remainingTypes) =
    validateType context firstType ++ validateTypeList context remainingTypes

  validateOptionalType :
       ValidationContext -> Maybe SurfaceTy -> List ValidationError
  validateOptionalType context Nothing            = []
  validateOptionalType context (Just writtenType) = validateType context writtenType

  validateType : ValidationContext -> SurfaceTy -> List ValidationError
  validateType context (MkAstNode _ _ typeNode) =
    case typeNode of
      TyPrimitive _                    => []
      TyPath _                         => []
      TyUnit                           => []
      TyParenthesized innerType        => validateType context innerType
      TyTuple elementTypes             => validateTypeList1 context elementTypes
      TyArray elementType sizeExpression =>
        validateType context elementType ++ arrayLengthErrors sizeExpression ++ validateExpression context sizeExpression
      TySlice elementType              => validateType context elementType
      TyReference (MkAstNode borrowInfo _ borrowKind)
                  referencedType@(MkAstNode _ _ referencedTypeNode) =>
        (case borrowKind of
           MutableBorrow =>
             if isSyntacticallyQbitType referencedTypeNode
               then [MutableBorrowOfQbit borrowInfo.span]
               else []
           SharedBorrow  => [])
          ++ qualifiersBehindReference referencedType
          ++ validateType context referencedType
      TyQualified _ qualifiedType => validateType context qualifiedType
      TyFunction _ functionParameters returnType =>
        validateFunctionTypeParameterList context functionParameters
          ++ validateOptionalType context returnType

  validateFunctionTypeParameterList :
       ValidationContext
    -> List (AstNode SurfaceAstPhase (FunctionTypeParameterNode SurfaceAstPhase SurfaceExpr))
    -> List ValidationError
  validateFunctionTypeParameterList context [] = []
  validateFunctionTypeParameterList context
    (MkAstNode _ _ (MkFunctionTypeParameterNode _ parameterType) :: remainingParameters) =
    validateType context parameterType ++ validateFunctionTypeParameterList context remainingParameters
