module Compiler.Frontend.Desugarer.Desugar

import Compiler.Helper
import Compiler.Frontend.Desugarer.Helper
import Data.List
import Data.List1
import Compiler.Frontend.ASTData
import Compiler.Frontend.ASTPhases
import Compiler.Frontend.Syntax.Attribute
import Compiler.Frontend.Syntax.AST
import Compiler.Frontend.Syntax.Contract
import Compiler.Frontend.Syntax.Common
import Compiler.Frontend.Syntax.Doc
import Compiler.Frontend.Syntax.Literal
import Compiler.Frontend.Syntax.Name
import Compiler.Frontend.Syntax.Operator
import Compiler.Frontend.Syntax.Pattern
import Compiler.Frontend.Syntax.Type

--- TODO deusgar bit conditions in typechecked one we know b is not a boolean
-- if b { fun(&q); } -> if b == 1 { fun(&q); }

%default total

desugarAstNode : {a : Type} -> AstNode SurfaceAstPhase a -> AstNode CanonicalAstPhase a
desugarAstNode (MkAstNode astInfo _ nodeValue) = canonicalAstNode astInfo WrittenCode nodeValue

||| If the attribute is missing argument(s), the name of the function is set as attrribute argument.
||| Unsupported attributes names are ignored, meaning no desugaring is performed for those.
desugarAttribute : String -> Nat -> SurfaceAttribute -> (CanonicalAttribute, Nat)
desugarAttribute functionNameText nextDesugarIdOffset (MkAstNode attributeInfo _ (MkAttributeNode attributeName attributeArguments)) =
  let (desugaredArguments, followingDesugarIdOffset) = desugarArguments attributeArguments
      desugaredAttribute = canonicalAstNode attributeInfo WrittenCode $
        MkAttributeNode
          (desugarAstNode attributeName)
          desugaredArguments
  in (desugaredAttribute, followingDesugarIdOffset)
  where
    defaultArgumentInfo : AstInfo
    defaultArgumentInfo = astInfoWithDesugarIdOffset attributeInfo nextDesugarIdOffset
    defaultArguments : Maybe (List (AttributeArgument CanonicalAstPhase))
    defaultArguments = Just [canonicalAstNode defaultArgumentInfo DesugaredDefaultAttributeArgument (AttributeArgumentStringLit ("\"" ++ functionNameText ++ "\""))]
    desugarArguments : Maybe (List(AttributeArgument SurfaceAstPhase)) -> (Maybe (List (AttributeArgument CanonicalAstPhase)), Nat)
    desugarArguments (Just writtenArguments) = (Just ((map desugarAstNode) writtenArguments), nextDesugarIdOffset)
    desugarArguments Nothing =
      case recognizeKnownAttribute attributeName.nodeValue.nameNodeText of
        Just KnownQasmGate => (defaultArguments, S nextDesugarIdOffset)
        Just KnownQasmDef  => (defaultArguments, S nextDesugarIdOffset)
        Nothing            => (Nothing, nextDesugarIdOffset)

desugarPath : SurfacePath -> CanonicalPath
desugarPath (MkAstNode pathAstInfo metadata (MkPathNode firstSegment remainingSegments)) =
  canonicalAstNode pathAstInfo WrittenCode $
    MkPathNode (desugarAstNode firstSegment) (map desugarAstNode remainingSegments)

-- Perenthesized patterns will be removed
desugarPattern : SurfacePattern -> CanonicalPattern
desugarPattern (MkAstNode patternInfo _ patternNode) =
  canonicalAstNode patternInfo WrittenCode $
    case patternNode of
      PatternWildcard =>
        PatternWildcard
      PatternName mutability binderName =>
        PatternName mutability (desugarAstNode binderName)
      PatternPath valuePath =>
        PatternPath (desugarPath valuePath)
      PatternLiteral literal =>
        PatternLiteral (desugarAstNode literal)
      PatternParenthesized innerPattern =>
        (recur innerPattern).nodeValue
      PatternTuple elementPatterns =>
        PatternTuple (map recur elementPatterns)
      PatternArray elementPatterns =>
        PatternArray (map recur elementPatterns)
      PatternStruct structPath fieldPatterns =>
        PatternStruct
          (desugarPath structPath)
          (map desugarStructPatternField fieldPatterns)
      PatternEnumTuple variantPath argumentPatterns =>
        PatternEnumTuple
          (desugarPath variantPath)
          (map recur argumentPatterns)
  where
    recur : SurfacePattern -> CanonicalPattern
    recur nestedPattern =
      desugarPattern (assert_smaller patternNode nestedPattern)

    desugarStructPatternField : SurfaceStructPatternField -> CanonicalStructPatternField
    desugarStructPatternField (MkAstNode fieldInfo _ fieldNode) =
      canonicalAstNode fieldInfo WrittenCode $
        case fieldNode of
          -- { x } becomes { x: x }, and { mut x } becomes { x: mut x }.
          -- The field refers to a member, while the pattern introduces a local
          -- binding: they must be separate name nodes before name resolution.
          -- TODO: add tests one parser supports structs
          StructPatternFieldShorthand mutability (MkAstNode nameInfo _ fieldNameNode) =>
            StructPatternFieldExplicit
              (canonicalAstNode nameInfo WrittenCode fieldNameNode)
              (canonicalAstNode
                (MkAstInfo (astInfoWithDesugarIdOffset nameInfo 2).nodeId fieldInfo.span)
                DesugaredFieldShorthand $
                PatternName mutability $
                  canonicalAstNode (astInfoWithDesugarIdOffset nameInfo 1) DesugaredFieldShorthand fieldNameNode)
          StructPatternFieldExplicit fieldName fieldPattern =>
            StructPatternFieldExplicit
              (desugarAstNode fieldName)
              (recur fieldPattern)

mutual
  -- Perenthesized expressions will be removed
  desugarExpressionNode : AstInfo -> ExpressionNode SurfaceAstPhase -> ExpressionNode CanonicalAstPhase
  desugarExpressionNode expressionInfo expressionNode =
    case expressionNode of
      ExprLiteral literal => ExprLiteral (desugarAstNode literal)
      ExprName valueName => ExprName (desugarAstNode valueName)
      ExprPath valuePath => ExprPath (desugarPath valuePath)
      ExprBuiltin builtin => ExprBuiltin builtin
      ExprSelf selfReceiver => ExprSelf selfReceiver
      ExprParenthesized innerExpression => (desugarNestedExpression innerExpression).nodeValue
      ExprTuple elementExpressions => ExprTuple (map desugarNestedExpression elementExpressions)
      ExprArray elementExpressions => ExprArray (map desugarNestedExpression elementExpressions)
      ExprRepeatedArray repeatedElement repeatCount => ExprRepeatedArray (desugarNestedExpression repeatedElement) (desugarNestedExpression repeatCount)
      ExprStructLiteral structPath fieldInitializers => ExprStructLiteral (desugarPath structPath) (map desugarFieldInitializer fieldInitializers)
      ExprCall callee arguments => ExprCall (desugarNestedExpression callee) (map desugarNestedExpression arguments)
      ExprMethodCall receiver methodName arguments => ExprMethodCall (desugarNestedExpression receiver) (desugarAstNode methodName) (map desugarNestedExpression arguments)
      ExprField accessedObject fieldName => ExprField (desugarNestedExpression accessedObject) (desugarAstNode fieldName)
      ExprTupleIndex indexedTuple indexText => ExprTupleIndex (desugarNestedExpression indexedTuple) indexText
      ExprIndex indexedObject index => ExprIndex (desugarNestedExpression indexedObject) (desugarNestedExpression index)
      ExprUnary unaryOperator operand => ExprUnary (desugarAstNode unaryOperator) (desugarNestedExpression operand)
      ExprBinary binaryOperator leftOperand rightOperand => ExprBinary (desugarAstNode binaryOperator) (desugarNestedExpression leftOperand) (desugarNestedExpression rightOperand)
      ExprRange rangeStart rangeOperator rangeEnd => ExprRange (map desugarNestedExpression rangeStart) (desugarAstNode rangeOperator) (map desugarNestedExpression rangeEnd)
      ExprCast castOperand castTargetType => ExprCast (desugarNestedExpression castOperand) (desugarType castTargetType)
      ExprBlock block => ExprBlock (desugarBlockExpression block)
      ExprIf ifNode => ExprIf (desugarIfNode expressionInfo ifNode)
      ExprQIf ifNode => notImplemented __FILE__ {function = "desugarExpressionNode"} {feature = "ExprQIf"}
      ExprSIf ifNode => notImplemented __FILE__ {function = "desugarExpressionNode"} {feature = "ExprSIf"}
      ExprMatch matchNode => notImplemented __FILE__ {function = "desugarExpressionNode"} {feature = "ExprMatch"}
      ExprQMatch matchNode => notImplemented __FILE__ {function = "desugarExpressionNode"} {feature = "ExprQMatch"}
      ExprSMatch matchNode => notImplemented __FILE__ {function = "desugarExpressionNode"} {feature = "ExprSMatch"}
      ExprLoop loopBody => ExprLoop (desugarBlockExpression loopBody)
      ExprWhile loopCondition loopBody => ExprWhile (desugarNestedExpression loopCondition) (desugarBlockExpression loopBody)
      ExprFor binderPattern iterable loopBody => ExprFor (desugarPattern binderPattern) (desugarNestedExpression iterable) (desugarBlockExpression loopBody)
      ExprBreak breakValue => ExprBreak (map desugarNestedExpression breakValue)
      ExprContinue => ExprContinue
      ExprReturn Nothing =>
        ExprReturn $ Just $
          canonicalAstNode
            (astInfoWithDesugarIdOffset expressionInfo 1)
            DesugaredExpression $
            ExprLiteral $
              canonicalAstNode
                (astInfoWithDesugarIdOffset expressionInfo 2)
                DesugaredUnitValue
                LiteralUnit
      ExprReturn (Just returnValue) => ExprReturn (Just (desugarNestedExpression returnValue))
      ExprCtrl control => ExprCtrl (desugarControlExpressionNode expressionInfo control)
      ExprAdjoint adjoint => ExprAdjoint (desugarAdjointExpressionNode adjoint)
    where
      desugarNestedExpression : SurfaceExpr -> CanonicalExpr
      desugarNestedExpression nestedExpression =
        desugarExpression (assert_smaller expressionNode nestedExpression)

      desugarFieldInitializer : AstNode SurfaceAstPhase (FieldInitializerNode SurfaceAstPhase) ->
        AstNode CanonicalAstPhase (FieldInitializerNode CanonicalAstPhase)
      desugarFieldInitializer (MkAstNode fieldInfo _ fieldNode) =
        canonicalAstNode fieldInfo WrittenCode $
          case fieldNode of
            -- TODO: add tests one parser supports structs
            -- Point { x } becomes Point { x: x }. Keep the original name for
            -- the field and create a separate name for the local value lookup.
            FieldInitShorthand (MkAstNode nameInfo _ fieldNameNode) =>
              FieldInitExplicit
                (canonicalAstNode nameInfo WrittenCode fieldNameNode)
                (canonicalAstNode (astInfoWithDesugarIdOffset nameInfo 2) DesugaredFieldShorthand $
                  ExprName $
                    canonicalAstNode (astInfoWithDesugarIdOffset nameInfo 1) DesugaredFieldShorthand fieldNameNode)
            FieldInitExplicit fieldName fieldValue =>
              FieldInitExplicit (desugarAstNode fieldName) (desugarNestedExpression fieldValue)

      desugarBlockExpression : SurfaceBlock -> CanonicalBlock
      desugarBlockExpression 
        (MkAstNode blockAstInfo _ (MkBlockNode blockInnerDocs blockStatements finalExpression)) =
        canonicalAstNode blockAstInfo WrittenCode $
          MkBlockNode 
            (map desugarAstNode blockInnerDocs) 
            (map (\statement => desugarStatement (assert_smaller expressionNode statement)) blockStatements) 
            (map desugarNestedExpression finalExpression)
      mutual
        -- in case the else statement branch is missing, desugaring adds a default "else { () }" block
        desugarIfNode : AstInfo -> ClassicalIfNode SurfaceAstPhase -> ClassicalIfNode CanonicalAstPhase
        desugarIfNode ifExpressionInfo ifNode@(MkClassicalIfNode ifCondition ifThenBlock Nothing) =
          MkClassicalIfNode
            (desugarNestedExpression ifCondition)
            (desugarBlockExpression ifThenBlock)
            (Just $ ElseBlock (canonicalAstNode desugaredElseBlockAstInfo DesugaredElseBlock unitBlockNode))
          where
            desugaredElseBlockAstInfo = astInfoWithDesugarIdOffset ifExpressionInfo 1
            desugaredUnitExpressionAstInfo = astInfoWithDesugarIdOffset ifExpressionInfo 2
            desugaredDefaultUnitValueAstInfo = astInfoWithDesugarIdOffset ifExpressionInfo 3
            unitBlockNode : BlockNode CanonicalAstPhase
            unitBlockNode =
              MkBlockNode [] [] $
                Just (canonicalAstNode 
                  desugaredUnitExpressionAstInfo
                  DesugaredExpression
                  (ExprLiteral $ canonicalAstNode desugaredDefaultUnitValueAstInfo DesugaredUnitValue LiteralUnit)
                )
        desugarIfNode _ ifNode@(MkClassicalIfNode ifCondition ifThenBlock ifElseBranch) =
          MkClassicalIfNode
            (desugarNestedExpression ifCondition)
            (desugarBlockExpression ifThenBlock)
            (map (desugarElseNode ifNode) ifElseBranch)
        desugarElseNode : ClassicalIfNode SurfaceAstPhase -> ClassicalElseNode SurfaceAstPhase -> ClassicalElseNode CanonicalAstPhase
        desugarElseNode _ (ElseBlock elseBlock) =
          ElseBlock (desugarBlockExpression elseBlock)
        desugarElseNode ifNode (ElseChainedIf (MkAstNode chainedIfInfo _ chainedIfNode)) =
          ElseChainedIf $
            canonicalAstNode chainedIfInfo WrittenCode $
              desugarIfNode chainedIfInfo (assert_smaller ifNode chainedIfNode)

      -- Desugar control invocation by adding on() invocation to ctrl() if missing,
      -- in order to obtain the default control syntax: ctrl(&q0, &q1).on(bs"11")
      desugarOnBasis : Nat -> AstInfo -> Maybe (AstNode SurfaceAstPhase String) -> Maybe (AstNode CanonicalAstPhase String)
      desugarOnBasis controlCount controlExpressionAstInfo Nothing =
        Just $ canonicalAstNode onBasisAstInfo DesugaredCtrlDefaultOnInvocation onBasisString
        where
          onBasisAstInfo = astInfoWithDesugarIdOffset controlExpressionAstInfo 1
          onBasisString = "bs\"" ++ pack (replicate controlCount '1') ++ "\""
      desugarOnBasis _ _ (Just writtenOnBasis) = Just $ desugarAstNode writtenOnBasis

      desugarControlExpressionNode : AstInfo -> ControlExpressionNode SurfaceAstPhase -> ControlExpressionNode CanonicalAstPhase
      desugarControlExpressionNode expressionAstInfo (ControlledCallable controlQbits onBasisRaw controlledCallable) =
        ControlledCallable
          (map desugarNestedExpression controlQbits)
          (desugarOnBasis (length controlQbits) expressionAstInfo onBasisRaw)
          (desugarNestedExpression controlledCallable)
      desugarControlExpressionNode expressionAstInfo (ControlledBlock controlQbits onBasisRaw controlledBlock) =
        ControlledBlock
          (map desugarNestedExpression controlQbits)
          (desugarOnBasis (length controlQbits) expressionAstInfo onBasisRaw)
          (desugarBlockExpression controlledBlock)

      desugarAdjointExpressionNode : AdjointExpressionNode SurfaceAstPhase -> AdjointExpressionNode CanonicalAstPhase
      desugarAdjointExpressionNode (AdjointOfCallable adjointedCallable) = AdjointOfCallable (desugarNestedExpression adjointedCallable)
      desugarAdjointExpressionNode (AdjointBlock adjointedBlock) = AdjointBlock (desugarBlockExpression adjointedBlock)

  desugarExpression : SurfaceExpr -> CanonicalExpr
  desugarExpression (MkAstNode expressionInfo metadata expressionNode) =
    canonicalAstNode expressionInfo WrittenCode (desugarExpressionNode expressionInfo expressionNode)

  desugarType : Ty SurfaceAstPhase (Expr SurfaceAstPhase) -> Ty CanonicalAstPhase (Expr CanonicalAstPhase)
  desugarType writtenType = addDefaultLinearToUnqualifiedQbits (desugarWrittenType writtenType)

  -- Perenthesized types will be removed. The parameters and result of a
  -- function type own their values, so they get the default `linear`; the
  -- rest of the type's owned positions are left to the caller.
  desugarWrittenType : Ty SurfaceAstPhase (Expr SurfaceAstPhase) -> Ty CanonicalAstPhase (Expr CanonicalAstPhase)
  desugarWrittenType (MkAstNode typeAstInfo _ typeNode) =
    canonicalAstNode typeAstInfo WrittenCode $
      case typeNode of
        TyPrimitive primitiveName =>
          TyPrimitive primitiveName
        TyPath typePath =>
          TyPath (desugarPath typePath)
        TyUnit =>
          TyUnit
        TyParenthesized innerType =>
          (desugarNestedType innerType).nodeValue
        TyTuple elementTypes =>
          TyTuple (map desugarNestedType elementTypes)
        TyArray elementType sizeExpression =>
          TyArray 
            (desugarNestedType elementType) 
            (desugarExpression sizeExpression)
        TySlice elementType =>
          TySlice (desugarNestedType elementType)
        TyReference borrowKind referencedType =>
          TyReference 
            (desugarAstNode borrowKind) 
            (desugarNestedType referencedType)
        TyQualified quantumUsageQualifier qualifiedType =>
          TyQualified (desugarAstNode quantumUsageQualifier) (desugarNestedType qualifiedType)
        TyFunction functionEffect functionParameters returnType =>
          TyFunction
            (map desugarAstNode functionEffect)
            (map desugarFunctionTypeParameter functionParameters)
            (map desugarTypeAddingDefaultLinear returnType)
      where
        desugarNestedType : SurfaceTy -> CanonicalTy
        desugarNestedType nestedType =
          desugarWrittenType (assert_smaller typeNode nestedType)
        desugarTypeAddingDefaultLinear : SurfaceTy -> CanonicalTy
        desugarTypeAddingDefaultLinear nestedType =
          desugarType (assert_smaller typeNode nestedType)
        desugarFunctionTypeParameter : SurfaceAstNode (FunctionTypeParameterNode SurfaceAstPhase (SurfaceAstNode (ExpressionNode SurfaceAstPhase))) ->
          CanonicalAstNode (FunctionTypeParameterNode CanonicalAstPhase (CanonicalAstNode (ExpressionNode CanonicalAstPhase)))
        desugarFunctionTypeParameter (MkAstNode parameterAstInfo _ (MkFunctionTypeParameterNode parameterName parameterType)) =
          canonicalAstNode parameterAstInfo WrittenCode $
            MkFunctionTypeParameterNode (desugarAstNode parameterName) (desugarTypeAddingDefaultLinear parameterType)

  desugarFunctionParameter: AstNode SurfaceAstPhase (FunctionParameterNode SurfaceAstPhase) -> AstNode CanonicalAstPhase (FunctionParameterNode CanonicalAstPhase)
  desugarFunctionParameter (MkAstNode parameterInfo metadata (NormalParameter parameterDocs parameterMutability parameterName parameterType)) =
    canonicalAstNode parameterInfo WrittenCode $
      NormalParameter
        (map desugarAstNode parameterDocs)
        (map desugarAstNode parameterMutability)
        (desugarAstNode parameterName)
        (desugarType parameterType)
  desugarFunctionParameter (MkAstNode parameterInfo metadata (ReceiverParameter receiverDocs receiverBorrow)) =
    canonicalAstNode parameterInfo WrittenCode $
      ReceiverParameter
        (map desugarAstNode receiverDocs)
        (map desugarAstNode receiverBorrow)

  desugarSignedPauliTerm : SurfaceSignedPauliTerm -> SignedPauliTerm CanonicalAstPhase
  desugarSignedPauliTerm (MkAstNode termInfo metadata (MkSignedPauliTermNode sign pauliString)) =
    canonicalAstNode termInfo WrittenCode $
      MkSignedPauliTermNode sign (desugarAstNode pauliString)

  desugarContractPredicate : SurfaceContractPredicate -> CanonicalContractPredicate
  desugarContractPredicate (MkAstNode predicateInfo metadata predicateNode) =
    canonicalAstNode predicateInfo WrittenCode $
      case predicateNode of
        ContractClean qbitArgument =>
          ContractClean (desugarExpression qbitArgument)
        ContractBasis qbitArgument pauliString =>
          ContractBasis
            (desugarExpression qbitArgument)
            (desugarAstNode pauliString)
        ContractSeparable qbitArgument =>
          ContractSeparable (desugarExpression qbitArgument)
        ContractIsolated qbitArgument =>
          ContractIsolated (desugarExpression qbitArgument)
        ContractProduct firstQbitSet otherQbitSets =>
          ContractProduct
            (desugarExpression firstQbitSet)
            (map desugarExpression otherQbitSets)
        ContractStabilized qbitArgument stabilizerTerms =>
          ContractStabilized
            (desugarExpression qbitArgument)
            (map desugarSignedPauliTerm stabilizerTerms)

  desugarContractClause : ContractClause SurfaceAstPhase (Expr SurfaceAstPhase) -> ContractClause CanonicalAstPhase (Expr CanonicalAstPhase) 
  desugarContractClause (MkAstNode contractAstInfo metadata contractClauseNode) =
    canonicalAstNode contractAstInfo WrittenCode $
      case contractClauseNode of
        RequiresClause predicate => RequiresClause (desugarContractPredicate predicate)
        EnsuresClause predicate => EnsuresClause (desugarContractPredicate predicate)

  desugarLetInitializer : LetInitializerNode SurfaceAstPhase -> LetInitializerNode CanonicalAstPhase
  desugarLetInitializer (MkLetInitializerNode initializerMarker initializerValue) =
    MkLetInitializerNode (desugarAstNode initializerMarker) (desugarExpression initializerValue)

  desugarAssignmentTarget : SurfaceAstNode (AssignmentTargetNode SurfaceAstPhase) -> CanonicalAstNode (AssignmentTargetNode CanonicalAstPhase)
  desugarAssignmentTarget (MkAstNode assignmentTargetAstInfo metadata assignmentTargetNode) =
    canonicalAstNode assignmentTargetAstInfo WrittenCode $
      case assignmentTargetNode of
        AssignTargetName targetName =>
          AssignTargetName (desugarAstNode targetName)
        AssignTargetIndex targetObject indexExpression =>
          AssignTargetIndex
            (desugarExpression targetObject)
            (desugarExpression indexExpression)
        AssignTargetField targetObject fieldName =>
          AssignTargetField
            (desugarExpression targetObject)
            (desugarAstNode fieldName)
        AssignTargetTupleIndex targetObject tupleIndexRawText =>
          AssignTargetTupleIndex
            (desugarExpression targetObject)
            tupleIndexRawText

  ||| A `let`'s `linear`/`affine` is moved into the owned positions of its
  ||| annotation, keeping the keyword's span, and the default `linear` is
  ||| added where none was written.
  ||| Desugar each assignment target and value once, preserving the operator.
  ||| Compound assignment lowering must wait until types and places are known:
  ||| copying a target into the RHS would duplicate evaluation and any scopes
  ||| introduced by its subexpressions, while reusing their node IDs.
  desugarStatement : Statement SurfaceAstPhase -> Statement CanonicalAstPhase
  desugarStatement (MkAstNode statementAstInfo metadata statementNode) =
    canonicalAstNode statementAstInfo WrittenCode $
      case statementNode of
        StatementLet (MkLetBindingNode writtenQualifiers letPattern writtenTypeAnnotation letInitializer) =>
          let (remainingLetQualifiers, qualifiedTypeAnnotation) =
                moveLetQuantumUsageIntoType
                  (map desugarAstNode writtenQualifiers)
                  (map (\annotationType => desugarWrittenType (assert_smaller statementNode annotationType)) writtenTypeAnnotation)
          in StatementLet $
               MkLetBindingNode
                 remainingLetQualifiers
                 (desugarPattern letPattern)
                 qualifiedTypeAnnotation
                 (map (\initializer => desugarLetInitializer (assert_smaller statementNode initializer)) letInitializer)
        StatementAssignment (MkAssignmentNode assignmentTarget assignmentOperator assignmentValue) =>
          StatementAssignment $
            MkAssignmentNode
              (desugarAssignmentTarget assignmentTarget)
              (desugarAstNode assignmentOperator)
              (desugarExpression assignmentValue)
        StatementSemiExpression statementExpression =>
          StatementSemiExpression (desugarExpression statementExpression)
        StatementExpression statementExpression =>
          StatementExpression (desugarExpression statementExpression)

||| A final expression is desugared to a return statement. If there is no
||| final expression, an explicit `return ();` statement is generated, unless
||| the body already ends in a `return` statement such as "return x;".
||| Also "return 2" is desugared to "return 2;"
||| Also "(return 2)" is desugared to "return 2;"
desugarFunctionBody : Block SurfaceAstPhase -> Block CanonicalAstPhase
desugarFunctionBody (MkAstNode functionBodyAstInfo metadata (MkBlockNode blockInnerDocs blockStatements finalExpression)) =
  canonicalAstNode functionBodyAstInfo WrittenCode $
    MkBlockNode
      (map desugarAstNode blockInnerDocs)
      (desugaredStatements ++ desugarFinalExpression finalExpression)
      Nothing
    where
      desugaredStatements : List (AstNode CanonicalAstPhase (StatementNode CanonicalAstPhase))
      desugaredStatements = map desugarStatement blockStatements

      -- Only a written `return` is recognized here; a statement that leaves the
      -- function on every path, like an if whose branches all return, needs
      -- typechecking to be recognized.
      endsInReturn : Bool
      endsInReturn =
        case last' desugaredStatements of
          Just (MkAstNode _ _ (StatementSemiExpression (MkAstNode _ _ (ExprReturn _)))) => True
          _ => False

      desugarFinalExpression : Maybe (AstNode SurfaceAstPhase (ExpressionNode SurfaceAstPhase)) -> List (AstNode CanonicalAstPhase (StatementNode CanonicalAstPhase))
      desugarFinalExpression Nothing =
        if endsInReturn
          then []
          else
            let statementSemiExpressionInfo = astInfoWithDesugarIdOffset functionBodyAstInfo 1
                expressionReturnInfo = astInfoWithDesugarIdOffset functionBodyAstInfo 2
                unitExpressionInfo = astInfoWithDesugarIdOffset functionBodyAstInfo 3
                unitValueInfo = astInfoWithDesugarIdOffset functionBodyAstInfo 4
            in
              [canonicalAstNode statementSemiExpressionInfo DesugaredReturnStatement
                (StatementSemiExpression $
                  canonicalAstNode expressionReturnInfo DesugaredReturnStatement $
                    ExprReturn $ Just $
                      canonicalAstNode unitExpressionInfo DesugaredExpression $
                        ExprLiteral $
                          canonicalAstNode unitValueInfo DesugaredUnitValue LiteralUnit)]
      desugarFinalExpression (Just finalExpression@(MkAstNode finalExpressionInfo _ _)) =
        let statementSemiExpressionInfo = { span := finalExpressionInfo.span } (astInfoWithDesugarIdOffset functionBodyAstInfo 1)
            desugaredFinalExpression = desugarExpression finalExpression
        in case desugaredFinalExpression.nodeValue of
          ExprReturn _ =>
            [canonicalAstNode statementSemiExpressionInfo DesugaredReturnStatement (StatementSemiExpression desugaredFinalExpression)]
          _ =>
            let expressionReturnInfo = { span := finalExpressionInfo.span } (astInfoWithDesugarIdOffset functionBodyAstInfo 2)
            in
              [canonicalAstNode statementSemiExpressionInfo DesugaredReturnStatement
                (StatementSemiExpression $ canonicalAstNode expressionReturnInfo DesugaredReturnStatement (ExprReturn (Just desugaredFinalExpression)))]

desugarItem : SurfaceItem -> CanonicalItem
desugarItem (MkAstNode itemInfo _ itemNode) =
  canonicalAstNode itemInfo WrittenCode $
    case itemNode of
      ItemModule declaration => notImplemented __FILE__ {function = "desugarItem"} {feature = "ItemModule"}
      ItemUse declaration => notImplemented __FILE__ {function = "desugarItem"} {feature = "ItemUse"}
      ItemConst constDeclaration => ItemConst $ desugarConstDeclaration constDeclaration
      ItemEnum declaration => notImplemented __FILE__ {function = "desugarItem"} {feature = "ItemEnum"}
      ItemQEnum declaration => notImplemented __FILE__ {function = "desugarItem"} {feature = "ItemQEnum"}
      ItemStruct declaration => notImplemented __FILE__ {function = "desugarItem"} {feature = "ItemStruct"}
      ItemImpl declaration => notImplemented __FILE__ {function = "desugarItem"} {feature = "ItemImpl"}
      ItemFunction functionDeclaration => ItemFunction $ desugarFunctionDeclaration functionDeclaration
    where
      desugarConstDeclaration : ConstDeclarationNode SurfaceAstPhase -> ConstDeclarationNode CanonicalAstPhase
      desugarConstDeclaration
          (MkConstDeclarationNode
            constDocs
            constVisibility
            constName
            constType
            constValue) =
              MkConstDeclarationNode
                (map desugarAstNode constDocs)
                (map desugarAstNode constVisibility)
                (desugarAstNode constName)
                (desugarType constType)
                (desugarExpression constValue)
      -- if function effect is missing, desugaring adds the default function effect:
      -- "classical" for a const function (const functions are classical), "general" otherwise
      -- if return type is missing, the default "unit" return type is added to function declaration
      -- if function does not return anything, desugaring chnages function body to return the "unit" data
      desugarFunctionDeclaration : FunctionDeclarationNode SurfaceAstPhase -> FunctionDeclarationNode CanonicalAstPhase
      desugarFunctionDeclaration
          (MkFunctionDeclarationNode
            functionDocs
            functionAttributes
            functionVisibility
            functionConstness
            functionEffect
            functionName
            functionParameters
            returnType
            supportClause
            contractClauses
            functionBody
          ) = let
                functionNameText = functionName.nodeValue.nameNodeText
                (desugaredAttributes, offsetAfterAttributes) = mapThreadingDesugarIdOffset (desugarAttribute functionNameText) 1 functionAttributes
                (desugaredFunctionEffect, offsetAfterEffect) = desugarFunctionEffect functionEffect offsetAfterAttributes
                desugaredReturnType = desugarReturnType returnType offsetAfterEffect
              in 
                MkFunctionDeclarationNode
                (map desugarAstNode functionDocs)
                desugaredAttributes
                (map desugarAstNode functionVisibility)
                (map desugarAstNode functionConstness)
                desugaredFunctionEffect
                (desugarAstNode functionName)
                (map desugarFunctionParameter functionParameters)
                desugaredReturnType
                (map desugarAstNode supportClause)
                (map desugarContractClause contractClauses)
                (desugarFunctionBody functionBody)
              where
                desugarFunctionEffect : Maybe (AstNode SurfaceAstPhase FunctionEffect) -> Nat -> (Maybe (AstNode CanonicalAstPhase FunctionEffect), Nat)
                desugarFunctionEffect Nothing desugarIdOffset =
                  let defaultFunctionEffect = maybe EffectGeneral (const EffectClassical) functionConstness
                  in (Just $ canonicalAstNode (astInfoWithDesugarIdOffset itemInfo desugarIdOffset) DesugaredDefaultFunctionEffect defaultFunctionEffect, desugarIdOffset + 1)
                desugarFunctionEffect (Just functionEffectNode) desugarIdOffset = (Just $ desugarAstNode functionEffectNode, desugarIdOffset)
                desugarReturnType : Maybe (Ty SurfaceAstPhase (Expr SurfaceAstPhase)) -> Nat -> Maybe (Ty CanonicalAstPhase (Expr CanonicalAstPhase))
                desugarReturnType Nothing desugarIdOffset = Just $ canonicalAstNode (astInfoWithDesugarIdOffset itemInfo desugarIdOffset) DesugaredDefaultFunctionReturnType TyUnit
                desugarReturnType (Just writtenReturnType) _ = Just $ desugarType writtenReturnType

export
desugarSurfaceSyntax : SurfaceSourceFile -> CanonicalSourceFile
desugarSurfaceSyntax
    (MkAstNode fileInfo _ (MkSourceFileNode fileDocs sourceFileItems)) =
  canonicalAstNode fileInfo WrittenCode $
    MkSourceFileNode
      (map desugarAstNode fileDocs)
      (map desugarItem sourceFileItems)
