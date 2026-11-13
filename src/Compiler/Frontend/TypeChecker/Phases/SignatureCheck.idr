module Compiler.Frontend.TypeChecker.Phases.SignatureCheck

import Data.List1
import Data.SortedMap
import Data.SortedSet

import Control.Monad.State
import Compiler.Frontend.ScopeAndNameResolution.Data
import Compiler.Frontend.TypeChecker.Data
import Compiler.Frontend.TypeChecker.Helper
import Compiler.Frontend.TypeChecker.Phases.BodyCheck
import Compiler.Frontend.TypeChecker.State
import Compiler.Frontend.TypeChecker.Type
import Compiler.Frontend.ASTData
import Compiler.Frontend.ASTPhases
import Compiler.Frontend.QuantumAnnotations
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

%default total

checkedFunctionEffect  : Maybe (ResolvedAstNode FunctionConstness)
                      -> Maybe (ResolvedAstNode FunctionEffect)
                      -> StateT TypeCheckerState (Either CheckFailure) FunctionEffect
checkedFunctionEffect  _ Nothing = unreachable {function = "checkedFunctionEffect"} {reason = "desugaring did not supply a function effect"}
checkedFunctionEffect  Nothing (Just (MkAstNode _ _ writtenEffect)) = pure writtenEffect
checkedFunctionEffect  (Just _) (Just (MkAstNode _ _ EffectClassical)) = pure EffectClassical
checkedFunctionEffect  (Just _) (Just (MkAstNode info _ writtenEffect)) = typeError (EffectViolation EffectClassical writtenEffect info.span)

checkFunctionDeclaration : FunctionDeclarationNode ResolvedAstPhase -> StateT TypeCheckerState (Either CheckFailure) ()
checkFunctionDeclaration
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
    ) = do
      functionEffect <- checkedFunctionEffect functionConstness functionEffect
      -- First pass: syntactic errors in every written type.
      -- They must be reported before any array length is evaluated.
      traverse_
        (\parameter =>
          case parameter.nodeValue of
            NormalParameter _ _ _ parameterType => checkTypeIsSized parameterType
            ReceiverParameter _ _ => unreachable {function = "checkFunctionDeclaration"} {reason = "the parser does yet not produce receiver parameters"}
        ) functionParameters
      traverse_ checkTypeIsSized returnType
      -- Second pass: evaluate lengths and record the types.
      paramLeafTypes <- traverse
        (\parameter =>
          case parameter.nodeValue of
            NormalParameter _ _ (MkAstNode _ _ (MkResolvedNameNode nameNodeText nameNodeSymbolId)) parameterType => do
              paramLeafType <- writtenLeafTypeM evalConstExprNat parameterType
              typeCheckerState <- get
              case lookup nameNodeSymbolId typeCheckerState.tables.symbols of
                Nothing => unreachable {function = "checkFunctionDeclaration"} {reason = "parameter symbol cannot be found in checker state"}
                Just symbolInfo =>
                  case symbolInfo.symbolKind of
                    SymbolFunctionParameter => do
                      recordSymbolType nameNodeSymbolId paramLeafType
                      recordParameterStorage nameNodeSymbolId paramLeafType
                    _ => pure ()
              pure paramLeafType
            ReceiverParameter _ _ => unreachable {function = "checkFunctionDeclaration"} {reason = "the parser does not produce receiver parameters"}
        ) functionParameters
      returnLeafType <- case returnType of
        Just resolvedTy => writtenLeafTypeM evalConstExprNat resolvedTy
        Nothing => unreachable {function = "checkFunctionDeclaration"} {reason = "desugaring did not supply a return type"}
      let functionNameSymbolId = functionName.nodeValue.nameNodeSymbolId
      recordSymbolType functionNameSymbolId (LeafFunctionType functionEffect (map (.nodeValue) supportClause) paramLeafTypes returnLeafType)

checkConstDeclaration : ConstDeclarationNode ResolvedAstPhase ->  StateT TypeCheckerState (Either CheckFailure) ()
checkConstDeclaration (MkConstDeclarationNode constDocs constVisibility constName constType constValue) = do
      checkTypeIsSized constType
      let constSymbolId = constName.nodeValue.nameNodeSymbolId
      constLeafType <- writtenLeafTypeM evalConstExprNat constType
      recordSymbolType constSymbolId constLeafType

export
checkSignature : ResolvedItem -> StateT TypeCheckerState (Either CheckFailure) ()
checkSignature (MkAstNode itemInfo metadata item) = do
  case item of
      ItemModule declaration => notImplemented {function = "checkItem"} {feature = "ItemModule"}
      ItemUse declaration => notImplemented {function = "checkItem"} {feature = "ItemUse"}
      ItemConst declaration => checkConstDeclaration declaration
      ItemEnum declaration => notImplemented {function = "checkItem"} {feature = "ItemEnum"}
      ItemQEnum declaration => notImplemented {function = "checkItem"} {feature = "ItemQEnum"}
      ItemStruct declaration => notImplemented {function = "checkItem"} {feature = "ItemStruct"}
      ItemImpl declaration => notImplemented {function = "checkItem"} {feature = "ItemImpl"}
      ItemFunction declaration => checkFunctionDeclaration declaration

