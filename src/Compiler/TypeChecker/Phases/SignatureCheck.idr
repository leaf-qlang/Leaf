module Compiler.TypeChecker.Phases.SignatureCheck

import Data.List1
import Data.SortedMap
import Data.SortedSet

import Control.Monad.State
import Compiler.ScopeAndNameResolution.Data
import Compiler.TypeChecker.Data
import Compiler.TypeChecker.Helper
import Compiler.TypeChecker.Phases.BodyCheck
import Compiler.TypeChecker.State
import Compiler.TypeChecker.Type
import Frontend.ASTData
import Frontend.ASTPhases
import Frontend.Syntax.Attribute
import Frontend.Syntax.AST
import Frontend.Syntax.Contract
import Frontend.Syntax.Common
import Frontend.Syntax.Doc
import Frontend.Syntax.Literal
import Frontend.Syntax.Name
import Frontend.Syntax.Operator
import Frontend.Syntax.Pattern
import Frontend.Syntax.Type

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
      traverse_
        (\parameter =>
          case parameter.nodeValue of
            NormalParameter _ _ (MkAstNode _ _ (MkResolvedNameNode nameNodeText nameNodeSymbolId)) parameterType => do
              checkWrittenType parameterType
              leafType <- writtenLeafTypeM evalConstExprNat parameterType
              updateState nameNodeSymbolId (ResolvedType leafType)
            ReceiverParameter _ _ => notImplemented {function = "checkFunctionDeclaration"} {feature = "receiver parameters"})
        functionParameters
      case returnType of
           Just resolvedTy => do
             checkWrittenType resolvedTy
             ignore (writtenLeafTypeM evalConstExprNat resolvedTy)
           Nothing => pure ()
    where
      typedSymbolInfo : TypedSymbolInfo -> InferredType -> TypedSymbolInfo
      typedSymbolInfo symbolInfo inferredType =
        case symbolInfo.symbolKind of
          SymbolFunctionParameter => { symbolType := inferredType } symbolInfo
          _ => symbolInfo
      updateState : SymbolId -> InferredType -> StateT TypeCheckerState (Either CheckFailure) ()  
      updateState symbolId inferredType = do
        typeCheckerState <- get
        case lookup symbolId typeCheckerState.tables.symbols of
          Nothing => unreachable {function = "updateState"} {reason = "parameter symbol cannot be found in checker state"}
          Just symbolInfo =>
            modify $ \typeCheckerState =>
              {
                tables.symbols := insert symbolId (typedSymbolInfo symbolInfo inferredType) typeCheckerState.tables.symbols
              } typeCheckerState


checkConstDeclaration : ConstDeclarationNode ResolvedAstPhase ->  StateT TypeCheckerState (Either CheckFailure) ()
checkConstDeclaration (MkConstDeclarationNode constDocs constVisibility constName constType constValue) = ?checkConstDeclarationH

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

