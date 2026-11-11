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
import Frontend.QuantumAnnotations
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
      -- First pass: syntactic errors in every written type.
      -- They must be reported before any array length is evaluated.
      traverse_
        (\parameter =>
          case parameter.nodeValue of
            NormalParameter _ _ _ parameterType => checkWrittenType parameterType
            ReceiverParameter _ _ => unreachable {function = "checkFunctionDeclaration"} {reason = "the parser does not produce receiver parameters"}
        ) functionParameters
      traverse_ checkWrittenType returnType
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

