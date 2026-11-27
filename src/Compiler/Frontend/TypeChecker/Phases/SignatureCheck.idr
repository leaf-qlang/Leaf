module Compiler.Frontend.TypeChecker.Phases.SignatureCheck

import Compiler.Helper
import Data.List1
import Data.SortedMap
import Data.SortedSet

import Control.Monad.State
import Compiler.Frontend.ScopeAndNameResolver.Data
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
checkedFunctionEffect  _ Nothing = unreachable __FILE__ {function = "checkedFunctionEffect"} {reason = "desugaring did not supply a function effect"}
checkedFunctionEffect  Nothing (Just (MkAstNode _ _ writtenEffect)) = pure writtenEffect
checkedFunctionEffect  (Just _) (Just (MkAstNode _ _ EffectClassical)) = pure EffectClassical
checkedFunctionEffect  (Just _) (Just (MkAstNode info _ writtenEffect)) = liftTypeError (EffectViolation EffectClassical writtenEffect info.span)

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
      -- First pass: written-type errors (unsized slices, `affine`) in every
      -- parameter and the result, before any of their types is recorded.
      -- Rendering an `UnsizedValue` evaluates array lengths and may block;
      -- retrying is sound because a blocked check leaves no state behind.
      traverse_
        (\parameter =>
          case parameter.nodeValue of
            NormalParameter _ _ _ parameterType => checkWrittenTypeIsSizedAndSupported parameterType
            ReceiverParameter _ _ => notImplemented __FILE__ {function = "checkFunctionDeclaration"} {feature = "receiver parameters"}
        ) functionParameters
      traverse_ checkWrittenTypeIsSizedAndSupported returnType
      -- Second pass: evaluate array lengths and record the types.
      paramLeafTypes <- traverse
        (\parameter =>
          case parameter.nodeValue of
            NormalParameter _ _ (MkAstNode _ _ (MkResolvedNameNode nameNodeText nameNodeSymbolId)) parameterType => do
              paramLeafType <- writtenLeafTypeM evalConstExprNat parameterType
              typeCheckerState <- get
              case lookup nameNodeSymbolId typeCheckerState.typeTables.symbols of
                Nothing => unreachable __FILE__ {function = "checkFunctionDeclaration"} {reason = "parameter symbol cannot be found in checker state"}
                Just symbolInfo =>
                  case symbolInfo.symbolKind of
                    SymbolFunctionParameter => do
                      recordSymbolType nameNodeSymbolId paramLeafType
                      recordLocalStorage nameNodeSymbolId paramLeafType
                    _ => pure ()
              pure paramLeafType
            ReceiverParameter _ _ => notImplemented __FILE__ {function = "checkFunctionDeclaration"} {feature = "receiver parameters"}
        ) functionParameters
      returnLeafType <- case returnType of
        Just resolvedTy => writtenLeafTypeM evalConstExprNat resolvedTy
        Nothing => unreachable __FILE__ {function = "checkFunctionDeclaration"} {reason = "desugaring did not supply a return type"}
      let functionNameSymbolId = functionName.nodeValue.nameNodeSymbolId
      recordSymbolType functionNameSymbolId (LeafFunctionType functionEffect (map (.nodeValue) supportClause) paramLeafTypes returnLeafType)

checkConstDeclaration : ConstDeclarationNode ResolvedAstPhase ->  StateT TypeCheckerState (Either CheckFailure) ()
checkConstDeclaration (MkConstDeclarationNode constDocs constVisibility constName constType constValue) = do
      checkWrittenTypeIsSizedAndSupported constType
      let constSymbolId = constName.nodeValue.nameNodeSymbolId
      constLeafType <- writtenLeafTypeM evalConstExprNat constType
      recordSymbolType constSymbolId constLeafType

export
checkSignature : ResolvedItem -> StateT TypeCheckerState (Either CheckFailure) ()
checkSignature (MkAstNode itemInfo metadata item) = do
  case item of
      ItemModule declaration => notImplemented __FILE__ {function = "checkSignature"} {feature = "ItemModule"}
      ItemUse declaration => notImplemented __FILE__ {function = "checkSignature"} {feature = "ItemUse"}
      ItemConst declaration => checkConstDeclaration declaration
      ItemEnum declaration => notImplemented __FILE__ {function = "checkSignature"} {feature = "ItemEnum"}
      ItemQEnum declaration => notImplemented __FILE__ {function = "checkSignature"} {feature = "ItemQEnum"}
      ItemStruct declaration => notImplemented __FILE__ {function = "checkSignature"} {feature = "ItemStruct"}
      ItemImpl declaration => notImplemented __FILE__ {function = "checkSignature"} {feature = "ItemImpl"}
      ItemFunction declaration => checkFunctionDeclaration declaration

