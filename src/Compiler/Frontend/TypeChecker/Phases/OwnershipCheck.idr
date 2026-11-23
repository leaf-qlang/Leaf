module Compiler.Frontend.TypeChecker.Phases.OwnershipCheck

import Compiler.Helper
import Data.List1
import Data.SortedMap

import Control.Monad.State
import Compiler.Frontend.ScopeAndNameResolver.Data
import Compiler.Frontend.TypeChecker.Data
import Compiler.Frontend.TypeChecker.State
import Compiler.Frontend.TypeChecker.Type
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

%default total

export
checkOwnership : TypeTables -> TypedSourceFile -> Either TypeError OwnershipTables
checkOwnership typeTables typedAst = ?checkOwnershipHole
