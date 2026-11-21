module Compiler.Frontend.TypeChecker.Phases.ConstEval

import Compiler.Helper
import Control.Monad.State

import Compiler.Frontend.TypeChecker.Data
import Compiler.Frontend.TypeChecker.Numeric
import Compiler.Frontend.TypeChecker.State
import Compiler.Frontend.TypeChecker.Type
import Compiler.Frontend.ASTData
import Compiler.Frontend.ASTPhases
import Compiler.Frontend.Syntax.AST
import Compiler.Frontend.Syntax.Literal
import Compiler.Frontend.Token

%default total
