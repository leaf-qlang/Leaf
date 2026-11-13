module Compiler.Frontend.TypeChecker.Phases.EffectsCheck

import Compiler.Frontend.TypeChecker.Data
import Compiler.Frontend.Syntax.AST

%default total

export
checkEffects : TypeTables -> TypedSourceFile -> Either TypeError ()


