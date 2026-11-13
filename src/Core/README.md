# Core IR

This directory is reserved for Leaf's typed quantum lambda-calculus IR and
operations defined on that representation. `Core.Data` is currently a
placeholder; the IR is not implemented yet.

Keep Core independent of `Compiler` and `DSL`. Translation from the checked
Leaf AST belongs in `Compiler/Lowering/ToCore`; translation from Core to the
circuit DSL belongs in `Compiler/Lowering/CoreToDSL`.

`DSL.Core` is a separate module containing basic DSL definitions.
