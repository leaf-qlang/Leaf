# Lowering Core to DSL

Planned translation from the quantum lambda-calculus IR in `Core` to the
circuit representation in `DSL`. This pass may depend on both representations;
neither representation should depend on this pass or on the other one.

Execution-target emission belongs in `Compiler/Backend`; DSL export to
Lean belongs in `Compiler/Exporter`. This directory does not contain an
implemented lowering pass yet.
