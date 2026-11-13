# DSL export to Lean

This directory will contain the code that exports the DSL representation
to Lean for formal verification. The exporter consumes `DSL` definitions
and produces Lean definitions representing the program or circuit.

Keep `DSL` independent of the exporter. OpenQASM and other execution-target
output belong in `Compiler/Backend`.

The Lean exporter is planned and is not implemented yet.
