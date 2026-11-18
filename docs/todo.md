
### Features Pending Implementation

This document compiles a list of features which are covered by the [language documentation](README.md) but not yet planned for the alpha release.

Higher priority:

- Lean 4 code generation.
- Modules and imports.
- Uncomputation support, enable: `:=`, `uncompute`, `scratch`.
- Add support for `affine` qubits.
- Add a classical expression language to Idris2 DSL.
- Handle supports adjoint/ctrl function clauses.
- Support for `adjoint` operation.
- Support for `ctrl` blocks: `ctrl(...) { ... }`. The callable form `ctrl(...).apply(f)` is supported.
- Quantum contracts.
- Quantum conditionals.
  - `qif`+`qelse` & `qmatch`.
  - `sif`+`selse` & `smatch`.

Other:

- Rust style generic types and generic const parameters.
- Rust style built-in methods.
- Quantum Boolean data and Boolean coherent operations.
- Signed/unsigned quantum integers and quantum arithmetic.
- Signed/unsigned quantum floats and quantum operations.
- Arrays, tuples formed from the 3 above must work.
- Sum & Product data types:
  - `enum`
  - `qenum`
  - `struct` + `impl` blocks.
- Recursion.
- Recursive data structures.
- Documentation comments.


