This project is the compiler for the Leaf quantum programming language.

Leaf is a strongly and statically typed quantum programming language with Rust-inspired syntax that will compile to OpenQASM 3. The compiler is implemented in Idris 2 and will support Lean-based formal verification of quantum algorithms.

Leaf follows Rust’s syntax and compiler conventions unless otherwise specified. Unlike Rust, Leaf compiles programs to OpenQASM 3 code for execution on a quantum computer rather than to machine code.

The specification for the Leaf programming language can be found in `specs/Language-Syntax-Specification.rs`. Leaf is deliberately designed to replicate Rust’s basic syntax, with conservative extensions for quantum programming that are meant to look and feel like Rust.

The Markdown documentation for the Leaf language can be found in `docs/README.md` and the Markdown documents linked from it. Not all features described in the documentation are currently supported. A tentative list of unsupported features planned for future work can be found in `docs/todo.md`.

The Leaf source code is organized as follows:

```text
src/
├── Core/                       # Quantum lambda calculus high-level IR
├── DSL/                        # Idris 2 DSL low-level IR
├── Compiler/
│   ├── Frontend/
│   │   ├── Lexer/
│   │   ├── Parser/
│   │   ├── Syntax/
│   │   ├── Validator/
│   │   ├── Desugarer/
│   │   ├── ScopeAndNameResolver/
│   │   ├── TypeChecker/
│   │   └── Utils/
│   ├── Lowering/               # Translation between program representations
│   │   ├── ToCore/             # Typed AST (surface syntax) to high-level IR
│   │   └── CoreToDSL/          # High-level IR to low-level IR
│   ├── Backend/                # Output code generation
│   │   └── OpenQASM3/          # Low-level IR to OpenQASM 3
│   └── Exporter/               # Low-level IR to Lean exporter
├── Leaf.idr                    # REPL entry point
└── Main.idr                    # Command-line entry point
```

Tests can be found in the `test` folder at the project root.

The compilation pipeline for Leaf code is as follows (the typechecker is currently a work in progress):

- Frontend: lexes and parses Leaf source code, validates and desugars its syntax, resolves names, and checks types, ownership, and effects to produce a checked AST.
- Lowering to Core: translates the checked AST into a small, typed IR based on quantum lambda calculus (TODO).
- Lowering to DSL: translates Core into the circuit-oriented IR implemented as an Idris 2 DSL (TODO).
- Exporter: generates an equivalent Lean representation from the Idris 2 DSL program representation (TODO).
- Backend: emits code in the target representation from the DSL. OpenQASM 3 is currently supported; QIR support will be added later.
