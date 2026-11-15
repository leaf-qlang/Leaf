
This project is the compiler for the Leaf quantum programming language.

Leaf is a strongly, statically typed, quantum programming language with a Rust inspired syntax that will compile to OpenQasm 3, implemented in Idris 2 and will supporting Lean-based formal verification of quantum algorithms.

Leaf follows the Rust language syntax and Rust compiler convention whenever not specified otherwise. Unlike Rust, a Leaf program is not compiled to machine code, it is compiled to OpenQASM 3 code that will be able to be executed on a quantum computer.

The specifications for the Leaf programming language can be found in: specs/Language-Syntax-Specification.rs. Leaf is deliberately designed to replicate Rust’s basic syntax, with conservative extensions for quantum programming which are meant to look and feel like Rust.

The MD documentation files for the Leaf language can be found in: docs/README.md and linked MD documents. Not all the features in the documentation are supported at this time. A tentative list with features not yet supported and planned for future work can be found in: docs/todo.md.

The organization of Leaf source code files is as follows:

src/
├── Core/                       # Quantum lambda-calculus high level IR
├── DSL/                        # Idris2 DSL low-level IR
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
│   ├── Lowering/               # Translating between program representations
│   │   ├── ToCore/             # - typed AST (surface syntax) to high-level IR
│   │   └── CoreToDSL/          # - high-level IR to low-level IR
│   ├── Backend/                # Output code generation
│   │   └── OpenQASM3/          #  - low level IR to OpenQasm 3  
│   └── Exporter/               # Low level IR to Lean exporter
├── Leaf.idr                    # REPL entry point
└── Main.idr                    # Command-line entry point

Tests can be found under folder named "test" in project root.

The compilation lifecycle of Leaf code is as follows (typechecker is work in progress at this moment):

- Frontend: lexes and parses Leaf source, validates and desugars its syntax, resolves names, and checks types, ownership, and effects to produce a checked AST.
- Lowering to Core: translates the checked AST to a small, typed IR based on quantum lambda calculus.
- Lowering to DSL: translates Core to the circuit-oriented IR implemented as an Idris2 DSL.
- Exporter: generates from an Idris2 DSL program representation an equivalent Lean representation.
- Backend: emits the backend target representation from the DSL:
-- OpenQASM3 for now.
-- QIR to be added later.
