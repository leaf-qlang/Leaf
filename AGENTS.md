This project is the compiler for the Leaf quantum programming language.

Leaf is a strongly and statically typed quantum programming language with Rust-inspired syntax that will compile to OpenQASM 3. The compiler is implemented in Idris 2 and will support Lean-based formal verification of quantum algorithms.

Leaf follows Rust’s syntax conventions unless otherwise specified (**for** example when dealing with quantum data, qubits are linear or affine variable). Unlike Rust, Leaf compiles programs to OpenQASM 3 code for execution on a quantum computer rather than to machine code.

The specification for the Leaf programming language can be found in `specs/Language-Syntax-Specification.rs`. Leaf is deliberately designed to replicate Rust’s basic syntax, with conservative extensions for quantum programming that are meant to look and feel like Rust.

The Markdown documentation for the Leaf language can be found in `docs/README.md` and the Markdown documents linked from it. Not all features described in the documentation are currently supported. A tentative list of unsupported features planned for future work can be found in `docs/todo.md`.

The Leaf source code is organized as follows:

```text
src/
├── Core/                       # Quantum lambda calculus high-level IR (PLANNED)
├── DSL/                        # Idris 2 DSL low-level IR (PROTOTYPE)
├── Compiler/
│   ├── Frontend/
│   │   ├── Lexer/
│   │   ├── Parser/
│   │   ├── Syntax/
│   │   ├── Validator/
│   │   ├── Desugarer/
│   │   ├── ScopeAndNameResolver/
│   │   ├── TypeChecker/        # WIP
│   │   └── Utils/              # AST printing utilities
│   ├── Lowering/               # Translation between program representations
│   │   ├── ToCore/             # Typed AST (surface syntax) to high-level IR  (PLANNED)
│   │   └── CoreToDSL/          # High-level IR to low-level IR (PLANNED)
│   ├── Backend/                # Output code generation
│   │   └── OpenQASM3/          # Low-level IR to OpenQASM 3    (PROTOTYPE)
│   └── Exporter/               # Low-level IR to Lean exporter (PLANNED)
├── Leaf.idr                    # REPL entry point
└── Main.idr                    # Command-line entry point
test/                           # Tests folder
```

The compilation pipeline for Leaf code is as follows ():

- Frontend: lexes and parses Leaf source code, validates and desugars its syntax, resolves names, and checks types, ownership, and effects to produce a checked AST.
- Lowering to Core: translates the checked AST into a small, typed IR based on quantum lambda calculus (TODO).
- Lowering to DSL: translates Core into the circuit-oriented IR implemented as an Idris 2 DSL (TODO).
- Exporter: generates an equivalent Lean representation from the Idris 2 DSL program representation (TODO).
- Backend: emits code in the target representation fromthe pipeline currently stops at resolver, the typechecker is currently a work in progress the DSL. OpenQASM 3 is currently supported; QIR support will be added later.

Note that the pipeline currently stops at resolver, the typechecker is currently a work in progress, other components beyond tyechecker are not yet implemented or at prototipe stage.

Useful commands:

- Build the compiler: `pack build leaf`

- Run the current command-line frontend: `pack run leaf examples/01_coin_flip.rs`

- Run tests using the command used by CI: `pack -v test leaf`

Keep the current the library dependencies, the code layout and the code conventions for both production and test code. Whenever in doubt ask.
