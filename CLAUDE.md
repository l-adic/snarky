# Snarky - Zero-Knowledge Circuit DSL

A PureScript DSL for constructing zero-knowledge proof circuits, with Rust cryptographic backends.

## Build Commands

### Prerequisites
This project requires building Rust native modules before PureScript compilation. The build process is managed through Makefiles.

### Top-level Commands
```bash
# Build everything (Rust + PureScript)
make all

# Build individual packages
make build-curves    # Build native Rust curves + PureScript FFI
make build-snarky    # Build circuit DSL (requires curves)

# Clean everything
make clean

# Run main executable
make run-snarky

# Get help
make help
```

### Package-level Commands

**For curves package** (handles Rust N-API compilation):
```bash
cd packages/curves

# Full build (installs deps, builds native module, builds PureScript)
make all

# Individual steps
make install-deps    # Install npm dependencies
make build-napi      # Build Rust curves-napi module
make build           # Build PureScript (after native module)

# Clean
make clean
```

**For snarky package** (pure PureScript):
```bash
cd packages/snarky

# Standard spago commands work after curves is built
spago build
spago test
spago run
```

### Build Dependencies
1. **curves-napi**: Rust crate compiled to Node.js native module via N-API
2. **curves**: PureScript FFI bindings to the native module  
3. **snarky**: Circuit DSL depending on curves package

**Important**: Always build `curves` before `snarky`. The top-level `make all` handles this dependency order.

## Testing

### Running Tests

**Full package test suites:**
```bash
# Test curves package (cryptographic primitives)
spago test -p curves

# Test snarky package (circuit DSL) 
spago test -p snarky

# Test everything
make test
```

**Test filtering and options:**
```bash
# See all test runner options
spago test -p <package> -- --help

# Filter tests by name (case-sensitive text matching)
spago test -p snarky -- -e "Field Circuit"
spago test -p curves -- -e "BaseField"

# Filter tests by regex (case-insensitive)
spago test -p snarky -- -E "bool.*circuit"

# Fail fast on first failure
spago test -p snarky -- --fail-fast

# Run only previously failed tests
spago test -p snarky -- --only-failures
```

### Test Structure

- **curves**: Tests elliptic curve operations (BN254, Pallas, Vesta)
- **snarky**: Tests circuit DSL with property-based testing via QuickCheck
  - Field operations (mul, square, inv, div, eq)
  - Boolean operations (and, or, xor, not, ifThenElse) 
  - Assertion circuits (assertEqual, assertNonZero)
  - Bit operations (pack, unpack)
  - Circuit constraint satisfaction and correctness verification

Tests use `mkCircuitSpec` pattern for property-based verification of both constraint satisfaction and semantic correctness.

## PureScript Dependencies & Code Understanding

### Leveraging .spago Directory
Since PureScript is a niche language, the `.spago/p/` directory contains **full source code** for all dependencies - invaluable for understanding PureScript patterns and idioms:

- **Library Usage Patterns**: How to properly use PureScript libraries
- **Type-level Programming**: Row types, type-level strings, and constraints  
- **Functional Patterns**: Monad transformers and functional abstractions
- **FFI Patterns**: JavaScript interop

### Using Repomix for Dependency Analysis
```bash
# Pack dependencies for AI analysis
npx repomix pack .spago/p/ --style xml --output deps-analysis.xml

# Focus on specific libraries
npx repomix pack .spago/p/ --include "**/effect/**,**/transformers/**" --output monads-analysis.xml

# Analyze testing libraries  
npx repomix pack .spago/p/ --include "**/spec/**,**/quickcheck/**" --output testing-analysis.xml
```

### Key Dependencies to Study

**Core Libraries:**
- `prelude/` - Core language constructs
- `effect/` - Effect monad for side effects
- `transformers/` - Monad transformers

**Data Structures:**
- `arrays/`, `ordered-collections/` - Collections
- `maybe/`, `either/` - Option and Either types

**Testing:**
- `spec/` - Test framework  
- `quickcheck/` - Property-based testing

**Type-level Programming:**
- `typelevel-prelude/` - Type-level utilities
- `record/` - Row type manipulation (unique to PureScript)

### Key PureScript vs Haskell Differences

1. **Row Types**: Extensible record types not found in Haskell
2. **Effect Monad**: Uses `Effect` for side effects (simpler than Haskell's IO)
3. **FFI**: Direct JavaScript interop instead of C FFI
4. **Type Classes**: Instance chains instead of overlapping instances; functional dependencies and multi-param type classes but no associated types
5. **Syntax**: Similar but with important differences

Consult `.spago/p/` sources for proper PureScript idioms and avoid Haskell assumptions.

## Repomix for Code Analysis

### Repomix as MCP Tool
This project is configured with Repomix as an MCP (Model Context Protocol) tool. This is **critical** for effective development because:

1. **Context-aware Analysis**: Repomix can pack entire codebases or specific sections for AI analysis
2. **Dependency Understanding**: Essential for analyzing `.spago/p/` dependencies 
3. **Cross-package Analysis**: Helps understand relationships between `curves` and `snarky` packages
4. **Pattern Discovery**: Identifies coding patterns and conventions across the codebase

### When to Use Repomix

**Always use Repomix when:**
- Adding new DSL operations (analyze existing patterns first)
- Debugging complex circuit constraints (understand constraint flow)
- Working with FFI (study existing Rust-PureScript bindings)
- Understanding library usage (pack relevant `.spago/p/` sections)
- Refactoring across packages (analyze cross-dependencies)

### Repomix Usage Patterns

```bash
# Pack full codebase for architectural understanding
npx repomix pack . --output full-analysis.xml

# Focus on circuit DSL patterns
npx repomix pack packages/snarky/src --include "**/DSL/**" --output dsl-patterns.xml

# Study FFI patterns
npx repomix pack packages/curves --include "**/*.purs,**/*.rs" --output ffi-analysis.xml

# Analyze specific dependency usage
npx repomix pack .spago/p/ --include "**/transformers/**,**/effect/**" --output monad-patterns.xml

# Study test patterns for new test creation
npx repomix pack . --include "**/test/**,**/Test/**" --output test-patterns.xml
```

### MCP Integration Benefits
With Repomix as an MCP tool, you can:
- **Automatically pack relevant code sections** for context-aware assistance
- **Analyze patterns before implementing** new features
- **Understand complex type-level programming** by studying existing code
- **Debug by understanding full constraint chains** across modules
- **Learn PureScript idioms** from dependency source code

This makes development significantly more efficient, especially in a niche language like PureScript with complex cryptographic concepts.

## OCaml Snarky Reference (Rosetta Stone)

### Core Translation Source
This project is a **direct port** of the OCaml Snarky library, which is included as a Git submodule in the `snarky/` directory. This serves as our **Rosetta Stone** for translating additional OCaml modules to PureScript.

### Key OCaml Source Directories

**Primary Translation Target:**
- `snarky/src/base/` - Core Snarky functionality (maps to our `packages/snarky/` package)

**Important OCaml Modules for Reference:**
- `as_prover.ml` → Circuit prover computations
- `boolean.ml` → Boolean circuit operations  
- `checked.ml` → Checked computation monad
- `constraint_system.ml` → R1CS constraint system
- `cvar.ml` → Circuit variables
- `number.ml` → Field arithmetic
- `typ.ml` → Type-safe circuit types
- `snark.ml` → Main SNARK interface

### Translation Workflow with Repomix

**When translating new OCaml modules:**

```bash
# Pack OCaml source for translation reference
npx repomix pack snarky/src/base --include "**/*.ml,**/*.mli" --output ocaml-reference.xml

# Pack our current PureScript implementation for pattern comparison
npx repomix pack packages/snarky/src --output purescript-current.xml

# Pack both for side-by-side analysis
npx repomix pack . --include "**/snarky/src/base/**/*.ml,**/packages/snarky/src/**/*.purs" --output translation-analysis.xml
```

### Translation Patterns to Study

1. **OCaml functors** → PureScript type classes and module patterns
2. **OCaml modules** → PureScript modules and namespaces  
3. **OCaml GADTs** → PureScript phantom types and type-level programming
4. **OCaml effects/handlers** → PureScript Effect monad and monad transformers
5. **OCaml polymorphic variants** → PureScript sum types and row types

### Using Repomix for Translation

**Essential for OCaml→PureScript translation:**
- Compare existing successful translations as templates
- Understand OCaml→PureScript mapping patterns
- Study how complex OCaml type system features were adapted
- Analyze FFI boundaries between OCaml native code and our Rust implementations
- Identify which OCaml modules remain to be translated

The `snarky/` submodule is the authoritative reference for implementing new circuit DSL features and understanding the intended semantics of the zero-knowledge proof system.

## Spago Build Tool Documentation

### Dynamic Documentation Access
Spago is the primary PureScript build tool. For any complex Spago operations, **always pull in the documentation dynamically**:

```bash
# Get help for any command
spago --help
spago build --help
spago test --help

# Access the complete local documentation
cat node_modules/spago/README.md

# For complex operations, pack the docs with repomix
npx repomix pack node_modules/spago --include "**/README.md" --output spago-docs.xml
```

### When to Pull Documentation
- Setting up new packages or workspaces
- Advanced dependency management
- Configuration file modifications
- Troubleshooting build issues
- Understanding CLI options

**Don't memorize Spago commands** - use `spago --help` and the local README to understand the current version's capabilities and syntax.