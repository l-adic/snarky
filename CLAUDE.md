# Snarky

PureScript zero-knowledge circuit library with a Rust cryptography backend.

## Prerequisites

- Node.js 23
- Rust stable toolchain

## Project Initialization

```bash
# Install dependencies and build the kimchi-napi native binding
npm install

# Download SRS files (required for snarky-kimchi and pickles tests)
make fetch-srs

# Generate linearization code (required to build pickles)
make gen-linearization
```

## Build & Test

```bash
# Build everything
npx spago build

# Type-check only (no JS codegen) — fast compiler feedback
# Use this routinely after edits instead of full builds
npx purs compile -g corefn $(npx spago sources -p <package> 2>/dev/null) --json-errors

# Type-check a package including its tests (exclude other packages' test files)
npx purs compile -g corefn $(npx spago sources -p <package> 2>/dev/null | grep -v '/test/') packages/<package>/test/**/*.purs --json-errors

# Test a specific package
npx spago test -p snarky-kimchi

# Test with pattern matching (run only tests matching string)
npx spago test -p snarky-kimchi -- --example "VarBaseMul"

# Build with strict checking (warnings as errors, clean up spago.yaml)
npx spago build --pedantic-packages --strict
```

## Formatting & Linting

```bash
# Format and lint everything
make lint

# Or individually:
npx purs-tidy format-in-place 'packages/*/src/**/*.purs' 'packages/*/test/**/*.purs'
cargo fmt --all
cargo clippy --workspace --all-targets -- -D warnings
```

## Documentation is Local

**PureScript libraries** — All dependencies have full source in `.spago/p/`. When uncertain about a function, look it up:
```
.spago/p/prelude-7.0.0/src/...
.spago/p/transformers-6.1.0/src/...
```

**Spago documentation** — Spago is installed as an npm dev dependency. Its README has extensive documentation:
```
node_modules/spago/README.md
```

**Project conventions** — See `.claude/skills/project-developer-guide/` for testing patterns, FFI conventions, and other project-specific practices.

**Lean formalization (`formal/`)** — The `Kimchi` Lean 4 / Mathlib proofs of the EC gates have their own agent guide: `formal/CLAUDE.md` (auto-loaded when working under `formal/`). It is a constraint-predicate + Mathlib-`WeierstrassCurve` formalization — **not** a circuit-DSL embedding.

## Project Structure

### Crypto Backend
- **kimchi-napi** — Rust napi-rs crate exposing upstream proof-systems (kimchi/arkworks) as the `kimchi-napi` node module

### Core
- **snarky** — Circuit-building DSL
- **curves** — Prime field and elliptic curve types/classes
- **sized-vector** — Type-level sized vectors

### Backends
- **snarky-kimchi** — Kimchi proving system backend (Pasta curves)
- **snarky-bulletproofs** — Bulletproofs backend (Pasta curves)
- **snarky-groth16** — Groth16 backend (BN254)

### Crypto Primitives
- **poseidon** — Poseidon hash function
- **random-oracle** — Random oracle / sponge construction
- **schnorr** — Schnorr signatures

### Higher-Level
- **pickles** — Pickles recursive proof system
- **merkle-tree** — Merkle tree circuits

### Infrastructure
- **snarky-test-utils** — Testing utilities for circuits
- **pickles-codegen** — Code generation for pickles linearization

### Example
- **example** — Example circuits and usage patterns
