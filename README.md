# Snarky

Embedded DSL for constructing recursive zero-knowledge circuits in PureScript. Faithfully implements the pickles recursive snark protocol backed by o1-labs [proof-systmes](https://github.com/o1-labs/proof-systems)


## Summary
A port of the [ocaml snarky DSL](https://github.com/o1-labs/snarky) to PureScript,
backed by [arkworks](https://github.com/arkworks-rs/algebra) for the finite field
arithmetic and cryptography (using [napi-rs](https://napi.rs/)).

## Example
For a practical demonstration, refer to `packages/example`. This implements a simple Merkle tree-based cryptocurrency ledger with `createAccount`, `getAccount`, and `transfer` circuits. It showcases foundational ZK application development.

## Prerequisites

- Node.js 23 and a stable Rust toolchain
- `npm install` — install dependencies and build the `kimchi-napi` native binding
- `make fetch-srs` — download SRS files (required for the kimchi/pickles tests)
- `make gen-linearization` — generate Kimchi linearization code (required to build pickles)

## Build

```bash
make all
```

## Test

```bash
make test
```

## Structure

### Core Libraries
- `packages/kimchi-napi/` - Rust ([napi-rs](https://napi.rs/)) crate exposing o1Labs [proof-systems](https://github.com/o1-labs/proof-systems) (Kimchi/arkworks) as the `kimchi-napi` Node module — the crypto backend
- `packages/curves/` - Prime field and elliptic curve operations (Pallas, Vesta, BN254)
- `packages/snarky/` - Circuit DSL for building zero-knowledge circuits
- `packages/sized-vector/` - Type-level sized vectors

### Proof System Backends
- `packages/snarky-kimchi/` - o1Labs [Kimchi](https://github.com/o1-labs/proof-systems) plonk backend (Pasta curves)
- `packages/pickles/` - Pickles recursive proof system (2-cycle recursion over Pasta)

### Circuit Libraries
- `packages/snarky-curves/` - Elliptic curve arithmetic circuits using the DSL
- `packages/poseidon/` - Poseidon hash permutation
- `packages/random-oracle/` - Random-oracle / sponge construction and circuits
- `packages/schnorr/` - Schnorr signatures (in-circuit verifier + out-of-circuit signer/verifier)
- `packages/merkle-tree/` - Merkle trees and circuits (fixed-depth and unbounded)

### Utilities
- `packages/snarky-test-utils/` - Testing utilities for circuit development
- `packages/union-find/` - Union-find data structure
- `packages/pickles-codegen/` - Kimchi linearization PureScript codegen (`make gen-linearization`)

### Reference Implementation
- `mina/` - OCaml Snarky source (Git submodule) used as translation reference
