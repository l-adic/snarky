# Snarky

Embedded DSL for constructing zero-knowledge circuits in PureScript.


## Summary
A port of the [ocaml snarky DSL](https://github.com/o1-labs/snarky) to PureScript,
backed by [arkworks](https://github.com/arkworks-rs/algebra) for the finite field
arithmetic and cryptography (using [napi-rs](https://napi.rs/)).

## Example
For a practical demonstration, refer to `packages/example`. This implements a simple Merkle tree-based cryptocurrency ledger with `createAccount`, `getAccount`, and `transfer` circuits. It showcases foundational ZK application development.

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
- `packages/curves/` - Elliptic curve field operations (Pallas, Vesta, BN254) with Rust N-API backend
- `packages/snarky/` - Circuit DSL for building zero-knowledge circuits

### Proof System Backends
- `packages/snarky-kimchi/` - o1Labs [Kimchi](https://github.com/o1-labs/proof-systems) plonk backend
- `packages/snarky-bulletproofs/` - l-adic [bulletproof](https://github.com/l-adic/bulletproofs) R1CS backend
- `packages/groth16` - arkworks [Groth16](https://github.com/arkworks-rs/groth16) R1CS backend

### Circuit Libraries
- `packages/snarky-curves/` - Elliptic curve arithmetic circuits using the DSL

### Utilities
- `packages/snarky-test-utils/` - Testing utilities for circuit development
- `packages/union-find/` - Union-find data structure

### Reference Implementation
- `mina/` - OCaml Snarky source (Git submodule) used as translation reference
