# Pickles Development Guide

This document outlines the engineering principles, testing strategies, and implementation status for the Pickles project.

## 1. The Golden Rule: Rust FFI as Ground Truth

All cryptographic computation and proof generation logic is governed by the `proof-systems` Rust library. We treat the Rust implementation as the definitive source of truth.

### The Constraint
We **NEVER** re-implement cryptographic primitives from scratch in PureScript if they exist in Rust. Our goal is to match the Rust behavior exactly.

### Modifying proof-systems Code
The `proof-systems` Rust library lives at `mina/src/lib/crypto/proof-systems/` (a git submodule of the mina repo). All Cargo workspace dependencies point there. We **can and should** modify it to expose internals for testing.
- ✅ **DO**: Make private fields or methods `pub`.
- ✅ **DO**: Add "checkpoint" methods to return internal state (e.g., sponge state).
- ❌ **DON'T**: Re-implement Rust logic in the FFI layer (`crypto-provider/`). This creates a risk of testing PureScript against a flawed re-implementation rather than the actual audited code.

---

## 2. Testing Strategy

We follow a strict hierarchy of verification:
1. **FFI Ground Truth**: Extract oracles, evaluations, and challenges from a real Rust-generated proof.
2. **Pure Reference**: Implement a PureScript `pure` version of the logic and verify it matches the FFI values.
3. **Circuit Verification**: Implement the Snarky circuit and verify it accepts the same values and produces the same constraints.

### Test Context Infrastructure
The `Test.Pickles.TestContext` module provides the engine for these tests:
- `createStepProofContext`: Generates a real Schnorr Step proof (domain $2^{16}$).
- `createWrapProofContext`: Generates a real Wrap proof by wrapping a Step proof (domain $2^{15}$).

---

## 3. Implementation Status & Roadmap

### Completed Foundations
- [x] **Field Shifting**: Type1 and Type2 `Shifted` instances with roundtrip tests.
- [x] **IPA Verification**: `ipaFinalCheckCircuit` implementing the core IPA equation.
- [x] **Challenge Extraction**: In-circuit extraction from L/R pairs matching Rust's sponge state.
- [x] **Plonk Components**: `ftEval0` composition and `combinedInnerProduct` batching.
- [x] **Sponge Transcripts**: `xi_correct` and `r_correct` checks via Fiat-Shamir replay.

---

## 4. OCaml Source Mapping

When implementing a feature, reference these core Mina modules:

| Feature | OCaml Module |
|---------|--------------|
| Step Verifier Logic | `mina/src/lib/pickles/step_verifier.ml` |
| Wrap Verifier Logic | `mina/src/lib/pickles/wrap_verifier.ml` |
| Deferred Values | `mina/src/lib/pickles/composition_types.ml` |
| Shifting Logic | `mina/src/lib/crypto/plonkish_prelude/shifted_value.ml` |
| Dummies/Base Case | `mina/src/lib/pickles/unfinalized.ml` |
