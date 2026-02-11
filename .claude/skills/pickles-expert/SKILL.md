---
name: pickles-expert
description: Expert guidance on the Pickles recursive proof system (2-cycle recursion). Use when working with Step/Wrap verifiers, cross-field arithmetic (Type1/Type2 shifting), polynomial commitment batching (IPA), or translating Pickles logic from Mina's OCaml implementation.
---

# Pickles Expert

This skill provides specialized knowledge and workflows for implementing and maintaining the Pickles recursive proof system in PureScript. It focuses on the cryptographic bridge between the Pallas and Vesta curve cycles.

## Overview

Pickles enables recursive proofs by cycling between two curves. This skill captures the precise field-shifting protocols, Fiat-Shamir transcript replaying, and architectural duality (Step vs. Wrap) required for a sound implementation.

## Core Guidelines

### 1. The Duality Principle
Always identify which side of the recursion you are on:
- **Step (Tick/Fq)**: Verifies Wrap proofs and runs application logic. Operates natively on $F_p$. Uses **Type2** shifting for foreign $F_q$ scalars ($F_q > F_p$).
- **Wrap (Tock/Fp)**: Verifies Step proofs (accumulation). Operates natively on $F_q$. Uses **Type1** shifting for foreign $F_p$ scalars ($F_p < F_q$).

### 2. Protocol Fidelity
- **Rust as Ground Truth**: Never re-implement cryptographic primitives. Verify PureScript logic against Rust FFI outputs (via `Test.Pickles.TestContext`).
- **Shifted Values**: Strictly follow the $s - 2^n$ shift protocol for Type2 scalars to ensure roundtrip consistency.

### 3. Translation from OCaml
When translating from `mina/src/lib/pickles`, pay close attention to:
- **Sponge Transcripts**: The exact order of absorption in `fq_sponge` and `fr_sponge`.
- **Deferred Values**: Which values are computed in the current circuit vs. passed to the next (e.g., `combined_inner_product`, `b`).

## Workflow: Verifying a Sub-circuit

1.  **Extract Ground Truth**: Use `createStepProofContext` or `createWrapProofContext` in tests to get a real proof and its oracles.
2.  **Verify Pure Implementation**: Compare a `pure` PureScript implementation of the logic against the FFI oracles.
3.  **Validate Circuit**: Run the Snarky circuit with the same values and assert satisfiability.

## References

- **[Architecture Guide](references/architecture.md)**: Recursion cycle, deferred values, and OCaml source citations.
- **[Field Conventions](references/conventions.md)**: Master mapping table for Tick/Tock, Fp/Fq, and Type1/Type2 protocol.
- **[Development Standards](references/development.md)**: The "Ground Truth" philosophy and testing strategy.

## Specific Task Guidance

- **IPA/Bulletproofs**: Reference `Pickles.IPA` for the final verification equation and challenge extraction.
- **Plonk Checks**: Reference `Pickles.PlonkChecks.FtEval` for the composition of gate and permutation constraints.
- **Dummies/Base Case**: Reference `Pickles.Step.Dummy` for the `shouldFinalize = false` bootstrapping protocol.
