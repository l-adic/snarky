---
name: pickles-architecture
description: Pickles recursive proof system architecture, diagrams, cross-field handling, and Step/Wrap verifier design. Use when implementing pickles circuits, IPA verification, deferred values, or cross-field computations.
---

# Pickles Architecture Guide

## Source Diagrams

**Official diagrams**: [o1-labs/proof-systems book](https://o1-labs.github.io/proof-systems/)
**Original drawio file**: `vendor/proof-systems/book/src/pickles/pickles_structure.drawio`
**Local copies**: `docs/pickles-diagrams/` (wrap.svg, step.svg, wrap-deferred-values.svg)

---

## Critical Architecture Constraint: Rust FFI as Ground Truth

**All proof generation and cryptographic computation happens in Rust (proof-systems).**

We **NEVER** implement cryptographic primitives from scratch in PureScript. proof-systems is treated as **given by god** - our job is to match whatever it does exactly.

### FORBIDDEN: Re-implementing in FFI

When testing that PureScript matches proof-systems, you must **NEVER** re-implement proof-systems logic in the FFI layer (`crypto-provider/`).

- **WRONG**: Write new Rust code in `crypto-provider/` that re-implements the algorithm
- **WRONG**: Copy-paste logic from proof-systems into FFI wrapper

### CORRECT: Modify vendored proof-systems to expose internals

Because `vendor/proof-systems/` is a locally vendored dependency, you **CAN and SHOULD** modify it to expose values or methods that aren't currently public.

- **RIGHT**: Add `pub` to an existing private field/method
- **RIGHT**: Add a new method that returns internal state (like `checkpoint()`)
- **RIGHT**: Make a private struct field public for testing access

---

## The Recursive Cycle

```
                    ┌────────────────────────────────────────┐
                    │                                        │
                    ▼                                        │
WrapProof(s) ──expand_proof──► StepCircuit ──prove──► StepProof
   (Tock)           │              (Tick)                (Tick)
                    │                                        │
                    │    deferred_values                     │
                    │         ↓                              │
                    │    WrapCircuit ◄───────────────────────┘
                    │       (Tock)
                    │         │
                    │         ▼
                    └──── WrapProof
                          (Tock)
```

**Step** (Tick/Pallas curve, Fq field):
- Verifies previous wrap proof(s)
- Runs application logic
- Outputs step proof

**Wrap** (Tock/Vesta curve, Fp field):
- Verifies previous step proof
- No application logic (just accumulation)
- Outputs wrap proof

---

## Step vs Wrap Verifier Differences

**Mina does NOT use a single shared parameterized verifier circuit.** It uses two fundamentally different implementations:

| Aspect | Step Verifier | Wrap Verifier |
|--------|---------------|---------------|
| **Circuit field** | Fq (Tick) | Fp (Tock) |
| **Inner curve** | Pallas | Vesta |
| **Verifies** | Wrap proof + app | Step proof |
| **Domain** | Dynamic (side-loaded) | Fixed |
| **Shifted type** | Type1 | Type2 |
| **Plonk fields** | 8 | 4 |
| **Scale function** | `scale_fast2` | `scale_fast` |
| **Lines of code** | 1229 | 1707 |

**OCaml files**:
- `mina/src/lib/pickles/step_verifier.ml` (1229 lines)
- `mina/src/lib/pickles/wrap_verifier.ml` (1707 lines)

---

## Cross-Field Value Handling

In the Pasta curve cycle:
- **Pallas curve**: base field = Fp, scalar field = Fq
- **Vesta curve**: base field = Fq, scalar field = Fp

### Value Categories

| Category | Description | Handling |
|----------|-------------|----------|
| **Native** | Can be directly computed in-circuit | Direct computation |
| **Foreign** | Must use special encoding (Shifted_value) | Type1/Type2 encoding |
| **Deferred** | Verified in the next circuit of the recursion | Pass as witness, verify later |

### Type1 vs Type2 Shifted Values

**Source**: `mina/src/lib/crypto/plonkish_prelude/shifted_value.ml`

**Type1** (lines 98-149): Single field element
- Encoding: `t = (s - 2^n - 1) / 2`
- Decoding: `s = 2*t + 2^n + 1`
- Used in Wrap circuit (Fq native, Fp foreign, Fp < Fq)

**Type2** (lines 151-211): Split representation
- Encoding: `(s >> 1, s & 1)` - high bits and parity bit
- Used in Step circuit (Fp native, Fq foreign, Fq > Fp)
- Efficient for `scale_fast2` operations

| Circuit | Other Field Size | Use |
|---------|------------------|-----|
| **Step** (Fp native) | Fq > Fp | **Type2** |
| **Wrap** (Fq native) | Fp < Fq | **Type1** |

### What CAN be done in-circuit (native operations)

1. **Curve point operations** on inner curve points (L/R, delta, sg, U, H)
2. **Sponge squeezing** to get challenges in native field
3. **Endo multiplications** with 128-bit challenges (c, xi)
4. **scaleFast2** with Type2 shifted scalars (z1, z2, b, combined_inner_product)
5. **Commitment combination** using endo (combineSplitCommitments)

### What MUST be deferred

1. **Verification of `combined_inner_product`** correctness
2. **Verification of `b`** (b_poly evaluation)
3. **Verification of polynomial evaluations** (implicit via CIP)

---

## Deferred Values Structure

**Source**: `mina/src/lib/pickles/composition_types/composition_types.ml`

| Value | Computed In | Verified In | Encoding |
|-------|-------------|-------------|----------|
| `combined_inner_product` | This circuit | Next circuit | Type2 Shifted |
| `b` (b_poly result) | This circuit | Next circuit | Type2 Shifted |
| `xi` (polyscale) | This circuit | Next circuit | ScalarChallenge (128-bit) |
| `bulletproof_challenges` | This circuit | Next circuit | Full field (endo-mapped) |
| PLONK challenges | This circuit | Next circuit | Various |

---

## Key Data Structures

| Structure | Contents | Role |
|-----------|----------|------|
| `StepProofState` | Unfinalized proof data | Input from step |
| `MFNStep` | `challenge_poly_commitment`, `old_bulletproof_challenges` | Messages passed to wrap |
| `WrapDeferredValues` | `xi`, `plonk`, `combined_inner_product`, `bulletproof_challenges`, `branch_data` | Expensive values computed outside, verified inside |
| `OpeningProof` | `sg`, `lr`, `delta`, `z1`, `z2` | IPA opening proof components |
| `AllEvals` | Polynomial evaluations at `zeta`, `zeta*omega` | Circuit inputs |

---

## Key Formulas

### b_poly (Challenge Polynomial)
```
b_poly(chals, x) = ∏_i (1 + chals[i] * x^{2^{k-1-i}})
b = b_poly(chals, zeta) + r * b_poly(chals, zetaOmega)
```

### IPA Equation (step_verifier.ml lines 295-331)
```
LHS = c*Q + delta
RHS = z1*(sg + b*u) + z2*H
```
Where:
- `c` is 128-bit scalar challenge (native, used with endo)
- `b`, `z1`, `z2` are Type2 shifted values (other field scalars)
- Curve operations are on native curve points

### ftEval0
```
ftEval0 = permContribution + publicEval - gateConstraints
```

---

## FFI Mapping (Test.Pickles.ProofFFI)

| Diagram Value | FFI Source |
|---------------|------------|
| `zeta` | `proofOracles.zeta` |
| `zetaw` | `proofOracles.zeta * domainGenerator(log2)` |
| `xi` (polyscale) | `proofOracles.v` |
| `r` (evalscale) | `proofOracles.u` |
| `b` | `computeB0` |
| `combined_inner_product` | `proofOracles.combinedInnerProduct` |
| `bulletproof_challenges` | `proofBulletproofChallenges` |
| `plonk0` / `ft_eval0` | `proofOracles.ftEval0` |
| `fq_digest` | `proofOracles.fqDigest` |

---

## Existing PureScript Implementation

### Completed Components

| Module | Checkpoint | Status |
|--------|------------|--------|
| `Pickles/Sponge.purs` | V-1 (Sponge) | Done |
| `Pickles/ScalarChallenge.purs` | V-2 (Challenges) | Done |
| `Pickles/PlonkChecks/GateConstraints.purs` | V-3 | Done |
| `Pickles/PlonkChecks/Permutation.purs` | V-4 | Done |
| `Pickles/PlonkChecks/FtEval.purs` | V-3, V-4 | Done |
| `Pickles/PlonkChecks/CombinedInnerProduct.purs` | V-6 | Done |
| `Pickles/PlonkChecks/XiCorrect.purs` | V-2 (xi, r) | Done |
| `Pickles/IPA.purs` | V-5 (IPA) | Done |
| `Pickles/Commitments.purs` | C-4, C-5, C-6 | Done |

### IPA Module Components (Pickles.IPA)

| Component | Pure | Circuit | Description |
|-----------|:----:|:-------:|-------------|
| `bPoly` | ✓ | ✓ | Challenge polynomial |
| `computeB` | ✓ | ✓ | Combined b at zeta/zetaOmega |
| `bCorrect` | ✓ | ✓ | Verify b matches expected |
| `extractScalarChallenges` | ✓ | ✓ | 128-bit challenges from L/R pairs |
| `bulletReduce` | ✓ | ✓ | lr_prod computation |
| `ipaFinalCheckCircuit` | — | ✓ | Full IPA equation |
| `type1ScalarOps` | — | ✓ | For Pallas circuits |
| `type2ScalarOps` | — | ✓ | For Vesta circuits |

### What's Missing

| Category | Items |
|----------|-------|
| Data Structures | `StepStatement`, `WrapStatement`, `MFNStep`, `MFNWrap`, `StepProofState`, `WrapProofState`, `StepDeferredValues`, `WrapDeferredValues` |
| Prover-Side | `expand_proof`, oracle creation, statement hashing |
| Verifier Composition | Full verifier assembly (`finalize_other_proof`) |
| Circuit Assembly | `StepVerifier`, `WrapVerifier`, `step_main`, `wrap_main` |
| Integration | End-to-end recursive proof cycle |

---

## Implementation Recommendations

### Option 1: Follow Mina's Approach (Recommended)

Create two separate verifier modules:
```
packages/pickles/src/Pickles/
  StepVerifier.purs    -- Circuit over Fq (Pallas scalar field)
  WrapVerifier.purs    -- Circuit over Fp (Vesta scalar field)
  Verifier/
    Common.purs        -- Shared helpers
```

**Pros**: Easier to verify correctness against Mina, clear separation

### Option 2: Unified with Type Classes

```purescript
class Verifier f f' shiftType | f -> f', f -> shiftType where
  scaleOtherField :: AffinePoint (FVar f) -> shiftType (FVar f) -> Snarky ...

instance stepVerifier :: Verifier Fq Fp Type2 where ...
instance wrapVerifier :: Verifier Fp Fq Type1 where ...
```

**Cons**: Harder to verify against Mina, risk of subtle bugs

---

## Testing Pattern

```
1. Create circuit + prover index (PureScript circuit definition, Rust compilation)
2. Generate proof via Rust FFI (createProof)
3. Extract oracles/evals/challenges via FFI (ground truth)
4. Feed values into PureScript circuit as witness
5. Assert circuit:
   - Accepts valid proof data
   - Rejects tampered data (negative tests)
```

---

## Key Source Files

| File | Description |
|------|-------------|
| `mina/src/lib/pickles/step_verifier.ml` | Step verifier (1229 lines) |
| `mina/src/lib/pickles/wrap_verifier.ml` | Wrap verifier (1707 lines) |
| `mina/src/lib/pickles/wrap.ml` | Wrap prover |
| `mina/src/lib/pickles/step.ml` | Step prover |
| `mina/src/lib/pickles/wrap_main.ml` | Wrap circuit assembly |
| `mina/src/lib/pickles/step_main.ml` | Step circuit assembly |
| `mina/src/lib/pickles/common.ml` | Shared utilities |
| `mina/src/lib/pickles/plonk_curve_ops.ml` | Curve operation helpers |
| `mina/src/lib/pickles/scalar_challenge.ml` | Scalar challenge operations |
| `mina/src/lib/pickles/composition_types/composition_types.ml` | Deferred values types |
| `mina/src/lib/crypto/plonkish_prelude/shifted_value.ml` | Type1/Type2 encoding |
