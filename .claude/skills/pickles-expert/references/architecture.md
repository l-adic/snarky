# Pickles Architecture & Protocol Reference

This document provides a technical overview of the Pickles recursive proof system, focusing on its implementation in PureScript and its correspondence with the Mina OCaml implementation.

## 1. The Recursion Cycle (Step vs Wrap Duality)

Pickles uses a 2-cycle of curves (Pallas and Vesta) to enable efficient recursion. The system is split into two distinct circuit types, each operating on one curve while verifying proofs from the other.

| Component | Curve | Circuit Field | Verifies | OCaml Reference |
|-----------|-------|---------------|----------|-----------------|
| **Step** | Pallas | Fq (Vesta Base) | Wrap Proofs + App Logic | `step_verifier.ml` |
| **Wrap** | Vesta | Fp (Pallas Base) | Step Proofs | `wrap_verifier.ml` |

### Key Architectural Differences
- **Step Verifier**: Supports dynamic "side-loaded" domains and verifies application-specific logic. It handles the "merge" of multiple previous proofs.
- **Wrap Verifier**: Has a fixed structure and fixed domains. Its primary role is to "wrap" a Step proof to prepare it for the next recursion step, often referred to as the "accumulation" phase.

**Source Citations:**
- `mina/src/lib/pickles/step_verifier.ml`
- `mina/src/lib/pickles/wrap_verifier.ml`
- [o1-labs proof-systems book: Pickles](https://o1-labs.github.io/proof-systems/pickles/introduction.html)

---

## 2. Field Conventions & Cross-Field Handling

When verifying a proof from the "other" field, Pickles categorizes values to manage the bit-size mismatch between fields.

### Value Categories
1. **Native**: Values computed directly in the circuit's field (e.g., challenges squeezed from a native sponge).
2. **Foreign (Shifted)**: Scalars from the other field that are larger than the circuit field. These use the **Shifted_value** protocol.
3. **Deferred**: Values that are too expensive to verify in the current circuit and are passed to the next circuit in the recursion.

### Shifted Value Protocol (Type1 vs Type2)
Depending on whether the scalar field is larger or smaller than the circuit field, different shifts are used.

- **Type1**: Used when `scalar field < circuit field`. Shift: $s = 2t + (2^n + 1)$.
- **Type2**: Used when `scalar field > circuit field`. Shift: $s = 2 \cdot s_{div2} + s_{odd} + 2^n$. This allows efficient scalar multiplication via `scale_fast2`.

**Source Citations:**
- `mina/src/lib/crypto/plonkish_prelude/shifted_value.ml`
- `mina/src/lib/pickles/plonk_curve_ops.ml` (Lines 236-252: `scale_fast2` implementation)

---

## 3. Data Structures

### Unfinalized Proof (Deferred Values)
The "bridge" between recursion steps. It contains values computed by the prover that must be checked by the verifier in the next step.

| Value | Encoding | Role | OCaml Reference |
|-------|----------|------|-----------------|
| `plonk` | Native/128-bit | alpha, beta, gamma, zeta challenges | `composition_types.ml:200` |
| `combined_inner_product` | Type1/2 Shifted | Batch poly evaluation at zeta | `composition_types.ml:233` |
| `b` | Type1/2 Shifted | Challenge poly evaluation at zeta | `composition_types.ml` |
| `xi` | 128-bit | Polyscale for IPA | `composition_types.ml` |

### Bootstrapping & Dummies
The base case (Step0) uses dummy proofs with a `should_finalize = false` flag. The circuit asserts `finalized || not should_finalize`, allowing recursion to start from empty state.

**Source Citations:**
- `mina/src/lib/pickles/unfinalized.ml` (Lines 25-104: Dummy creation)
- `mina/src/lib/pickles/step_main.ml` (Line 34: Bootstrapping assertion)

---

## 4. In-Circuit Verification Logic

### IPA Equation (The Final Check)
The Inner Product Argument (IPA) is the core of the polynomial commitment scheme. The final check in the circuit is:
$$c \cdot Q + \delta = z_1 \cdot (sg + b \cdot u) + z_2 \cdot H$$

Where:
- $c$ is a 128-bit scalar challenge.
- $z_1, z_2, b$ are Type2 shifted values (other-field scalars).
- All curve points are native.

**Source Citations:**
- `mina/src/lib/pickles/step_verifier.ml` (Lines 295-331: IPA equation implementation)
- `mina/src/lib/pickles/wrap_verifier.ml` (Lines 570-616: Bulletproof check structure)

### Plonk Checks
- **ft_eval0**: The composition of permutation, public input, and gate constraints.
- Formula: `ftEval0 = permContribution + publicEval - gateConstraints`
- Reference: `mina/src/lib/pickles/plonk_checks/plonk_checks.ml` (Lines 349-399)
