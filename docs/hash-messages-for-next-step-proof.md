# Implement `hashMessagesForNextStepProof`

## What it does

Computes a Poseidon digest that threads application state and IPA accumulation
data through the recursive proof chain. Only computed in the Step circuit; Wrap
receives it as public input and asserts equality.

## Algorithm

**Phase 1 — Absorb wrap verification key (compile-time constant):**

Create a fresh Poseidon sponge and absorb all field elements from the wrap
circuit's `Plonk_verification_key_evals`. These are 28 curve point commitments,
each serialized as (x, y) = 56 field elements total:

| Commitment | Count |
|------------|-------|
| sigma_comm | 7 |
| coefficients_comm | 15 |
| generic_comm | 1 |
| psm_comm | 1 |
| complete_add_comm | 1 |
| mul_comm | 1 |
| emul_comm | 1 |
| endomul_scalar_comm | 1 |

OCaml stages this as `sponge_after_index` — computed once, copied per proof.

**Phase 2 — Absorb proof-specific data (per previous Wrap proof):**

Copy the sponge from phase 1, then absorb:
1. `app_state` — the application's public input/output, serialized to field
   elements via `CircuitType`'s `varToFields`
2. For each of the `n` previous proofs:
   - `sg` point (challenge polynomial commitment, 2 field elements)
   - `bulletproofChallenges` (d raw challenge scalars)

**Phase 3 — Squeeze** to get a single field element digest.

## OCaml references

- `common.ml:47` — pure version (`hash_messages_for_next_step_proof`)
- `step_verifier.ml:1088` — `sponge_after_index` (absorbs verification key)
- `step_verifier.ml:1099` — circuit version (copies sponge, absorbs rest, squeezes)
- `step_main.ml:555` — call site in the Step circuit
- `composition_types.ml:528` — `Messages_for_next_step_proof` data structure
- `composition_types.ml:558` — `to_field_elements_without_index` (serialization)

## What needs to change

1. **`stepCircuit` parameters** — needs the wrap verification key commitments.
   Already available as `columnComms` in `IncrementallyVerifyProofParams`, just
   not passed to `stepCircuit` currently.

2. **`stepCircuit` constraints** — needs `CircuitType` on the app input/output
   type so we can call `varToFields` to serialize `app_state`.

3. **`sg` points** — come from `getOpeningProof` (already in StepWitnessM).
   Requires IVP to be wired into stepCircuit first.

4. **Replace `hashMessagesForNextStepProofStub`** with real Poseidon sponge
   computation.

## Key properties

- **Purely a Pickles construct** — no Rust FFI oracle exists for this value.
- **Step computes, Wrap asserts** — the Wrap circuit receives the digest as
  public input and checks `Field.Assert.equal` against the previous Step's claim.
- **Security comes from proof verification**, not the digest itself. The digest
  is an optimization for compact public input threading.

## Testing

The existing Step → Wrap → Step e2e test flow should pick this up: Step₁
computes the digest, and when Wrap₁ eventually asserts equality, a mismatch
would cause proof failure.
