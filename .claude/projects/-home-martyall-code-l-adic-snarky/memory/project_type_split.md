---
name: Step vs Wrap type families (merlin-verified)
description: OCaml has two distinct Plonk/DeferredValues/FOP type families for Step and Wrap, verified via merlin queries
type: project
---

**Merlin-verified** type split in OCaml's composition_types.ml:

## Step types (Step circuit output, Wrap FOP input)

- `Step.Plonk.In_circuit.t` — 3 params: `('challenge, 'scalar_challenge, 'fq)` — 7 fields, NO feature_flags, NO joint_combiner
- `Step.Deferred_values.t_` — 4 params: `('plonk, 'scalar_challenge, 'fq, 'bp_chals)` — NO branch_data
- `Step.Per_proof.In_circuit.t` — wraps `Step.Deferred_values.t_` + should_finalize + sponge_digest
- Used by: `Impls.Step.unfinalized_proof_var`, `wrap_verifier.finalize_other_proof`

## Wrap types (Wrap statement, Step FOP input)

- `Wrap.Plonk.In_circuit.t` — 6 params: `('challenge, 'scalar_challenge, 'fp, 'fp_opt, 'scalar_challenge_opt, 'bool)` — 9 fields, WITH feature_flags + joint_combiner
- `Wrap.Deferred_values.In_circuit.t` — 8 params: includes `'branch_data` (= `Branch_data.Checked.Step.t`)
- `Wrap.Statement.In_circuit.t` — wraps `Wrap.Proof_state` (with Wrap.Deferred_values) + messages_for_next_step_proof
- Used by: `step_verifier.finalize_other_proof`, `step_verifier.verify`, `Wrap.Statement.In_circuit.to_data` → Spec.pack

## Key: FOP functions use DIFFERENT type families

| FOP function | Input type | branch_data | feature_flags |
|---|---|---|---|
| `step_verifier.finalize_other_proof` | `Wrap.Deferred_values.In_circuit.t` | YES (actively used for domain/mask) | YES |
| `wrap_verifier.finalize_other_proof` | `Step.Deferred_values.In_circuit.t` | NO | NO |

**Why:** Step FOP verifies a Wrap proof (uses Wrap's richer types). Wrap FOP verifies a Step proof (uses Step's simpler types).

## Current PureScript gap

PureScript has ONE `DeferredValues` matching Step's (no branch_data), ONE `PlonkInCircuit` matching Step's (no feature_flags). The Step FOP (`finalizeOtherProofCircuit`) takes `UnfinalizedProof` with Step's types, but OCaml's equivalent takes Wrap's types. The `branch_data` fields (domain_log2, proofs_verified_mask) are passed as separate params instead.

**How to apply:** When aligning the data model, create separate Step and Wrap type families. The Step FOP must take Wrap's DeferredValues (with branch_data and Wrap's PlonkInCircuit).

See: `composition_types.ml` lines 96-116 (Wrap.Plonk), 185-213 (Wrap.DeferredValues), 970-983 (Step.Plonk), 1086-1098 (Step.DeferredValues), step_verifier.ml:828-850, wrap_verifier.ml:1511-1519
