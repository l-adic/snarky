# Step vs Wrap Verifier Architecture in Mina Pickles

## Summary

**Mina's Pickles does NOT use a single shared parameterized verifier circuit.**

Instead, it uses two fundamentally different verifier implementations:
- `step_verifier.ml` (1229 lines) - Circuit over Tick/Fq field (Pallas curve)
- `wrap_verifier.ml` (1707 lines) - Circuit over Tock/Fp field (Vesta curve)

Each is specifically tailored for its role in the recursive proof system.

---

## Key Differences

### 1. Function Signatures

**Step `incrementally_verify_proof`** (step_verifier.ml line 484):
```ocaml
val incrementally_verify_proof
  : ...
  -> domain:[ `Known of Domain.t | `Side_loaded of Branch_data.One_hot.t ]
  -> sponge_after_index:Sponge.t
  -> proof:Wrap_proof.Checked.t
  -> plonk:(* 6-field variant *)
  -> ...
```

**Wrap `incrementally_verify_proof`** (wrap_verifier.ml line 799):
```ocaml
val incrementally_verify_proof
  : ...
  -> actual_proofs_verified_mask:(Boolean.var, b) Vector.t
  -> step_domains:(Domains.t, a) Vector.t
  -> verification_key:(* different type *)
  -> openings_proof:Bulletproof.t
  -> plonk:(* 4-field variant *)
  -> ...
```

### 2. Domain Handling

| Verifier | Domain Type | Source |
|----------|-------------|--------|
| **Step** | Dynamic side-loaded domains supported | step_verifier.ml line 484 |
| **Wrap** | Fixed pre-computed domains only | wrap_verifier.ml line 799 |

### 3. Shifted Value Types

| Verifier | Shift Type | Shift Constant | Source |
|----------|------------|----------------|--------|
| **Step** | Type1 | `shift1 = 2^n + 1` | step_verifier.ml line 853 |
| **Wrap** | Type2 | `shift2 = 2^n` | wrap_verifier.ml line 1422 |

### 4. Plonk Types

| Verifier | Plonk Variant | Fields | Source |
|----------|---------------|--------|--------|
| **Step** | 8-field variant | Includes Branch_data, feature flags | step_verifier.ml |
| **Wrap** | 4-field variant | Simpler structure | wrap_verifier.ml |

### 5. Bulletproof/IPA Verification

**Step `check_bulletproof`** (step_verifier.ml line 232):
```ocaml
let scale_fast2 p (s : Other_field.t Shifted_value.Type2.t) =
  Ops.scale_fast2 p s ~num_bits:Field.size_in_bits

(* Uses Pcs_batch.combine_split_commitments with Maybe_finite matching *)
(* Handles Type2 shifted values *)
```

**Wrap `check_bulletproof`** (wrap_verifier.ml line 564):
```ocaml
let scale_fast p s =
  Ops.scale_fast p s ~num_bits:(Nat.to_int Tick.Field.size_in_bits)

(* Uses Split_commitments.combine ~xi *)
(* Handles Type1 shifted values *)
```

### 6. Commitment Combination

| Verifier | Function | Source |
|----------|----------|--------|
| **Step** | `Pcs_batch.combine_split_commitments` with `Maybe_finite` | step_verifier.ml line 266-291 |
| **Wrap** | `Split_commitments.combine ~xi` | wrap_verifier.ml line 588 |

### 7. Proof Structure Being Verified

| Verifier | Verifies | Application Circuit |
|----------|----------|---------------------|
| **Step** | Wrap proof + application circuit | Yes - verifies app logic |
| **Wrap** | Step proof only | No - just accumulates |

---

## Algorithmic Differences in Detail

### IPA Equation Implementation

**Step** (step_verifier.ml lines 295-331):
```ocaml
(* Uses Type2 shifted values for z1, z2, b, combined_inner_product *)
let rhs =
  let b_u = scale_fast2 u advice.b in
  let g_plus_b_u = Ops.add_fast challenge_polynomial_commitment b_u in
  let z1_g_plus_b_u = scale_fast2 g_plus_b_u z_1 in
  let z2_h = scale_fast2 h z_2 in
  Ops.add_fast z1_g_plus_b_u z2_h
```

**Wrap** (wrap_verifier.ml lines 595-616):
```ocaml
(* Uses Type1 shifted values *)
(* Different helper functions and absorption patterns *)
```

### Finalize Other Proof

**Step `finalize_other_proof`** (step_verifier.ml line 823):
- Supports side-loaded domains (dynamic domain selection)
- Uses `shift1` (Type1)
- 8-field Plonk variant
- Validates feature flags during proof finalization

**Wrap `finalize_other_proof`** (wrap_verifier.ml line 1450):
- Fixed domains only
- Uses `shift2` (Type2)
- 4-field Plonk variant
- Simpler validation

---

## What IS Shared

Some helper modules are used by both verifiers:

| Module | Location | Shared Functions |
|--------|----------|------------------|
| `plonk_curve_ops.ml` | `mina/src/lib/pickles/` | `scale_fast`, `scale_fast2`, `add_fast` |
| `common.ml` | `mina/src/lib/pickles/` | `combined_evaluation`, utilities |
| `scalar_challenge.ml` | `mina/src/lib/pickles/` | `endo`, `endo_inv`, `to_field` |
| `pcs_batch.ml` | `mina/src/lib/pickles/` | `combine_split_commitments`, `combine_split_evaluations` |

---

## Why This Architecture?

The Pasta 2-cycle design **requires** different implementations because:

1. **Curve duality**: Each verifier operates in its target field while verifying proofs from the opposite field

2. **Asymmetric recursion**:
   - Step verifies one prior state + application logic
   - Wrap accumulates multiple step proofs

3. **Different IPA accumulation strategies**: The bulletproof challenge handling differs based on which direction of the cycle we're in

4. **Domain flexibility**: Step circuits can have variable domains (for different application circuits); Wrap has fixed structure

5. **Shifted value encoding**: Type1 vs Type2 shifting is determined by which field is "larger" relative to the circuit field

---

## Implications for PureScript Translation

### Option 1: Follow Mina's Approach (Recommended)

Create two separate verifier modules:
```
packages/pickles/src/Pickles/
  StepVerifier.purs    -- Circuit over Fq (Pallas scalar field)
  WrapVerifier.purs    -- Circuit over Fp (Vesta scalar field)
  Verifier/
    Common.purs        -- Shared helpers
    ScalarChallenge.purs
    PlonkCurveOps.purs
```

**Pros**:
- Easier to verify correctness against Mina
- Clear separation of concerns
- Matches Mina's structure for debugging

**Cons**:
- Some code duplication
- Two modules to maintain

### Option 2: Unified with Type Classes

Create a single parameterized verifier using PureScript type classes:
```purescript
class Verifier f f' shiftType | f -> f', f -> shiftType where
  scaleOtherField :: AffinePoint (FVar f) -> shiftType (FVar f) -> Snarky ...
  combineCommitments :: ...
  -- etc.

instance stepVerifier :: Verifier Fq Fp Type2 where ...
instance wrapVerifier :: Verifier Fp Fq Type1 where ...
```

**Pros**:
- Less code duplication
- More "PureScript-like"

**Cons**:
- Harder to verify against Mina
- The differences are significant enough that the abstraction may be leaky
- Risk of subtle bugs from over-abstraction

### Recommendation

Start with **Option 1** (two separate modules) because:
1. The differences are substantial (Type1 vs Type2, different Plonk variants, domain handling)
2. Easier to debug against Mina's implementation
3. Can refactor to shared code once correctness is established

---

## File References

All paths relative to `/home/martyall/code/l-adic/snarky/mina/src/lib/pickles/`:

| File | Lines | Description |
|------|-------|-------------|
| `step_verifier.ml` | 1229 | Step verifier implementation |
| `step_verifier.mli` | ~100 | Step verifier interface |
| `wrap_verifier.ml` | 1707 | Wrap verifier implementation |
| `wrap_verifier.mli` | ~150 | Wrap verifier interface |
| `common.ml` | ~300 | Shared utilities |
| `plonk_curve_ops.ml` | ~300 | Curve operation helpers |
| `scalar_challenge.ml` | ~250 | Scalar challenge operations |
| `pcs_batch.ml` | ~100 | Polynomial commitment batching |

---

## Comparison Table

| Aspect | Step Verifier | Wrap Verifier |
|--------|---------------|---------------|
| **Circuit field** | Fq (Tick) | Fp (Tock) |
| **Inner curve** | Pallas | Vesta |
| **Verifies** | Wrap proof + app | Step proof |
| **Domain** | Dynamic (side-loaded) | Fixed |
| **Shifted type** | Type1 | Type2 |
| **Plonk fields** | 8 | 4 |
| **Scale function** | `scale_fast2` | `scale_fast` |
| **Commitment combine** | `Pcs_batch.combine_split_commitments` | `Split_commitments.combine` |
| **Feature flags** | Validated | N/A |
| **Lines of code** | 1229 | 1707 |
