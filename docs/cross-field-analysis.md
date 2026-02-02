# Cross-Field Value Handling in Mina Pickles

## Overview

In the Pasta curve cycle:
- **Pallas curve**: base field = Fp, scalar field = Fq
- **Vesta curve**: base field = Fq, scalar field = Fp

When verifying a proof created over one field in a circuit over the other field, values fall into categories:
1. **Native** - can be directly computed in-circuit
2. **Foreign** - must use special encoding (Shifted_value) or be deferred
3. **Deferred** - verified in the next circuit of the recursion

---

## 1. POLYNOMIAL EVALUATIONS

### Finding: Evaluations are in the "other" field and are DEFERRED

**Wrap Verifier** (circuit over Fp, verifying Step proofs):
- Polynomial evaluations are in Fq (the scalar field of Vesta)
- They are NOT computed in-circuit
- Instead, `combined_inner_product` is a deferred value

**Source**: `mina/src/lib/pickles/wrap_verifier.ml`
- Lines 1582-1643: `combined_inner_product_correct` verification happens in `finalize_other_proof`
- Line 233 of `composition_types.ml`: `combined_inner_product : 'fp` in Deferred_values

**Step Verifier** (circuit over Fq, verifying Wrap proofs):
- Polynomial evaluations are in Fp (the scalar field of Pallas)
- Similarly deferred via `combined_inner_product`

**Source**: `mina/src/lib/pickles/step_verifier.ml`
- Lines 1001-1051: `combined_inner_product_correct` verification of deferred values

### Implication for Our Code

The `combinedInnerProduct` computation in our verifier is correct, BUT:
- The evaluations themselves (witness, sigma, etc.) should be in the **circuit's scalar field**
- If our circuit is over Vesta.BaseField (Fp), evaluations are in Fq
- We CANNOT directly use Fq values in an Fp circuit
- The `combined_inner_product` result is passed as a **Shifted_value.Type2**

---

## 2. CHALLENGES (alpha, beta, gamma, zeta, xi/v, u, c)

### Finding: Challenges are squeezed in the circuit's NATIVE field

**Source**: `mina/src/lib/pickles/wrap_verifier.ml`
- Lines 1208-1209: `beta`, `gamma` sampled via `sample()` in Fp
- Lines 1225, 1232: `alpha`, `zeta` sampled as scalar challenges in Fp
- Line 1534: `let xi = scalar_to_field xi in` - converts 128-bit to full field

**Source**: `mina/src/lib/pickles/step_verifier.ml`
- Lines 549-554: Challenges sampled in Fq

### Key Insight: Challenges are NOT used cross-field

The circuit that samples the challenges uses them directly. The NEXT circuit in the recursion:
1. Re-samples the challenges from the sponge
2. Compares with the claimed deferred values
3. This verification is in `assert_eq_deferred_values` (step_verifier.ml line 336)

### Implication for Our Code

Our challenges (`alpha`, `beta`, `gamma`, `zeta`) are CORRECTLY handled as native field elements.
They are sampled in the circuit's field and used directly.

---

## 3. OPENING PROOF VALUES (z1, z2, sg, delta, L/R pairs)

### Finding: Curve points are native, scalars use Type2 Shifted_value

**Source**: `mina/src/lib/pickles/step_verifier.ml`
- Line 238-239:
  ```ocaml
  ({ lr; delta; z_1; z_2; challenge_polynomial_commitment } :
    (Inner_curve.t, Other_field.t Shifted_value.Type2.t) Bulletproof.t )
  ```

**z1 and z2**:
- Type: `Other_field.t Shifted_value.Type2.t`
- These are scalars from the OTHER field, encoded as Type2 shifted values
- NOT directly usable as field elements in the circuit

**L/R pairs, delta, sg**:
- Type: `Inner_curve.t` (curve points in the circuit's native curve)
- Coordinates are in the circuit's base field (native)
- CAN be used directly for curve operations

### How scale_fast2 works with Type2

**Source**: `mina/src/lib/pickles/step_verifier.ml` lines 228-230:
```ocaml
let scale_fast2 p (s : Other_field.t Shifted_value.Type2.t) =
  Ops.scale_fast2 p s ~num_bits:Field.size_in_bits
```

**Source**: `mina/src/lib/pickles/plonk_curve_ops.ml` lines 236-252:
```ocaml
let scale_fast2 (g : G.t)
    (Pickles_types.Shifted_value.Type2.Shifted_value
      ((s_div_2 : Field.t), (s_odd : Boolean.var)) ) ~(num_bits : int) : G.t =
  (* s_div_2 is (s >> 1), s_odd is (s & 1) *)
```

The Type2 shifted value stores `(s >> 1, s & 1)` where s is in the other field.
This allows efficient scalar multiplication without full other-field arithmetic.

### Implication for Our Code

Our `z1`, `z2` handling with `Type2 f b` is CORRECT in principle, BUT:
- We need to ensure the Type2 values come from the correct field
- The `scaleFast2` operation works with this encoding

---

## 4. THE IPA EQUATION

### Finding: IPA equation is verified with shifted scalars

**Source**: `mina/src/lib/pickles/step_verifier.ml` lines 295-331:
```ocaml
(* Check the IPA relation *)
(* LHS = c*Q + delta *)
let lhs =
  let cq = Scalar_challenge.endo q c in
  Ops.add_fast cq delta
in
(* RHS = z1*(G + b*U) + z2*H *)
let rhs =
  let b_u = scale_fast2 u advice.b in
  let g_plus_b_u = Ops.add_fast challenge_polynomial_commitment b_u in
  let z1_g_plus_b_u = scale_fast2 g_plus_b_u z_1 in
  let z2_h = scale_fast2 h z_2 in
  Ops.add_fast z1_g_plus_b_u z2_h
in
```

Key observations:
1. `c` is a 128-bit scalar challenge (native field, used with `endo`)
2. `b`, `z1`, `z2` are Type2 shifted values (other field scalars)
3. All curve operations are on native curve points
4. `scale_fast2` handles other-field scalars efficiently

### Implication for Our Code

Our IPA equation structure is correct:
- `c` as `SizedF 128 f` with `endo` - CORRECT
- `z1`, `z2` as `Type2 f b` with `scaleFast2` - CORRECT
- `b` needs to be Type2 shifted - NEEDS VERIFICATION

---

## 5. WHAT IS EXPLICITLY DEFERRED

### Source: `mina/src/lib/pickles/composition_types/composition_types.ml`

**Wrap Deferred_values** (lines 200-355):
```ocaml
type ('plonk, 'scalar_challenge, 'fp, ...) t =
  { plonk : 'plonk                    (* alpha, beta, gamma, zeta, etc. *)
  ; combined_inner_product : 'fp      (* Type2 shifted *)
  ; b : 'fp                           (* Type2 shifted *)
  ; xi : 'scalar_challenge            (* 128-bit *)
  ; bulletproof_challenges : ...      (* IPA challenges *)
  }
```

**Step Deferred_values** (lines 1086-1120):
```ocaml
type ('plonk, 'scalar_challenge, 'fq, ...) t =
  { plonk : 'plonk
  ; combined_inner_product : 'fq
  ; b : 'fq
  ; xi : 'scalar_challenge
  ; bulletproof_challenges : ...
  }
```

### What gets deferred:

| Value | Computed In | Verified In | Encoding |
|-------|-------------|-------------|----------|
| `combined_inner_product` | This circuit | Next circuit | Type2 Shifted |
| `b` (b_poly result) | This circuit | Next circuit | Type2 Shifted |
| `xi` (polyscale) | This circuit | Next circuit | ScalarChallenge (128-bit) |
| `bulletproof_challenges` | This circuit | Next circuit | Full field (endo-mapped) |
| PLONK challenges | This circuit | Next circuit | Various |

---

## 6. SHIFTED_VALUE TYPES

### Type1 vs Type2

**Source**: `mina/src/lib/crypto/plonkish_prelude/shifted_value.ml`

**Type1** (lines 98-149):
- Used when scalar field ≈ base field (same size)
- Encoding: `Shifted_value((s - (2^n + 1))/2)`
- Decoding: `2*t + (2^n + 1)`
- Used in same-field verification scenarios

**Type2** (lines 151-211):
```ocaml
(* When the scalar field is larger than the inner field of the circuit,
   we need to encode a scalar [s] as a pair ((s >> 1), s & 1). In other
   words, the high bits, and then the low bit separately.
*)
```
- Used when verifying proofs from the OTHER field
- Encoding: `(s >> 1, s & 1)`
- This splits the scalar into high bits and parity bit
- Efficient for `scale_fast2` operations

### Why Type2 works

For a scalar `s` in the other field:
1. Store as `(s_div_2, s_odd)` where `s = 2*s_div_2 + s_odd`
2. `s_div_2` fits in the circuit's field (roughly)
3. `s_odd` is a boolean
4. Multiplication: `s * P = 2*(s_div_2 * P) + s_odd * P`
5. This avoids full other-field arithmetic

---

## 7. ANALYSIS OF OUR buildVerifierInput

### Problem Areas in E2E.purs

Looking at the commented-out `buildVerifierInput`:

```purescript
-- PROBLEM 1: scalarToBase for polynomial evaluations
convertPointEval :: PointEval Vesta.ScalarField -> PointEval (F Vesta.BaseField)
convertPointEval pe = { zeta: F (scalarToBase pe.zeta), ... }
```

**Issue**: Polynomial evaluations are in Vesta.ScalarField (Fq).
They CANNOT be directly converted to Vesta.BaseField (Fp).
**Solution**: These should be deferred via `combined_inner_product` (Type2 shifted).

```purescript
-- PROBLEM 2: scalarToBase for shifts and permutation values
, permutation:
    { shifts: map (F <<< scalarToBase) shifts
    , alpha: F (scalarToBase ctx.oracles.alpha)
    ...
```

**Issue**: These are trying to convert Fq scalars to Fp.
**Analysis**:
- `shifts` are domain constants - need investigation
- `alpha, beta, gamma` - these should be RE-SQUEEZED in the Fp circuit, not converted!

```purescript
-- PROBLEM 3: challenges conversion
challengesBase :: Vector 16 (F Vesta.BaseField)
challengesBase = unsafePartial $ fromJust $ Vector.toVector $
  map (F <<< scalarToBase) challengesArray
```

**Issue**: Bulletproof challenges are endo-mapped full field values in Fq.
They CANNOT be converted to Fp by truncation.
**Solution**: These must be recomputed in the Fp circuit from the L/R pairs.

---

## 8. RECOMMENDED APPROACH FOR OUR VERIFIER

### What CAN be done in our circuit (native operations):

1. **Curve point operations** on Vesta points (L/R, delta, sg, U, H)
2. **Sponge squeezing** to get challenges in Fp
3. **Endo multiplications** with 128-bit challenges (c, xi)
4. **scaleFast2** with Type2 shifted scalars (z1, z2, b, combined_inner_product)
5. **Commitment combination** using endo (combineSplitCommitments)

### What MUST be deferred to the next (dual) circuit:

1. **Verification of `combined_inner_product`** correctness
   - The CIP is computed from polynomial evaluations in Fq
   - We receive it as a Type2 shifted value
   - We use it in the IPA equation
   - The NEXT circuit (over Fq) verifies it was computed correctly

2. **Verification of `b`** (b_poly evaluation)
   - Same pattern as CIP

3. **Verification of polynomial evaluations**
   - Not directly checked in our circuit
   - Implicitly verified via CIP in the next circuit

### What MUST be done in the SAME circuit type (next recursion step):

1. **Sponge state verification** - the challenges we squeezed must match
2. **sg verification** - `sg = MSM(SRS.g, b_poly_coeffs(challenges))`

---

## 9. CORRECTED VerifyInput STRUCTURE

Based on this analysis, our `VerifyInput` should be:

```purescript
type VerifyInput d n f b =
  { -- Polynomial COMMITMENTS (curve points, native to circuit)
    commitments :: Vector n (AffinePoint f)

  -- IPA opening proof (curve points native, scalars as Type2)
  , ipa ::
      { opening ::
          { lr :: Vector d { l :: AffinePoint f, r :: AffinePoint f }
          , delta :: AffinePoint f
          , z1 :: Type2 f b        -- Other-field scalar, Type2 encoded
          , z2 :: Type2 f b        -- Other-field scalar, Type2 encoded
          , sg :: AffinePoint f
          }
      , h :: AffinePoint f
      , u :: AffinePoint f
      -- Challenges squeezed in THIS circuit's field (native)
      , challenges :: Vector d f   -- IPA challenges (recomputed from L/R in circuit)
      , c :: SizedF 128 f          -- 128-bit, for endo
      }

  -- Values from the OTHER field, passed as Type2 shifted
  , deferredFromOtherField ::
      { combinedInnerProduct :: Type2 f b  -- NOT computed here, verified later
      , b :: Type2 f b                      -- NOT computed here, verified later
      }

  -- Batching scalars (128-bit challenges, native to circuit)
  , polyscale :: SizedF 128 f    -- xi/v_chal
  , evalscale :: SizedF 128 f    -- u_chal

  -- Evaluation points (native field)
  , zeta :: f
  , zetaOmega :: f
  }
```

Note: The polynomial evaluations (witness, sigma, etc.) should NOT be in VerifyInput
at all - they're in the other field! The `combinedInnerProduct` encapsulates them.

---

## 10. KEY SOURCE FILES

| File | Lines | Content |
|------|-------|---------|
| `wrap_verifier.ml` | 570-616 | Bulletproof check structure |
| `wrap_verifier.ml` | 1208-1232 | Challenge sampling |
| `wrap_verifier.ml` | 1582-1643 | Deferred value verification |
| `step_verifier.ml` | 228-334 | IPA equation with Type2 scalars |
| `step_verifier.ml` | 549-554 | Challenge sampling |
| `shifted_value.ml` | 151-211 | Type2 encoding math |
| `composition_types.ml` | 200-355 | Wrap Deferred_values type |
| `composition_types.ml` | 1086-1120 | Step Deferred_values type |
| `plonk_curve_ops.ml` | 236-252 | scale_fast2 implementation |
