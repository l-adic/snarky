# FinalizeOtherProof: Sub-Circuit Comparison Plan

## Strategy

Match OCaml's `Step_verifier.finalize_other_proof` (step_verifier.ml:828-1165) step by step.
For each sub-circuit:
1. Add an OCaml dump in `dump_circuit_impl.ml` with flat array input
2. Implement matching PureScript circuit (fresh, following OCaml structure exactly)
3. Compare JSON — gate types, counts, wiring must match

Only after all sub-circuits match individually do we compose them and check correctness
against existing Rust FFI tests.

## Current Status

| Sub-circuit | OCaml dump | PS impl | JSON match |
|-------------|-----------|---------|------------|
| Linearization (scalars_env) | Yes | Yes | Yes |
| Full FOP | Yes | Yes | 305 gate gap |

## OCaml Steps → Sub-Circuits

### 1. `expand_plonk` (Steps 2+4)

**What it does**: Expand scalar challenges alpha, zeta via endo. Compute zetaw = generator * zeta.

**OCaml code** (step_verifier.ml:867-889):
```ocaml
let scalar = SC.to_field_checked ~endo:Endo.Wrap_inner_curve.scalar in
let plonk = Plonk.In_circuit.map_challenges ~f:Fn.id ~scalar plonk in
let zetaw = Field.mul domain#generator plonk.zeta in
```

`map_challenges` applies `scalar` to `alpha` and `zeta` only. `beta`, `gamma` pass through
unchanged (`~f:Fn.id`). `joint_combiner` is `Opt.Nothing` so it's skipped.

**Input layout** (6 fields):
```
0: alpha (scalar_challenge inner, 128-bit)
1: beta (plain field)
2: gamma (plain field)
3: zeta (scalar_challenge inner, 128-bit)
4: domain_generator (constant, but include for completeness)
5: endo_scalar (constant)
```

**Output**: expanded alpha, beta (=input), gamma (=input), expanded zeta, zetaw

**Expected gates**: 2 EndoScalar expansions (2×8=16 EndoScalar) + 1 Generic (zetaw mul) + assertion gates

**Why it matters**: Verifies our `expandPlonkMinimalCircuit` + `toField` match OCaml exactly.
Tests EndoScalar gate generation in isolation.

---

### 2. `challenge_digest` (Step 7a)

**What it does**: Compute challenge digest from prev_challenges using opt_sponge.

**OCaml code** (step_verifier.ml:923-933):
```ocaml
let challenge_digest =
  let opt_sponge = Opt_sponge.create sponge_params in
  Vector.iter2 actual_width_mask prev_challenges ~f:(fun keep chals ->
    Vector.iter chals ~f:(fun chal ->
      Opt_sponge.absorb opt_sponge (keep, chal) )) ;
  Opt_sponge.squeeze opt_sponge
in
```

**Input layout** (34 fields):
```
0-1:   mask (2 booleans)
2-17:  prev_challenges[0] (16 fields)
18-33: prev_challenges[1] (16 fields)
```

**Output**: 1 field (challenge_digest)

**Expected gates**: PoseidonGate (sponge absorb/squeeze) + Generic (opt_sponge if/then)

**Why it matters**: We have `challengeDigestCircuit` in PureScript. This verifies the
opt_sponge logic matches OCaml's pattern of conditional absorption.

---

### 3. `sponge_and_challenges` (Steps 7+8)

**What it does**: Full sponge reconstruction from digest through squeezing xi and r.

**OCaml code** (step_verifier.ml:920-999):
```ocaml
(* Initialize sponge with sponge_digest (done before this function) *)
Sponge.absorb sponge (`Field challenge_digest) ;
Sponge.absorb sponge (`Field ft_eval1) ;
(* Absorb public_input evals *)
Array.iter ~f:(fun x -> Sponge.absorb sponge (`Field x)) (fst evals.public_input) ;
Array.iter ~f:(fun x -> Sponge.absorb sponge (`Field x)) (snd evals.public_input) ;
(* Absorb all polynomial evaluations *)
let xs = Evals.In_circuit.to_absorption_sequence evals.evals in
List.iter xs ~f:(...) ;
(* Squeeze challenges *)
let xi_actual = squeeze_challenge sponge in
let r_actual = squeeze_challenge sponge in
(* Convert to field *)
let xi = scalar xi in
let r = scalar (Import.Scalar_challenge.create r_actual) in
```

**Input layout**: sponge_digest + challenge_digest + ft_eval1 + all_evals + xi_expected
(exact layout TBD from dump)

**Output**: xi_correct (bool), xi (field), r (field)

**Expected gates**: PoseidonGate (many absorb/squeeze) + 2 EndoScalar (xi, r expansion) +
Generic (xi_correct equals check)

**Why it matters**: This is the full Fiat-Shamir reconstruction. All PoseidonGate gates come
from here. Matching this sub-circuit pins down the -11 PoseidonGate gap.

**Note**: The absorption sequence includes `Maybe` handling for optional evals. With all
feature flags false, the `Maybe` branches simplify to `Nothing` (skip). Need to verify
`to_absorption_sequence` order matches our `absorbAllEvals`.

---

### 4. `combined_evals` (Step 9)

**What it does**: Combine chunked polynomial evaluations using powers of zeta.

**OCaml code** (step_verifier.ml:1006-1016):
```ocaml
let n = Int.ceil_log2 Max_degree.step in
let zeta_n = pow2_pow plonk.zeta n in
let zetaw_n = pow2_pow zetaw n in
Evals.In_circuit.map ~f:(fun (x0, x1) ->
  (actual_evaluation ~pt_to_n:zeta_n x0,
   actual_evaluation ~pt_to_n:zetaw_n x1)) evals.evals
```

`actual_evaluation` for single-element arrays (our case) is just `e.(0)` — no-op.
But `pow2_pow` still generates gates for `zeta_n` and `zetaw_n`.

**Input layout** (2 fields):
```
0: zeta
1: zetaw
```

**Output**: zeta_n, zetaw_n (both computed but only used if chunked evals exist)

**Expected gates**: 2 × `ceil_log2(Max_degree.step)` squarings. `Max_degree.step` is
likely 2^18 or similar — need to check.

**Why it matters**: OCaml computes these even when evals are single-element. If we don't,
that's missing gates. Could explain some of the GenericPlonkGate gap.

**TODO**: Check `Max_degree.step` value. If it generates gates we're not producing,
that explains some of the gap (but in the WRONG direction — OCaml would have MORE generic
gates, not fewer). Actually OCaml has fewer generics, so this isn't the gap source.

---

### 5. `sg_evals` (Steps 5+6)

**What it does**: Build challenge polynomials from prev_challenges and evaluate at zeta/zetaw.

**OCaml code** (step_verifier.ml:898-914):
```ocaml
let sg_olds = Vector.map prev_challenges ~f:(fun chals ->
  unstage (challenge_polynomial (Vector.to_array chals))) in
let sg_evals1, sg_evals2 =
  let sg_evals pt =
    Vector.map2 ~f:(fun keep f -> (keep, f pt))
      (Vector.trim_front actual_width_mask ...) sg_olds in
  (sg_evals plonk.zeta, sg_evals zetaw)
```

`challenge_polynomial` (wrap_verifier.ml:35-57) for k=16 challenges:
- Computes pow_two_pows: 15 squarings of `pt` (k-1 muls)
- Computes product of k terms: k-1 muls, each term is `1 + chals[i] * pow_two_pows[k-1-i]`
  which is k muls + k adds

Per evaluation point, per proof: ~15 + 16 + 15 = ~46 multiplications.
With 2 proofs × 2 eval points = 4 evaluations: ~184 multiplications.

**Input layout** (36 fields):
```
0-15:  prev_challenges[0] (16 expanded challenges)
16-31: prev_challenges[1] (16 expanded challenges)
32:    zeta
33:    zetaw
34-35: mask (2 booleans)
```

**Output**: sg_evals1 (2 values with keeps), sg_evals2 (2 values with keeps)

**Expected gates**: ~184 Generic (multiplications) + mask handling

**Why it matters**: This is a MAJOR component we're completely missing in our PS circuit.
~184 multiplications = ~184 GenericPlonkGate. We have 349 FEWER generics than OCaml... wait,
we have 349 MORE. So this isn't the source of our excess either. But it IS functionality
we're missing — these sg_evals feed into the CIP computation (Step 11).

**IMPORTANT**: The sg_evals are prepended to the CIP evaluation vector. Our CIP doesn't
include them, which means our CIP structure differs from OCaml's. This could cause gate
ordering differences even if the total gate count is similar.

---

### 6. `scalars_env` (Step 10)

**Already done** — this is the linearization circuit. Our `evaluateGateConstraintsM` with
`buildCircuitEnvM` matches OCaml's `Plonk_checks.scalars_env`.

The linearization JSON comparison test passes.

---

### 7. `ft_eval0` (Step 11a)

**What it does**: Compute quotient polynomial evaluation at zeta from PlonK relation.

**OCaml code** (step_verifier.ml:1073-1077):
```ocaml
let ft_eval0 =
  Plonk_checks.ft_eval0 (module Field) ~env ~domain plonk_minimal combined_evals
    evals1.public_input
```

This calls `plonk_checks.ml:350-398` which computes:
- `constant_term`: evaluate linearization polynomial using `env`
- Permutation contribution (from `perm` field in `derive_plonk`)
- `ft_eval0 = perm - constant_term - public_eval + domain_contribution`

**Input layout**: Same as linearization inputs + permutation inputs + public_eval +
domain values (from scalars_env).

This is closely related to the linearization circuit but adds the permutation and
public_eval terms. We have `ftEval0CircuitM` which should match.

**Recommendation**: Dump this as a separate sub-circuit to verify our `ftEval0CircuitM`
independently. The permutation contribution involves shifts, which we now get from FFI.

---

### 8. `combined_inner_product` (Step 11b)

**What it does**: Compute the combined inner product from all evaluations.

**OCaml code** (step_verifier.ml:1082-1120):
```ocaml
let combine ~ft ~sg_evals x_hat (e : _ Evals.In_circuit.t) =
  let sg_evals = sg_evals |> Vector.to_list
    |> List.map ~f:(fun (keep, eval) -> [| Opt.Maybe (keep, eval) |]) in
  let a = Evals.In_circuit.to_list e |> List.map ~f:(...) in
  let v = List.append sg_evals (Array.map ~f:Opt.just x_hat :: [| Opt.just ft |] :: a) in
  Common.combined_evaluation (module Impl) ~xi v
in
combine ~ft:ft_eval0 ~sg_evals:sg_evals1 evals1.public_input evals1.evals
+ r * combine ~ft:ft_eval1 ~sg_evals:sg_evals2 evals2.public_input evals2.evals
```

**Key difference from our current implementation**: OCaml prepends `sg_evals` (challenge
polynomial evaluations) to the evaluation list. Also uses `Maybe` for optional evaluations
(though all are `Just` or `Nothing` with standard features).

**Why it matters**: The sg_evals inclusion is the biggest structural difference. Our
`combinedInnerProductCircuit` doesn't include them.

---

### 9. `b_correct` (Step 12)

**What it does**: Verify b = b(zeta) + r * b(zetaw) where b(X) is the challenge polynomial.

**OCaml code** (step_verifier.ml:1126-1141):
```ocaml
let bulletproof_challenges = compute_challenges ~scalar bulletproof_challenges in
let challenge_poly = unstage (challenge_polynomial (Vector.to_array bulletproof_challenges)) in
let b_actual = challenge_poly plonk.zeta + (r * challenge_poly zetaw) in
let b_used = Shifted_value.Type1.to_field ~shift:shift1 b in
equal b_used b_actual
```

`compute_challenges ~scalar` expands 16 bulletproof challenges via endo (16 EndoScalar).
Then evaluates challenge_polynomial at zeta and zetaw (same as Step 5-6 but with expanded
challenges).

**Input layout** (20 fields):
```
0-15:  bulletproof_challenges (16 scalar_challenge inners)
16:    zeta
17:    zetaw
18:    r
19:    claimed_b (Type1 shifted)
```

**Output**: b_correct (bool)

**Expected gates**: 16 EndoScalar (expand challenges) + ~92 Generic (challenge_poly × 2
eval points) + 1 Generic (r * ...) + 1 Generic (add) + 1 Generic (unshift) + 1 Generic (equals)

**Why it matters**: Verifies our `bCorrectCircuit` matches OCaml's structure. The challenge
polynomial evaluation is the same algorithm as sg_evals but with expanded challenges.

---

### 10. `plonk_checks_passed` (Step 13)

**What it does**: Check the PlonK permutation relation.

**OCaml code** (step_verifier.ml:1147-1151):
```ocaml
Plonk_checks.checked (module Impl) ~env ~shift:shift1 plonk combined_evals
```

This calls `derive_plonk` to compute the expected permutation value, then compares with
the claimed value via `Shifted_value.equal`.

**Input layout**: permutation inputs + alpha, beta, gamma, zeta + domain values

**Output**: plonk_checks_passed (bool)

**Expected gates**: Small — just permutation contribution + shifted value comparison.

**Why it matters**: Verifies `plonkArithmeticCheckCircuit` matches.

---

### 11. `boolean_all` (Step 14)

**What it does**: Combine checks: `Boolean.all [xi_correct; b_correct; cip_correct; plonk_passed]`

**Expected gates**: 3 Generic (boolean AND chain)

Trivial, but worth including for completeness.

---

## Recommended Order

Priority based on: (a) largest expected gate contribution, (b) most likely to reveal structural
differences, (c) dependencies.

### Phase 1: Independent sub-circuits (no dependencies between them)

1. **`expand_plonk`** (Steps 2+4) — Small, verifies EndoScalar generation. Quick win.
2. **`challenge_digest`** (Step 7a) — Verifies opt_sponge. We have PS impl already.
3. **`b_correct`** (Step 12) — Includes challenge_polynomial eval (key algorithm).
   Also tests `compute_challenges ~scalar` (16 EndoScalar expansions).

### Phase 2: Building blocks for CIP

4. **`sg_evals`** (Steps 5+6) — Challenge polynomial evaluation. Major missing piece.
   Shares algorithm with b_correct but uses raw prev_challenges (not endo-expanded).
5. **`sponge_and_challenges`** (Steps 7+8) — Full Fiat-Shamir. Pins down PoseidonGate gap.

### Phase 3: Composition

6. **`ft_eval0`** (Step 11a) — Already have `ftEval0CircuitM`, verify independently.
7. **`combined_inner_product`** (Step 11b) — Needs sg_evals from Phase 2.
8. **`plonk_checks_passed`** (Step 13) — Already have `plonkArithmeticCheckCircuit`.

### Phase 4: Full composition

9. Compose all sub-circuits and compare against full `finalize_other_proof_circuit.json`.

## Notes

- Each OCaml dump needs its own function in `dump_circuit_impl.ml` with a flat array input
  layout, just like the existing `linearization_tick_circuit` and `finalize_other_proof_circuit`.
- PureScript implementations should follow OCaml's structure exactly — don't abstract or
  simplify until the JSON matches.
- The `domain_for_compiled` with two identical domains (both log2=16) degenerates to a
  single-element selection, so domain handling is nearly trivial for the Known case.
- `Max_degree.step` determines `pow2_pow` exponent in combined_evals. Need to check if this
  generates gates that affect the comparison.
