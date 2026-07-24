import Bulletproof.Forking.Adapter

/-!
# Special soundness of the Schnorr wrapper, as computed data

Kimchi's wire verifier does not check the IPA leaf equation directly: the final folded scalar
`a₀` and the accumulated blinder are hidden behind a Schnorr layer — the proof carries
`(δ, z1, z2)` with `z1 = a₀·c + d`, and the acceptance equation is

```
c • Q + δ = z1 • sg + (z1·b0) • U + z2 • H        (VerifierAcceptsAt, first conjunct)
```

for the transcript-derived Schnorr challenge `c`. Ironwood's halo2 deployment has no such
wrapper, so this is the one extraction step the reuse cannot supply.

It is 2-special-sound: two accepting runs at the same transcript prefix — same `Q`, `δ`, `sg`,
`b0` — and distinct Schnorr challenges eliminate `δ` by subtraction and divide by `c − c'`,
yielding the de-Schnorr'd equation `Q = ā • sg + (ā·b0) • U + ρ̄ • H` with

```
ā = (z1 − z1')/(c − c'),    ρ̄ = (z2 − z2')/(c − c').
```

For an honest prover `ā = a₀` and `ρ̄` is the accumulated blinder. Returned as data (`Σ'`), per
the breaks-as-computed-data convention: the leaf scalars feed ironwood's deployed tree, where a
`Prop`-level existential would be unrecoverable.
-/

namespace Bulletproof.Forking

open Bulletproof

variable {F G : Type*} [Field F] [AddCommGroup G] [Module F G]

/-- **The Schnorr layer is 2-special-sound, with explicit extraction formulas.** Two accepting
verifier equations at the same recombined commitment `Q`, Schnorr commitment `δ`, folded
generator `sg` and eval scalar `b0`, with distinct challenges `c ≠ c'`, determine the
de-Schnorr'd leaf equation at the difference quotients — the extracted scalar
`(z1 − z1')/(c − c')` and blinder `(z2 − z2')/(c − c')`.

Stated with the formulas inline (rather than behind an existential or a `Σ'`) so the fork
certificate can *compute* its leaf data from the two transcripts and this theorem can then
discharge the certificate's validity by rewriting — the breaks-as-computed-data convention. -/
theorem schnorr_fork_eq (U H Q δ sg : G) (b0 : F) {c z1 z2 c' z1' z2' : F} (hne : c ≠ c')
    (h : c • Q + δ = z1 • sg + (z1 * b0) • U + z2 • H)
    (h' : c' • Q + δ = z1' • sg + (z1' * b0) • U + z2' • H) :
    Q = ((z1 - z1') / (c - c')) • sg + (((z1 - z1') / (c - c')) * b0) • U
        + ((z2 - z2') / (c - c')) • H := by
  have hcc : c - c' ≠ 0 := sub_ne_zero.mpr hne
  -- Subtract the two acceptance equations: `δ` cancels.
  have hsub : (c - c') • Q
      = (z1 - z1') • sg + ((z1 - z1') * b0) • U + (z2 - z2') • H := by
    calc (c - c') • Q
        = (c • Q + δ) - (c' • Q + δ) := by rw [sub_smul]; abel
      _ = (z1 • sg + (z1 * b0) • U + z2 • H)
            - (z1' • sg + (z1' * b0) • U + z2' • H) := by rw [h, h']
      _ = (z1 - z1') • sg + ((z1 - z1') * b0) • U + (z2 - z2') • H := by
          simp only [sub_smul, sub_mul]; abel
  -- Divide by `c − c'`.
  have hQ : Q = (c - c')⁻¹ • ((c - c') • Q) := by
    rw [smul_smul, inv_mul_cancel₀ hcc, one_smul]
  rw [hQ, hsub]
  match_scalars <;> field_simp

end Bulletproof.Forking
