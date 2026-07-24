import Zcash.Snark.Soundness.Forking.Probability

/-!
# W3 · Sequential escape bounds over uniform challenge vectors

The guard antecedents of `RunGuardImp` exclude each Fiat–Shamir challenge from a bad set
determined by data absorbed *before* that challenge's squeeze — a chained family: `β`'s set is
challenge-free, `γ`'s depends on `β`, and so on. This module proves the generic escape bounds:
over a uniform challenge vector, the probability that *some* coordinate lands in its
(earlier-coordinates-determined) bad set is at most the sum of the per-set cardinality bounds
over `|F|`.

Everything here is a statement about `PMF.uniformOfFintype (Fin k → F)` — the challenge vector's
own distribution; no oracle table appears. W4 lifts these bounds to the finite-domain oracle
game with `Zcash.Snark.uniformOfFintype_fresh_read_bound`, whose `S`-family is exactly the
events below (that is why they are stated over `Fin k → F`) and whose injectivity input is the
prefix distinctness proved in `Forking.Transcript`.

Consumes `zcash/ironwood`'s `Forking.Probability` (the first `Zcash` import in the build):
`uniformOfFintype_toOuterMeasure_finset`, `map_uniformOfFintype_equiv`, and
`uniformOfFintype_prod_fiber_bound`.
-/

namespace Kimchi.Verifier.Forking

open Zcash.Snark MeasureTheory
open scoped ENNReal

variable {F : Type*} [Fintype F] [DecidableEq F] [Nonempty F]

/-- One coordinate's escape: if a bad-set family reads only the *other* coordinates and every
member has card `≤ b`, a uniform vector's `i`-th coordinate lands in it with probability
`≤ b / |F|`. The `i`-th coordinate is a fresh uniform draw against a set fixed by the rest. -/
theorem escape_coord {k : ℕ} (i : Fin k) (S : (Fin k → F) → Finset F) {b : ℕ}
    (hcard : ∀ χ, (S χ).card ≤ b)
    (hdep : ∀ χ χ' : Fin k → F, (∀ j, j ≠ i → χ j = χ' j) → S χ = S χ') :
    (PMF.uniformOfFintype (Fin k → F)).toOuterMeasure {χ | χ i ∈ S χ}
      ≤ (b : ℝ≥0∞) / Fintype.card F := by
  classical
  set e : (Fin k → F) ≃ F × ({j : Fin k // j ≠ i} → F) := Equiv.piSplitAt i (fun _ => F)
  -- the family read off the non-`i` coordinates alone
  set S' : ({j : Fin k // j ≠ i} → F) → Set F :=
    fun r => ↑(S (e.symm (Classical.arbitrary F, r))) with hS'
  have hev : {χ : Fin k → F | χ i ∈ S χ} = e ⁻¹' {p | p.1 ∈ S' p.2} := by
    ext χ
    have h1 : (e χ).1 = χ i := rfl
    have hSχ : S (e.symm (Classical.arbitrary F, (e χ).2)) = S χ := by
      refine hdep _ _ fun j hj => ?_
      simp [e, Equiv.piSplitAt, dif_neg hj]
    simp only [Set.mem_setOf_eq, Set.mem_preimage, hS', Finset.mem_coe, h1, hSχ]
  rw [hev, ← PMF.toOuterMeasure_map_apply, map_uniformOfFintype_equiv e]
  refine uniformOfFintype_prod_fiber_bound S' fun r => ?_
  rw [hS', uniformOfFintype_toOuterMeasure_finset]
  exact ENNReal.div_le_div_right (by exact_mod_cast hcard _) _

/-- Two chained challenges (the fr side, `v` then `u`): escape from a fixed set and a
first-coordinate-determined set, with probability `≤ (b₁ + b₂)/|F|`. -/
theorem escape2 (S₁ : Finset F) (S₂ : F → Finset F) {b₁ b₂ : ℕ}
    (h₁ : S₁.card ≤ b₁) (h₂ : ∀ x, (S₂ x).card ≤ b₂) :
    (PMF.uniformOfFintype (Fin 2 → F)).toOuterMeasure
      {χ | χ 0 ∈ S₁ ∨ χ 1 ∈ S₂ (χ 0)} ≤ (b₁ + b₂ : ℝ≥0∞) / Fintype.card F := by
  have h0 : (PMF.uniformOfFintype (Fin 2 → F)).toOuterMeasure {χ | χ 0 ∈ S₁}
      ≤ (b₁ : ℝ≥0∞) / Fintype.card F :=
    escape_coord 0 (fun _ => S₁) (fun _ => h₁) (fun _ _ _ => rfl)
  have h1 : (PMF.uniformOfFintype (Fin 2 → F)).toOuterMeasure {χ | χ 1 ∈ S₂ (χ 0)}
      ≤ (b₂ : ℝ≥0∞) / Fintype.card F :=
    escape_coord 1 (fun χ => S₂ (χ 0)) (fun _ => h₂ _)
      (fun χ χ' h => congrArg S₂ (h 0 (by decide)))
  calc (PMF.uniformOfFintype (Fin 2 → F)).toOuterMeasure {χ | χ 0 ∈ S₁ ∨ χ 1 ∈ S₂ (χ 0)}
      ≤ (PMF.uniformOfFintype (Fin 2 → F)).toOuterMeasure {χ | χ 0 ∈ S₁}
        + (PMF.uniformOfFintype (Fin 2 → F)).toOuterMeasure {χ | χ 1 ∈ S₂ (χ 0)} := by
        rw [Set.setOf_or]; exact measure_union_le _ _
    _ ≤ (b₁ : ℝ≥0∞) / Fintype.card F + (b₂ : ℝ≥0∞) / Fintype.card F := add_le_add h0 h1
    _ = (b₁ + b₂ : ℝ≥0∞) / Fintype.card F := ENNReal.div_add_div_same

/-- Four chained challenges (the fq side, `β γ α ζ`): escape from a chained bad-set family,
with probability `≤ (b₁ + b₂ + b₃ + b₄)/|F|`. -/
theorem escape4 (S₁ : Finset F) (S₂ : F → Finset F) (S₃ : F → F → Finset F)
    (S₄ : F → F → F → Finset F) {b₁ b₂ b₃ b₄ : ℕ}
    (h₁ : S₁.card ≤ b₁) (h₂ : ∀ x, (S₂ x).card ≤ b₂)
    (h₃ : ∀ x y, (S₃ x y).card ≤ b₃) (h₄ : ∀ x y z, (S₄ x y z).card ≤ b₄) :
    (PMF.uniformOfFintype (Fin 4 → F)).toOuterMeasure
      {χ | χ 0 ∈ S₁ ∨ χ 1 ∈ S₂ (χ 0) ∨ χ 2 ∈ S₃ (χ 0) (χ 1)
        ∨ χ 3 ∈ S₄ (χ 0) (χ 1) (χ 2)}
      ≤ (b₁ + b₂ + b₃ + b₄ : ℝ≥0∞) / Fintype.card F := by
  have h0 : (PMF.uniformOfFintype (Fin 4 → F)).toOuterMeasure {χ | χ 0 ∈ S₁}
      ≤ (b₁ : ℝ≥0∞) / Fintype.card F :=
    escape_coord 0 (fun _ => S₁) (fun _ => h₁) (fun _ _ _ => rfl)
  have h1 : (PMF.uniformOfFintype (Fin 4 → F)).toOuterMeasure {χ | χ 1 ∈ S₂ (χ 0)}
      ≤ (b₂ : ℝ≥0∞) / Fintype.card F :=
    escape_coord 1 (fun χ => S₂ (χ 0)) (fun _ => h₂ _)
      (fun χ χ' h => congrArg S₂ (h 0 (by decide)))
  have h2 : (PMF.uniformOfFintype (Fin 4 → F)).toOuterMeasure {χ | χ 2 ∈ S₃ (χ 0) (χ 1)}
      ≤ (b₃ : ℝ≥0∞) / Fintype.card F :=
    escape_coord 2 (fun χ => S₃ (χ 0) (χ 1)) (fun _ => h₃ _ _)
      (fun χ χ' h => by
        show S₃ (χ 0) (χ 1) = S₃ (χ' 0) (χ' 1)
        rw [h 0 (by decide), h 1 (by decide)])
  have h3 : (PMF.uniformOfFintype (Fin 4 → F)).toOuterMeasure
        {χ | χ 3 ∈ S₄ (χ 0) (χ 1) (χ 2)} ≤ (b₄ : ℝ≥0∞) / Fintype.card F :=
    escape_coord 3 (fun χ => S₄ (χ 0) (χ 1) (χ 2)) (fun _ => h₄ _ _ _)
      (fun χ χ' h => by
        show S₄ (χ 0) (χ 1) (χ 2) = S₄ (χ' 0) (χ' 1) (χ' 2)
        rw [h 0 (by decide), h 1 (by decide), h 2 (by decide)])
  have hu2 : (PMF.uniformOfFintype (Fin 4 → F)).toOuterMeasure
        {χ | χ 1 ∈ S₂ (χ 0) ∨ χ 2 ∈ S₃ (χ 0) (χ 1) ∨ χ 3 ∈ S₄ (χ 0) (χ 1) (χ 2)}
      ≤ (PMF.uniformOfFintype (Fin 4 → F)).toOuterMeasure {χ | χ 1 ∈ S₂ (χ 0)}
        + (PMF.uniformOfFintype (Fin 4 → F)).toOuterMeasure
            {χ | χ 2 ∈ S₃ (χ 0) (χ 1) ∨ χ 3 ∈ S₄ (χ 0) (χ 1) (χ 2)} := by
    rw [Set.setOf_or]; exact measure_union_le _ _
  have hu3 : (PMF.uniformOfFintype (Fin 4 → F)).toOuterMeasure
        {χ | χ 2 ∈ S₃ (χ 0) (χ 1) ∨ χ 3 ∈ S₄ (χ 0) (χ 1) (χ 2)}
      ≤ (PMF.uniformOfFintype (Fin 4 → F)).toOuterMeasure {χ | χ 2 ∈ S₃ (χ 0) (χ 1)}
        + (PMF.uniformOfFintype (Fin 4 → F)).toOuterMeasure
            {χ | χ 3 ∈ S₄ (χ 0) (χ 1) (χ 2)} := by
    rw [Set.setOf_or]; exact measure_union_le _ _
  calc (PMF.uniformOfFintype (Fin 4 → F)).toOuterMeasure
        {χ | χ 0 ∈ S₁ ∨ χ 1 ∈ S₂ (χ 0) ∨ χ 2 ∈ S₃ (χ 0) (χ 1) ∨ χ 3 ∈ S₄ (χ 0) (χ 1) (χ 2)}
      ≤ (PMF.uniformOfFintype (Fin 4 → F)).toOuterMeasure {χ | χ 0 ∈ S₁}
        + (PMF.uniformOfFintype (Fin 4 → F)).toOuterMeasure
            {χ | χ 1 ∈ S₂ (χ 0) ∨ χ 2 ∈ S₃ (χ 0) (χ 1) ∨ χ 3 ∈ S₄ (χ 0) (χ 1) (χ 2)} := by
        rw [Set.setOf_or]; exact measure_union_le _ _
    _ ≤ (b₁ : ℝ≥0∞) / Fintype.card F + ((b₂ : ℝ≥0∞) / Fintype.card F
          + ((b₃ : ℝ≥0∞) / Fintype.card F + (b₄ : ℝ≥0∞) / Fintype.card F)) :=
        add_le_add h0 (le_trans hu2 (add_le_add h1 (le_trans hu3 (add_le_add h2 h3))))
    _ = (b₁ + b₂ + b₃ + b₄ : ℝ≥0∞) / Fintype.card F := by
        rw [ENNReal.div_add_div_same, ENNReal.div_add_div_same, ENNReal.div_add_div_same]
        congr 1
        ring

end Kimchi.Verifier.Forking
