import Kimchi.Columns
import Kimchi.Domain
import Kimchi.GrandProduct
import Kimchi.Shifted

/-!
# The permutation argument: constraints and quotient soundness

The kimchi permutation constraints as polynomial data (proof-systems `permutation.rs`), and
their soundness: if `zH` divides all three, then on the unmasked rows the accumulator meets
the hypotheses of `prod_eq_of_accumulator`, so the shift-side and σ-side grand products agree.

The constraints:

* `zkpm · (z · ∏ᵢ (wᵢ + γ + β·shiftᵢ·X) - z(ωX) · ∏ᵢ (wᵢ + γ + β·σᵢ))` — the accumulator
  recurrence, gated off the three roots of `zkpm`: the two rows whose successor accumulator
  value the prover randomizes, and the wrap-around row `n−1`. `zkpm` has three factors at
  any `zkRows`, so the recurrence still holds on rows `n−zkRows+2 … n−2`;
* `(z - 1) · lagNumer 0` — the accumulator starts at `1`;
* `(z - 1) · lagNumer (n-zkRows)` — it returns to `1` at the end of the unmasked region.

The permutation is not an `Argument` instance: the aggregation reads the accumulator at two
rows and is gated by a row set rather than a selector column. Its soundness composes
`zH_dvd_iff` directly with two row lemmas: the mask's nonvanishing off its roots, and the
Lagrange pins. `copy_soundness_of_dvd` turns the product equality into the copy constraints.
-/

namespace Kimchi.Permutation

open Kimchi.GrandProduct

open Polynomial

variable {F : Type*} [Field F]

/-! ## The constraint data -/

/-- The permutation mask: three factors at any `zkRows`, not the whole last-`zkRows` window
(the two coincide at `zkRows = 3`). It gates the accumulator recurrence off exactly the three
rows the prover breaks it on. -/
noncomputable def zkpm (ω : F) (n zkRows : ℕ) : Polynomial F :=
  (X - C (ω ^ (n - zkRows))) * (X - C (ω ^ (n - zkRows + 1))) * (X - C (ω ^ (n - 1)))

/-- The shift-side row product `∏ᵢ (wᵢ + γ + β·shiftᵢ·X)` — the identity-permutation side
of the accumulator recurrence. -/
noncomputable def shiftSide (w : Fin permCols → Polynomial F)
    (shifts : Fin permCols → F) (β γ : F) :
    Polynomial F :=
  ∏ i, (w i + C γ + C β * C (shifts i) * X)

/-- The σ-side row product `∏ᵢ (wᵢ + γ + β·σᵢ)`. -/
noncomputable def sigmaSide (w σ : Fin permCols → Polynomial F) (β γ : F) : Polynomial F :=
  ∏ i, (w i + C γ + C β * σ i)

/-- The indicator of row `r`, whose `columnPoly` is the Lagrange basis at row `r`. -/
def rowIndicator {n : ℕ} (r : Fin n) : Fin n → F :=
  fun j => if j = r then 1 else 0

/-- Interpolation is linear in the column: `columnPoly v = ∑ⱼ vⱼ • Lⱼ` with
`Lⱼ = columnPoly (rowIndicator j)` the Lagrange basis. Degree-`< n` agreement on the
domain: at node `i` the left side reads `vᵢ` and the right collapses to the `j = i`
term. -/
theorem columnPoly_eq_sum_indicator {F : Type*} [Field F] {n : ℕ} {ω : F}
    (hω : IsPrimitiveRoot ω n) (hn : 0 < n) (v : Fin n → F) :
    columnPoly ω v
      = ∑ j : Fin n, v j • columnPoly ω (rowIndicator j) := by
  have hd2 : (∑ j : Fin n, v j • columnPoly ω (rowIndicator j)).degree
      < n := by
    apply lt_of_le_of_lt (degree_sum_le _ _)
    rw [Finset.sup_lt_iff (by exact_mod_cast WithBot.bot_lt_coe (n : ℕ))]
    exact fun j _ => lt_of_le_of_lt (degree_smul_le _ _) (degree_columnPoly_lt hω _)
  refine eq_of_eval_eq_on_domain hω hn (degree_columnPoly_lt hω _) hd2 ?_
  intro i hi
  rw [show ((ω : F) ^ i) = ω ^ ((⟨i, hi⟩ : Fin n) : ℕ) from rfl, eval_columnPoly hω,
    eval_finsetSum]
  rw [Finset.sum_eq_single (⟨i, hi⟩ : Fin n)]
  · rw [eval_smul, eval_columnPoly hω, rowIndicator, if_pos rfl,
      smul_eq_mul, mul_one]
  · intro j _ hj
    rw [eval_smul, eval_columnPoly hω, rowIndicator,
      if_neg (fun hEq => hj hEq.symm), smul_eq_mul, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- The un-normalized Lagrange numerator `(Xⁿ − 1)/(X − ω^r)`, as the scaled basis
`n·ω^{−r}·L_r`: the boundary-pin factor at the scale `boundaryEval` reads it. -/
noncomputable def lagNumer (ω : F) {n : ℕ} (r : Fin n) : Polynomial F :=
  C ((n : F) * (ω ^ (r : ℕ))⁻¹) * columnPoly ω (rowIndicator r)

/-- The three permutation constraints: the gated aggregation and the boundary pins at rows
`r₀` (initialisation) and `r₁` (final value). -/
noncomputable def constraints {n : ℕ} (ω : F) (zkRows : ℕ) (z : Polynomial F)
    (w σ : Fin permCols → Polynomial F) (shifts : Fin permCols → F) (β γ : F) (r₀ r₁ : Fin n) :
    Fin 3 → Polynomial F :=
  ![zkpm ω n zkRows * (z * shiftSide w shifts β γ - Kimchi.shift ω z * sigmaSide w σ β γ),
    (z - 1) * lagNumer ω r₀,
    (z - 1) * lagNumer ω r₁]

/-! ## Row lemmas -/

/-- The mask does not vanish on the unmasked rows: `zkpm(ωⁱ) ≠ 0` for `i < n - zkRows`.
Needs `2 ≤ zkRows` so that all three root exponents lie in `[n − zkRows, n)`; at
`zkRows = 1` the middle root is row `0`. -/
private theorem zkpm_eval_ne_zero {ω : F} {n : ℕ} (hω : IsPrimitiveRoot ω n)
    {zkRows : ℕ} (hzk2 : 2 ≤ zkRows) (hzkn : zkRows ≤ n) {i : ℕ}
    (hi : i < n - zkRows) : (zkpm ω n zkRows).eval (ω ^ i) ≠ 0 := by
  unfold zkpm
  simp only [eval_mul, eval_sub, eval_X, eval_C]
  have hne : ∀ e : ℕ, n - zkRows ≤ e → e < n → (ω : F) ^ i - ω ^ e ≠ 0 := by
    intro e hlo hhi
    rw [sub_ne_zero]
    intro hEq
    have : i = e := hω.pow_inj (by omega) hhi hEq
    omega
  exact mul_ne_zero
    (mul_ne_zero (hne _ le_rfl (by omega)) (hne _ (by omega) (by omega)))
    (hne _ (by omega) (by omega))

/-- The mask vanishes on its three gated rows — the completeness twin of
`zkpm_eval_ne_zero`. -/
private theorem zkpm_eval_zero {ω : F} {n : ℕ} (zkRows : ℕ) {i : ℕ}
    (hi : i = n - zkRows ∨ i = n - zkRows + 1 ∨ i = n - 1) :
    (zkpm ω n zkRows).eval (ω ^ i) = 0 := by
  unfold zkpm
  simp only [eval_mul, eval_sub, eval_X, eval_C]
  rcases hi with h | h | h <;> subst h <;> simp

/-- A Lagrange-gated pin: if `zH F n ∣ (z - 1) · lagNumer r` then the accumulator is `1`
at row `r` — the numerator's value at its own node is `n·ω^{−r} ≠ 0` (a primitive root
forces `(n : F) ≠ 0`), so the pin factor must vanish. -/
private theorem eval_eq_one_of_boundary {ω : F} {n : ℕ} (hω : IsPrimitiveRoot ω n) (hn : 0 < n)
    (z : Polynomial F) (r : Fin n)
    (h : zH F n ∣ (z - 1) * lagNumer ω r) :
    z.eval (ω ^ (r : ℕ)) = 1 := by
  haveI : NeZero n := ⟨hn.ne'⟩
  have hnF : ((n : ℕ) : F) ≠ 0 := hω.neZero'.out
  have hωr : (ω ^ (r : ℕ)) ≠ 0 := pow_ne_zero _ (hω.ne_zero hn.ne')
  have hrow := (zH_dvd_iff hω hn _).mp h r r.isLt
  rw [lagNumer, eval_mul, eval_mul, eval_C, eval_columnPoly hω _ r, rowIndicator,
    if_pos rfl, mul_one, eval_sub, eval_one] at hrow
  rcases mul_eq_zero.mp hrow with hz | hc
  · exact sub_eq_zero.mp hz
  · exact absurd hc (mul_ne_zero hnF (inv_ne_zero hωr))

/-- The gated aggregation forces the division-free recurrence on the unmasked rows:
`z(ωⁱ⁺¹) · sigmaSide(ωⁱ) = z(ωⁱ) · shiftSide(ωⁱ)` for `i < n - zkRows`. -/
private theorem step_of_aggregation {ω : F} {n : ℕ} (hω : IsPrimitiveRoot ω n) (hn : 0 < n)
    {zkRows : ℕ} (hzk2 : 2 ≤ zkRows) (hzkn : zkRows ≤ n)
    (z : Polynomial F) (w σ : Fin permCols → Polynomial F) (shifts : Fin permCols → F) (β γ : F)
    (h : zH F n ∣ zkpm ω n zkRows
      * (z * shiftSide w shifts β γ - Kimchi.shift ω z * sigmaSide w σ β γ))
    {i : ℕ} (hi : i < n - zkRows) :
    z.eval (ω ^ (i + 1)) * (sigmaSide w σ β γ).eval (ω ^ i)
      = z.eval (ω ^ i) * (shiftSide w shifts β γ).eval (ω ^ i) := by
  have hrow := (zH_dvd_iff hω hn _).mp h i (by omega)
  rw [eval_mul] at hrow
  have h2 := (mul_eq_zero.mp hrow).resolve_left (zkpm_eval_ne_zero hω hzk2 hzkn hi)
  rw [eval_sub, eval_mul, eval_mul, sub_eq_zero] at h2
  have hcomp : (Kimchi.shift ω z).eval (ω ^ i) = z.eval (ω ^ (i + 1)) := by
    rw [Kimchi.shift, eval_comp, eval_mul, eval_C, eval_X, ← pow_succ']
  rw [hcomp] at h2
  exact h2.symm

/-! ## The headline -/

/-- **Permutation quotient soundness.** If `zH` divides each of the three permutation
constraints, the accumulator telescopes over the unmasked rows: the shift-side and σ-side
grand products agree there. -/
theorem soundness_of_dvd {ω : F} {n : ℕ} (hω : IsPrimitiveRoot ω n) (hn : 0 < n)
    {zkRows : ℕ} (hzk2 : 2 ≤ zkRows) (hzkn : zkRows ≤ n)
    (z : Polynomial F) (w σ : Fin permCols → Polynomial F) (shifts : Fin permCols → F) (β γ : F)
    (hdvd : ∀ s, zH F n ∣ constraints ω zkRows z w σ shifts β γ
      (⟨0, hn⟩ : Fin n) ⟨n - zkRows, by omega⟩ s) :
    ∏ j ∈ Finset.range (n - zkRows), (shiftSide w shifts β γ).eval (ω ^ j)
      = ∏ j ∈ Finset.range (n - zkRows), (sigmaSide w σ β γ).eval (ω ^ j) := by
  refine prod_eq_of_accumulator _ _ (fun j => z.eval (ω ^ j)) ?_ ?_ ?_
  · simpa using eval_eq_one_of_boundary hω hn z _ (hdvd 1)
  · simpa using eval_eq_one_of_boundary hω hn z _ (hdvd 2)
  · exact fun j hj => step_of_aggregation hω hn hzk2 hzkn z w σ shifts β γ (hdvd 0) hj
/-- **Permutation completeness.** If the σ-side row products are nonzero on every row and
the grand products agree over the unmasked rows, some accumulator makes all three
constraints divisible by `zH`: the converse of `soundness_of_dvd`, pointwise in `(β, γ)`.
The accumulator is `accumulator_of_prod_eq`'s running ratio up to row `n − zkRows`, `1` on
the next two rows, then the ratio restarted; the recurrence is live inside the mask, hence
nonvanishing on every row. -/
theorem constraints_dvd_of_prods {ω : F} {n : ℕ} (hω : IsPrimitiveRoot ω n) (hn : 0 < n)
    {zkRows : ℕ} (hzk2 : 2 ≤ zkRows) (hzkn : zkRows ≤ n)
    (w σ : Fin permCols → Polynomial F) (shifts : Fin permCols → F) (β γ : F)
    (hden : ∀ j < n, (sigmaSide w σ β γ).eval (ω ^ j) ≠ 0)
    (hprod : ∏ j ∈ Finset.range (n - zkRows), (shiftSide w shifts β γ).eval (ω ^ j)
      = ∏ j ∈ Finset.range (n - zkRows), (sigmaSide w σ β γ).eval (ω ^ j)) :
    ∃ z : Polynomial F, ∀ s, zH F n ∣ constraints ω zkRows z w σ shifts β γ
      (⟨0, hn⟩ : Fin n) ⟨n - zkRows, by omega⟩ s := by
  set num : ℕ → F := fun j => (shiftSide w shifts β γ).eval (ω ^ j) with hnumDef
  set den : ℕ → F := fun j => (sigmaSide w σ β γ).eval (ω ^ j) with hdenDef
  obtain ⟨zc, hz0, hzm, hstep⟩ := accumulator_of_prod_eq num den
    (fun k hk => hden k (by omega)) hprod
  -- the tail accumulator: restarted at `1` on row `n − zkRows + 2`, running ratio on
  set tail : ℕ → F := fun k => Nat.rec (motive := fun _ => F) 1
    (fun k acc => acc * num (n - zkRows + 2 + k) / den (n - zkRows + 2 + k)) k
    with htailDef
  have htailStep : ∀ k, n - zkRows + 2 + k < n →
      tail (k + 1) * den (n - zkRows + 2 + k) = tail k * num (n - zkRows + 2 + k) := by
    intro k hk
    show tail k * num (n - zkRows + 2 + k) / den (n - zkRows + 2 + k)
        * den (n - zkRows + 2 + k) = _
    rw [div_mul_cancel₀]
    exact hden _ hk
  -- the accumulator column: head ratio to the boundary, `1` on the two randomized
  -- rows, tail ratio beyond (indexed by ℕ so the branch arithmetic stays coercion-free)
  set zrow : ℕ → F := fun i =>
    if i ≤ n - zkRows then zc i
    else if i = n - zkRows + 1 then 1
    else tail (i - (n - zkRows + 2)) with hzrow
  refine ⟨columnPoly ω (fun i : Fin n => zrow (i : ℕ)), ?_⟩
  have hzeval : ∀ i : ℕ, i < n →
      (columnPoly ω (fun i : Fin n => zrow (i : ℕ))).eval (ω ^ i) = zrow i := fun i hi => by
    rw [show (ω ^ i : F) = ω ^ (((⟨i, hi⟩ : Fin n)) : ℕ) from rfl,
      eval_columnPoly hω]
  intro s
  rw [zH_dvd_iff hω hn]
  intro i hi
  match s with
  | 0 =>
    show ((zkpm ω n zkRows) * _).eval _ = 0
    rw [eval_mul]
    by_cases hmask : i = n - zkRows ∨ i = n - zkRows + 1 ∨ i = n - 1
    · -- one of the three gated rows
      rw [zkpm_eval_zero zkRows hmask, zero_mul]
    · -- a live recurrence row: head or restarted tail
      simp only [not_or] at hmask
      obtain ⟨hm0, hm1, hm2⟩ := hmask
      have hi1 : i + 1 < n := by omega
      have hcomp : (Kimchi.shift ω (columnPoly ω (fun i : Fin n => zrow (i : ℕ)))).eval (ω ^ i)
          = (columnPoly ω (fun i : Fin n => zrow (i : ℕ))).eval (ω ^ (i + 1)) := by
        rw [Kimchi.shift, eval_comp, eval_mul, eval_C, eval_X, ← pow_succ']
      rw [eval_sub, eval_mul, eval_mul, hcomp, hzeval i hi, hzeval (i + 1) hi1]
      refine mul_eq_zero_of_right _ (sub_eq_zero.mpr ?_)
      rcases Nat.lt_or_ge i (n - zkRows) with hlt | hge
      · -- head: the accumulator step
        have e1 : zrow i = zc i := by
          simp only [hzrow]
          rw [if_pos (by omega : i ≤ n - zkRows)]
        have e2 : zrow (i + 1) = zc (i + 1) := by
          simp only [hzrow]
          rw [if_pos (by omega : i + 1 ≤ n - zkRows)]
        rw [e1, e2]
        exact (hstep i hlt).symm
      · -- tail: the restarted ratio (`n − zkRows + 2 ≤ i ≤ n − 2`)
        have hge2 : n - zkRows + 2 ≤ i := by omega
        have e1 : zrow i = tail (i - (n - zkRows + 2)) := by
          simp only [hzrow]
          rw [if_neg (by omega), if_neg (by omega)]
        have e2 : zrow (i + 1) = tail (i - (n - zkRows + 2) + 1) := by
          simp only [hzrow]
          rw [if_neg (by omega), if_neg (by omega),
            show i + 1 - (n - zkRows + 2) = i - (n - zkRows + 2) + 1 from by omega]
        have := htailStep (i - (n - zkRows + 2)) (by omega)
        rw [show n - zkRows + 2 + (i - (n - zkRows + 2)) = i from by omega] at this
        rw [e1, e2]
        exact this.symm
  | 1 =>
    show ((_ - 1) * lagNumer ω (⟨0, hn⟩ : Fin n)).eval _ = 0
    rw [lagNumer, eval_mul]
    by_cases h0 : i = 0
    · subst h0
      rw [eval_sub, eval_one, hzeval 0 hn]
      have : zrow 0 = 1 := by
        simp only [hzrow]
        rw [if_pos (Nat.zero_le _)]
        exact hz0
      rw [this]
      simp
    · rw [eval_mul, show (ω ^ i : F) = ω ^ (((⟨i, hi⟩ : Fin n)) : ℕ) from rfl,
        eval_columnPoly hω, rowIndicator, if_neg (by simp [Fin.ext_iff, h0]), mul_zero,
        mul_zero]
  | 2 =>
    show ((_ - 1) * lagNumer ω (⟨n - zkRows, by omega⟩ : Fin n)).eval _
      = 0
    rw [lagNumer, eval_mul]
    by_cases hb : i = n - zkRows
    · subst hb
      rw [eval_sub, eval_one, hzeval (n - zkRows) (by omega)]
      have : zrow (n - zkRows) = 1 := by
        simp only [hzrow]
        rw [if_pos le_rfl]
        exact hzm
      rw [this]
      simp
    · rw [eval_mul, show (ω ^ i : F) = ω ^ (((⟨i, hi⟩ : Fin n)) : ℕ) from rfl,
        eval_columnPoly hω, rowIndicator, if_neg (by simp [Fin.ext_iff, hb]), mul_zero,
        mul_zero]

end Kimchi.Permutation
