import Kimchi.Aggregate
import Kimchi.SchwartzZippel
import Kimchi.GrandProduct

/-!
# The permutation argument: constraints and quotient soundness

The kimchi permutation constraints as single-source polynomial data (proof-systems
`permutation.rs`), and their soundness under the quotient argument: the three constraints
— the `zkpm`-gated accumulator aggregation and the two Lagrange-gated boundary pins —
force, on the unmasked rows, exactly the hypotheses of the accumulator telescoping
(`prod_eq_of_accumulator`), hence the grand-product equality
`∏ⱼ shiftSide(ωʲ) = ∏ⱼ sigmaSide(ωʲ)` over the constrained region.

The constraints, with `zkpm(X) = (X − ω^{n−zkRows})(X − ω^{n−zkRows+1})(X − ω^{n−1})`
(production's `permutation_vanishing_polynomial` — THREE factors at any `zkRows`, NOT
the full `vanishes_on_last_n_rows` window; the two coincide exactly at `zkRows = 3`)
and `L_r` the Lagrange basis at row `r` (`columnPoly` at an indicator):

* `zkpm · (z · ∏ᵢ (wᵢ + γ + β·shiftᵢ·X) - z(ωX) · ∏ᵢ (wᵢ + γ + β·σᵢ))` — the division-free
  accumulator recurrence, gated off exactly the three rows where the prover breaks it:
  the two whose successor accumulator value is randomized (`perm_aggreg` randomizes
  `z[n−zkRows+1]` and `z[n−zkRows+2]`) and the wrap-around row `n−1`; on the remaining
  masked rows `n−zkRows+2 … n−2` the recurrence HOLDS (the prover's fold continues
  through them);
* `(z - 1) · lagNumer 0` — the accumulator initialises to `1` (the pin carried by the
  un-normalized numerator `(Xⁿ−1)/(X−1)`, the deployed verifier's form);
* `(z - 1) · lagNumer (n-zkRows)` — the accumulator returns to `1` at the end of the
  unmasked region.

The permutation is not an `Argument` instance: the aggregation reads the accumulator at
two rows (`z(X)` and `z(ωX)`) and is gated by the complement of a row set rather than a
selector column. Its soundness therefore composes the shared quotient machinery directly
(`zH_dvd_of_eval`, `dvd_separation`, `zH_dvd_iff`) with two bespoke row lemmas: the
gate's nonvanishing off the masked rows, and the Lagrange pins.

The conclusion feeds milestone 4: at the challenges `(β, γ)` the two sides are the pair
factors of `Kimchi.GrandProduct`, so the product equality at an injective grid
forces the multiset equality behind the copy constraints.
-/

namespace Kimchi.Permutation

open Kimchi.GrandProduct

open Polynomial

variable {F : Type*} [Field F]

/-! ## The constraint data -/

/-- The permutation zero-knowledge mask
`(X − ω^{n−zkRows})(X − ω^{n−zkRows+1})(X − ω^{n−1})` — production's
`permutation_vanishing_polynomial` (permutation.rs:112–121), a THREE-factor product at
any `zkRows` (at `zkRows = 3` it coincides with the full `vanishes_on_last_n_rows`
window, which is what made the windowed transcription pass every `zkRows = 3` fixture).
It gates the accumulator recurrence off exactly the three rows the prover breaks it
on. -/
noncomputable def zkpm (ω : F) (n zkRows : ℕ) : Polynomial F :=
  (X - C (ω ^ (n - zkRows))) * (X - C (ω ^ (n - zkRows + 1))) * (X - C (ω ^ (n - 1)))

/-- The shift-side row product `∏ᵢ (wᵢ + γ + β·shiftᵢ·X)` — the identity-permutation side
of the accumulator recurrence. -/
noncomputable def shiftSide (w : Fin 7 → Polynomial F) (shifts : Fin 7 → F) (β γ : F) :
    Polynomial F :=
  ∏ i, (w i + C γ + C β * C (shifts i) * X)

/-- The σ-side row product `∏ᵢ (wᵢ + γ + β·σᵢ)`. -/
noncomputable def sigmaSide (w σ : Fin 7 → Polynomial F) (β γ : F) : Polynomial F :=
  ∏ i, (w i + C γ + C β * σ i)

/-- The next-row view `z(ωX)` of the accumulator. -/
noncomputable def shiftRow (ω : F) (z : Polynomial F) : Polynomial F :=
  z.comp (C ω * X)

/-- The indicator of row `r`, whose `columnPoly` is the Lagrange basis `L_r`. -/
def rowIndicator {n : ℕ} (r : Fin n) : Fin n → F :=
  fun j => if j = r then 1 else 0

/-- The un-normalized Lagrange numerator `(Xⁿ − 1)/(X − ω^r)`, as the scaled basis
`n·ω^{−r}·L_r` — the boundary-pin polynomial exactly as the deployed verifier reads it
(`ft_eval0`'s boundary quotient, `verifier.rs`). The scale matters by value, not by
vanishing: the verifier's α-weighted equation uses this form, so the members must too
for the linearization bridge to be an equality. -/
noncomputable def lagNumer (ω : F) {n : ℕ} (r : Fin n) : Polynomial F :=
  C ((n : F) * (ω ^ (r : ℕ))⁻¹) * columnPoly ω (rowIndicator r)

/-- `lagNumer` is the Horner quotient `∑ᵢ ω^{r(n−1−i)} Xⁱ`: degree-`< n` agreement on
the domain — both vanish at every node but `ω^r`, where both take `n·ω^{−r}`. -/
private theorem lagNumer_eq_geom {ω : F} {n : ℕ} (hω : IsPrimitiveRoot ω n) (hn : 0 < n)
    (r : Fin n) :
    lagNumer ω r = ∑ i ∈ Finset.range n, C ((ω ^ (r : ℕ)) ^ (n - 1 - i)) * X ^ i := by
  haveI : NeZero n := ⟨hn.ne'⟩
  have hωr : (ω ^ (r : ℕ)) ≠ 0 := pow_ne_zero _ (hω.ne_zero hn.ne')
  have hpow : (ω ^ (r : ℕ)) ^ n = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, hω.pow_eq_one, one_pow]
  -- the geom sum times (X − ω^r) is Xⁿ − 1
  have hgeom : (∑ i ∈ Finset.range n, C ((ω ^ (r : ℕ)) ^ (n - 1 - i)) * X ^ i)
      * (X - C (ω ^ (r : ℕ))) = zH F n := by
    have h := geom_sum₂_mul (X : Polynomial F) (C (ω ^ (r : ℕ))) n
    simp only [← C_pow] at h
    rw [show (∑ i ∈ Finset.range n, C ((ω ^ (r : ℕ)) ^ (n - 1 - i)) * X ^ i)
        = ∑ i ∈ Finset.range n, X ^ i * C ((ω ^ (r : ℕ)) ^ (n - 1 - i)) from
      Finset.sum_congr rfl fun i _ => mul_comm _ _, h, hpow, map_one]
    rfl
  have hd1 : (lagNumer ω r).degree < n := by
    rw [lagNumer, ← smul_eq_C_mul]
    exact lt_of_le_of_lt (degree_smul_le _ _) (degree_columnPoly_lt hω _)
  have hd2 : (∑ i ∈ Finset.range n,
      C ((ω ^ (r : ℕ)) ^ (n - 1 - i)) * X ^ i).natDegree < n := by
    apply lt_of_le_of_lt (natDegree_sum_le _ _)
    rw [Finset.fold_max_lt]
    exact ⟨hn, fun i hi => lt_of_le_of_lt (natDegree_C_mul_le _ _)
      (by simpa using Finset.mem_range.mp hi)⟩
  refine eq_of_eval_eq_on_domain hω hn hd1
    (lt_of_le_of_lt degree_le_natDegree (by exact_mod_cast hd2)) ?_
  · -- node-by-node agreement
    intro i hi
    have hgeval : ∀ x : F, (∑ j ∈ Finset.range n,
        C ((ω ^ (r : ℕ)) ^ (n - 1 - j)) * X ^ j).eval x
          * (x - ω ^ (r : ℕ)) = x ^ n - 1 := by
      intro x
      have := congrArg (Polynomial.eval x) hgeom
      simpa [zH] using this
    by_cases hir : i = (r : ℕ)
    · -- at the node ω^r both sides take n·ω^{−r}
      subst hir
      rw [lagNumer, eval_mul, eval_C, eval_columnPoly hω _ r, rowIndicator,
        if_pos rfl, mul_one]
      rw [eval_finsetSum]
      simp only [eval_mul, eval_C, eval_pow, eval_X]
      have : ∀ j ∈ Finset.range n,
          ((ω ^ (r : ℕ)) ^ (n - 1 - j)) * (ω ^ (r : ℕ)) ^ j
            = (ω ^ (r : ℕ)) ^ (n - 1) := fun j hj => by
        rw [← pow_add]
        congr 1
        have := Finset.mem_range.mp hj
        omega
      rw [Finset.sum_congr rfl this, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      congr 1
      field_simp
      rw [← pow_succ']
      have : n - 1 + 1 = n := by omega
      rw [this, hpow]
    · -- at every other node both sides vanish
      have hz : (ω : F) ^ i - ω ^ (r : ℕ) ≠ 0 := by
        rw [sub_ne_zero]
        exact fun hEq => hir (hω.pow_inj hi r.isLt hEq)
      have h0 : ((ω : F) ^ i) ^ n - 1 = 0 := by
        rw [← pow_mul, mul_comm, pow_mul, hω.pow_eq_one, one_pow, sub_self]
      have := hgeval ((ω : F) ^ i)
      rw [h0] at this
      have hgz := (mul_eq_zero.mp this).resolve_right hz
      rw [hgz, lagNumer, eval_mul,
        show ((ω : F) ^ i) = ω ^ ((⟨i, hi⟩ : Fin n) : ℕ) from rfl,
        eval_columnPoly hω, rowIndicator,
        if_neg (fun hEq => hir (congrArg Fin.val hEq)), mul_zero]

/-- **The numerator identity**: `lagNumer r · (X − ω^r) = Xⁿ − 1`. The boundary pins'
division-free form — the bridge to `ft_eval0`'s boundary quotient clears its
denominators through this. -/
theorem lagNumer_mul_sub {ω : F} {n : ℕ} (hω : IsPrimitiveRoot ω n) (hn : 0 < n)
    (r : Fin n) :
    lagNumer ω r * (X - C (ω ^ (r : ℕ))) = zH F n := by
  rw [lagNumer_eq_geom hω hn r]
  have h := geom_sum₂_mul (X : Polynomial F) (C (ω ^ (r : ℕ))) n
  simp only [← C_pow] at h
  rw [show (∑ i ∈ Finset.range n, C ((ω ^ (r : ℕ)) ^ (n - 1 - i)) * X ^ i)
      = ∑ i ∈ Finset.range n, X ^ i * C ((ω ^ (r : ℕ)) ^ (n - 1 - i)) from
    Finset.sum_congr rfl fun i _ => mul_comm _ _, h]
  rw [show ((ω : F) ^ (r : ℕ)) ^ n = 1 by
    rw [← pow_mul, mul_comm, pow_mul, hω.pow_eq_one, one_pow], map_one]
  rfl

/-- The three permutation constraint polynomials (`permutation.rs` / `verifier.rs`
`ft_eval0`, deployed orientation and scale), with the boundary rows `r₀`
(initialisation) and `r₁` (final value) explicit. -/
noncomputable def constraints {n : ℕ} (ω : F) (zkRows : ℕ) (z : Polynomial F)
    (w σ : Fin 7 → Polynomial F) (shifts : Fin 7 → F) (β γ : F) (r₀ r₁ : Fin n) :
    Fin 3 → Polynomial F :=
  ![zkpm ω n zkRows * (z * shiftSide w shifts β γ - shiftRow ω z * sigmaSide w σ β γ),
    (z - 1) * lagNumer ω r₀,
    (z - 1) * lagNumer ω r₁]

/-! ## Row lemmas -/

/-- The mask does not vanish on the unmasked rows: `zkpm(ωⁱ) ≠ 0` for `i < n - zkRows`.
Needs `2 ≤ zkRows` so that all three root exponents lie in `[n − zkRows, n)` (at
`zkRows = 1` the middle factor's exponent is `n`, i.e. row `0` — production never runs
below `zkRows = 3`). -/
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

/-- A Lagrange-gated pin: if `Z_H ∣ (z - 1) · lagNumer r` then the accumulator is `1`
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
    (z : Polynomial F) (w σ : Fin 7 → Polynomial F) (shifts : Fin 7 → F) (β γ : F)
    (h : zH F n ∣ zkpm ω n zkRows
      * (z * shiftSide w shifts β γ - shiftRow ω z * sigmaSide w σ β γ))
    {i : ℕ} (hi : i < n - zkRows) :
    z.eval (ω ^ (i + 1)) * (sigmaSide w σ β γ).eval (ω ^ i)
      = z.eval (ω ^ i) * (shiftSide w shifts β γ).eval (ω ^ i) := by
  have hrow := (zH_dvd_iff hω hn _).mp h i (by omega)
  rw [eval_mul] at hrow
  have h2 := (mul_eq_zero.mp hrow).resolve_left (zkpm_eval_ne_zero hω hzk2 hzkn hi)
  rw [eval_sub, eval_mul, eval_mul, sub_eq_zero] at h2
  have hcomp : (shiftRow ω z).eval (ω ^ i) = z.eval (ω ^ (i + 1)) := by
    rw [shiftRow, eval_comp, eval_mul, eval_C, eval_X, ← pow_succ']
  rw [hcomp] at h2
  exact h2.symm

/-! ## The headline -/

/-- **Permutation quotient soundness, divisibility form.** With `Z_H` dividing each of
the three permutation constraints, the accumulator telescopes over the unmasked region:
the grand products of the shift side and the σ side agree,
`∏_{j < n-zkRows} shiftSide(ωʲ) = ∏_{j < n-zkRows} sigmaSide(ωʲ)`. This is the core the
derandomized eval-check form (`soundness`) and the full-aggregate assembly
(`Kimchi/Index/Aggregate.lean`) both enter through. -/
theorem soundness_of_dvd {ω : F} {n : ℕ} (hω : IsPrimitiveRoot ω n) (hn : 0 < n)
    {zkRows : ℕ} (hzk2 : 2 ≤ zkRows) (hzkn : zkRows ≤ n)
    (z : Polynomial F) (w σ : Fin 7 → Polynomial F) (shifts : Fin 7 → F) (β γ : F)
    (hdvd : ∀ s, zH F n ∣ constraints ω zkRows z w σ shifts β γ
      (⟨0, hn⟩ : Fin n) ⟨n - zkRows, by omega⟩ s) :
    ∏ j ∈ Finset.range (n - zkRows), (shiftSide w shifts β γ).eval (ω ^ j)
      = ∏ j ∈ Finset.range (n - zkRows), (sigmaSide w σ β γ).eval (ω ^ j) := by
  refine prod_eq_of_accumulator _ _ (fun j => z.eval (ω ^ j)) ?_ ?_ ?_
  · simpa using eval_eq_one_of_boundary hω hn z _ (hdvd 1)
  · simpa using eval_eq_one_of_boundary hω hn z _ (hdvd 2)
  · exact fun j hj => step_of_aggregation hω hn hzk2 hzkn z w σ shifts β γ (hdvd 0) hj
/-- **Permutation completeness.** With nonvanishing σ-side row products (the
nondegeneracy of `(β, γ)`, on EVERY row — the mask no longer erases the recurrence on
the interior zero-knowledge rows) and agreeing grand products over the unmasked region,
an accumulator exists whose three permutation constraints are all divisible by `Z_H`.
The construction mirrors production's `perm_aggreg`: the running ratio of
`accumulator_of_prod_eq` up to the boundary row `n − zkRows` (where it returns to `1`),
an arbitrary value on the two rows production randomizes (`z[n−zkRows+1]`,
`z[n−zkRows+2]` — here `1`), and the running ratio RESTARTED from there: the recurrence
rows are exactly the complement of `zkpm`'s three roots, so the fold must continue
through the interior of the mask. The converse of `soundness_of_dvd`, pointwise in
`(β, γ)`. -/
theorem constraints_dvd_of_prods {ω : F} {n : ℕ} (hω : IsPrimitiveRoot ω n) (hn : 0 < n)
    {zkRows : ℕ} (hzk2 : 2 ≤ zkRows) (hzkn : zkRows ≤ n)
    (w σ : Fin 7 → Polynomial F) (shifts : Fin 7 → F) (β γ : F)
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
      have hcomp : (shiftRow ω (columnPoly ω (fun i : Fin n => zrow (i : ℕ)))).eval (ω ^ i)
          = (columnPoly ω (fun i : Fin n => zrow (i : ℕ))).eval (ω ^ (i + 1)) := by
        rw [shiftRow, eval_comp, eval_mul, eval_C, eval_X, ← pow_succ']
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
