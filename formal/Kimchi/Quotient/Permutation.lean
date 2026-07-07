import Kimchi.Quotient.Accumulator
import Kimchi.Quotient.Pinning
import Kimchi.Quotient.Aggregate

/-!
# The permutation argument: constraints and quotient soundness

The kimchi permutation constraints as single-source polynomial data (proof-systems
`permutation.rs`), and their soundness under the quotient argument: the three constraints
— the `zkpm`-gated accumulator aggregation and the two Lagrange-gated boundary pins —
force, on the unmasked rows, exactly the hypotheses of the accumulator telescoping
(`prod_eq_of_accumulator`), hence the grand-product equality
`∏ⱼ shiftSide(ωʲ) = ∏ⱼ sigmaSide(ωʲ)` over the constrained region.

The constraints, with `zkpm(X) = ∏_{j=n-zkRows}^{n-1} (X - ωʲ)` masking the final `zkRows`
zero-knowledge rows and `L_r` the Lagrange basis at row `r` (`columnPoly` at an
indicator):

* `zkpm · (z · ∏ᵢ (wᵢ + γ + β·shiftᵢ·X) - z(ωX) · ∏ᵢ (wᵢ + γ + β·σᵢ))` — the division-free
  accumulator recurrence, gated off the masked rows;
* `(z - 1) · L₀` — the accumulator initialises to `1`;
* `(z - 1) · L_{n-zkRows}` — the accumulator returns to `1` at the end of the unmasked region.

The permutation is not an `Argument` instance: the aggregation reads the accumulator at
two rows (`z(X)` and `z(ωX)`) and is gated by the complement of a row set rather than a
selector column. Its soundness therefore composes the shared quotient machinery directly
(`zH_dvd_of_evals`, `dvd_separation`, `zH_dvd_iff`) with two bespoke row lemmas: the
gate's nonvanishing off the masked rows, and the Lagrange pins.

The conclusion feeds milestone 4: at the challenges `(β, γ)` the two sides are the pair
factors of `Kimchi.Quotient.GrandProduct`, so the product equality at an injective grid
forces the multiset equality behind the copy constraints.
-/

namespace Kimchi.Quotient.Permutation

open Polynomial Kimchi.Quotient

variable {F : Type*} [Field F]

/-! ## The constraint data -/

/-- The zero-knowledge mask `∏_{j=n-zkRows}^{n-1} (X - ωʲ)` (`vanishes_on_last_n_rows`):
vanishes exactly on the final `zkRows` rows of the domain, gating the accumulator recurrence
off them. -/
noncomputable def zkpm (ω : F) (n zkRows : ℕ) : Polynomial F :=
  ∏ j ∈ Finset.Ico (n - zkRows) n, (X - C (ω ^ j))

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

/-- The three permutation constraint polynomials (`permutation.rs`), with the boundary
rows `r₀` (initialisation) and `r₁` (final value) explicit. -/
noncomputable def constraints {n : ℕ} (ω : F) (zkRows : ℕ) (z : Polynomial F)
    (w σ : Fin 7 → Polynomial F) (shifts : Fin 7 → F) (β γ : F) (r₀ r₁ : Fin n) :
    Fin 3 → Polynomial F :=
  ![zkpm ω n zkRows * (z * shiftSide w shifts β γ - shiftRow ω z * sigmaSide w σ β γ),
    (z - 1) * columnPoly ω (rowIndicator r₀),
    (z - 1) * columnPoly ω (rowIndicator r₁)]

/-! ## Row lemmas -/

/-- The mask does not vanish on the unmasked rows: `zkpm(ωⁱ) ≠ 0` for `i < n - zkRows`. -/
theorem zkpm_eval_ne_zero {ω : F} {n : ℕ} (hω : IsPrimitiveRoot ω n) (zkRows : ℕ) {i : ℕ}
    (hi : i < n - zkRows) : (zkpm ω n zkRows).eval (ω ^ i) ≠ 0 := by
  unfold zkpm
  rw [eval_prod]
  refine Finset.prod_ne_zero_iff.mpr fun j hj => ?_
  obtain ⟨hj₁, hj₂⟩ := Finset.mem_Ico.mp hj
  simp only [eval_sub, eval_X, eval_C, sub_ne_zero]
  intro hEq
  have : i = j := hω.pow_inj (by omega) hj₂ hEq
  omega

/-- A Lagrange-gated pin: if `Z_H ∣ (z - 1) · L_r` then the accumulator is `1` at row
`r`. -/
theorem eval_eq_one_of_boundary {ω : F} {n : ℕ} (hω : IsPrimitiveRoot ω n) (hn : 0 < n)
    (z : Polynomial F) (r : Fin n)
    (h : zH F n ∣ (z - 1) * columnPoly ω (rowIndicator r)) :
    z.eval (ω ^ (r : ℕ)) = 1 := by
  have hrow := (zH_dvd_iff hω hn _).mp h r r.isLt
  rw [eval_mul, eval_columnPoly hω _ r, rowIndicator, if_pos rfl, mul_one, eval_sub,
    eval_one, sub_eq_zero] at hrow
  exact hrow

/-- The gated aggregation forces the division-free recurrence on the unmasked rows:
`z(ωⁱ⁺¹) · sigmaSide(ωⁱ) = z(ωⁱ) · shiftSide(ωⁱ)` for `i < n - zkRows`. -/
theorem step_of_aggregation {ω : F} {n : ℕ} (hω : IsPrimitiveRoot ω n) (hn : 0 < n)
    (zkRows : ℕ) (z : Polynomial F) (w σ : Fin 7 → Polynomial F) (shifts : Fin 7 → F) (β γ : F)
    (h : zH F n ∣ zkpm ω n zkRows
      * (z * shiftSide w shifts β γ - shiftRow ω z * sigmaSide w σ β γ))
    {i : ℕ} (hi : i < n - zkRows) :
    z.eval (ω ^ (i + 1)) * (sigmaSide w σ β γ).eval (ω ^ i)
      = z.eval (ω ^ i) * (shiftSide w shifts β γ).eval (ω ^ i) := by
  have hrow := (zH_dvd_iff hω hn _).mp h i (by omega)
  rw [eval_mul] at hrow
  have h2 := (mul_eq_zero.mp hrow).resolve_left (zkpm_eval_ne_zero hω zkRows hi)
  rw [eval_sub, eval_mul, eval_mul, sub_eq_zero] at h2
  have hcomp : (shiftRow ω z).eval (ω ^ i) = z.eval (ω ^ (i + 1)) := by
    rw [shiftRow, eval_comp, eval_mul, eval_C, eval_X, ← pow_succ']
  rw [hcomp] at h2
  exact h2.symm

/-! ## The headline -/

/-- **Permutation quotient soundness.** Under the derandomized quotient-argument
hypotheses for the three permutation constraints — an injective challenge family `α`
separating the aggregate, an injective evaluation family `ζ` pinning each aggregate to a
multiple of `Z_H` within the degree bound — the accumulator telescopes over the unmasked
region: the grand products of the shift side and the σ side agree,
`∏_{j < n-zkRows} shiftSide(ωʲ) = ∏_{j < n-zkRows} sigmaSide(ωʲ)`. -/
theorem soundness {ω : F} {n N : ℕ} (hω : IsPrimitiveRoot ω n) (hn : 0 < n)
    {zkRows : ℕ} (hzk0 : 0 < zkRows) (hzkn : zkRows ≤ n)
    (z : Polynomial F) (w σ : Fin 7 → Polynomial F) (shifts : Fin 7 → F) (β γ : F)
    (α : Fin 3 → F) (hα : Function.Injective α)
    (ζ : Fin N → F) (hζ : Function.Injective ζ)
    (t : Fin 3 → Polynomial F) (D : ℕ) (hD : D < N)
    (hCdeg : ∀ s, (aggregate (α s) (constraints ω zkRows z w σ shifts β γ
      (⟨0, hn⟩ : Fin n) ⟨n - zkRows, by omega⟩)).natDegree ≤ D)
    (htdeg : ∀ s, (t s * zH F n).natDegree ≤ D)
    (hcheck : ∀ s p, (aggregate (α s) (constraints ω zkRows z w σ shifts β γ
        (⟨0, hn⟩ : Fin n) ⟨n - zkRows, by omega⟩)).eval (ζ p)
      = (t s * zH F n).eval (ζ p)) :
    ∏ j ∈ Finset.range (n - zkRows), (shiftSide w shifts β γ).eval (ω ^ j)
      = ∏ j ∈ Finset.range (n - zkRows), (sigmaSide w σ β γ).eval (ω ^ j) := by
  set E := constraints ω zkRows z w σ shifts β γ (⟨0, hn⟩ : Fin n) ⟨n - zkRows, by omega⟩ with hE
  have hdvd : ∀ c, zH F n ∣ E c :=
    dvd_separation hω hn α hα E fun s =>
      zH_dvd_of_evals hω hn ζ hζ _ (t s) D (hCdeg s) (htdeg s) hD (hcheck s)
  refine prod_eq_of_accumulator _ _ (fun j => z.eval (ω ^ j)) ?_ ?_ ?_
  · simpa using eval_eq_one_of_boundary hω hn z _ (hdvd 1)
  · simpa using eval_eq_one_of_boundary hω hn z _ (hdvd 2)
  · exact fun j hj => step_of_aggregation hω hn zkRows z w σ shifts β γ (hdvd 0) hj

end Kimchi.Quotient.Permutation
