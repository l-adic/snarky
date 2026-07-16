import Mathlib
import Bulletproof.Basic

/-!
# The linear algebra of one IPA round (soundness)

The elementary algebra behind IPA soundness: bilinearity of the generator
commitment `⟨a, g⟩`, the three-point Vandermonde functional, and the
3-special-soundness of a single round.

A round folds the generators by the challenge `u` (`g ↦ gLo + u • gHi`) and
recombines the commitment as `P + u⁻¹ • L + u • R`. From three sub-openings at
distinct nonzero challenges the round is 3-special-sound: an explicit Vandermonde
combination of the three folded witnesses opens the parent commitment `P`, with no
binding assumption — pure module linear algebra.
-/

namespace Bulletproof

variable {F G : Type*} [Field F] [AddCommGroup G] [Module F G]

/-! ## Bilinearity of the generator commitment

The commitment `⟨a, g⟩ = ∑ i, a i • g i` is bilinear: additive and homogeneous in
both the witness `a` and the generators `g`. -/

/-- Additivity in the witness: `⟨a + a', g⟩ = ⟨a, g⟩ + ⟨a', g⟩`. -/
theorem commitGen_add_left {n : ℕ} (g : Fin n → G) (a a' : Fin n → F) :
    commitGen g (a + a') = commitGen g a + commitGen g a' := by
  simp only [commitGen, Pi.add_apply, add_smul, Finset.sum_add_distrib]

/-- Homogeneity in the witness: `⟨c • a, g⟩ = c • ⟨a, g⟩`. -/
theorem commitGen_smul_left {n : ℕ} (g : Fin n → G) (c : F) (a : Fin n → F) :
    commitGen g (c • a) = c • commitGen g a := by
  simp only [commitGen, Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum]

/-- Additivity in the generators: `⟨a, g + g'⟩ = ⟨a, g⟩ + ⟨a, g'⟩`. -/
theorem commitGen_add_gen {n : ℕ} (g g' : Fin n → G) (a : Fin n → F) :
    commitGen (g + g') a = commitGen g a + commitGen g' a := by
  simp only [commitGen, Pi.add_apply, smul_add, Finset.sum_add_distrib]

/-- Homogeneity in the generators: `⟨a, c • g⟩ = c • ⟨a, g⟩`. -/
theorem commitGen_smul_gen {n : ℕ} (c : F) (g : Fin n → G) (a : Fin n → F) :
    commitGen (c • g) a = c • commitGen g a := by
  simp only [commitGen, Pi.smul_apply, Finset.smul_sum]
  exact Finset.sum_congr rfl fun i _ => smul_comm (a i) c (g i)

/-- Subtractivity in the witness: `⟨a - a', g⟩ = ⟨a, g⟩ - ⟨a', g⟩`. -/
theorem commitGen_sub {n : ℕ} (g : Fin n → G) (a a' : Fin n → F) :
    commitGen g (a - a') = commitGen g a - commitGen g a' := by
  simp only [commitGen, Pi.sub_apply, sub_smul, Finset.sum_sub_distrib]

/-! ## The three-point Vandermonde functional -/

/-- For distinct `u₁, u₂, u₃` there are coefficients `l₁, l₂, l₃` with `Σ lᵢ = 0`,
`Σ lᵢuᵢ = 1`, and `Σ lᵢuᵢ² = 0`: the functional `p ↦ Σ lᵢ · p(uᵢ)` reads off the
linear coefficient of any degree-≤2 polynomial `p`. -/
theorem vandermonde3 (u₁ u₂ u₃ : F) (h12 : u₁ ≠ u₂) (h13 : u₁ ≠ u₃)
    (h23 : u₂ ≠ u₃) :
    ∃ l₁ l₂ l₃ : F, (l₁ + l₂ + l₃ = 0)
      ∧ (l₁ * u₁ + l₂ * u₂ + l₃ * u₃ = 1)
      ∧ (l₁ * u₁ ^ 2 + l₂ * u₂ ^ 2 + l₃ * u₃ ^ 2 = 0) := by
  have d12 : u₁ - u₂ ≠ 0 := sub_ne_zero.mpr h12
  have d13 : u₁ - u₃ ≠ 0 := sub_ne_zero.mpr h13
  have d23 : u₂ - u₃ ≠ 0 := sub_ne_zero.mpr h23
  have d21 : u₂ - u₁ ≠ 0 := sub_ne_zero.mpr h12.symm
  have d31 : u₃ - u₁ ≠ 0 := sub_ne_zero.mpr h13.symm
  have d32 : u₃ - u₂ ≠ 0 := sub_ne_zero.mpr h23.symm
  refine ⟨-(u₂ + u₃) / ((u₁ - u₂) * (u₁ - u₃)), -(u₁ + u₃) / ((u₂ - u₁) * (u₂ - u₃)),
    -(u₁ + u₂) / ((u₃ - u₁) * (u₃ - u₂)), ?_, ?_, ?_⟩ <;> field_simp <;> ring

/-! ## Round soundness (3-special) -/

/-- One IPA round is 3-special-sound for the commitment, with an explicit witness.
Given three openings `⟨cᵢ, gLo + uᵢ • gHi⟩ = P + uᵢ⁻¹ • L + uᵢ • R` against the
`uᵢ`-folded generators at distinct nonzero challenges, and Vandermonde coefficients
`lᵢ`, the parent witness `aLo = Σ lᵢ(uᵢ cᵢ)`, `aHi = Σ lᵢ(uᵢ² cᵢ)` opens `P`:
`⟨aLo, gLo⟩ + ⟨aHi, gHi⟩ = P`. No binding assumption; the witness is explicit, so
the same combination serves the inner-product side at `G := F`. -/
theorem ipa_round_commit_with_coeffs {m : ℕ} (g_lo g_hi : Fin m → G) (P L R : G)
    (c₁ c₂ c₃ : Fin m → F) (u₁ u₂ u₃ l₁ l₂ l₃ : F)
    (hl0 : l₁ + l₂ + l₃ = 0) (hl1 : l₁ * u₁ + l₂ * u₂ + l₃ * u₃ = 1)
    (hl2 : l₁ * u₁ ^ 2 + l₂ * u₂ ^ 2 + l₃ * u₃ ^ 2 = 0)
    (hu₁ : u₁ ≠ 0) (hu₂ : u₂ ≠ 0) (hu₃ : u₃ ≠ 0)
    (e₁ : commitGen (g_lo + u₁ • g_hi) c₁ = P + u₁⁻¹ • L + u₁ • R)
    (e₂ : commitGen (g_lo + u₂ • g_hi) c₂ = P + u₂⁻¹ • L + u₂ • R)
    (e₃ : commitGen (g_lo + u₃ • g_hi) c₃ = P + u₃⁻¹ • L + u₃ • R) :
    commitGen g_lo (l₁ • (u₁ • c₁) + l₂ • (u₂ • c₂) + l₃ • (u₃ • c₃))
        + commitGen g_hi
            (l₁ • (u₁ ^ 2 • c₁) + l₂ • (u₂ ^ 2 • c₂)
              + l₃ • (u₃ ^ 2 • c₃))
      = P := by
  -- Expand the folded generators: the generator half carries `u`, not `u⁻¹`.
  rw [commitGen_add_gen, commitGen_smul_gen] at e₁ e₂ e₃
  -- e_i : commitGen g_lo c_i + u_i • commitGen g_hi c_i = P + u_i⁻¹ • L + u_i • R
  -- Multiply each opening by `u_i` to clear the `u_i⁻¹` on `L`; the `g_hi` half picks up `u_i²`.
  have s₁ : u₁ • commitGen g_lo c₁ + u₁ ^ 2 • commitGen g_hi c₁ = u₁ • P + L + u₁ ^ 2 • R := by
    have h := congrArg (u₁ • ·) e₁
    simp only [smul_add, smul_smul, mul_inv_cancel₀ hu₁, one_smul, ← pow_two] at h
    exact h
  have s₂ : u₂ • commitGen g_lo c₂ + u₂ ^ 2 • commitGen g_hi c₂ = u₂ • P + L + u₂ ^ 2 • R := by
    have h := congrArg (u₂ • ·) e₂
    simp only [smul_add, smul_smul, mul_inv_cancel₀ hu₂, one_smul, ← pow_two] at h
    exact h
  have s₃ : u₃ • commitGen g_lo c₃ + u₃ ^ 2 • commitGen g_hi c₃ = u₃ • P + L + u₃ ^ 2 • R := by
    have h := congrArg (u₃ • ·) e₃
    simp only [smul_add, smul_smul, mul_inv_cancel₀ hu₃, one_smul, ← pow_two] at h
    exact h
  -- Isolate the `g_hi` sub-commitments (the `u_i²` half).
  have hB₁ : u₁ ^ 2 • commitGen g_hi c₁
      = u₁ • P + L + u₁ ^ 2 • R - u₁ • commitGen g_lo c₁ := by rw [← s₁]; abel
  have hB₂ : u₂ ^ 2 • commitGen g_hi c₂
      = u₂ • P + L + u₂ ^ 2 • R - u₂ • commitGen g_lo c₂ := by rw [← s₂]; abel
  have hB₃ : u₃ ^ 2 • commitGen g_hi c₃
      = u₃ • P + L + u₃ ^ 2 • R - u₃ • commitGen g_lo c₃ := by rw [← s₃]; abel
  simp only [commitGen_add_left, commitGen_smul_left, hB₁, hB₂, hB₃]
  match_scalars <;>
    first
      | linear_combination hl1
      | linear_combination hl0
      | linear_combination hl2
      | ring

end Bulletproof
