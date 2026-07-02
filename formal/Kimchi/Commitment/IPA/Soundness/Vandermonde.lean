import Mathlib

/-!
# The `n`-point Vandermonde dual basis

The algebraic engine of the batched-opening extraction: reading off one coefficient
of a degree-`< n` polynomial from its values at `n` distinct nodes.

Given `n` pairwise-distinct nodes `ξ : Fin n → F` and a target index `d : Fin n`,
there is a coefficient vector `l : Fin n → F` such that the functional
`p ↦ ∑ s, l s * p (ξ s)` reads off the coefficient of `X ^ d`. Concretely,
`∑ s, l s * (ξ s) ^ i = [i = d]`.

This generalizes the three-node `vandermonde3` (Soundness/Linear.lean) to any
`n`. The engine is Mathlib's `Matrix.vandermonde` together with
`Matrix.det_vandermonde` (the determinant is `∏_{s < s'} (ξ s' - ξ s)`, nonzero
under injectivity, so the Vandermonde matrix is invertible over the field).
-/

namespace Kimchi.Commitment.IPA

variable {F : Type*} [Field F] [DecidableEq F]

omit [DecidableEq F] in
/-- **`n`-point Vandermonde dual basis.** For pairwise-distinct nodes
`ξ : Fin n → F` (injective) and a target index `d`, there exist coefficients
`l : Fin n → F` with `∑ s, l s * (ξ s) ^ i = [i = d]` for every `i`. Equivalently,
the functional `p ↦ ∑ s, l s * p (ξ s)` reads off the coefficient of `X ^ d` of any
polynomial of degree `< n`. Generalizes `vandermonde3`; the engine is
`Matrix.vandermonde` + `Matrix.det_vandermonde`. -/
theorem vandermondeN {n : ℕ} (ξ : Fin n → F) (hξ : Function.Injective ξ)
    (d : Fin n) :
    ∃ l : Fin n → F,
      ∀ i : Fin n, ∑ s, l s * (ξ s) ^ (i : ℕ) = if i = d then 1 else 0 := by
  -- `M` is the transpose of Mathlib's Vandermonde matrix: `M i s = (ξ s) ^ i`.
  set M : Matrix (Fin n) (Fin n) F := (Matrix.vandermonde ξ).transpose with hM
  -- `M` is invertible: its determinant equals that of `Matrix.vandermonde ξ`,
  -- which is nonzero because `ξ` is injective.
  have hdet : M.det ≠ 0 := by
    rw [hM, Matrix.det_transpose]
    exact Matrix.det_vandermonde_ne_zero_iff.mpr hξ
  have hunit : IsUnit M.det := isUnit_iff_ne_zero.mpr hdet
  -- Take `l` as the preimage of the `d`-th standard basis vector under `M`.
  refine ⟨M⁻¹.mulVec (Pi.single d 1), fun i => ?_⟩
  have hmul : M.mulVec (M⁻¹.mulVec (Pi.single d 1)) = Pi.single d 1 := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv M hunit, Matrix.one_mulVec]
  -- The functional `∑ s, l s * (ξ s) ^ i` is exactly `(M.mulVec l) i`.
  have hval : ∑ s, M⁻¹.mulVec (Pi.single d 1) s * (ξ s) ^ (i : ℕ)
      = (M.mulVec (M⁻¹.mulVec (Pi.single d 1))) i := by
    simp only [Matrix.mulVec, dotProduct, hM, Matrix.transpose_apply,
      Matrix.vandermonde_apply]
    exact Finset.sum_congr rfl fun s _ => by ring
  rw [hval, hmul, Pi.single_apply]

end Kimchi.Commitment.IPA
