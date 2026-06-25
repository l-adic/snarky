import Kimchi.Cycle.Axioms

/-!
# Group-order non-degeneracy toolkit

In the point group of a `CMCurve`, the `order` is prime, so a nonzero point times a
scalar strictly between `0` and `order` is itself nonzero. Hence a multiple `k • T` of a
nonzero point `T`, with `k` strictly between `1` and `order − 1`, is neither `T` nor `−T`,
and (on a short-Weierstrass curve) has a different `x`-coordinate than `T`.

These are standalone library lemmas — the mathematical core of "the partial accumulators
stay away from `±T`" — to be wired into the per-row accumulators in a later step.
-/

namespace Kimchi.Cycle

open WeierstrassCurve.Affine

variable {F : Type*} [Field F] [DecidableEq F]

/-- **Core non-degeneracy.** With prime `order`, a nonzero point times a scalar strictly
    between `0` and `order` is nonzero. -/
lemma smul_ne_zero_of_lt (c : CMCurve F) {T : c.W.Point} (hT : T ≠ 0)
    {k : ℤ} (h0 : 0 < k) (hlt : k < (c.order : ℤ)) : k • T ≠ 0 := by
  intro h_contra
  -- prime `order` together with `0 < k < order` forces `gcd k order = 1`
  have h_coprime : Int.gcd k (c.order : ℤ) = 1 := by
    refine Nat.coprime_comm.mp (c.order_prime.coprime_iff_not_dvd.mpr fun hd => ?_)
    have := Int.le_of_dvd (by positivity) (Int.natCast_dvd.mpr hd)
    omega
  -- Bézout: `k * a + order * b = 1`
  obtain ⟨a, b, hab⟩ : ∃ a b : ℤ, k * a + (c.order : ℤ) * b = 1 := by
    have h := Int.gcd_eq_gcd_ab k (c.order : ℤ)
    exact ⟨_, _, h.symm.trans (by rw [h_coprime]; simp)⟩
  -- hence `T = a • (k • T) + b • (order • T)`, and both terms vanish
  have h_decomp : T = a • (k • T) + b • ((c.order : ℤ) • T) := by
    rw [← mul_smul, ← mul_smul, ← add_smul, mul_comm a k, mul_comm b (c.order : ℤ), hab,
      one_zsmul]
  rw [h_contra, c.order_smul, smul_zero, smul_zero, add_zero] at h_decomp
  exact hT h_decomp

/-- A nonzero point times a scalar strictly between `1` and `order − 1` is neither `T`
    nor `−T`. -/
lemma smul_ne_base (c : CMCurve F) {T : c.W.Point} (hT : T ≠ 0)
    {k : ℤ} (h1 : 1 < k) (h2 : k + 1 < (c.order : ℤ)) :
    k • T ≠ T ∧ k • T ≠ -T := by
  refine ⟨?_, ?_⟩
  · intro h_contra
    have h_eq : (k - 1) • T = 0 := by
      rw [sub_smul, one_zsmul, h_contra, sub_self]
    exact smul_ne_zero_of_lt c hT (by linarith) (by linarith) h_eq
  · intro h_contra
    have h_eq : (k + 1) • T = 0 := by
      rw [add_zsmul, one_zsmul, h_contra, neg_add_cancel]
    exact smul_ne_zero_of_lt c hT (by linarith) (by linarith) h_eq

/-- **x-coordinate bridge.** On a short-Weierstrass curve, a point that is neither `T`
    nor `−T` has a different `x`-coordinate. -/
lemma x_ne_xT_of_ne_base (c : CMCurve F) {x y xT yT : F}
    (h : c.W.Nonsingular x y) (hT : c.W.Nonsingular xT yT)
    (hne : Point.some h ≠ Point.some hT) (hneg : Point.some h ≠ -Point.some hT) :
    x ≠ xT := by
  contrapose! hneg
  contrapose! hne
  simp_all +decide [WeierstrassCurve.Affine.negY]
  have h_eq : y ^ 2 + c.W.a₁ * xT * y + c.W.a₃ * y
      = yT ^ 2 + c.W.a₁ * xT * yT + c.W.a₃ * yT := by
    have := h.1; have := hT.1
    simp_all +decide [WeierstrassCurve.Affine.equation_iff]
  exact mul_left_cancel₀ (sub_ne_zero_of_ne hne) (by linear_combination h_eq)

end Kimchi.Cycle
