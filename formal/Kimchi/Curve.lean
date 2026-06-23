/-
  Curve.lean

  The elliptic-curve oracle for the kimchi EC gates.

  The custom EC gates (AddComplete, VarBaseMul, EndoMul) all operate on the Pasta
  curves (Pallas / Vesta), which are short Weierstrass curves `y² = x³ + b` — i.e.
  every `a`-invariant except `a₆` vanishes. The gates are checked against
  Mathlib's `WeierstrassCurve.Affine` specialized to this shape, so we name the
  shape predicate once here and share it across the gate proofs instead of
  inlining the four-way conjunction in every theorem.
-/
import Mathlib

namespace Kimchi

/-- The short-Weierstrass shape the kimchi EC gates assume: `a₁ = a₂ = a₃ = a₄ = 0`
    (so the curve is `y² = x³ + a₆`). The Pasta curves have exactly this shape.

    An `abbrev` so it unfolds transparently to the underlying conjunction — proofs
    can `obtain ⟨_, _, _, _⟩` it and reconstruct it with `⟨_, _, _, _⟩` directly. -/
abbrev IsShortShape {F : Type*} [CommRing F] (W : WeierstrassCurve.Affine F) : Prop :=
  W.a₁ = 0 ∧ W.a₂ = 0 ∧ W.a₃ = 0 ∧ W.a₄ = 0

open WeierstrassCurve.Affine

variable {F : Type*} [Field F] [DecidableEq F]

omit [DecidableEq F] in
/-- `Point.some` depends on the `y`-coordinate only through its value, not the
    nonsingularity proof: equal coordinates give equal points. A thin congruence
    for rewriting a target point into a recognizable form. -/
theorem some_eq_some (W : WeierstrassCurve.Affine F) {x y y' : F}
    (h : W.Nonsingular x y) (h' : W.Nonsingular x y') (hy : y = y') :
    Point.some h = Point.some h' := by
  subst hy; rfl

/-- One non-vertical (secant) affine addition, packaged with explicit output
    coordinates. If `(x₁,y₁)`, `(x₂,y₂)` are nonsingular points with `x₁ ≠ x₂`,
    and `ℓ, x₃, y₃` are the secant slope and resulting coordinates, then their
    group sum is the nonsingular point `(x₃, y₃)`. (No `y₁ ≠ 0` hypothesis: the
    doubling branch is excluded by `x₁ ≠ x₂`.) -/
lemma secant_add
    (W : WeierstrassCurve.Affine F) (ha : IsShortShape W)
    {x1 y1 x2 y2 : F}
    (h1 : W.Nonsingular x1 y1) (h2 : W.Nonsingular x2 y2)
    (hx : x1 ≠ x2)
    {l x3 y3 : F}
    (hl : l = (y1 - y2) / (x1 - x2))
    (hx3 : x3 = l * l - x1 - x2)
    (hy3 : y3 = l * (x1 - x3) - y1) :
    ∃ h3 : W.Nonsingular x3 y3,
      Point.some h1 + Point.some h2 = Point.some h3 := by
  obtain ⟨ha1, ha2, ha3, ha4⟩ := ha
  have hslope : W.slope x1 x2 y1 y2 = l := by
    rw [WeierstrassCurve.Affine.slope_of_X_ne hx, hl]
  have hfin : ¬(x1 = x2 ∧ y1 = W.negY x2 y2) := fun hc => hx hc.1
  have hx3' : W.addX x1 x2 (W.slope x1 x2 y1 y2) = x3 := by
    rw [hslope]; simp only [WeierstrassCurve.Affine.addX, ha1, ha2]
    rw [hx3]; ring
  have hy3' : W.addY x1 x2 y1 (W.slope x1 x2 y1 y2) = y3 := by
    rw [hslope]
    simp only [WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negY,
      WeierstrassCurve.Affine.negAddY, WeierstrassCurve.Affine.addX, ha1, ha2, ha3]
    rw [hy3, hx3]; ring
  rw [← hx3', ← hy3']
  exact ⟨WeierstrassCurve.Affine.nonsingular_add h1 h2 hfin,
         WeierstrassCurve.Affine.Point.add_some hfin⟩

/-- The sign-selected target. For a base point `(xT, yT)` on a short curve, the
    point `(xT, (2b−1)·yT)` with `b ∈ {0,1}` is `±` the base: `e • base` for the
    integer `e = 2b−1 ∈ {−1,1}` (negation on a short curve is `y ↦ −y`). -/
lemma signed_target
    (W : WeierstrassCurve.Affine F) (ha : IsShortShape W)
    {b xT yT : F}
    (hT : W.Nonsingular xT yT)
    (hQ : W.Nonsingular xT ((2 * b - 1) * yT))
    (hb : b = 0 ∨ b = 1) :
    ∃ e : ℤ, Point.some hQ = e • Point.some hT ∧ (e : F) = 2 * b - 1 := by
  obtain ⟨ha1, _, ha3, _⟩ := ha
  rcases hb with rfl | rfl
  · refine ⟨-1, ?_, by push_cast; ring⟩
    rw [neg_one_zsmul, Point.neg_some]
    exact some_eq_some W hQ _ (by rw [WeierstrassCurve.Affine.negY, ha1, ha3]; ring)
  · refine ⟨1, ?_, by push_cast; ring⟩
    rw [one_zsmul]
    exact some_eq_some W hQ hT (by ring)

end Kimchi
