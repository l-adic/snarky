import Kimchi.Gate.AddComplete
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

/-! # AddComplete semantics

    The gate computes affine point addition in Mathlib's elliptic-curve group law: the
    field-level soundness and completeness, the point-level payoff they add up to, and a
    runnable example. -/

namespace Kimchi.Gate.AddComplete

variable {F : Type u} [Field F]

/-- These coordinates name that point: the pair is nonsingular and the point it gives is
    `P`. What a caller holding coordinates and a caller holding a point agree on — the
    gate layer states it so the circuit layer can read its own points through it. -/
def IsPoint (W : WeierstrassCurve.Affine F) (x y : F) (P : W.Point) : Prop :=
  ∃ h : W.Nonsingular x y, P = WeierstrassCurve.Affine.Point.some _ _ h

/-- Two coordinate pairs naming the same point are the same pair. -/
theorem IsPoint.coords_eq {W : WeierstrassCurve.Affine F} {x y x' y' : F} {P : W.Point}
    (h : IsPoint W x y P) (h' : IsPoint W x' y' P) : x = x' ∧ y = y' := by
  obtain ⟨n, rfl⟩ := h
  obtain ⟨n', heq⟩ := h'
  simp only [WeierstrassCurve.Affine.Point.some.injEq] at heq
  exact heq

variable {F : Type*}

section Faithfulness

variable [Field F] [DecidableEq F]

/-- SOUNDNESS: a satisfying witness can't lie. If the 7 constraints hold for
    on-curve inputs with finite result, then the witnessed slope and output are
    EXACTLY Mathlib's affine group-law values. Since the sum of two affine
    points has coordinates `(addX, addY)` (`Point.add_some`), this says the gate
    computes `(x1,y1) + (x2,y2)` on the curve. -/
theorem sound_noninf
    (W : WeierstrassCurve.Affine F)
    (ha : W.a₁ = 0 ∧ W.a₂ = 0 ∧ W.a₃ = 0 ∧ W.a₄ = 0)
    (w : Witness F)
    (_hon1 : W.Equation w.x1 w.y1) (_hon2 : W.Equation w.x2 w.y2)
    (h : Holds w) (hinf : w.inf = 0)
    -- the prime-order side-conditions the Rust comments call out
    (hy1 : w.y1 ≠ 0) (h2 : (2 : F) ≠ 0) :
    w.s = W.slope w.x1 w.x2 w.y1 w.y2
    ∧ w.x3 = W.addX w.x1 w.x2 w.s
    ∧ w.y3 = W.addY w.x1 w.x2 w.y1 w.s := by
  obtain ⟨ha1, ha2, ha3, ha4⟩ := ha
  rw [holds_iff] at h
  obtain ⟨c1, c2, c3, c4, c5, c6, _⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · -- slope: w.s = W.slope …
    by_cases hx : w.x1 = w.x2
    · -- x₁ = x₂  ⇒  sameX = 1  (from the zero_check constraint c1)
      have hx21 : w.x2 - w.x1 = 0 := by rw [hx]; ring
      rw [hx21] at c1
      have hsame : w.sameX = 1 := by linear_combination c1
      by_cases hy : w.y1 = W.negY w.x2 w.y2
      · -- vertical case (sum = ∞): excluded by inf = 0 together with y₁ ≠ 0
        exfalso
        have hnegY2 : W.negY w.x2 w.y2 = -w.y2 := by
          simp [WeierstrassCurve.Affine.negY, ha1, ha3]
        rw [hnegY2] at hy
        rw [hsame, hinf] at c6
        have hy21 : w.y2 - w.y1 = 0 := by linear_combination c6
        exact (mul_ne_zero h2 hy1) (by linear_combination hy - hy21)
      · -- doubling: slope = 3x₁²/(2y₁), matching c3 (2·s·y₁ = 3x₁²)
        have hnegY : W.negY w.x1 w.y1 = -w.y1 := by
          simp [WeierstrassCurve.Affine.negY, ha1, ha3]
        have hden : w.y1 - W.negY w.x1 w.y1 ≠ 0 := by
          rw [hnegY, sub_neg_eq_add, ← two_mul]; exact mul_ne_zero h2 hy1
        rw [hsame] at c3
        rw [WeierstrassCurve.Affine.slope_of_Y_ne hx hy, eq_div_iff hden, hnegY]
        simp only [ha1, ha2, ha4]
        linear_combination c3
    · -- x₁ ≠ x₂  ⇒  sameX = 0  (from c2), giving the secant slope (y₁−y₂)/(x₁−x₂)
      have hx21 : w.x2 - w.x1 ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
      have hsame : w.sameX = 0 := (mul_eq_zero.mp c2).resolve_right hx21
      rw [hsame] at c3
      rw [WeierstrassCurve.Affine.slope_of_X_ne hx, eq_div_iff (sub_ne_zero.mpr hx)]
      linear_combination -c3
  · -- x₃ = addX = s² − x₁ − x₂  (exactly constraint c4)
    simp only [WeierstrassCurve.Affine.addX, ha1, ha2]
    linear_combination c4
  · -- y₃ = addY = s(x₁ − x₃) − y₁  (constraint c5, using c4 for x₃)
    simp only [WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negY,
      WeierstrassCurve.Affine.negAddY, WeierstrassCurve.Affine.addX, ha1, ha2, ha3]
    linear_combination -c5 - w.s * c4

/-- The canonical satisfying row: the slope, sum coordinates, and the three auxiliary
    witnesses, as one pure function of the operand values — the row the honest prover
    fills. `checkFinite` pins `inf` to `0`; otherwise `inf` is the inverse-pair test. -/
def build (checkFinite : Bool) (x1 y1 x2 y2 : F) : Witness F :=
  let s : F := if x1 = x2 then 3 * x1 * x1 / (2 * y1) else (y2 - y1) / (x2 - x1)
  let x3 : F := s * s - (x1 + x2)
  { x1 := x1, y1 := y1, x2 := x2, y2 := y2
    x3 := x3
    y3 := s * (x1 - x3) - y1
    inf := if checkFinite then 0
      else if decide (x1 = x2) && !decide (y1 = y2) then 1 else 0
    sameX := if decide (x1 = x2) then 1 else 0
    s := s
    infZ := if y1 = y2 then 0 else if x1 = x2 then (y2 - y1)⁻¹ else 0
    x21Inv := if x1 = x2 then 0 else (x2 - x1)⁻¹ }

/-- COMPLETENESS, constructive: the canonical row satisfies the gate. For on-curve
    operands with `y₁ ≠ 0` — `checkFinite` adding the finite-sum precondition —
    `build`'s row meets every constraint. The consumable form for a deployed prover,
    which is fixed code: an existential witness cannot certify the row it actually
    fills. `complete` below is the existential corollary. -/
theorem complete_build
    (W : WeierstrassCurve.Affine F)
    (ha : W.a₁ = 0 ∧ W.a₂ = 0 ∧ W.a₃ = 0 ∧ W.a₄ = 0)
    {checkFinite : Bool} {x1 y1 x2 y2 : F}
    (hon1 : W.Equation x1 y1) (hon2 : W.Equation x2 y2)
    (hy1 : y1 ≠ 0) (h2 : (2 : F) ≠ 0)
    (hfin : checkFinite = true → ¬(x1 = x2 ∧ y1 = W.negY x2 y2)) :
    Holds (build checkFinite x1 y1 x2 y2) := by
  obtain ⟨ha1, ha2, ha3, ha4⟩ := ha
  have hcancel := mul_inv_cancel₀ (mul_ne_zero h2 hy1)
  rw [holds_iff]
  by_cases hx : x1 = x2
  · -- Equal x-coordinates: on-curve, the y-coordinates agree or are opposite.
    have hyy : (y1 - y2) * (y1 + y2) = 0 := by
      rw [WeierstrassCurve.Affine.equation_iff] at hon1 hon2
      rw [ha1, ha2, ha3, ha4] at hon1 hon2
      rw [hx] at hon1
      linear_combination hon1 - hon2
    by_cases hy : y1 = y2
    · -- Doubling: `inf = 0` in both modes, `infZ = 0`.
      simp only [build, if_pos hx, if_pos hy, decide_eq_true hx, decide_eq_true hy,
        Bool.not_true, Bool.and_false, Bool.false_eq_true, if_false, if_true, ite_self]
      refine ⟨by ring, by linear_combination -hx, ?_, by ring, by ring, ?_, by ring⟩
      · linear_combination (3 * x1 * x1) * hcancel
      · linear_combination -hy
    · -- Inverse pair: `y₂ = −y₁`; excluded under `checkFinite`, else `inf = 1`.
      have hy2 : y2 = -y1 := by
        rcases mul_eq_zero.mp hyy with h | h
        · exact absurd (by linear_combination h) hy
        · linear_combination h
      have hne : y2 - y1 ≠ 0 := by
        rw [hy2]
        intro h
        rcases mul_eq_zero.mp (show y1 * 2 = 0 by linear_combination -h) with h' | h'
        · exact hy1 h'
        · exact h2 h'
      cases checkFinite with
      | true =>
        exact absurd ⟨hx, by rw [WeierstrassCurve.Affine.negY, ha1, ha3, hy2]; ring⟩
          (hfin rfl)
      | false =>
        simp only [build, if_pos hx, if_neg hy, decide_eq_true hx, decide_eq_false hy,
          Bool.not_false, Bool.and_true, Bool.false_eq_true, if_false, if_true]
        refine ⟨by ring, by linear_combination -hx, ?_, by ring, by ring, by ring, ?_⟩
        · linear_combination (3 * x1 * x1) * hcancel
        · linear_combination mul_inv_cancel₀ hne
  · -- Distinct x-coordinates: the secant row; `inf = 0` in both modes.
    have hne : x2 - x1 ≠ 0 := fun h => hx (by linear_combination -h)
    simp only [build, if_neg hx, decide_eq_false hx, Bool.false_and,
      Bool.false_eq_true, if_false, ite_self]
    refine ⟨?_, by ring, ?_, by ring, by ring, by ring, by ring⟩
    · linear_combination mul_inv_cancel₀ hne
    · linear_combination (y2 - y1) * mul_inv_cancel₀ hne

/-- COMPLETENESS, existential: for any on-curve inputs with `y₁ ≠ 0` a satisfying
    witness exists — `build`'s row. (`y₁ ≠ 0` excludes 2-torsion, which the
    prime-order kimchi curves don't have — so it is no real restriction there.) -/
theorem complete
    (W : WeierstrassCurve.Affine F)
    (ha : W.a₁ = 0 ∧ W.a₂ = 0 ∧ W.a₃ = 0 ∧ W.a₄ = 0)
    (x1 y1 x2 y2 : F)
    (hon1 : W.Equation x1 y1) (hon2 : W.Equation x2 y2)
    (hy1 : y1 ≠ 0) (h2 : (2 : F) ≠ 0) :
    ∃ w : Witness F, w.x1 = x1 ∧ w.y1 = y1 ∧ w.x2 = x2 ∧ w.y2 = y2 ∧ Holds w :=
  ⟨build false x1 y1 x2 y2, rfl, rfl, rfl, rfl,
    complete_build W ha hon1 hon2 hy1 h2 (fun h => Bool.noConfusion h)⟩

end Faithfulness

/-! ## Main theorems: the gate computes `Point` addition.

    The coordinate theorems above are the *inputs* to this section. Combined with
    `add_some`, they upgrade "the output columns equal the addition formulas" into
    a statement about Mathlib's **proven** elliptic-curve group `W.Point` — which
    certifies the output is a genuine curve point and lets all downstream EC
    reasoning use the group axioms (associativity, inverses, `n • P`) instead of
    re-deriving field identities.

    We take the inputs' nonsingularity as hypotheses (`h1`, `h2`); when these are
    instantiated at the Pasta curves they hold for every on-curve point, since
    those curves are nonsingular. The two cases — finite sum and the point at
    infinity (`inf = 1`) — are exhaustive: the constraints force `inf` to match
    the geometry (`inf = 1 ↔ x₁ = x₂ ∧ y₁ = -y₂`). -/

section Point

open WeierstrassCurve.Affine

variable [Field F] [DecidableEq F]

/-- Finite case (`inf = 0`): the gate's output `(x₃, y₃)` is a nonsingular curve
    point, and as a group element it equals the sum `(x₁,y₁) + (x₂,y₂)`. -/
theorem sound_point_noninf
    (W : WeierstrassCurve.Affine F)
    (ha : W.a₁ = 0 ∧ W.a₂ = 0 ∧ W.a₃ = 0 ∧ W.a₄ = 0)
    (w : Witness F)
    (h1 : W.Nonsingular w.x1 w.y1) (h2 : W.Nonsingular w.x2 w.y2)
    (hcons : Holds w)
    (hy1 : w.y1 ≠ 0) (htwo : (2 : F) ≠ 0) (hinf : w.inf = 0) :
    ∃ h3 : W.Nonsingular w.x3 w.y3,
      Point.some _ _ h1 + Point.some _ _ h2 = Point.some _ _ h3 := by
  obtain ⟨ha1, ha2, ha3, ha4⟩ := ha
  -- `inf = 0` rules out the vertical (sum-is-∞) case.
  have hfin : ¬(w.x1 = w.x2 ∧ w.y1 = W.negY w.x2 w.y2) := by
    rintro ⟨hxe, hye⟩
    have hc := hcons
    rw [holds_iff] at hc
    obtain ⟨c1, c2, c3, c4, c5, c6, c7⟩ := hc
    have hx21 : w.x2 - w.x1 = 0 := by rw [hxe]; ring
    rw [hx21] at c1
    have hsame : w.sameX = 1 := by linear_combination c1
    have hnegY2 : W.negY w.x2 w.y2 = -w.y2 := by simp [WeierstrassCurve.Affine.negY, ha1, ha3]
    rw [hnegY2] at hye
    have hy2ne : w.y2 ≠ 0 := fun h => hy1 (by rw [hye, h, neg_zero])
    have hy21ne : w.y2 - w.y1 ≠ 0 := by
      rw [hye, sub_neg_eq_add, ← two_mul]; exact mul_ne_zero htwo hy2ne
    rw [hsame, hinf] at c6
    exact hy21ne (by linear_combination c6)
  obtain ⟨hs, hx3, hy3⟩ := sound_noninf W ⟨ha1, ha2, ha3, ha4⟩ w h1.1 h2.1 hcons hinf hy1 htwo
  have hx3' : W.addX w.x1 w.x2 (W.slope w.x1 w.x2 w.y1 w.y2) = w.x3 := by rw [← hs, ← hx3]
  have hy3' : W.addY w.x1 w.x2 w.y1 (W.slope w.x1 w.x2 w.y1 w.y2) = w.y3 := by rw [← hs, ← hy3]
  -- Rewrite the goal's output coords to the formula coords *before* unpacking the
  -- existential, so the bound nonsingularity proof's motive stays well-typed.
  rw [← hx3', ← hy3']
  exact ⟨nonsingular_add h1 h2 hfin, Point.add_some hfin⟩

/-- Infinity case (`inf = 1`): the gate signals the sum is the point at infinity,
    and indeed `(x₁,y₁) + (x₂,y₂) = 0` in the group. -/
theorem sound_point_inf
    (W : WeierstrassCurve.Affine F)
    (w : Witness F)
    (h1 : W.Nonsingular w.x1 w.y1) (h2 : W.Nonsingular w.x2 w.y2)
    (hcons : Holds w) (hinf : w.inf = 1) :
    Point.some _ _ h1 + Point.some _ _ h2 = 0 := by
  rw [holds_iff] at hcons
  obtain ⟨c1, c2, c3, c4, c5, c6, c7⟩ := hcons
  rw [hinf] at c6 c7
  -- c7 forces y₂ ≠ y₁ (otherwise `0·infZ − 1 = 0`, i.e. `1 = 0`).
  have hy21ne : w.y2 - w.y1 ≠ 0 := by
    intro hz; rw [hz] at c7
    exact one_ne_zero (show (1 : F) = 0 by linear_combination -c7)
  -- c6 then forces sameX = 1, and c2 forces x₁ = x₂.
  have hsame : w.sameX = 1 := by
    rcases mul_eq_zero.mp c6 with h | h
    · exact absurd h hy21ne
    · linear_combination h
  rw [hsame] at c2
  have hx : w.x1 = w.x2 := (sub_eq_zero.mp (by linear_combination c2)).symm
  -- on the curve with x₁ = x₂ and y₂ ≠ y₁, the points must be negatives.
  rcases Y_eq_of_X_eq h1.1 h2.1 hx with hyy | hyn
  · exact absurd (by linear_combination -hyy) hy21ne
  · exact Point.add_of_Y_eq hx hyn

/-- The `inf` flag is boolean on a satisfying witness: `inf ∈ {0, 1}`. (If `y₂ = y₁`,
    `c7` forces `inf = 0`; otherwise `c6` ties `inf` to `sameX`, which `c1`/`c2` pin to
    `0` or `1` according to whether `x₁ = x₂`.) -/
theorem inf_boolean (w : Witness F) (hcons : Holds w) :
    w.inf = 0 ∨ w.inf = 1 := by
  rw [holds_iff] at hcons
  obtain ⟨c1, c2, _c3, _c4, _c5, c6, c7⟩ := hcons
  by_cases hy21 : w.y2 - w.y1 = 0
  · rw [hy21] at c7
    exact Or.inl (by linear_combination -c7)
  · have hsame : w.sameX = w.inf := by
      rcases mul_eq_zero.mp c6 with h | h
      · exact absurd h hy21
      · linear_combination h
    by_cases hx21 : w.x2 - w.x1 = 0
    · rw [hx21] at c1
      have hone : w.sameX = 1 := by linear_combination c1
      exact Or.inr (by rw [← hsame]; exact hone)
    · have hzero : w.sameX = 0 := (mul_eq_zero.mp c2).resolve_right hx21
      exact Or.inl (by rw [← hsame]; exact hzero)

/-- THE GATE COMPUTES COMPLETE ADDITION — both cases in one statement. For a satisfying
    witness, either the `inf` flag is set and the sum `(x₁,y₁) + (x₂,y₂)` is the point at
    infinity, or the flag is clear and the affine output `(x₃, y₃)` is that sum. Unifies
    `sound_point_inf` and `sound_point_noninf` via the boolean `inf`. -/
theorem sound
    (W : WeierstrassCurve.Affine F)
    (ha : W.a₁ = 0 ∧ W.a₂ = 0 ∧ W.a₃ = 0 ∧ W.a₄ = 0)
    (w : Witness F)
    (h1 : W.Nonsingular w.x1 w.y1) (h2 : W.Nonsingular w.x2 w.y2)
    (hcons : Holds w) (hy1 : w.y1 ≠ 0) (htwo : (2 : F) ≠ 0) :
    (w.inf = 1 ∧ Point.some _ _ h1 + Point.some _ _ h2 = 0)
      ∨ (w.inf = 0 ∧ ∃ h3 : W.Nonsingular w.x3 w.y3,
          Point.some _ _ h1 + Point.some _ _ h2 = Point.some _ _ h3) := by
  rcases inf_boolean w hcons with hinf | hinf
  · exact Or.inr ⟨hinf, sound_point_noninf W ha w h1 h2 hcons hy1 htwo hinf⟩
  · exact Or.inl ⟨hinf, sound_point_inf W w h1 h2 hcons hinf⟩

end Point

/-! ## A concrete, runnable example.

    Curve `y² = x³ + 4` over `ZMod 17`. Double the point `(0, 2)`:
    tangent is horizontal (slope 0), so `2·(0,2) = (0,-2) = (0,15)`.
    Same-x doubling ⇒ `sameX = 1`, `s = 0`, `x21Inv = 0`, `inf = 0`. -/

/-- The doubling witness of the example above: `2·(0,2) = (0,15)` on `y² = x³ + 4` over
`ZMod 17`. -/
def egDouble : Witness (ZMod 17) :=
  { x1 := 0, y1 := 2, x2 := 0, y2 := 2, x3 := 0, y3 := 15
  , inf := 0, sameX := 1, s := 0, infZ := 0, x21Inv := 0 }

#eval ok egDouble   -- expect true

example : Holds egDouble := by
  rw [← ok_iff]; rfl

end Kimchi.Gate.AddComplete
