import Kimchi.Gate.VarBaseMul
import Kimchi.Gate.Semantics.AddComplete
import Pasta.Shifted
import Mathlib

/-! # VarBaseMul semantics

One gate row runs a bit of the double-and-add ladder, with soundness and completeness. The
multi-row chain folds those rows into variable-base scalar multiplication `[σ]·T`, including
the Type1 and Type2 caller scalars at the Pasta curves.

Beyond the per-row development, the file has two parts: `§ Supporting development` (the
recurrence folds, the number-theoretic ladder kernel, and the group-order non-degeneracy
toolkit) and `§ The deployed circuit` (the per-curve entry points). -/

namespace Kimchi.Gate.VarBaseMul

variable {F : Type*}

/-! ## Soundness.

    Per bit, a satisfying block computes the double-and-add step

        output = (input + Q) + input        (= 2·input + (2·b − 1)·target)

    in the curve group, where `Q := (xb, (2b−1)·yb)` is the sign-selected target
    (`Q = target` when `b = 1`, `Q = −target` when `b = 0`, since on a short
    Weierstrass curve negation is `y ↦ −y`).

    The content is that the fused `s2 = u/t` formula — which skips the
    intermediate `Y` of `input + Q` — equals the slope of the SECOND addition, so
    the block is exactly the composite of two Mathlib affine additions. This
    builds on the already-proven `Kimchi.Gate.AddComplete`, whose `sound_point_*`
    theorems characterize one such addition. The non-degeneracy hypotheses
    `xi ≠ xb` (first addition non-vertical) and `2·xi + xb − s1² ≠ 0` (i.e.
    `t ≠ 0`, second addition non-vertical) are exactly when the two divisions are
    defined. -/

section Soundness

open WeierstrassCurve.Affine

variable [Field F] [DecidableEq F]

/-- One non-vertical (secant) affine addition, packaged with explicit output
    coordinates. If `(x₁,y₁)`, `(x₂,y₂)` are nonsingular points with `x₁ ≠ x₂`,
    and `ℓ, x₃, y₃` are the secant slope and resulting coordinates, then their
    group sum is the nonsingular point `(x₃, y₃)`.

    This is the secant specialization of
    `Kimchi.Gate.AddComplete.sound_point_noninf` (its first slope branch); unlike that
    theorem it carries no `y₁ ≠ 0` hypothesis, since the doubling branch is
    excluded by `x₁ ≠ x₂`. -/
lemma secant_add
    (W : WeierstrassCurve.Affine F) (ha : W.a₁ = 0 ∧ W.a₂ = 0 ∧ W.a₃ = 0)
    {x1 y1 x2 y2 : F}
    (h1 : W.Nonsingular x1 y1) (h2 : W.Nonsingular x2 y2)
    (hx : x1 ≠ x2)
    {l x3 y3 : F}
    (hl : l = (y1 - y2) / (x1 - x2))
    (hx3 : x3 = l * l - x1 - x2)
    (hy3 : y3 = l * (x1 - x3) - y1) :
    ∃ h3 : W.Nonsingular x3 y3,
      Point.some _ _ h1 + Point.some _ _ h2 = Point.some _ _ h3 := by
  obtain ⟨ha1, ha2, ha3⟩ := ha
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

/-- Per-bit soundness. A single-bit block that
    satisfies `singleBitHolds` computes `output = (input + Q) + input` in the
    group, where `Q = (xb, (2b−1)·yb)` is the sign-selected target. The output is
    a genuine nonsingular curve point (hence the `∃ hO`, mirroring
    `Kimchi.Gate.AddComplete.sound_point_noninf`).

    The block is exactly the composite of two affine additions: `R := I + Q`
    (first slope `s1`, non-vertical since `xi ≠ xb`) followed by `O := R + I`
    (second slope `s2 = u/t`, non-vertical since `t = 2·xi + xb − s1² ≠ 0`). The
    fused `s2 = u/t` formula skips the intermediate `Y` of `R`; we recover it from
    the `xo`/`yo` constraints, then close with `secant_add` twice.

    No booleanity hypothesis on `b` is needed: the algebraic argument holds for
    arbitrary `b`, since `Q`'s validity as a curve point is supplied directly by
    `hQ`. (At the gate level the `b ∈ {0,1}` constraint is what makes
    `Q = (2b−1)·target` equal `±target`.) -/
private theorem singleBit_sound
    (W : WeierstrassCurve.Affine F) (ha : W.a₁ = 0 ∧ W.a₂ = 0 ∧ W.a₃ = 0)
    (b xb yb s1 xi yi xo yo : F)
    (hI : W.Nonsingular xi yi)
    (hQ : W.Nonsingular xb ((2 * b - 1) * yb))
    (hxne : xi ≠ xb)
    (htne : 2 * xi + xb - s1 * s1 ≠ 0)
    (h : singleBitHolds b xb yb s1 xi yi xo yo) :
    ∃ hO : W.Nonsingular xo yo,
      Point.some _ _ hO = (Point.some _ _ hI + Point.some _ _ hQ) + Point.some _ _ hI := by
  obtain ⟨ha1, ha2, ha3⟩ := ha
  rw [singleBitHolds_iff] at h
  obtain ⟨hbool, hc_s1, hc_xo, hc_yo⟩ := h
  have hdiff1 : xi - xb ≠ 0 := sub_ne_zero.mpr hxne
  -- the first addition `I + Q` has slope `s1`
  have hl1 : s1 = (yi - (2 * b - 1) * yb) / (xi - xb) := by
    rw [eq_div_iff hdiff1]; linear_combination hc_s1
  -- name the intermediate point `R = (rx, ry)` and the second slope `s2`
  set rx : F := s1 * s1 - xi - xb with hrx
  set ry : F := s1 * (xi - rx) - yi with hry
  set s2 : F := (ry - yi) / (rx - xi) with hs2
  clear_value s2 ry rx
  have htval : xi - rx = 2 * xi + xb - s1 * s1 := by rw [hrx]; ring
  have htt : xi - rx ≠ 0 := by rw [htval]; exact htne
  have hrxne : rx ≠ xi := by intro hc; exact htt (by rw [hc]; ring)
  have hxine : rx - xi ≠ 0 := sub_ne_zero.mpr hrxne
  -- first addition: `I + Q = R`
  obtain ⟨hR, hAdd1⟩ :=
    secant_add W ⟨ha1, ha2, ha3⟩ hI hQ hxne hl1 hrx hry
  -- the fused `s2 = u/t` is the slope of the second addition: `s2² = xo − xb + s1²`
  have hs2sq : s2 * s2 = xo - xb + s1 * s1 := by
    rw [hs2, div_mul_div_comm, div_eq_iff (mul_ne_zero hxine hxine), hry]
    linear_combination hc_xo
  have hxo : xo = s2 * s2 - rx - xi := by rw [hs2sq, hrx]; ring
  have hyo : yo = s2 * (rx - xo) - ry := by
    have hsr : s2 * (rx - xi) = ry - yi := by
      rw [hs2, div_mul_cancel₀]; exact hxine
    have hyo' : yo = (xi - xo) * s2 - yi := by
      rw [hs2]; field_simp
      linear_combination -hc_yo - (xi - xo) * hry
    rw [hyo']; linear_combination -hsr
  -- second addition: `R + I = O`
  obtain ⟨hO, hAdd2⟩ :=
    secant_add W ⟨ha1, ha2, ha3⟩ hR hI hrxne hs2 hxo hyo
  exact ⟨hO, by rw [hAdd1, hAdd2]⟩

/-- Full-gate scalar multiplication. Chaining `singleBit_sound` across all five
    blocks, a satisfying gate computes the double-and-add accumulation

        P₅ = 32·P₀ + 16·Q₀ + 8·Q₁ + 4·Q₂ + 2·Q₃ + Q₄

    in the curve group, where `Pᵢ = (xᵢ, yᵢ)` is the accumulator chain and
    `Qᵢ = (xT, (2bᵢ−1)·yT)` is the sign-selected target for bit `i` (so `Qᵢ = ±T`
    when `bᵢ ∈ {0,1}`). This is exactly variable-base scalar multiplication by the
    signed-binary digits `b₀..b₄`. The companion `decompHolds` constraint records
    the same digits in the scalar register `n → n' = 32n + 16b₀ + ⋯ + b₄`.

    `Pᵢ` nonsingularity and the per-step non-degeneracy (`xᵢ ≠ xT`, `tᵢ ≠ 0`) are
    hypotheses; booleanity of each `bᵢ` is available from `Holds` if needed. -/
private theorem gate_scalarMul
    (W : WeierstrassCurve.Affine F) (ha : W.a₁ = 0 ∧ W.a₂ = 0 ∧ W.a₃ = 0) (w : Witness F)
    (h0 : W.Nonsingular w.x0 w.y0) (h1 : W.Nonsingular w.x1 w.y1)
    (h2 : W.Nonsingular w.x2 w.y2) (h3 : W.Nonsingular w.x3 w.y3)
    (h4 : W.Nonsingular w.x4 w.y4) (h5 : W.Nonsingular w.x5 w.y5)
    (hQ0 : W.Nonsingular w.xT ((2 * w.b0 - 1) * w.yT))
    (hQ1 : W.Nonsingular w.xT ((2 * w.b1 - 1) * w.yT))
    (hQ2 : W.Nonsingular w.xT ((2 * w.b2 - 1) * w.yT))
    (hQ3 : W.Nonsingular w.xT ((2 * w.b3 - 1) * w.yT))
    (hQ4 : W.Nonsingular w.xT ((2 * w.b4 - 1) * w.yT))
    (hxne0 : w.x0 ≠ w.xT) (hxne1 : w.x1 ≠ w.xT) (hxne2 : w.x2 ≠ w.xT)
    (hxne3 : w.x3 ≠ w.xT) (hxne4 : w.x4 ≠ w.xT)
    (htne0 : 2 * w.x0 + w.xT - w.s0 * w.s0 ≠ 0)
    (htne1 : 2 * w.x1 + w.xT - w.s1 * w.s1 ≠ 0)
    (htne2 : 2 * w.x2 + w.xT - w.s2 * w.s2 ≠ 0)
    (htne3 : 2 * w.x3 + w.xT - w.s3 * w.s3 ≠ 0)
    (htne4 : 2 * w.x4 + w.xT - w.s4 * w.s4 ≠ 0)
    (h : Holds w) :
    Point.some _ _ h5
      = (32 : ℕ) • Point.some _ _ h0
        + (16 : ℕ) • Point.some _ _ hQ0 + (8 : ℕ) • Point.some _ _ hQ1
        + (4 : ℕ) • Point.some _ _ hQ2 + (2 : ℕ) • Point.some _ _ hQ3
        + Point.some _ _ hQ4 := by
  obtain ⟨_hdecomp, hb0, hb1, hb2, hb3, hb4⟩ := (holds_iff w).mp h
  obtain ⟨_, e0⟩ := singleBit_sound W ha w.b0 w.xT w.yT w.s0 w.x0 w.y0 w.x1 w.y1
    h0 hQ0 hxne0 htne0 hb0
  obtain ⟨_, e1⟩ := singleBit_sound W ha w.b1 w.xT w.yT w.s1 w.x1 w.y1 w.x2 w.y2
    h1 hQ1 hxne1 htne1 hb1
  obtain ⟨_, e2⟩ := singleBit_sound W ha w.b2 w.xT w.yT w.s2 w.x2 w.y2 w.x3 w.y3
    h2 hQ2 hxne2 htne2 hb2
  obtain ⟨_, e3⟩ := singleBit_sound W ha w.b3 w.xT w.yT w.s3 w.x3 w.y3 w.x4 w.y4
    h3 hQ3 hxne3 htne3 hb3
  obtain ⟨_, e4⟩ := singleBit_sound W ha w.b4 w.xT w.yT w.s4 w.x4 w.y4 w.x5 w.y5
    h4 hQ4 hxne4 htne4 hb4
  -- match the existential outputs with the given nonsingularity proofs by proof irrelevance
  have eq1 : Point.some _ _ h1 = (Point.some _ _ h0 + Point.some _ _ hQ0) + Point.some _ _ h0 := e0
  have eq2 : Point.some _ _ h2 = (Point.some _ _ h1 + Point.some _ _ hQ1) + Point.some _ _ h1 := e1
  have eq3 : Point.some _ _ h3 = (Point.some _ _ h2 + Point.some _ _ hQ2) + Point.some _ _ h2 := e2
  have eq4 : Point.some _ _ h4 = (Point.some _ _ h3 + Point.some _ _ hQ3) + Point.some _ _ h3 := e3
  have eq5 : Point.some _ _ h5 = (Point.some _ _ h4 + Point.some _ _ hQ4) + Point.some _ _ h4 := e4
  rw [eq5, eq4, eq3, eq2, eq1]
  abel

omit [DecidableEq F] in
/-- Two affine points with the same `x` and provably-equal `y` are equal (proof
    irrelevance on the nonsingularity witness). -/
private lemma some_eq_some (W : WeierstrassCurve.Affine F) {x y y' : F}
    (h : W.Nonsingular x y) (h' : W.Nonsingular x y') (hy : y = y') :
    Point.some _ _ h = Point.some _ _ h' := by
  subst hy; rfl

omit [DecidableEq F] in
/-- Booleanity from the field constraint `b·b − b = 0`. -/
private lemma bool_of_sq {b : F} (h : b * b - b = 0) : b = 0 ∨ b = 1 := by
  have hmul : b * (b - 1) = 0 := by ring_nf; linear_combination h
  rcases mul_eq_zero.mp hmul with h1 | h1
  · exact Or.inl h1
  · exact Or.inr (by linear_combination h1)

omit [DecidableEq F] in
/-- The sign-selected target `(xT, (2b−1)·yT)` is itself a nonsingular point once `b ∈ {0,1}` and
    the base `(xT, yT)` is: it equals `(xT, yT)` when `b = 1` and its negation when `b = 0` (short
    shape). So this nonsingularity never has to be supplied separately — it follows from `hT` and
    booleanity. -/
lemma signed_target_nonsingular
    (W : WeierstrassCurve.Affine F) (ha : W.a₁ = 0 ∧ W.a₂ = 0 ∧ W.a₃ = 0)
    {b xT yT : F} (hT : W.Nonsingular xT yT) (hb : b = 0 ∨ b = 1) :
    W.Nonsingular xT ((2 * b - 1) * yT) := by
  obtain ⟨ha1, _, ha3⟩ := ha
  rcases hb with rfl | rfl
  · have h : (2 * (0 : F) - 1) * yT = W.negY xT yT := by
      rw [WeierstrassCurve.Affine.negY, ha1, ha3]; ring
    rw [h]; exact (W.nonsingular_neg xT yT).mpr hT
  · have h : (2 * (1 : F) - 1) * yT = yT := by ring
    rw [h]; exact hT

/-- The sign-selected target `Q = (xT, (2b−1)·yT)` is `±T` once `b ∈ {0,1}`:
    on a short Weierstrass curve negation is `y ↦ −y`, so `Q = (2b−1)•T` as an
    integer scalar multiple of `T = (xT, yT)`. -/
lemma signed_target
    (W : WeierstrassCurve.Affine F) (ha : W.a₁ = 0 ∧ W.a₂ = 0 ∧ W.a₃ = 0)
    {b xT yT : F}
    (hT : W.Nonsingular xT yT)
    (hQ : W.Nonsingular xT ((2 * b - 1) * yT))
    (hb : b = 0 ∨ b = 1) :
    ∃ e : ℤ, Point.some _ _ hQ = e • Point.some _ _ hT ∧ (e : F) = 2 * b - 1
           ∧ (e = 1 ∨ e = -1) := by
  obtain ⟨ha1, _, ha3⟩ := ha
  rcases hb with rfl | rfl
  · refine ⟨-1, ?_, by push_cast; ring, Or.inr rfl⟩
    rw [neg_one_zsmul, Point.neg_some]
    exact some_eq_some W hQ _ (by rw [WeierstrassCurve.Affine.negY, ha1, ha3]; ring)
  · refine ⟨1, ?_, by push_cast; ring, Or.inl rfl⟩
    rw [one_zsmul]
    exact some_eq_some W hQ hT (by ring)

/-- The bridge to the integer-scalar form. A
    satisfying gate computes `P₅ = 32·P₀ + c·T` for an integer `c` — the gate's
    signed 5-bit value `c = 16(2b₀−1) + 8(2b₁−1) + 4(2b₂−1) + 2(2b₃−1) + (2b₄−1)`.

    This folds `gate_scalarMul`'s point sum `16·Q₀ + ⋯ + Q₄` into `c·T`: each
    `Qᵢ = (xT, (2bᵢ−1)·yT)` is `±T` once `bᵢ ∈ {0,1}` (booleanity, available from
    the `b·b − b = 0` constraint inside `Holds`), since on a short curve negation
    is `y ↦ −y`. This is exactly the per-gate relation `chain_scalarMul` consumes,
    so it closes the gap between one gate and the arbitrary-length chain. -/
theorem sound
    (W : WeierstrassCurve.Affine F) (ha : W.a₁ = 0 ∧ W.a₂ = 0 ∧ W.a₃ = 0) (w : Witness F)
    (h0 : W.Nonsingular w.x0 w.y0) (h1 : W.Nonsingular w.x1 w.y1)
    (h2 : W.Nonsingular w.x2 w.y2) (h3 : W.Nonsingular w.x3 w.y3)
    (h4 : W.Nonsingular w.x4 w.y4) (h5 : W.Nonsingular w.x5 w.y5)
    (hT : W.Nonsingular w.xT w.yT)
    (hxne0 : w.x0 ≠ w.xT) (hxne1 : w.x1 ≠ w.xT) (hxne2 : w.x2 ≠ w.xT)
    (hxne3 : w.x3 ≠ w.xT) (hxne4 : w.x4 ≠ w.xT)
    (htne0 : 2 * w.x0 + w.xT - w.s0 * w.s0 ≠ 0)
    (htne1 : 2 * w.x1 + w.xT - w.s1 * w.s1 ≠ 0)
    (htne2 : 2 * w.x2 + w.xT - w.s2 * w.s2 ≠ 0)
    (htne3 : 2 * w.x3 + w.xT - w.s3 * w.s3 ≠ 0)
    (htne4 : 2 * w.x4 + w.xT - w.s4 * w.s4 ≠ 0)
    (h : Holds w) :
    ∃ c : ℤ, Point.some _ _ h5 = (32 : ℤ) • Point.some _ _ h0 + c • Point.some _ _ hT
           ∧ (c : F) = 2 * w.nPrime - 64 * w.n - 31
           ∧ c.natAbs ≤ 31 := by
  -- booleanity of each bit from the `b·b − b = 0` constraint inside `Holds`; the sign-selected
  -- targets are then nonsingular by `signed_target_nonsingular` (no need to assume them)
  obtain ⟨hdec, hbit0, hbit1, hbit2, hbit3, hbit4⟩ := (holds_iff w).mp h
  have hQ0 := signed_target_nonsingular W ha hT (bool_of_sq hbit0.bool)
  have hQ1 := signed_target_nonsingular W ha hT (bool_of_sq hbit1.bool)
  have hQ2 := signed_target_nonsingular W ha hT (bool_of_sq hbit2.bool)
  have hQ3 := signed_target_nonsingular W ha hT (bool_of_sq hbit3.bool)
  have hQ4 := signed_target_nonsingular W ha hT (bool_of_sq hbit4.bool)
  -- the Q-point sum from the already-proven nat-smul gate soundness
  have main := gate_scalarMul W ha w h0 h1 h2 h3 h4 h5 hQ0 hQ1 hQ2 hQ3 hQ4
    hxne0 hxne1 hxne2 hxne3 hxne4 htne0 htne1 htne2 htne3 htne4 h
  obtain ⟨e0, q0, he0, hd0⟩ := signed_target W ha hT hQ0 (bool_of_sq hbit0.bool)
  obtain ⟨e1, q1, he1, hd1⟩ := signed_target W ha hT hQ1 (bool_of_sq hbit1.bool)
  obtain ⟨e2, q2, he2, hd2⟩ := signed_target W ha hT hQ2 (bool_of_sq hbit2.bool)
  obtain ⟨e3, q3, he3, hd3⟩ := signed_target W ha hT hQ3 (bool_of_sq hbit3.bool)
  obtain ⟨e4, q4, he4, hd4⟩ := signed_target W ha hT hQ4 (bool_of_sq hbit4.bool)
  refine ⟨16 * e0 + 8 * e1 + 4 * e2 + 2 * e3 + e4, ?_, ?_, ?_⟩
  · rw [main, q0, q1, q2, q3, q4]
    simp only [← natCast_zsmul, smul_smul]
    push_cast
    rw [add_smul, add_smul, add_smul, add_smul]
    abel
  · -- `c` matches the scalar register: `(c:F) = 2·n' − 64·n − 31`, from `decompHolds`.
    simp only [decompHolds, decompCons] at hdec
    push_cast
    rw [he0, he1, he2, he3, he4]
    linear_combination -2 * hdec
  · -- magnitude: each signed digit is ±1, so `|c| ≤ 16+8+4+2+1 = 31`.
    rcases hd0 with rfl | rfl <;> rcases hd1 with rfl | rfl <;>
      rcases hd2 with rfl | rfl <;> rcases hd3 with rfl | rfl <;>
      rcases hd4 with rfl | rfl <;> decide

end Soundness

/-! ## Completeness: the witness generator satisfies the constraints

`sound` shows a satisfying witness computes `[s]·T`. Completeness is the converse direction —
the honest computation yields a satisfying witness: the generated chain `build` satisfies `Holds`,
under the same non-degeneracy conditions soundness needs (each step's two additions are
non-vertical: `xᵢ ≠ xT` and `tᵢ = 2·xᵢ + xT − sᵢ² ≠ 0`). It is purely algebraic — no curve
membership is required. -/

/-- A single block's constraints hold for any `(s1, s2, xo, yo)` linked by the generation
    relations (slope `s1` chord, slope `s2` tangent, and the output point), given booleanity.
    Stated with the slopes in *multiplicative* form so it is pure polynomial algebra. -/
private theorem singleBitHolds_of_step [CommRing F] (b xb yb s1 s2 xi yi xo yo : F)
    (hb : b * b - b = 0)
    (hsl : (xi - xb) * s1 = yi - (2 * b - 1) * yb)
    (hs2 : (2 * xi + xb - s1 * s1) * s2 = 2 * yi - (2 * xi + xb - s1 * s1) * s1)
    (hxo : xo = xb + s2 * s2 - s1 * s1)
    (hyo : yo = (xi - xo) * s2 - yi) :
    singleBitHolds b xb yb s1 xi yi xo yo := by
  rw [singleBitHolds_iff]
  refine ⟨hb, by linear_combination hsl, ?_, ?_⟩
  · subst hxo
    linear_combination
      (-(2 * yi - (2 * xi + xb - s1 * s1) * s1) - (2 * xi + xb - s1 * s1) * s2) * hs2
  · subst hyo hxo
    linear_combination (xi - (xb + s2 * s2 - s1 * s1)) * hs2

/-- The generated single-bit step satisfies the single-bit constraints, given booleanity of `b`
    and the two non-degeneracy conditions (`xi ≠ xb`, `t ≠ 0`) — the denominators in `stepBit`. -/
private theorem stepBit_holds [Field F] (b xb yb xi yi : F)
    (hb : b * b - b = 0) (hx : xi - xb ≠ 0)
    (ht : 2 * xi + xb - (stepBit b xb yb xi yi).1 * (stepBit b xb yb xi yi).1 ≠ 0) :
    singleBitHolds b xb yb (stepBit b xb yb xi yi).1 xi yi
      (stepBit b xb yb xi yi).2.1 (stepBit b xb yb xi yi).2.2 := by
  set s1 := (yi - (2 * b - 1) * yb) / (xi - xb) with hs1
  have e1 : (stepBit b xb yb xi yi).1 = s1 := rfl
  set s2 := 2 * yi / (2 * xi + xb - s1 * s1) - s1 with hs2d
  have e2 : (stepBit b xb yb xi yi).2.1 = xb + s2 * s2 - s1 * s1 := rfl
  have e3 : (stepBit b xb yb xi yi).2.2 = (xi - (xb + s2 * s2 - s1 * s1)) * s2 - yi := rfl
  rw [e1] at ht ⊢
  rw [e2, e3]
  refine singleBitHolds_of_step b xb yb s1 s2 xi yi _ _ hb ?_ ?_ rfl rfl
  · rw [hs1]; field_simp
  · rw [hs2d]
    have ht' : 2 * xi + xb - s1 ^ 2 ≠ 0 := by rw [pow_two]; exact ht
    field_simp [ht']

/-- **Completeness of the VarBaseMul gate.** The witness produced by the generator `build`
    satisfies all 21 constraints (`Holds`), given booleanity of the five bits and the per-step
    non-degeneracy conditions (each accumulator `xᵢ ≠ xT` and each `tᵢ ≠ 0`) — the conditions
    under which the gate's incomplete additions are well-defined. Conditional, as expected for an
    incomplete-addition gate; `decompHolds` holds unconditionally by construction. -/
theorem complete [Field F] (xb yb x0 y0 n b0 b1 b2 b3 b4 : F)
    (w : Witness F) (hw : w = build xb yb x0 y0 n b0 b1 b2 b3 b4)
    (hb0 : b0 * b0 - b0 = 0) (hb1 : b1 * b1 - b1 = 0) (hb2 : b2 * b2 - b2 = 0)
    (hb3 : b3 * b3 - b3 = 0) (hb4 : b4 * b4 - b4 = 0)
    (hx0 : w.x0 ≠ w.xT) (ht0 : 2 * w.x0 + w.xT - w.s0 * w.s0 ≠ 0)
    (hx1 : w.x1 ≠ w.xT) (ht1 : 2 * w.x1 + w.xT - w.s1 * w.s1 ≠ 0)
    (hx2 : w.x2 ≠ w.xT) (ht2 : 2 * w.x2 + w.xT - w.s2 * w.s2 ≠ 0)
    (hx3 : w.x3 ≠ w.xT) (ht3 : 2 * w.x3 + w.xT - w.s3 * w.s3 ≠ 0)
    (hx4 : w.x4 ≠ w.xT) (ht4 : 2 * w.x4 + w.xT - w.s4 * w.s4 ≠ 0) :
    Holds w := by
  subst hw
  refine (holds_iff _).mpr
    ⟨by simp only [decompHolds, decompCons, build]; ring, ?_, ?_, ?_, ?_, ?_⟩
  · exact stepBit_holds b0 xb yb x0 y0 hb0 (sub_ne_zero_of_ne hx0) ht0
  · exact stepBit_holds b1 xb yb _ _ hb1 (sub_ne_zero_of_ne hx1) ht1
  · exact stepBit_holds b2 xb yb _ _ hb2 (sub_ne_zero_of_ne hx2) ht2
  · exact stepBit_holds b3 xb yb _ _ hb3 (sub_ne_zero_of_ne hx3) ht3
  · exact stepBit_holds b4 xb yb _ _ hb4 (sub_ne_zero_of_ne hx4) ht4

end Kimchi.Gate.VarBaseMul

/-!
## Supporting development

Variable-base scalar multiplication composes `Kimchi.Gate.VarBaseMul` gate rows: `m` gates run
back to back, each consuming five bits of the scalar, with gate `i`'s output accumulator feeding
gate `i + 1`'s input and its scalar register threading alongside. Each gate's `sound` supplies the
per-step relation `P_{i+1} = 32·P_i + cᵢ·T`, and folding that recurrence over the `m` rows is pure
group algebra. This module gathers the definitions and lemmas on which the deployed correctness
theorems rest — the curve-specialized `varBaseMul_scaleFast1` and `varBaseMul_scaleFast2` (in
`Kimchi.Gate.VarBaseMul`) and the two generic roots `varBaseMul_subwrap_correct` and
`varBaseMul_forbidden_correct` it exposes here.

### Correspondence to the PureScript circuit

The hypotheses are exactly the constraints `Snarky.Circuit.Kimchi.VarBaseMul` emits
(`packages/snarky-kimchi/src/Snarky/Circuit/Kimchi/VarBaseMul.purs`):

* `P 0 = 2·T` ← `addFast CheckFinite base base` (acc := `[2]·base`);
* `N 0 = 0` ← `nAccPrev: const_ zero`; per-bit `n' = 2·n + b` ← `foldl (\a b -> double a + b)`;
* `q_j = (xT, (2·b − 1)·yT)` ← `Q = (xBase, (2·b − 1)·yBase)` (`computeVbmChain`);
* `N m` holds the caller's shifted register ← `assertEqual_ nAcc t`.

The two circuit entry points appear here as `scalarMul_shifted` (the core `varBaseMul`, computing
`[2·t + 2^n + 1]·g`) and `scalarMul_type2` (`scaleFast2`, the parity split). This is an audit-level
correspondence: the model's hypotheses match the PureScript constraints by inspection, not by a
mechanized extraction.

### Contents

* the point- and register-level recurrence folds (`chain_scalarMul`, `chain_register`,
  `chain_sum_bound`) and the folded scalar-multiplication theorems (`scalarMul`,
  `scalarMul_baseMul`, `scalarMul_shifted`, `scalarMul_type2`);
* the per-row hypothesis bundles `NonDegen` (the non-vertical side conditions) and `GateStep`;
* the number-theoretic ladder kernel (`Kimchi.Gate.VarBaseMul.Ladder`): the double-and-add
  ladder's bounds, the forbidden-band / forbidden-residue characterization of degenerate finals,
  and the unconditional sub-wrap non-degeneracy;
* the group-order non-degeneracy toolkit (`smul_ne_zero_of_lt`, `x_ne_xT_of_ne_base`,
  `tne_of_holds`): the partial accumulators stay away from `±T`;
* the soundness folds (`gate_chain_produce`, `gateStep_chain`) and the two regime roots
  `varBaseMul_forbidden_correct` / `varBaseMul_subwrap_correct`.

The `scalarMul_shifted` headline closes the loop with proof-systems: at the real init `P 0 = 2·T`,
`N 0 = 0`, the scalar `(n : F) = 2·(N m) + 2^(5m) + 1` is verbatim `Shifted_value.Type1.to_field`
and reproduces the reference value `[1 + 2^numBits + 2·n_bits]·BasePoint` from `varbasemul.rs`'s own
test, so the circuit computes `[s]·T` for the caller's scalar `s` once it is fed the shifted scalar.

### The number-theoretic ladder kernel

The non-degeneracy of every partial accumulator reduces to a pure statement about the integer
double-and-add ladder `k 0 = 2`, `k (j + 1) = 2·k j + εⱼ` with signs `εⱼ ∈ {-1, 1}`. The degenerate
finals are not characterized by `k L + 2^L ≡ ±1 (mod q)`; they form a small band around the
multiples of `q`, on `k L` itself. A degenerate input `k j` propagates forward through `d = L − j`
doublings to `k L = 2^d·k j + T` with `|T| ≤ 2^d − 1`; a size argument confines degeneracy to the
top three inputs (`d ≤ 3`), so every reachable degenerate final satisfies `k L ≡ t (mod q)` for some
`|t| ≤ 15`. For a prime `q ≡ 1 (mod 4)` the band shrinks to the eleven explicit residues
`forbiddenResidues = {0, ±1, ±2, ±3, 5, 7, 9, 11}` (`ladder_nondegen_tight`). When the whole ladder
fits below the modulus (`3·2^L ≤ q`) no input is degenerate at all (`ladder_subwrap_nondegen`). The
lower regime bound `2^(L-1) < q` situates the one-wrap regime; for the real parameters `L = 255`,
`q ≈ 2^254`, the band's 31 residues are a vanishing fraction of `q`.
-/

namespace Kimchi.Gate.VarBaseMul.Ladder

/-- Lower/upper envelope of the ladder: `2^j + 1 ≤ k j ≤ 3·2^j - 1` for `j ≤ L`. -/
private lemma ladder_bounds (L : ℕ) (k ε : ℕ → ℤ) (hk0 : k 0 = 2)
    (hε : ∀ j, j < L → ε j = 1 ∨ ε j = -1)
    (hrec : ∀ j, j < L → k (j + 1) = 2 * k j + ε j) :
    ∀ j, j ≤ L → 2 ^ j + 1 ≤ k j ∧ k j ≤ 3 * 2 ^ j - 1 := by
  intro j hj
  induction' j with j ih <;> norm_num [hk0, pow_succ']
  by_cases h : j < L <;> simp_all +decide
  grind

/-- Forward-propagation bound: after `d` doubling steps the value differs from `2^d · k j`
    by at most `2^d - 1` (because each step adds `ε ∈ {-1, 1}`). -/
private lemma ladder_step (L : ℕ) (k ε : ℕ → ℤ)
    (hε : ∀ j, j < L → ε j = 1 ∨ ε j = -1)
    (hrec : ∀ j, j < L → k (j + 1) = 2 * k j + ε j) :
    ∀ d j, j + d ≤ L → |k (j + d) - 2 ^ d * k j| ≤ 2 ^ d - 1 := by
  intro d j hjL
  induction d <;> simp_all +decide [pow_succ']
  grind +qlia

/-- Non-degeneracy of the "deep" inputs (`d = L - j ≥ 4`) by a pure size argument:
    `k j` and `2·k j` are then strictly between `1` and `q - 1`. -/
private lemma ladder_size (q L : ℕ) (k ε : ℕ → ℤ) (hk0 : k 0 = 2)
    (hreg₁ : 2 ^ (L - 1) < q)
    (hε : ∀ j, j < L → ε j = 1 ∨ ε j = -1)
    (hrec : ∀ j, j < L → k (j + 1) = 2 * k j + ε j) :
    ∀ j, j + 4 ≤ L → ¬ (q : ℤ) ∣ (k j - 1) ∧ ¬ (q : ℤ) ∣ (k j + 1)
                ∧ ¬ (q : ℤ) ∣ (2 * k j - 1) ∧ ¬ (q : ℤ) ∣ (2 * k j + 1) := by
  intro j hj
  have h_bounds : 2 ^ j + 1 ≤ k j ∧ k j ≤ 3 * 2 ^ j - 1 :=
    ladder_bounds L k ε hk0 hε hrec j (by linarith)
  -- From `hreg₁`, we have `8 * 2^(L - 4) < q`.
  have h_q_bound : 8 * 2 ^ (L - 4) < q := by
    rcases L with (_ | _ | _ | _ | L) <;> simp_all +decide [pow_succ']
    linarith
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intro h <;>
    have := Int.le_of_dvd (by linarith [pow_pos (zero_lt_two' ℤ) j]) h <;>
    nlinarith [pow_pos (zero_lt_two' ℤ) j,
      pow_le_pow_right₀ (by decide : 1 ≤ 2) (show j ≤ L - 4 by omega)]

/-- Every accumulator after the first step is odd (each step adds `ε ∈ {-1,1}`). -/
private lemma ladder_odd (L : ℕ) (k ε : ℕ → ℤ)
    (hε : ∀ j, j < L → ε j = 1 ∨ ε j = -1)
    (hrec : ∀ j, j < L → k (j + 1) = 2 * k j + ε j) :
    ∀ j, 1 ≤ j → j ≤ L → Odd (k j) := by
  intro j hj₁ hj₂;
  induction' j with j ih;
  · contradiction;
  · grind +splitImp

/-- The exact forbidden scalar residues for the Pasta VarBaseMul gate (verified by
    exhaustive computation, and identical for both Pasta scalar fields): the small
    scalars whose double-and-add drives the accumulator onto `±T` in the final
    doublings. For ANY prime `q ≡ 1 (mod 4)` in the one-wrap regime, the actual
    reachable degenerate set is a subset of these, so excluding them is sound; for the
    Pasta primes it is exactly this set. -/
private def forbiddenResidues : List ℤ := [0, 1, -1, 2, -2, 3, -3, 5, 7, 9, 11]

/-- Depth-1 input (`L = j + 1`): every degeneracy branch lands on a forbidden residue. -/
private lemma degen_d1 (q L : ℕ)
    (k ε : ℕ → ℤ)
    (hε : ∀ j, j < L → ε j = 1 ∨ ε j = -1)
    (hrec : ∀ j, j < L → k (j + 1) = 2 * k j + ε j) (j : ℕ) (hj : j < L) (hL : L = j + 1)
    (hdeg : (q : ℤ) ∣ (k j - 1) ∨ (q : ℤ) ∣ (k j + 1) ∨ (q : ℤ) ∣ (2 * k j - 1)
              ∨ (q : ℤ) ∣ (2 * k j + 1)) :
    ∃ t ∈ forbiddenResidues, (q : ℤ) ∣ (k L - t) := by
  obtain h | h | h | h := hdeg;
  · rcases hε j hj with ( hε | hε ) <;> simp_all +decide;
    · exact ⟨ 3, by decide, by convert h.mul_left 2 using 1; ring ⟩;
    · exact ⟨ 1, by decide, by convert h.mul_left 2 using 1; ring ⟩;
  · rcases hε j hj with ( hε | hε ) <;> simp_all +decide;
    · exact ⟨ -1, by decide, by convert h.mul_left 2 using 1; ring ⟩;
    · exact ⟨ -3, by decide, by convert h.mul_left 2 using 1; ring ⟩;
  · rcases hε j hj with ( hε | hε ) <;> simp_all +decide;
    · exact ⟨ 2, by decide, by convert h using 1; ring ⟩;
    · exact ⟨ 0, by decide, by simpa using h ⟩;
  · cases hε j hj <;> simp_all +decide;
    · exact ⟨ 0, by decide, by simpa using h ⟩;
    · exact ⟨ -2, by decide, by convert h using 1; ring ⟩

/-- Depth-2 input (`L = j + 2`). Branches `q∣(k j-1)` and `q∣(2 k j-1)` land on forbidden
    residues; `q∣(k j+1)` is impossible by parity+size; `q∣(2 k j+1)` is impossible by
    `q ≡ 1 (mod 4)`. -/
private lemma degen_d2 (q L : ℕ) (hq4 : q % 4 = 1)
    (hreg₁ : 2 ^ (L - 1) < q) (hreg₂ : q < 2 ^ L)
    (k ε : ℕ → ℤ) (hk0 : k 0 = 2)
    (hε : ∀ j, j < L → ε j = 1 ∨ ε j = -1)
    (hrec : ∀ j, j < L → k (j + 1) = 2 * k j + ε j) (j : ℕ) (hj : j < L) (hL : L = j + 2)
    (hdeg : (q : ℤ) ∣ (k j - 1) ∨ (q : ℤ) ∣ (k j + 1) ∨ (q : ℤ) ∣ (2 * k j - 1)
              ∨ (q : ℤ) ∣ (2 * k j + 1)) :
    ∃ t ∈ forbiddenResidues, (q : ℤ) ∣ (k L - t) := by
  obtain h | h | h | h := hdeg;
  · rcases hε j hj with ha | ha <;>
      rcases hε ( j + 1 ) ( by linarith ) with hb | hb <;> simp_all +decide;
    · exact ⟨ 7, by decide, by convert h.mul_left 4 using 1; ring ⟩;
    · use 5;
      exact ⟨ by decide, by convert h.mul_left 4 using 1; ring ⟩;
    · exact ⟨ 3, by decide, by convert h.mul_left 4 using 1; ring ⟩;
    · exact ⟨ 1, by decide, by convert h.mul_left 4 using 1; ring ⟩;
  · -- From hb, `0 < k j + 1 ≤ 3*2^j` and `2*q > 4*2^j > 3*2^j`, so `0 < k j + 1 < 2*q`;
    -- `Int.le_of_dvd` forces `k j + 1 = q` (the only positive multiple below `2q`).
    have h_eq_q : k j + 1 = q := by
      have h_eq_q : 0 < k j + 1 ∧ k j + 1 < 2 * q := by
        have h_bound : 0 < k j + 1 ∧ k j + 1 ≤ 3 * 2 ^ j := by
          have := ladder_bounds L k ε hk0 hε hrec j ( by linarith )
          norm_num at * ; constructor <;> linarith;
        simp_all +decide [ pow_succ' ];
        linarith;
      obtain ⟨ a, ha ⟩ := h; nlinarith [ show a = 1 by nlinarith ] ;
    obtain ⟨ m, hm ⟩ := ladder_odd L k ε hε hrec j ( by
      grind ) ( by
      grind );
    omega;
  · -- `q ∣ 2 * k j - 1` propagates to `q ∣ k L - t` for some `t ∈ forbiddenResidues`.
    have h_div : (q : ℤ) ∣ k L - (2 * ε j + ε (j + 1) + 2) := by
      convert h.mul_left 2 using 1
      rw [ hL, hrec _ ( by linarith ), hrec _ ( by linarith ) ] ; ring;
    cases hε j hj <;> cases hε ( j + 1 ) ( by linarith ) <;>
      simp_all +decide only [forbiddenResidues];
    · exact ⟨ 5, by decide, h_div ⟩;
    · exact ⟨ 3, by decide, h_div ⟩;
    · exact ⟨ 1, by decide, h_div ⟩;
    · exact ⟨ _, by decide, h_div ⟩;
  · -- `2 k j + 1` is odd and `0 < 2 k j + 1 < 3q`; writing `2 k j + 1 = q * c`, the range
    -- gives `c ∈ {1,2}`, and `c = 2` is even, so `c = 1`, i.e. `2 k j + 1 = q`.
    obtain ⟨c, hc⟩ := h
    have hc_val : c = 1 := by
      have hc_val : c = 1 ∨ c = 2 := by
        have hc_val : 0 < c ∧ c < 3 := by
          have hc_bounds : 0 < 2 * k j + 1 ∧ 2 * k j + 1 < 3 * q := by
            have := ladder_bounds L k ε hk0 hε hrec j ( by linarith )
            simp_all +decide [ pow_succ' ]
            constructor <;> linarith [ pow_pos ( zero_lt_two' ℤ ) j ];
          have hq2 : 2 ≤ q := by
            have h1 := Nat.one_le_pow (L - 1) 2 (by norm_num)
            omega
          constructor <;> nlinarith only [ hc, hc_bounds, hq2 ];
        cases hc_val ; interval_cases c <;> trivial;
      grind +qlia;
    obtain ⟨ m, hm ⟩ := ladder_odd L k ε hε hrec j ( by
      grind +qlia ) ( by
      linarith );
    grind

/-- Depth-3 input (`L = j + 3`). Branch `q∣(2 k j-1)` lands on a forbidden residue;
    `q∣(k j±1)` are impossible by size; `q∣(2 k j+1)` is impossible by `q ≡ 1 (mod 4)`
    (or, when `j = 0`, forces `q = 5`, where forbiddenResidues covers every residue). -/
private lemma degen_d3 (q L : ℕ) (hq : Nat.Prime q) (hq4 : q % 4 = 1)
    (hreg₁ : 2 ^ (L - 1) < q) (hreg₂ : q < 2 ^ L)
    (k ε : ℕ → ℤ) (hk0 : k 0 = 2)
    (hε : ∀ j, j < L → ε j = 1 ∨ ε j = -1)
    (hrec : ∀ j, j < L → k (j + 1) = 2 * k j + ε j) (j : ℕ) (hj : j < L) (hL : L = j + 3)
    (hdeg : (q : ℤ) ∣ (k j - 1) ∨ (q : ℤ) ∣ (k j + 1) ∨ (q : ℤ) ∣ (2 * k j - 1)
              ∨ (q : ℤ) ∣ (2 * k j + 1)) :
    ∃ t ∈ forbiddenResidues, (q : ℤ) ∣ (k L - t) := by
  rcases j with ( _ | j ) <;> simp_all +decide;
  · interval_cases q <;> simp_all +decide;
    rcases hε 0 ( by decide ) with ha | ha <;>
      rcases hε 1 ( by decide ) with hb | hb <;>
      rcases hε 2 ( by decide ) with hc | hc <;> simp +decide only [ha, hb, hc];
  · rcases hdeg with ( h | h | h | h );
    · have h_bounds : 2 ^ (j + 1) + 1 ≤ k (j + 1) ∧ k (j + 1) ≤ 3 * 2 ^ (j + 1) - 1 := by
        apply ladder_bounds (j + 3) k ε hk0 (fun j hj => hε j (by linarith))
          (fun j hj => hrec j (by linarith)) (j + 1) (by linarith);
      nlinarith [ Int.le_of_dvd ( by linarith [ pow_pos ( zero_lt_two' ℤ ) ( j + 1 ) ] ) h,
        pow_succ' ( 2 : ℤ ) j, pow_succ' ( 2 : ℤ ) ( j + 1 ), pow_succ' ( 2 : ℤ ) ( j + 2 ),
        pow_succ' ( 2 : ℤ ) ( j + 3 ) ];
    · obtain ⟨ m, hm ⟩ := h;
      have h_bounds : 2 ^ (j + 1) + 1 ≤ k (j + 1) ∧ k (j + 1) ≤ 3 * 2 ^ (j + 1) - 1 := by
        apply ladder_bounds (j + 3) k ε hk0 (fun j hj => hε j (by linarith))
          (fun j hj => hrec j (by linarith)) (j + 1) (by linarith);
      rcases lt_trichotomy m 0 with hm' | rfl | hm' <;> norm_num [ pow_succ' ] at * <;> nlinarith;
    · obtain ⟨ m, hm ⟩ := h;
      rcases hε ( j + 1 ) ( by linarith ) with ha | ha <;>
        rcases hε ( j + 2 ) ( by linarith ) with hb | hb <;>
        rcases hε ( j + 3 ) ( by linarith ) with hc | hc <;> simp_all +decide [ pow_succ' ];
      all_goals rw [ sub_eq_iff_eq_add ] at hm; norm_num [ hm, ha, hb, hc ] ; ring_nf ;
      all_goals norm_num [ forbiddenResidues ];
      all_goals norm_num [ dvd_mul_of_dvd_left ] ;
    · obtain ⟨ m, hm ⟩ := h;
      rcases lt_trichotomy m 1 with hm' | rfl | hm';
      · have h_contra : k (j + 1) ≥ 2 ^ (j + 1) + 1 := by
          apply (ladder_bounds (j + 3) k ε hk0 (fun j hj => hε j (by linarith))
            (fun j hj => hrec j (by linarith)) (j + 1) (by linarith)).left;
        nlinarith [ pow_pos ( zero_lt_two' ℤ ) ( j + 1 ), pow_succ' ( 2 : ℤ ) ( j + 1 ),
          pow_succ' ( 2 : ℤ ) ( j + 2 ), pow_succ' ( 2 : ℤ ) ( j + 3 ) ];
      · obtain ⟨ m, hm ⟩ :=
          ladder_odd ( j + 4 ) k ε hε hrec ( j + 1 ) ( by linarith ) ( by linarith )
        simp_all +decide [ parity_simps ];
        omega;
      · have := ladder_bounds ( j + 4 ) k ε hk0 ( fun i hi => hε i ( by linarith ) )
          ( fun i hi => hrec i ( by linarith ) ) ( j + 1 ) ( by linarith )
        norm_num [ pow_succ' ] at *
        nlinarith [ Int.mul_ediv_add_emod ( 2 * k ( j + 1 ) + 1 ) q,
          Int.emod_nonneg ( 2 * k ( j + 1 ) + 1 ) ( Nat.cast_ne_zero.mpr hq.ne_zero ),
          Int.emod_lt_of_pos ( 2 * k ( j + 1 ) + 1 ) ( Nat.cast_pos.mpr hq.pos ) ] ;

/-- **Core of the tight bound.** A degenerate input `k j` (`j < L`) propagates forward to
    a final value `k L ≡ t (mod q)` for some `t ∈ forbiddenResidues`. Inputs at depth
    `d = L - j ≥ 4` cannot be degenerate (`ladder_size`); for `d ≤ 3` the four degeneracy
    branches either land on an explicit forbidden residue, or are ruled out by a size /
    parity / `q ≡ 1 (mod 4)` argument. -/
private lemma degenerate_input_forces_forbidden (q L : ℕ) (hq : Nat.Prime q) (hq4 : q % 4 = 1)
    (hreg₁ : 2 ^ (L - 1) < q) (hreg₂ : q < 2 ^ L)
    (k ε : ℕ → ℤ) (hk0 : k 0 = 2)
    (hε : ∀ j, j < L → ε j = 1 ∨ ε j = -1)
    (hrec : ∀ j, j < L → k (j + 1) = 2 * k j + ε j) (j : ℕ) (hj : j < L)
    (hdeg : (q : ℤ) ∣ (k j - 1) ∨ (q : ℤ) ∣ (k j + 1) ∨ (q : ℤ) ∣ (2 * k j - 1)
              ∨ (q : ℤ) ∣ (2 * k j + 1)) :
    ∃ t ∈ forbiddenResidues, (q : ℤ) ∣ (k L - t) := by
  by_cases hsize : j + 4 ≤ L
  · exfalso
    obtain ⟨h1, h2, h3, h4⟩ := ladder_size q L k ε hk0 hreg₁ hε hrec j hsize
    rcases hdeg with h | h | h | h
    · exact h1 h
    · exact h2 h
    · exact h3 h
    · exact h4 h
  · have hcase : L = j + 1 ∨ L = j + 2 ∨ L = j + 3 := by omega
    rcases hcase with hL | hL | hL
    · exact degen_d1 q L k ε hε hrec j hj hL hdeg
    · exact degen_d2 q L hq4 hreg₁ hreg₂ k ε hk0 hε hrec j hj hL hdeg
    · exact degen_d3 q L hq hq4 hreg₁ hreg₂ k ε hk0 hε hrec j hj hL hdeg

/-- **Tight (exact-set) form.** The same double-and-add ladder, but for a prime
    `q ≡ 1 (mod 4)` the forbidden set shrinks from the `[-15,15]` band to the explicit
    11 residues `forbiddenResidues = {0, ±1, ±2, ±3, 5, 7, 9, 11}`. The `q ≡ 1 (mod 4)`
    hypothesis closes the `2·k ≡ -1` degeneracy branch (`(q-1)/2` is even, so it is not a
    reachable odd accumulator at the deep inputs), which is what would otherwise add the
    residues `-5, -7, -9, -11`. If `s = k L` avoids these 11 residues, every input
    `k j` (`j < L`) is non-degenerate. -/
private theorem ladder_nondegen_tight (q L : ℕ) (hq : Nat.Prime q) (hq4 : q % 4 = 1)
    (hreg₁ : 2 ^ (L - 1) < q) (hreg₂ : q < 2 ^ L)
    (k ε : ℕ → ℤ) (hk0 : k 0 = 2)
    (hε : ∀ j, j < L → ε j = 1 ∨ ε j = -1)
    (hrec : ∀ j, j < L → k (j + 1) = 2 * k j + ε j)
    (hnf : ∀ t ∈ forbiddenResidues, ¬ (q : ℤ) ∣ (k L - t)) :
    ∀ j, j < L → ¬ (q : ℤ) ∣ (k j - 1) ∧ ¬ (q : ℤ) ∣ (k j + 1)
                ∧ ¬ (q : ℤ) ∣ (2 * k j - 1) ∧ ¬ (q : ℤ) ∣ (2 * k j + 1) := by
  intro j hj
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intro hdvd <;>
    obtain ⟨t, ht, htd⟩ :=
      degenerate_input_forces_forbidden q L hq hq4 hreg₁ hreg₂ k ε hk0 hε hrec j hj
        (by tauto) <;>
    exact hnf t ht htd

/-- **Sub-wrap non-degeneracy.** When the whole ladder fits below the modulus (`3·2^L ≤ q`), every
    input is non-degenerate *unconditionally* — no primality, no `q ≡ 1 (mod 4)`, no forbidden set.
    The envelope `2^j + 1 ≤ k j ≤ 3·2^j - 1` (`ladder_bounds`) places each of `k j ± 1` and
    `2·k j ± 1` strictly inside `(0, q)`, so none can be a multiple of `q`. This is the small-`L`
    regime (`5m ≤ bitlength(order) - 1`), where the scalar is too small to ever drive an
    accumulator onto `±T`, so the gate is safe with no guard at all. -/
private lemma ladder_subwrap_nondegen (q L : ℕ) (hsub : 3 * 2 ^ L ≤ q)
    (k ε : ℕ → ℤ) (hk0 : k 0 = 2)
    (hε : ∀ j, j < L → ε j = 1 ∨ ε j = -1)
    (hrec : ∀ j, j < L → k (j + 1) = 2 * k j + ε j) :
    ∀ j, j < L → ¬ (q : ℤ) ∣ (k j - 1) ∧ ¬ (q : ℤ) ∣ (k j + 1)
                ∧ ¬ (q : ℤ) ∣ (2 * k j - 1) ∧ ¬ (q : ℤ) ∣ (2 * k j + 1) := by
  intro j hj
  obtain ⟨hlo, hhi⟩ := ladder_bounds L k ε hk0 hε hrec j hj.le
  have hjpos : (0 : ℤ) < 2 ^ j := by positivity
  have hps : (2 : ℤ) ^ (j + 1) = 2 * 2 ^ j := by rw [pow_succ]; ring
  have hpow : (2 : ℤ) ^ (j + 1) ≤ 2 ^ L := pow_le_pow_right₀ (by norm_num) (by omega)
  have hqz : (3 : ℤ) * 2 ^ L ≤ (q : ℤ) := by exact_mod_cast hsub
  -- `6·2^j = 3·2^(j+1) ≤ 3·2^L ≤ q`, so every value below is `< q`.
  have h6 : 6 * 2 ^ j ≤ (q : ℤ) := by linarith
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intro hdvd <;>
    have hle := Int.le_of_dvd (by nlinarith [hlo, hjpos]) hdvd <;>
    nlinarith [hhi, h6, hle, hjpos, hlo]

/--
**x-condition non-degeneracy from the register/magnitude bound** (pure number theory,
    orthogonal to the t-condition `tne_of_holds`). The deployed circuit's register is a
    valid field element `< baseFieldOrder`, so the ladder top is bounded:
    `k L < 2·baseFieldOrder + 2^L`. The only x-condition accumulator values are
    `k ≡ ±1 (mod order)`, whose smallest ODD representatives are `2·order ± 1` (the even
    reps `order ± 1` are unreachable since every `k j` with `1 ≤ j` is odd, `ladder_odd`).
    The regime `baseFieldOrder + 2^(L-1) < 2·order` (the Pasta `2δ > δ'` fact) puts those
    above the bounded range, so no INPUT `k j` (`j < L`) is `≡ ±1 (mod order)` — i.e. no
    accumulator equals `±T`. (No constraints, no curve, no forbidden set.)

    ## Why each side condition is needed

    Each of the three hypotheses is necessary — without it a concrete degenerate input exists:

    * `hodd : Odd order` — when `order` is even the even representatives `order ± 1` of
      `±1 (mod order)` are reachable. With `ladder_odd` (every `k j`, `1 ≤ j`, is odd)
      it rules out the even reps and forces the odd reps `2·order ± 1`. The real `order`
      is prime, hence odd.
    * `hbound : baseFieldOrder + 2^(L-1) + 2 ≤ 2·order` — for `j = L - 1` the `+1` branch
      (`k (L-1) = 2·order - 1`) gives `k L = 4·order - 2 + ε ≥ 4·order - 3`, which the
      slacker bound `baseFieldOrder + 2^(L-1) < 2·order` (`k L < 4·order - 2`) fails to
      exclude (e.g. `order = 5, baseFieldOrder = 5, L = 3`); tightening the slack by `2`
      (`k L < 4·order - 4`) closes it.
    * `horder : 3 < order` — for `order = 3, L = 2` the input `k 0 = 2` satisfies
      `order ∣ (k 0 + 1) = 3`.

    All three hold comfortably for the real Pasta parameters (`L = 255`,
    `order ≈ 2^254 + 4.56·10^37` a large prime, `2δ > δ'`).
-/
private theorem ladder_x_nondegen (order baseFieldOrder L : ℕ)
    (hreg₁ : 2 ^ (L - 1) < order)
    (hodd : Odd order) (horder : 3 < order)
    (hbound : baseFieldOrder + 2 ^ (L - 1) + 2 ≤ 2 * order)
    (k ε : ℕ → ℤ) (hk0 : k 0 = 2)
    (hε : ∀ j, j < L → ε j = 1 ∨ ε j = -1)
    (hrec : ∀ j, j < L → k (j + 1) = 2 * k j + ε j)
    (hkL : k L < 2 * (baseFieldOrder : ℤ) + 2 ^ L) :
    ∀ j, j < L → ¬ (order : ℤ) ∣ (k j - 1) ∧ ¬ (order : ℤ) ∣ (k j + 1) := by
  -- From `ladder_bounds`, `2^j + 1 ≤ k j` and `k j ≤ 3 * 2^j - 1` for all `j < L`.
  intros j hj
  have h_bounds : 2 ^ j + 1 ≤ k j ∧ k j ≤ 3 * 2 ^ j - 1 :=
    ladder_bounds L k ε hk0 hε hrec j (by linarith)
  constructor <;> intro h <;> obtain ⟨t, ht⟩ := h
  · rcases lt_trichotomy t 1 with ht' | rfl | ht' <;>
      try nlinarith [pow_pos (zero_lt_two' ℤ) j]
    · obtain ⟨m, hm⟩ := hodd
      simp_all +decide [parity_simps]
      rcases j with (_ | j) <;> simp_all +decide [pow_succ']
      grind
    · -- Propagate forward: `k L ≥ 2^(L-j) * k j - (2^(L-j) - 1)`.
      have h_step : k L ≥ 2 ^ (L - j) * k j - (2 ^ (L - j) - 1) := by
        have h_step : |k L - 2 ^ (L - j) * k j| ≤ 2 ^ (L - j) - 1 := by
          convert ladder_step L k ε hε hrec (L - j) j (by omega) using 1
          simp +decide [Nat.add_sub_of_le hj.le]
        linarith [abs_le.mp h_step]
      rcases L with (_ | L) <;> simp_all +decide [pow_succ']
      nlinarith [pow_pos (zero_lt_two' ℤ) (L + 1 - j),
        pow_le_pow_right₀ (by decide : 1 ≤ 2)
          (show L + 1 - j ≥ 1 from Nat.sub_pos_of_lt (by linarith))]
  · rcases t with ⟨_ | _ | _ | t⟩ <;> norm_num at ht
    · linarith [pow_pos (zero_lt_two' ℤ) j]
    · obtain ⟨m, hm⟩ := hodd
      simp_all +decide [parity_simps]
      exact absurd
        (ladder_odd L k ε hε hrec j (Nat.pos_of_ne_zero (by rintro rfl; linarith))
          (by linarith))
        (by norm_num [ht, parity_simps])
    · -- Propagate forward: `k L ≥ 2^(L-j) * k j - (2^(L-j) - 1)`.
      have h_step : k L ≥ 2 ^ (L - j) * k j - (2 ^ (L - j) - 1) := by
        have := ladder_step L k ε hε hrec (L - j) j (by omega)
        simp_all +decide [Nat.add_sub_of_le hj.le]
        linarith [abs_lt.mp this]
      rcases L with (_ | L) <;> simp_all +decide [pow_succ']
      nlinarith [pow_pos (zero_lt_two' ℤ) j,
        pow_le_pow_right₀ (by decide : 1 ≤ 2) hj,
        pow_pos (zero_lt_two' ℤ) (L + 1 - j),
        pow_le_pow_right₀ (by decide : 1 ≤ 2)
          (show L + 1 - j ≥ 1 from Nat.sub_pos_of_lt (by linarith))]
    · nlinarith [pow_pos (zero_lt_two' ℤ) j,
        pow_le_pow_right₀ (show 1 ≤ 2 by decide)
          (show j ≤ L - 1 from Nat.le_sub_one_of_lt hj)]
    · grind

end Kimchi.Gate.VarBaseMul.Ladder

namespace Kimchi.Gate.VarBaseMul

open Kimchi.Gate.VarBaseMul WeierstrassCurve.Affine Pasta.Shifted

variable {F : Type*} [Field F] [DecidableEq F]

/-- Chaining the per-gate relation `P_{i+1} = 32·P_i + cᵢ·T` over `m` gates gives
    the closed-form scalar multiple

        P_m = 32^m·P₀ + (∑_{i<m} 32^(m-1-i)·cᵢ)·T

    — i.e. `m` chained `VarBaseMul` gates compute variable-base scalar
    multiplication by the `5m`-bit scalar `k = ∑_{i<m} 32^(m-1-i)·cᵢ` (plus the
    carried `32^m·P₀`). The per-gate relation is supplied by `sound`
    after folding its `Qⱼ` points into `±T` via booleanity. -/
private theorem chain_scalarMul
    (W : WeierstrassCurve.Affine F)
    (m : ℕ) (P : ℕ → W.Point) (T : W.Point) (c : ℕ → ℤ)
    (hstep : ∀ i, i < m → P (i + 1) = (32 : ℤ) • P i + c i • T) :
    P m = (32 : ℤ) ^ m • P 0
        + (∑ i ∈ Finset.range m, (32 : ℤ) ^ (m - 1 - i) * c i) • T := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hs : P (m + 1) = (32 : ℤ) • P m + c m • T := hstep m (Nat.lt_succ_self m)
    have ih' := ih (fun i hi => hstep i (Nat.lt_succ_of_lt hi))
    have hsum : (∑ i ∈ Finset.range (m + 1), (32 : ℤ) ^ (m + 1 - 1 - i) * c i)
        = (32 : ℤ) * (∑ i ∈ Finset.range m, (32 : ℤ) ^ (m - 1 - i) * c i) + c m := by
      rw [Finset.sum_range_succ, Finset.mul_sum]
      simp only [Nat.add_sub_cancel, Nat.sub_self, pow_zero, one_mul]
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      have hi' : m - i = (m - 1 - i) + 1 := by
        have := Finset.mem_range.mp hi; omega
      rw [hi', pow_succ]
      ring
    rw [hs, ih', hsum, smul_add, smul_smul, smul_smul, add_smul, pow_succ']
    abel

omit [DecidableEq F] in
/-- The scalar-register companion to `chain_scalarMul`: if each step's integer
    contribution `c i` matches the register transition `N i → N (i+1)` by
    `(c i : F) = 2·N (i+1) − 64·N i − 31`, then the folded scalar
    `k = ∑ 32^(m-1-i)·c i` satisfies `(k : F) = 2·N m − 2·32^m·N 0 − (32^m − 1)`.
    (The `−31`s sum to `−(32^m−1)`; the register terms telescope.) -/
private theorem chain_register (m : ℕ) (N : ℕ → F) (c : ℕ → ℤ)
    (hstep : ∀ i, i < m → (c i : F) = 2 * N (i + 1) - 64 * N i - 31) :
    ((∑ i ∈ Finset.range m, (32 : ℤ) ^ (m - 1 - i) * c i : ℤ) : F)
      = 2 * N m - 2 * (32 : F) ^ m * N 0 - ((32 : F) ^ m - 1) := by
  induction' m with m ih <;> simp_all +decide [pow_succ', Finset.sum_range_succ]
  convert congr_arg (fun x : F => 32 * x + (2 * N (m + 1) - 64 * N m - 31))
    (ih fun i hi => hstep i hi.le) using 1
  · rw [Finset.mul_sum _ _ _]
    refine congr_arg₂ _ (Finset.sum_congr rfl fun i hi => ?_) rfl
    rw [← mul_assoc, ← pow_succ', tsub_right_comm,
      Nat.sub_add_cancel (Nat.succ_le_of_lt (Nat.sub_pos_of_lt (Finset.mem_range.mp hi)))]
  · ring

/-- Magnitude bound on the folded signed-digit multiplier. If each per-gate digit
    `c i` has `|c i| ≤ 31`, then the accumulated scalar
    `k = ∑_{i<m} 32^(m-1-i)·c i` satisfies `|k| ≤ 32^m − 1`. (Induction: the
    recurrence `k_{m+1} = 32·k_m + c m` and `32·(32^m−1) + 31 = 32^(m+1)−1`.) -/
private theorem chain_sum_bound (m : ℕ) (c : ℕ → ℤ) (hc : ∀ i, i < m → (c i).natAbs ≤ 31) :
    (∑ i ∈ Finset.range m, (32 : ℤ) ^ (m - 1 - i) * c i).natAbs ≤ 32 ^ m - 1 := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hsum : (∑ i ∈ Finset.range (m + 1), (32 : ℤ) ^ (m + 1 - 1 - i) * c i)
        = (32 : ℤ) * (∑ i ∈ Finset.range m, (32 : ℤ) ^ (m - 1 - i) * c i) + c m := by
      rw [Finset.sum_range_succ, Finset.mul_sum]
      simp only [Nat.add_sub_cancel, Nat.sub_self, pow_zero, one_mul]
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      have hi' : m - i = (m - 1 - i) + 1 := by
        have := Finset.mem_range.mp hi; omega
      rw [hi', pow_succ]
      ring
    rw [hsum]
    have ihb := ih (fun i hi => hc i (Nat.lt_succ_of_lt hi))
    have hcm := hc m (Nat.lt_succ_self m)
    set S := ∑ i ∈ Finset.range m, (32 : ℤ) ^ (m - 1 - i) * c i with hS
    have key : (32 * S + c m).natAbs ≤ 32 * S.natAbs + (c m).natAbs := by
      calc (32 * S + c m).natAbs
          ≤ (32 * S).natAbs + (c m).natAbs := Int.natAbs_add_le _ _
        _ = 32 * S.natAbs + (c m).natAbs := by rw [Int.natAbs_mul]; norm_num
    have h1 : (1 : ℕ) ≤ 32 ^ m := Nat.one_le_pow _ _ (by norm_num)
    have hps : 32 ^ (m + 1) = 32 * 32 ^ m := by rw [pow_succ]; ring
    omega

/-- The per-gate NON-DEGENERACY side conditions: the additions are non-vertical
    (`xⱼ ≠ xT`) and the second additions are non-vertical (`tⱼ ≠ 0`). For the kimchi
    VarBaseMul gate these are exactly what the deployed guards (`scaleFast1`'s forbidden-value
    check, `scaleFast2`'s register range-check) are supposed to secure for ANY satisfying
    witness (their soundness). -/
private structure NonDegen (g : Witness F) : Prop where
  x0 : g.x0 ≠ g.xT
  x1 : g.x1 ≠ g.xT
  x2 : g.x2 ≠ g.xT
  x3 : g.x3 ≠ g.xT
  x4 : g.x4 ≠ g.xT
  t0 : 2 * g.x0 + g.xT - g.s0 * g.s0 ≠ 0
  t1 : 2 * g.x1 + g.xT - g.s1 * g.s1 ≠ 0
  t2 : 2 * g.x2 + g.xT - g.s2 * g.s2 ≠ 0
  t3 : 2 * g.x3 + g.xT - g.s3 * g.s3 ≠ 0
  t4 : 2 * g.x4 + g.xT - g.s4 * g.s4 ≠ 0

/-- A full per-gate step: the nonsingular accumulator points `a0..a5`, the base `hT`, the gate
    constraints `holds`, and the `NonDegen` side conditions, in one flat bundle. The register
    subsystem `scalarMul` / `scalarMul_type2` consumes all of these via the gate `sound`. The
    deployed entry points derive a `GateStep` per row from `Holds` plus threading, via
    `gateStep_chain`. -/
private structure GateStep (W : WeierstrassCurve.Affine F) (g : Witness F) : Prop where
  a0 : W.Nonsingular g.x0 g.y0
  a1 : W.Nonsingular g.x1 g.y1
  a2 : W.Nonsingular g.x2 g.y2
  a3 : W.Nonsingular g.x3 g.y3
  a4 : W.Nonsingular g.x4 g.y4
  a5 : W.Nonsingular g.x5 g.y5
  hT : W.Nonsingular g.xT g.yT
  holds : Holds g
  x0 : g.x0 ≠ g.xT
  x1 : g.x1 ≠ g.xT
  x2 : g.x2 ≠ g.xT
  x3 : g.x3 ≠ g.xT
  x4 : g.x4 ≠ g.xT
  t0 : 2 * g.x0 + g.xT - g.s0 * g.s0 ≠ 0
  t1 : 2 * g.x1 + g.xT - g.s1 * g.s1 ≠ 0
  t2 : 2 * g.x2 + g.xT - g.s2 * g.s2 ≠ 0
  t3 : 2 * g.x3 + g.xT - g.s3 * g.s3 ≠ 0
  t4 : 2 * g.x4 + g.xT - g.s4 * g.s4 ≠ 0

/-! ## Main theorem: variable-base scalar multiplication -/

/-- A run of `m` `varBaseMul` rows realizing the point sequence `P` and the register
    sequence `N`: every row is a gate step, every row reads the base `T`, and each row's
    input/output accumulators are `P i` / `P (i + 1)` with registers `N i` / `N (i + 1)`.
    Unlike `EndoScalar`'s chain the linkage is stated against those sequences rather than
    between adjacent rows — the ladder's induction is over them. -/
private structure Chain (W : WeierstrassCurve.Affine F) (g : ℕ → Witness F) (m : ℕ)
    (T : W.Point) (P : ℕ → W.Point) (N : ℕ → F) : Prop where
  /-- Every row of the run is a gate step. -/
  steps : ∀ i, i < m → GateStep W (g i)
  /-- Every row reads the base point. -/
  base : ∀ i (hi : i < m), T = Point.some _ _ (steps i hi).hT
  /-- Row `i` opens at `P i`. -/
  inPt : ∀ i (hi : i < m), P i = Point.some _ _ (steps i hi).a0
  /-- Row `i` closes at `P (i + 1)`. -/
  outPt : ∀ i (hi : i < m), P (i + 1) = Point.some _ _ (steps i hi).a5
  /-- Row `i` opens at register `N i`. -/
  regIn : ∀ i, i < m → N i = (g i).n
  /-- Row `i` closes at register `N (i + 1)`. -/
  regOut : ∀ i, i < m → N (i + 1) = (g i).nPrime

/-- The computation the circuit provides. `m` chained `VarBaseMul` gates over a
    shared target `T`, threading BOTH the accumulator points `P` (gate `i`'s input
    `P i`, output `P (i+1)`) AND the scalar register `N` (input `N i = (g i).n`,
    output `N (i+1) = (g i).nPrime`), compute

        P m = 32^m·P₀ + k·T   with   (k : F) = 2·N m − 2·32^m·N 0 − (32^m − 1),

    i.e. the output point is the carried `32^m·P₀` plus `k·T`, where the integer
    scalar `k` is pinned to what the scalar register computed (`N 0 → N m`) — in
    signed-digit form. The proof folds the point chain with `chain_scalarMul` and
    the register chain with `chain_register`, both fed by the gate's
    `sound`. -/
private theorem scalarMul
    (W : WeierstrassCurve.Affine F) (ha : W.a₁ = 0 ∧ W.a₂ = 0 ∧ W.a₃ = 0)
    (m : ℕ) (g : ℕ → Witness F)
    (P : ℕ → W.Point) (T : W.Point) (N : ℕ → F) (hrun : Chain W g m T P N) :
    ∃ k : ℤ, P m = (32 : ℤ) ^ m • P 0 + k • T
           ∧ (k : F) = 2 * N m - 2 * (32 : F) ^ m * N 0 - ((32 : F) ^ m - 1)
           ∧ k.natAbs ≤ 32 ^ m - 1 := by
  have ⟨gs, hT, hin, hout, hregIn, hregOut⟩ := hrun
  obtain ⟨c, hc₁, hc₂, hc₃⟩ :
      ∃ c : ℕ → ℤ, (∀ i < m, P (i + 1) = (32 : ℤ) • P i + c i • T)
        ∧ (∀ i < m, (c i : F) = 2 * N (i + 1) - 64 * N i - 31)
        ∧ (∀ i < m, (c i).natAbs ≤ 31) := by
    choose! c hc₁ hc₂ hc₃ using fun i hi => sound W ha (g i)
      (gs i hi).a0 (gs i hi).a1 (gs i hi).a2 (gs i hi).a3 (gs i hi).a4 (gs i hi).a5
      (gs i hi).hT
      (gs i hi).x0 (gs i hi).x1 (gs i hi).x2 (gs i hi).x3 (gs i hi).x4
      (gs i hi).t0 (gs i hi).t1 (gs i hi).t2 (gs i hi).t3 (gs i hi).t4 (gs i hi).holds
    refine ⟨c, ?_, ?_, ?_⟩ <;> intros i hi <;> simp_all +decide only
    rw [hT i hi]
  refine ⟨∑ i ∈ Finset.range m, (32 : ℤ) ^ (m - 1 - i) * c i, ?_, ?_, ?_⟩
  · exact chain_scalarMul W m P T c hc₁
  · exact chain_register m N c hc₂
  · exact chain_sum_bound m c hc₃

/-- Clean variable-base scalar multiplication. When the accumulator is
    initialized to a multiple of the base (`P 0 = a · T`, `a : ℤ` — the circuit
    inits to `[2]T`), the carried `32^m·P₀` term is absorbed and the output is a
    SINGLE scalar multiple of the base:

        P m = n · T   for an explicit integer `n`,

    with `(n : F) = 32^m·a + 2·N m − 2·32^m·N 0 − (32^m − 1)`. So `m` chained
    `VarBaseMul` gates compute `[n]·T`: variable-base scalar multiplication of the
    base point `T`, the scalar `n` determined by the init `a` and the scalar
    register (`N 0 → N m`), in signed-digit form. -/
private theorem scalarMul_baseMul
    (W : WeierstrassCurve.Affine F) (ha : W.a₁ = 0 ∧ W.a₂ = 0 ∧ W.a₃ = 0)
    (m : ℕ) (g : ℕ → Witness F)
    (T : W.Point) (N : ℕ → F) (a : ℤ) (P : ℕ → W.Point) (hrun : Chain W g m T P N)
    (hP0 : P 0 = a • T) :
    ∃ n : ℤ, P m = n • T
           ∧ (n : F) = (32 : F) ^ m * (a : F) + 2 * N m
                        - 2 * (32 : F) ^ m * N 0 - ((32 : F) ^ m - 1)
           ∧ n.natAbs ≤ 32 ^ m * a.natAbs + (32 ^ m - 1) := by
  have ⟨gs, hT, hin, hout, hregIn, hregOut⟩ := hrun
  obtain ⟨k, hk, hkf, hkb⟩ := scalarMul W ha m g P T N hrun
  refine ⟨(32 : ℤ) ^ m * a + k, ?_, ?_, ?_⟩
  · rw [hk, hP0, smul_smul, ← add_smul]
  · push_cast; rw [hkf]; ring
  · calc ((32 : ℤ) ^ m * a + k).natAbs
        ≤ ((32 : ℤ) ^ m * a).natAbs + k.natAbs := Int.natAbs_add_le _ _
      _ = 32 ^ m * a.natAbs + k.natAbs := by rw [Int.natAbs_mul, Int.natAbs_pow]; norm_num
      _ ≤ 32 ^ m * a.natAbs + (32 ^ m - 1) := by omega

/-! ## Matching the real circuit: scalar-mul by the pickles Type1 unshift -/

/-- The circuit computes `[s]·T` for the pickles-unshifted scalar `s`. At the real
    circuit's parameters — accumulator initialized to `[2]·T` (`P 0 = 2·T`) and
    scalar register started at `0` (`N 0 = 0`) — the `m` gates (processing `5m`
    bits) compute `P m = n·T` where the scalar is exactly the pickles Type1
    unshift of the final register value:

        (n : F) = unshiftType1 (5·m) (N m) = 2·(N m) + 2^(5m) + 1.

    This closes the loop: `2·t + 2^numBits + 1` is verbatim
    `Shifted_value.Type1.to_field`, and it reproduces the kimchi reference value
    `[1 + 2^numBits + 2·n_bits]·BasePoint` asserted in proof-systems
    `varbasemul.rs`'s own test. So feeding the gate the Type1-shifted scalar
    `t = shift(s)` (`N m = t`) makes it compute `[s]·T` — variable-base scalar
    multiplication by the original scalar `s`, the cross-field shift being the
    pickles `Shifted_value` contract. -/
private theorem scalarMul_shifted
    (W : WeierstrassCurve.Affine F) (ha : W.a₁ = 0 ∧ W.a₂ = 0 ∧ W.a₃ = 0)
    (m : ℕ) (g : ℕ → Witness F)
    (T : W.Point) (N : ℕ → F) (P : ℕ → W.Point) (hrun : Chain W g m T P N)
    (hP0 : P 0 = (2 : ℤ) • T) (hN0 : N 0 = 0) :
    ∃ n : ℤ, P m = n • T ∧ (n : F) = unshiftType1 (5 * m) (N m)
           ∧ n.natAbs ≤ 3 * 32 ^ m := by
  have ⟨gs, hT, hin, hout, hregIn, hregOut⟩ := hrun
  obtain ⟨n, hn, hnf, hnb⟩ :=
    scalarMul_baseMul W ha m g T N 2 P hrun hP0
  refine ⟨n, hn, ?_, ?_⟩
  · have h32 : (2 : F) ^ (5 * m) = (32 : F) ^ m := by rw [pow_mul]; norm_num
    rw [hnf, hN0, unshiftType1, h32]
    push_cast
    ring
  · -- `a = 2`, so `(2 : ℤ).natAbs = 2` and `32^m·2 + (32^m − 1) ≤ 3·32^m`.
    have h2 : (2 : ℤ).natAbs = 2 := rfl
    rw [h2] at hnb
    omega

/-! ## The Type2 caller scalar: split + the odd correction -/

/-- Type2 scalar multiplication: split + the explicit low-bit correction. The
    `VarBaseMul` chain runs on the high part (register `N m = sHi`, giving
    `P m = [2·sHi + 2^(5m) + 1]·T`); the parity bit `sOdd` (a boolean column) then
    selects the final `if sOdd then P m else P m − T`. That corrected accumulator is
    `n·T` with `(n : F) = unshiftType2 (5m) (N m) sOdd = 2·(N m) + sOdd + 2^(5m)` — the
    Type2 scalar — in both bit cases. The correction is stated on `P m` directly (no
    prover-supplied output point or correction relation). -/
private theorem scalarMul_type2
    (W : WeierstrassCurve.Affine F) (ha : W.a₁ = 0 ∧ W.a₂ = 0 ∧ W.a₃ = 0)
    (m : ℕ) (g : ℕ → Witness F)
    (T : W.Point) (N : ℕ → F) (P : ℕ → W.Point) (hrun : Chain W g m T P N)
    (hP0 : P 0 = (2 : ℤ) • T) (hN0 : N 0 = 0)
    (sOdd : F) (hsOdd : sOdd = 0 ∨ sOdd = 1) :
    ∃ n : ℤ, (n : F) = unshiftType2 (5 * m) (N m) sOdd
      ∧ ((sOdd = 1 ∧ P m = n • T) ∨ (sOdd = 0 ∧ P m - T = n • T)) := by
  have ⟨gs, hT, hin, hout, hregIn, hregOut⟩ := hrun
  obtain ⟨n, hn, hnf, _⟩ :=
    scalarMul_shifted W ha m g T N P hrun hP0 hN0
  rcases hsOdd with ho | ho
  · refine ⟨n - 1, ?_, Or.inr ⟨ho, ?_⟩⟩
    · push_cast; rw [hnf, ho, unshiftType1, unshiftType2]; ring
    · rw [hn, sub_smul, one_zsmul]
  · exact ⟨n, by rw [hnf, ho, unshiftType1, unshiftType2]; ring, Or.inl ⟨ho, hn⟩⟩

/-! ## Group-order non-degeneracy toolkit

In the point group of a short-Weierstrass curve the `order` is prime, so a nonzero point times a
scalar strictly between `0` and `order` is itself nonzero. Hence a multiple `k • T` of a nonzero
point `T`, with `k` strictly between `1` and `order − 1`, is neither `T` nor `−T`, and has a
different `x`-coordinate than `T`. These library lemmas are the mathematical core of "the partial
accumulators stay away from `±T`", consumed by the per-row non-degeneracy below. -/

/-- **Core non-degeneracy.** With prime `order`, a nonzero point times a scalar strictly
    between `0` and `order` is nonzero. -/
lemma smul_ne_zero_of_lt (c : WeierstrassCurve.Affine F)
    [Fact (c.a₁ = 0 ∧ c.a₂ = 0 ∧ c.a₃ = 0)]
    [Fact (Nat.Prime c.order)] {T : c.Point} (hT : T ≠ 0)
    {k : ℤ} (h0 : 0 < k) (hlt : k < (c.order : ℤ)) : k • T ≠ 0 := by
  intro h_contra
  -- prime `order` together with `0 < k < order` forces `gcd k order = 1`
  have h_coprime : Int.gcd k (c.order : ℤ) = 1 := by
    refine Nat.coprime_comm.mp
      ((Fact.out : Nat.Prime c.order).coprime_iff_not_dvd.mpr fun hd => ?_)
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
  have hord : (c.order : ℤ) • T = 0 := by rw [natCast_zsmul]; exact card_nsmul_eq_zero'
  rw [h_contra, hord, smul_zero, smul_zero, add_zero] at h_decomp
  exact hT h_decomp

omit [DecidableEq F] in
/-- **x-coordinate bridge.** On a short-Weierstrass curve, a point that is neither `T`
    nor `−T` has a different `x`-coordinate. -/
lemma x_ne_xT_of_ne_base (c : WeierstrassCurve.Affine F)
    [Fact (c.a₁ = 0 ∧ c.a₂ = 0 ∧ c.a₃ = 0)]
    [Fact (Nat.Prime c.order)] {x y xT yT : F}
    (h : c.Nonsingular x y) (hT : c.Nonsingular xT yT)
    (hne : Point.some _ _ h ≠ Point.some _ _ hT) (hneg : Point.some _ _ h ≠ -Point.some _ _ hT) :
    x ≠ xT := by
  contrapose! hneg
  contrapose! hne
  simp_all +decide [WeierstrassCurve.Affine.negY]
  have h_eq : y ^ 2 + c.a₁ * xT * y + c.a₃ * y
      = yT ^ 2 + c.a₁ * xT * yT + c.a₃ * yT := by
    have := h.1; have := hT.1
    simp_all +decide [WeierstrassCurve.Affine.equation_iff]
  exact mul_left_cancel₀ (sub_ne_zero_of_ne hne) (by linear_combination h_eq)

/-- **Prime-order inversion.** If `Q = [s]·P` with `s` a unit mod the (prime) order,
    then `P = [s⁻¹]·Q` — the `recip` reading of a scalar multiple: `s⁻¹·s = 1 + m·order`
    and the order kills every point. -/
lemma eq_inv_smul_of_smul_eq (c : WeierstrassCurve.Affine F)
    [Fact (Nat.Prime c.order)]
    {P Q : c.Point} {s : ℤ} (hs : (s : ZMod c.order) ≠ 0) (h : Q = s • P) :
    P = ((s : ZMod c.order)⁻¹.val : ℕ) • Q := by
  haveI : NeZero c.order := ⟨(Fact.out : Nat.Prime c.order).ne_zero⟩
  set k : ℕ := ((s : ZMod c.order)⁻¹).val with hk
  have hks : ((k * s - 1 : ℤ) : ZMod c.order) = 0 := by
    push_cast
    rw [hk, ZMod.natCast_val, ZMod.cast_id, inv_mul_cancel₀ hs]
    ring
  obtain ⟨m, hm⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hks
  have hkill : (c.order : ℤ) • P = 0 := by rw [natCast_zsmul]; exact card_nsmul_eq_zero'
  have hint : (k : ℤ) • Q = P := by
    rw [h, smul_smul, show (k : ℤ) * s = 1 + c.order * m from by linarith,
      add_smul, one_smul, mul_comm (c.order : ℤ) m, mul_smul, hkill, smul_zero, add_zero]
  rw [← hint, natCast_zsmul]

/-- **Scalars act through their residues.** Two integers with the same image mod the
    (prime) order act identically on every point: the order kills the difference. -/
lemma smul_eq_smul_of_zmod_eq (c : WeierstrassCurve.Affine F)
    [Fact (Nat.Prime c.order)]
    {P : c.Point} {a b : ℤ} (h : (a : ZMod c.order) = (b : ZMod c.order)) :
    a • P = b • P := by
  haveI : NeZero c.order := ⟨(Fact.out : Nat.Prime c.order).ne_zero⟩
  have hd : ((a - b : ℤ) : ZMod c.order) = 0 := by push_cast [h]; ring
  obtain ⟨m, hm⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hd
  have hkill : (c.order : ℤ) • P = 0 := by rw [natCast_zsmul]; exact card_nsmul_eq_zero'
  have : a = b + c.order * m := by linarith
  rw [this, add_smul, mul_comm, mul_smul, hkill, smul_zero, add_zero]

/-- **No 2-torsion.** On a short-Weierstrass curve of odd prime `order`, every
    nonsingular affine point has `y ≠ 0`: a point with `y = 0` equals its own negation,
    hence is 2-torsion, and a group of odd prime order has none (`smul_ne_zero_of_lt`
    at `k = 2`). -/
lemma y_ne_zero_of_odd_order (c : WeierstrassCurve.Affine F)
    [Fact (c.a₁ = 0 ∧ c.a₂ = 0 ∧ c.a₃ = 0)]
    [Fact (Nat.Prime c.order)] (hodd : c.order ≠ 2)
    {x y : F} (hI : c.Nonsingular x y) : y ≠ 0 := by
  intro hy
  -- with `y = 0` (and short shape `a₁ = a₃ = 0`), `negY = y`, so `P = -P`
  obtain ⟨ha1, -, ha3⟩ := (Fact.out : c.a₁ = 0 ∧ c.a₂ = 0 ∧ c.a₃ = 0)
  have hneg : negY c x y = y := by
    simp [WeierstrassCurve.Affine.negY, ha1, ha3, hy]
  have hPselfneg : -(Point.some _ _ hI) = Point.some _ _ hI := by
    rw [Point.neg_some]; congr 1
  -- `P = -P` gives `2 • P = P + (-P) = 0`
  have hPne : Point.some _ _ hI ≠ 0 := Point.some_ne_zero hI
  have h2P : (2 : ℤ) • Point.some _ _ hI = 0 := by
    rw [two_zsmul]; nth_rewrite 2 [← hPselfneg]; rw [add_neg_cancel]
  -- `0 < 2 < order` (prime, `≠ 2`) contradicts `2 • P = 0` for `P ≠ 0`
  have hlt : (2 : ℤ) < (c.order : ℤ) := by
    have : 3 ≤ c.order := by have := (Fact.out : Nat.Prime c.order).two_le; omega
    exact_mod_cast this
  exact smul_ne_zero_of_lt c hPne (by norm_num) hlt h2P

/-- **t-condition self-enforcement.** The gate constraints together with prime order
    already force `t ≠ 0` — the forbidden check is *not* needed for the second-addition
    non-degeneracy. If `t = 2·xi + xb − s1² = 0`, then the `xo` constraint
    `u² − t²·(…) = 0` collapses to `u² = 0`, i.e. `u = 2·yi − t·s1 = 2·yi = 0`, so
    `yi = 0` — and an odd-prime-order curve has no such point
    (`y_ne_zero_of_odd_order`). Contradiction.

    The hypothesis `c.order ≠ 2` (equivalently, the prime `order` is odd) is genuinely
    required, not a convenience: the degenerate branch is real whenever the input point is
    2-torsion. Over `ZMod 7` with the curve `y² = x³ + 6` — whose group is `(ℤ/2)²`, of
    order `4` — the input point `(xi, yi) = (1, 0)` is nonsingular and
    `singleBitHolds 0 5 0 0 1 0 0 0` holds, yet `2·xi + xb − s1² = 2·1 + 5 − 0 = 7 = 0`.
    That curve is itself excluded by the prime-order `Fact`; at prime order the same failure
    is exactly the `order = 2` case, which this hypothesis rules out. The Pasta `order` is a
    255-bit prime, so it holds there — but it follows neither from `order` being prime (`2`
    is prime) nor from the short shape, so it is taken separately. -/
private lemma tne_of_holds (c : WeierstrassCurve.Affine F)
    [Fact (c.a₁ = 0 ∧ c.a₂ = 0 ∧ c.a₃ = 0)]
    [Fact (Nat.Prime c.order)] (h2 : (2 : F) ≠ 0) (hodd : c.order ≠ 2)
    {b xb yb s1 xi yi xo yo : F}
    (hI : c.Nonsingular xi yi)
    (hh : singleBitHolds b xb yb s1 xi yi xo yo) :
    2 * xi + xb - s1 * s1 ≠ 0 := by
  intro ht
  -- the `xo` constraint collapses (with `t = 0`) to `4·yi² = 0`, so `yi = 0`
  have hyi : yi = 0 := by
    rw [singleBitHolds_iff] at hh
    obtain ⟨_, _, h3, _⟩ := hh
    have htt : xi - (s1 * s1 - xi - xb) = 0 := by linear_combination ht
    rw [htt] at h3
    have hy2 : yi * yi = 0 := by
      have hfour : (4 : F) * (yi * yi) = 0 := by linear_combination h3
      have h4ne : (4 : F) ≠ 0 := by
        have h44 : (4 : F) = 2 * 2 := by norm_num
        rw [h44]; exact mul_ne_zero h2 h2
      exact (mul_eq_zero.mp hfour).resolve_left h4ne
    exact mul_self_eq_zero.mp hy2
  exact y_ne_zero_of_odd_order c hodd hI hyi

/-! ## Soundness: avoiding `±T` makes every row non-degenerate

The kimchi VarBaseMul gate uses incomplete addition, so each row needs its additions to be
non-vertical (`NonDegen`). The complete obstruction is the forbidden band `s ∈ [-15, 15] (mod
order)` — equivalently the eleven residues `forbiddenValues order` for a prime `order ≡ 1 (mod 4)`.
Excluding it makes every satisfying witness's rows non-degenerate, the guarantee the deployed
two-residue runtime check does not by itself provide. The accumulator nonsingularity is derived,
not assumed: from `Holds` per row plus the base, threading, and initial accumulator `2·T`,
`gate_chain_produce` and `gateStep_chain` produce the whole point sequence, and the two regime roots
conclude correctness — `varBaseMul_subwrap_correct` unconditionally below the order,
`varBaseMul_forbidden_correct` at the one-wrap width. -/

/-- The forbidden set for VarBaseMul non-degeneracy: the EXACT Pasta reachable
    degenerate residues `forbiddenResidues = {0, ±1, ±2, ±3, 5, 7, 9, 11}`. Sound for any
    prime `order ≡ 1 (mod 4)` (the actual degenerate set is `⊆` these), and exactly tight
    for the Pasta primes. -/
def forbiddenValues (order : ℕ) : Set ℤ :=
  {s | ∃ t ∈ Ladder.forbiddenResidues, (order : ℤ) ∣ (s - t)}

/-- `1` is a forbidden residue: a scalar `≡ 1 (mod order)` is in the band. The
membership an off-band caller inverts to keep its final accumulator away from the
base (`[s]·T = T` forces `order ∣ s − 1`). -/
theorem mem_forbiddenValues_of_dvd_sub_one (order : ℕ) {s : ℤ}
    (h : (order : ℤ) ∣ (s - 1)) : s ∈ forbiddenValues order :=
  ⟨1, by decide, h⟩

/-- **Prime order ⇒ full order.** For a nonzero point `T` on a `short-Weierstrass curve`, a scalar
    multiple `m • T` vanishes iff `order ∣ m`. (`order` is prime and `order • T = 0`, so
    `addOrderOf T ∣ order`; nonzero `T` rules out `addOrderOf T = 1`, hence it equals
    `order`.) -/
lemma zsmul_eq_zero_iff_order_dvd (c : WeierstrassCurve.Affine F)
    [Fact (c.a₁ = 0 ∧ c.a₂ = 0 ∧ c.a₃ = 0)]
    [Fact (Nat.Prime c.order)] {T : c.Point} (hT : T ≠ 0) (m : ℤ) :
    m • T = 0 ↔ (c.order : ℤ) ∣ m := by
  have hdvd : (addOrderOf T : ℤ) ∣ (c.order : ℤ) :=
    addOrderOf_dvd_iff_zsmul_eq_zero.mpr (by rw [natCast_zsmul]; exact card_nsmul_eq_zero')
  have horder : addOrderOf T = c.order := by
    have hnat : addOrderOf T ∣ c.order := by exact_mod_cast hdvd
    rcases Nat.Prime.eq_one_or_self_of_dvd (Fact.out : Nat.Prime c.order) _ hnat with h1 | h1
    · exact absurd (AddMonoid.addOrderOf_eq_one_iff.mp h1) hT
    · exact h1
  rw [← addOrderOf_dvd_iff_zsmul_eq_zero, horder]

/-- The raw bit processed at sub-step `j`: bit `j % 5` of gate `j / 5`. -/
private def gateBit (g : ℕ → Witness F) (j : ℕ) : F :=
  match j % 5 with
  | 0 => (g (j / 5)).b0
  | 1 => (g (j / 5)).b1
  | 2 => (g (j / 5)).b2
  | 3 => (g (j / 5)).b3
  | _ => (g (j / 5)).b4

/-- The `±1` sign a bit value selects: `+1` for `b = 1`, `−1` otherwise — the honest ℤ
reading of the gate's `2·b − 1`. -/
def bitSign (b : F) : ℤ := if b = 1 then 1 else -1

/-- Either sign, whatever the value. -/
lemma bitSign_eq (b : F) : bitSign b = 1 ∨ bitSign b = -1 := by
  unfold bitSign; split <;> simp

/-- The signed bit `±1` at sub-step `j`. -/
private def gateBitSign (g : ℕ → Witness F) (j : ℕ) : ℤ := bitSign (gateBit g j)

/-- The integer double-and-add ladder over the gate bits, with `k 0 = 2`. -/
def gateLadder (g : ℕ → Witness F) : ℕ → ℤ
  | 0 => 2
  | j + 1 => 2 * gateLadder g j + gateBitSign g j

@[simp] private lemma gateLadder_zero (g : ℕ → Witness F) : gateLadder g 0 = 2 := rfl

private lemma gateLadder_succ (g : ℕ → Witness F) (j : ℕ) :
    gateLadder g (j + 1) = 2 * gateLadder g j + gateBitSign g j := rfl

private lemma gateBitSign_eq (g : ℕ → Witness F) (j : ℕ) :
    gateBitSign g j = 1 ∨ gateBitSign g j = -1 := bitSign_eq _

/-- The unsigned bit at sub-step `j`: `1` if set, else `0` (same `= 1` test as `gateBitSign`). -/
private def ubit (g : ℕ → Witness F) (j : ℕ) : ℤ := if gateBit g j = 1 then 1 else 0

/-- The signed digit is `2·(unsigned bit) − 1`, unconditionally (same `gateBit = 1` test). -/
private lemma gateBitSign_eq_ubit (g : ℕ → Witness F) (j : ℕ) :
    gateBitSign g j = 2 * ubit g j - 1 := by
  unfold gateBitSign bitSign ubit; split <;> ring

/-- The unsigned scalar register the ladder bits encode (Horner over `ubit`), `r 0 = 0`. -/
def gateRegister (g : ℕ → Witness F) : ℕ → ℤ
  | 0 => 0
  | j + 1 => 2 * gateRegister g j + ubit g j

private lemma gateRegister_succ (g : ℕ → Witness F) (j : ℕ) :
    gateRegister g (j + 1) = 2 * gateRegister g j + ubit g j := rfl

/-- **Signed ladder ↔ unsigned register bridge.** The signed double-and-add top is the `Type1`
    unshift of the unsigned register it encodes, as an honest **ℤ** identity (no booleanity needed —
    the signed digits are `2·ubit − 1`): `gateLadder g L = 2·gateRegister g L + 2^L + 1`. This links
    the non-degeneracy path (`gateLadder`) to the scalar-register path: a range-check
    `gateRegister < 2^k` directly bounds the ladder top, hence the deployed `hkL`. -/
lemma gateLadder_eq_register (g : ℕ → Witness F) (L : ℕ) :
    gateLadder g L = 2 * gateRegister g L + 2 ^ L + 1 := by
  induction L with
  | zero => norm_num [gateLadder, gateRegister]
  | succ j ih =>
    rw [gateLadder_succ, ih, gateBitSign_eq_ubit, gateRegister_succ, pow_succ]; ring

omit [Field F] [DecidableEq F] in
/-- The five raw bits of gate `i` are the sub-step bits `5i … 5i+4`. -/
private lemma gateBit_block (g : ℕ → Witness F) (i : ℕ) :
    gateBit g (5 * i) = (g i).b0 ∧ gateBit g (5 * i + 1) = (g i).b1
      ∧ gateBit g (5 * i + 2) = (g i).b2 ∧ gateBit g (5 * i + 3) = (g i).b3
      ∧ gateBit g (5 * i + 4) = (g i).b4 := by
  unfold gateBit; simp +decide [ Nat.add_mod ] ;
  norm_num [ Nat.add_div ]

/-- The signed bit `e` produced by `signed_target` is the bit's sign. -/
private lemma e_eq_bitSign {b : F} (hbit : b = 0 ∨ b = 1) {e : ℤ}
    (he2 : (e : F) = 2 * b - 1) (he : e = 1 ∨ e = -1) (h2 : (2 : F) ≠ 0) :
    e = bitSign b := by
  cases hbit <;> simp_all +decide [ bitSign ];
  · cases he <;> simp_all +decide;
    exact h2 ( by linear_combination' he2 );
  · rcases he with ( rfl | rfl ) <;> norm_num at *;
    grind +extAll

/-- The gate-indexed reading of `e_eq_bitSign`. -/
private lemma e_eq_gateBitSign (g : ℕ → Witness F) (j : ℕ) {b : F} (hgb : gateBit g j = b)
    (hbit : b = 0 ∨ b = 1) {e : ℤ} (he2 : (e : F) = 2 * b - 1) (he : e = 1 ∨ e = -1)
    (h2 : (2 : F) ≠ 0) : e = gateBitSign g j := by
  rw [show gateBitSign g j = bitSign b from by unfold gateBitSign; rw [hgb]]
  exact e_eq_bitSign hbit he2 he h2

/-- Per sub-step advance using *only* the x-condition `k ≢ ±1`; the t-condition `t ≠ 0`
    is supplied by `tne_of_holds` (the constraints + prime order), not by `2k ≢ ±1`. -/
private lemma gate_step_advance' (c : WeierstrassCurve.Affine F)
    [Fact (c.a₁ = 0 ∧ c.a₂ = 0 ∧ c.a₃ = 0)]
    [Fact (Nat.Prime c.order)] (h2 : (2 : F) ≠ 0) (hodd : c.order ≠ 2)
    {xT yT b s1 xi yi xo yo : F}
    (hTns : c.Nonsingular xT yT)
    (hI : c.Nonsingular xi yi)
    (hQ : c.Nonsingular xT ((2 * b - 1) * yT))
    (hbit : b = 0 ∨ b = 1)
    (hTne : Point.some _ _ hTns ≠ 0)
    (k : ℤ) (hIk : Point.some _ _ hI = k • Point.some _ _ hTns)
    (hkx1 : ¬ ((c.order : ℤ) ∣ (k - 1))) (hkx2 : ¬ ((c.order : ℤ) ∣ (k + 1)))
    (hh : singleBitHolds b xT yT s1 xi yi xo yo) :
    xi ≠ xT ∧ (2 * xi + xT - s1 * s1 ≠ 0) ∧
      ∃ (hO : c.Nonsingular xo yo) (e : ℤ),
        (e = 1 ∨ e = -1) ∧ (e : F) = 2 * b - 1 ∧
          Point.some _ _ hO = (2 * k + e) • Point.some _ _ hTns := by
  have hshort : c.a₁ = 0 ∧ c.a₂ = 0 ∧ c.a₃ = 0 := Fact.out
  obtain ⟨e, he, he'⟩ := signed_target c hshort hTns hQ hbit
  have hxne : xi ≠ xT := by
    apply x_ne_xT_of_ne_base c hI hTns
    · contrapose! hkx1
      have hd : (k - 1) • Point.some _ _ hTns = 0 := by
        rw [sub_smul, one_smul, ← hIk, hkx1, sub_self]
      exact (zsmul_eq_zero_iff_order_dvd c hTne _).1 hd
    · contrapose! hkx2
      rw [← zsmul_eq_zero_iff_order_dvd c hTne, add_zsmul, one_zsmul, ← hIk, hkx2,
        neg_add_cancel]
  have htne : 2 * xi + xT - s1 * s1 ≠ 0 := tne_of_holds c h2 hodd hI hh
  obtain ⟨hO, hOeq⟩ := singleBit_sound c hshort b xT yT s1 xi yi xo yo hI hQ hxne htne hh
  refine ⟨hxne, htne, hO, e, he'.2, he'.1, ?_⟩
  rw [hOeq, hIk, he]
  module

/-- One gate block, deriving the output point's nonsingularity rather than asserting it: from the
    input point `a0` on-curve, the constraint `Holds`, and the base, it chains the five
    `gate_step_advance'` steps and produces `a5` existentially, together with the row's `NonDegen`
    side conditions. The deployed soundness needs only the threaded input. This mirrors EndoMul's
    `gate_advance`. -/
private lemma gate_block_produce (c : WeierstrassCurve.Affine F)
    [Fact (c.a₁ = 0 ∧ c.a₂ = 0 ∧ c.a₃ = 0)]
    [Fact (Nat.Prime c.order)] (g : ℕ → Witness F) (i : ℕ)
    (h2 : (2 : F) ≠ 0)
    {T : c.Point} (hTne : T ≠ 0)
    (hTns : c.Nonsingular (g i).xT (g i).yT) (hTeq : T = Point.some _ _ hTns)
    (ha0ns : c.Nonsingular (g i).x0 (g i).y0) (hh : Holds (g i))
    (ha0 : Point.some _ _ ha0ns = gateLadder g (5 * i) • T)
    (hodd : c.order ≠ 2)
    (hnd : ∀ ℓ, ℓ < 5 →
        ¬ (c.order : ℤ) ∣ (gateLadder g (5 * i + ℓ) - 1)
          ∧ ¬ (c.order : ℤ) ∣ (gateLadder g (5 * i + ℓ) + 1)) :
    NonDegen (g i) ∧ ∃ ha5ns : c.Nonsingular (g i).x5 (g i).y5,
      Point.some _ _ ha5ns = gateLadder g (5 * i + 5) • T := by
  have hT0 : Point.some _ _ hTns ≠ 0 := by rw [← hTeq]; exact hTne
  obtain ⟨_hdec, hsb0, hsb1, hsb2, hsb3, hsb4⟩ := (holds_iff _).mp hh
  obtain ⟨gb0, gb1, gb2, gb3, gb4⟩ := gateBit_block g i
  have hshort : c.a₁ = 0 ∧ c.a₂ = 0 ∧ c.a₃ = 0 := Fact.out
  have bit : ∀ {x : F}, x * x - x = 0 → x = 0 ∨ x = 1 := by
    intro x hx
    rcases mul_eq_zero.mp (show x * (x - 1) = 0 by linear_combination hx) with h | h
    · exact Or.inl h
    · exact Or.inr (by linear_combination h)
  have ha0' : Point.some _ _ ha0ns = gateLadder g (5 * i) • Point.some _ _ hTns := by
    rw [hTeq] at ha0; exact ha0
  obtain ⟨hx0, ht0, hO0, e0, hepm0, hef0, hOeq0⟩ :=
    gate_step_advance' c h2 hodd hTns ha0ns
      (signed_target_nonsingular c hshort hTns (bit hsb0.bool))
      (bit hsb0.bool) hT0 (gateLadder g (5 * i)) ha0'
      (hnd 0 (by omega)).1 (hnd 0 (by omega)).2 hsb0
  have ha1 : Point.some _ _ hO0 = gateLadder g (5 * i + 1) • Point.some _ _ hTns := by
    rw [hOeq0, e_eq_gateBitSign g (5 * i) gb0 (bit hsb0.bool) hef0 hepm0 h2, ← gateLadder_succ]
  obtain ⟨hx1, ht1, hO1, e1, hepm1, hef1, hOeq1⟩ :=
    gate_step_advance' c h2 hodd hTns hO0 (signed_target_nonsingular c hshort hTns (bit hsb1.bool))
      (bit hsb1.bool) hT0 (gateLadder g (5 * i + 1)) ha1
      (hnd 1 (by omega)).1 (hnd 1 (by omega)).2 hsb1
  have ha2 : Point.some _ _ hO1 = gateLadder g (5 * i + 2) • Point.some _ _ hTns := by
    rw [hOeq1, e_eq_gateBitSign g (5 * i + 1) gb1 (bit hsb1.bool) hef1 hepm1 h2, ← gateLadder_succ]
  obtain ⟨hx2, ht2, hO2, e2, hepm2, hef2, hOeq2⟩ :=
    gate_step_advance' c h2 hodd hTns hO1 (signed_target_nonsingular c hshort hTns (bit hsb2.bool))
      (bit hsb2.bool) hT0 (gateLadder g (5 * i + 2)) ha2
      (hnd 2 (by omega)).1 (hnd 2 (by omega)).2 hsb2
  have ha3 : Point.some _ _ hO2 = gateLadder g (5 * i + 3) • Point.some _ _ hTns := by
    rw [hOeq2, e_eq_gateBitSign g (5 * i + 2) gb2 (bit hsb2.bool) hef2 hepm2 h2, ← gateLadder_succ]
  obtain ⟨hx3, ht3, hO3, e3, hepm3, hef3, hOeq3⟩ :=
    gate_step_advance' c h2 hodd hTns hO2 (signed_target_nonsingular c hshort hTns (bit hsb3.bool))
      (bit hsb3.bool) hT0 (gateLadder g (5 * i + 3)) ha3
      (hnd 3 (by omega)).1 (hnd 3 (by omega)).2 hsb3
  have ha4 : Point.some _ _ hO3 = gateLadder g (5 * i + 4) • Point.some _ _ hTns := by
    rw [hOeq3, e_eq_gateBitSign g (5 * i + 3) gb3 (bit hsb3.bool) hef3 hepm3 h2, ← gateLadder_succ]
  obtain ⟨hx4, ht4, hO4, e4, hepm4, hef4, hOeq4⟩ :=
    gate_step_advance' c h2 hodd hTns hO3 (signed_target_nonsingular c hshort hTns (bit hsb4.bool))
      (bit hsb4.bool) hT0 (gateLadder g (5 * i + 4)) ha4
      (hnd 4 (by omega)).1 (hnd 4 (by omega)).2 hsb4
  have ha5 : Point.some _ _ hO4 = gateLadder g (5 * i + 5) • Point.some _ _ hTns := by
    rw [hOeq4, e_eq_gateBitSign g (5 * i + 4) gb4 (bit hsb4.bool) hef4 hepm4 h2, ← gateLadder_succ]
  exact ⟨⟨hx0, hx1, hx2, hx3, hx4, ht0, ht1, ht2, ht3, ht4⟩, hO4, by rw [hTeq]; exact ha5⟩

/-- Like `gate_block_produce`, but returns all five derived accumulator points `a1..a5` (not just
    `a5`), so the register subsystem (`scalarMul` / `scalarMul_type2`, which consume the whole
    `GateStep` bundle) can be fed the full per-row data. Same five-`gate_step_advance'` chain. -/
private lemma gate_block_full (c : WeierstrassCurve.Affine F)
    [Fact (c.a₁ = 0 ∧ c.a₂ = 0 ∧ c.a₃ = 0)]
    [Fact (Nat.Prime c.order)] (g : ℕ → Witness F) (i : ℕ)
    (h2 : (2 : F) ≠ 0)
    {T : c.Point} (hTne : T ≠ 0)
    (hTns : c.Nonsingular (g i).xT (g i).yT) (hTeq : T = Point.some _ _ hTns)
    (ha0ns : c.Nonsingular (g i).x0 (g i).y0) (hh : Holds (g i))
    (ha0 : Point.some _ _ ha0ns = gateLadder g (5 * i) • T)
    (hodd : c.order ≠ 2)
    (hnd : ∀ ℓ, ℓ < 5 →
        ¬ (c.order : ℤ) ∣ (gateLadder g (5 * i + ℓ) - 1)
          ∧ ¬ (c.order : ℤ) ∣ (gateLadder g (5 * i + ℓ) + 1)) :
    NonDegen (g i) ∧ ∃ (_a1 : c.Nonsingular (g i).x1 (g i).y1)
      (_a2 : c.Nonsingular (g i).x2 (g i).y2) (_a3 : c.Nonsingular (g i).x3 (g i).y3)
      (_a4 : c.Nonsingular (g i).x4 (g i).y4) (a5 : c.Nonsingular (g i).x5 (g i).y5),
      Point.some _ _ a5 = gateLadder g (5 * i + 5) • T := by
  have hT0 : Point.some _ _ hTns ≠ 0 := by rw [← hTeq]; exact hTne
  obtain ⟨_hdec, hsb0, hsb1, hsb2, hsb3, hsb4⟩ := (holds_iff _).mp hh
  obtain ⟨gb0, gb1, gb2, gb3, gb4⟩ := gateBit_block g i
  have hshort : c.a₁ = 0 ∧ c.a₂ = 0 ∧ c.a₃ = 0 := Fact.out
  have bit : ∀ {x : F}, x * x - x = 0 → x = 0 ∨ x = 1 := by
    intro x hx
    rcases mul_eq_zero.mp (show x * (x - 1) = 0 by linear_combination hx) with h | h
    · exact Or.inl h
    · exact Or.inr (by linear_combination h)
  have ha0' : Point.some _ _ ha0ns = gateLadder g (5 * i) • Point.some _ _ hTns := by
    rw [hTeq] at ha0; exact ha0
  obtain ⟨hx0, ht0, hO0, e0, hepm0, hef0, hOeq0⟩ :=
    gate_step_advance' c h2 hodd hTns ha0ns
      (signed_target_nonsingular c hshort hTns (bit hsb0.bool))
      (bit hsb0.bool) hT0 (gateLadder g (5 * i)) ha0'
      (hnd 0 (by omega)).1 (hnd 0 (by omega)).2 hsb0
  have ha1 : Point.some _ _ hO0 = gateLadder g (5 * i + 1) • Point.some _ _ hTns := by
    rw [hOeq0, e_eq_gateBitSign g (5 * i) gb0 (bit hsb0.bool) hef0 hepm0 h2, ← gateLadder_succ]
  obtain ⟨hx1, ht1, hO1, e1, hepm1, hef1, hOeq1⟩ :=
    gate_step_advance' c h2 hodd hTns hO0 (signed_target_nonsingular c hshort hTns (bit hsb1.bool))
      (bit hsb1.bool) hT0 (gateLadder g (5 * i + 1)) ha1
      (hnd 1 (by omega)).1 (hnd 1 (by omega)).2 hsb1
  have ha2 : Point.some _ _ hO1 = gateLadder g (5 * i + 2) • Point.some _ _ hTns := by
    rw [hOeq1, e_eq_gateBitSign g (5 * i + 1) gb1 (bit hsb1.bool) hef1 hepm1 h2, ← gateLadder_succ]
  obtain ⟨hx2, ht2, hO2, e2, hepm2, hef2, hOeq2⟩ :=
    gate_step_advance' c h2 hodd hTns hO1 (signed_target_nonsingular c hshort hTns (bit hsb2.bool))
      (bit hsb2.bool) hT0 (gateLadder g (5 * i + 2)) ha2
      (hnd 2 (by omega)).1 (hnd 2 (by omega)).2 hsb2
  have ha3 : Point.some _ _ hO2 = gateLadder g (5 * i + 3) • Point.some _ _ hTns := by
    rw [hOeq2, e_eq_gateBitSign g (5 * i + 2) gb2 (bit hsb2.bool) hef2 hepm2 h2, ← gateLadder_succ]
  obtain ⟨hx3, ht3, hO3, e3, hepm3, hef3, hOeq3⟩ :=
    gate_step_advance' c h2 hodd hTns hO2 (signed_target_nonsingular c hshort hTns (bit hsb3.bool))
      (bit hsb3.bool) hT0 (gateLadder g (5 * i + 3)) ha3
      (hnd 3 (by omega)).1 (hnd 3 (by omega)).2 hsb3
  have ha4 : Point.some _ _ hO3 = gateLadder g (5 * i + 4) • Point.some _ _ hTns := by
    rw [hOeq3, e_eq_gateBitSign g (5 * i + 3) gb3 (bit hsb3.bool) hef3 hepm3 h2, ← gateLadder_succ]
  obtain ⟨hx4, ht4, hO4, e4, hepm4, hef4, hOeq4⟩ :=
    gate_step_advance' c h2 hodd hTns hO3 (signed_target_nonsingular c hshort hTns (bit hsb4.bool))
      (bit hsb4.bool) hT0 (gateLadder g (5 * i + 4)) ha4
      (hnd 4 (by omega)).1 (hnd 4 (by omega)).2 hsb4
  have ha5 : Point.some _ _ hO4 = gateLadder g (5 * i + 5) • Point.some _ _ hTns := by
    rw [hOeq4, e_eq_gateBitSign g (5 * i + 4) gb4 (bit hsb4.bool) hef4 hepm4 h2, ← gateLadder_succ]
  exact ⟨⟨hx0, hx1, hx2, hx3, hx4, ht0, ht1, ht2, ht3, ht4⟩, hO0, hO1, hO2, hO3, hO4,
    by rw [hTeq]; exact ha5⟩

/-- Final-accumulator coordinates after `m` rows (row 0's `x0`/`y0` if `m = 0`, else row `(m-1)`'s
    `x5`/`y5`) — the concrete stand-in for the abstract accumulator point `P m`. -/
def accX (g : ℕ → Witness F) : ℕ → F
  | 0 => (g 0).x0
  | k + 1 => (g k).x5

/-- The `y`-companion of `accX`: row 0's input `y0` when `m = 0`, else row `(m-1)`'s
    output `y5`. -/
def accY (g : ℕ → Witness F) : ℕ → F
  | 0 => (g 0).y0
  | k + 1 => (g k).y5

/-- **Chained non-degeneracy and scalar multiple.** Over `m` rows, from `Holds` per row, the base
    nonsingularity (row 0), the column threading (`(g (i+1)).x0 = (g i).x5`), and the initial
    accumulator `2·T`, the chain derives every intermediate point's nonsingularity
    (`gate_block_produce`) and concludes the final accumulator equals `s·T` with every row
    `NonDegen`. The prover supplies only `Holds` and the threading; the accumulator nonsingularity
    is derived. The proof inducts on `k ≤ m`, carrying the invariant
    `∃ hk, Point.some _ _ hk = gateLadder g (5·k) • T`: the base case is `hP0ns`/`hP0`
    (`gateLadder g 0 = 2`), and each step feeds the threaded input (base transported to row `k` via
    `hbase`) to `gate_block_produce`. -/
private lemma gate_chain_produce (c : WeierstrassCurve.Affine F)
    [Fact (c.a₁ = 0 ∧ c.a₂ = 0 ∧ c.a₃ = 0)] [Fact (Nat.Prime c.order)]
    (m : ℕ) (g : ℕ → Witness F) (T : c.Point) (s : ℤ) (hTne : T ≠ 0)
    (hholds : ∀ i, i < m → Holds (g i))
    (hTns : c.Nonsingular (g 0).xT (g 0).yT) (hTeq : T = Point.some _ _ hTns)
    (hbase : ∀ i, i < m → (g i).xT = (g 0).xT ∧ (g i).yT = (g 0).yT)
    (hthread : ∀ i, i + 1 < m → (g (i + 1)).x0 = (g i).x5 ∧ (g (i + 1)).y0 = (g i).y5)
    (hP0ns : c.Nonsingular (g 0).x0 (g 0).y0)
    (hP0 : Point.some _ _ hP0ns = (2 : ℤ) • T)
    (h2 : (2 : F) ≠ 0) (hodd : c.order ≠ 2)
    (hND : ∀ n, n < 5 * m →
        ¬ (c.order : ℤ) ∣ (gateLadder g n - 1) ∧ ¬ (c.order : ℤ) ∣ (gateLadder g n + 1)
          ∧ ¬ (c.order : ℤ) ∣ (2 * gateLadder g n - 1)
          ∧ ¬ (c.order : ℤ) ∣ (2 * gateLadder g n + 1))
    (hs : s = gateLadder g (5 * m)) :
    ∃ hfin : c.Nonsingular (accX g m) (accY g m),
      Point.some _ _ hfin = s • T ∧ ∀ i, i < m → NonDegen (g i) := by
  -- Point congruence across equal coordinates (local analog of `Gate.EndoMul.some_congr`).
  have some_congr : ∀ {x x' y y' : F} (h : c.Nonsingular x y) (h' : c.Nonsingular x' y'),
      x = x' → y = y' → Point.some _ _ h = Point.some _ _ h' := by
    intro x x' y y' h h' hx hy; subst hx; subst hy; rfl
  -- coordinate threading: row `k`'s input column equals the accumulator at step `k`
  have haccP : ∀ k, k < m → (g k).x0 = accX g k ∧ (g k).y0 = accY g k := by
    intro k hk
    cases k with
    | zero => exact ⟨rfl, rfl⟩
    | succ j => exact hthread j hk
  -- per-step accumulator nonsingularity + point value + accumulated non-degeneracy
  have key : ∀ k, k ≤ m → ∃ hk : c.Nonsingular (accX g k) (accY g k),
      Point.some _ _ hk = gateLadder g (5 * k) • T ∧ (∀ i, i < k → NonDegen (g i)) := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨hP0ns, ?_, ?_⟩
      · change Point.some (g 0).x0 (g 0).y0 hP0ns = gateLadder g (5 * 0) • T
        rw [hP0]; simp only [Nat.mul_zero, gateLadder_zero]
      · intro i hi; omega
    | succ j ih =>
      intro hj1
      have hj' : j < m := by omega
      obtain ⟨hk, hPk, hNDk⟩ := ih (by omega)
      -- transport the base nonsingularity to row `j`
      obtain ⟨hbx, hby⟩ := hbase j hj'
      have hTns_j : c.Nonsingular (g j).xT (g j).yT := by rw [hbx, hby]; exact hTns
      have hTeq_j : T = Point.some _ _ hTns_j := by
        rw [hTeq]; exact some_congr hTns hTns_j hbx.symm hby.symm
      -- transport the threaded input accumulator to row `j`'s input column
      obtain ⟨hx0, hy0⟩ := haccP j hj'
      have ha0ns_j : c.Nonsingular (g j).x0 (g j).y0 := by rw [hx0, hy0]; exact hk
      have ha0_j : Point.some _ _ ha0ns_j = gateLadder g (5 * j) • T := by
        rw [some_congr ha0ns_j hk hx0 hy0]; exact hPk
      obtain ⟨hNDj, ha5ns, ha5eq⟩ :=
        gate_block_produce c g j h2 hTne hTns_j hTeq_j ha0ns_j (hholds j hj') ha0_j hodd
          (fun ℓ _ => ⟨(hND (5 * j + ℓ) (by omega)).1, (hND (5 * j + ℓ) (by omega)).2.1⟩)
      -- `accX g (j+1) = (g j).x5` and `gateLadder g (5*(j+1)) = gateLadder g (5*j+5)` defeq
      refine ⟨ha5ns, ?_, ?_⟩
      · rw [show 5 * (j + 1) = 5 * j + 5 from by ring]; exact ha5eq
      · intro i hi
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | h
        · exact hNDk i h
        · subst h; exact hNDj
  obtain ⟨hfin, hPfin, hNDfin⟩ := key m le_rfl
  exact ⟨hfin, by rw [hs]; exact hPfin, hNDfin⟩

/-- **`GateStep`-producing fold.** From `Holds` per row, the base, the threading, and the initial
    accumulator `2·T`, derives the full per-row `GateStep` bundle (every `a0..a5`, via
    `gate_block_full`) together with the threaded point sequence `P` — exactly the inputs the
    register subsystem (`scalarMul` / `scalarMul_type2`) consumes. The `scaleFast2` analog of
    `gate_chain_produce`. -/
private lemma gateStep_chain (c : WeierstrassCurve.Affine F)
    [Fact (c.a₁ = 0 ∧ c.a₂ = 0 ∧ c.a₃ = 0)] [Fact (Nat.Prime c.order)]
    (m : ℕ) (g : ℕ → Witness F) (T : c.Point) (hTne : T ≠ 0)
    (hholds : ∀ i, i < m → Holds (g i))
    (hTns : c.Nonsingular (g 0).xT (g 0).yT) (hTeq : T = Point.some _ _ hTns)
    (hbase : ∀ i, i < m → (g i).xT = (g 0).xT ∧ (g i).yT = (g 0).yT)
    (hthread : ∀ i, i + 1 < m → (g (i + 1)).x0 = (g i).x5 ∧ (g (i + 1)).y0 = (g i).y5)
    (hP0ns : c.Nonsingular (g 0).x0 (g 0).y0)
    (hP0 : Point.some _ _ hP0ns = (2 : ℤ) • T)
    (h2 : (2 : F) ≠ 0) (hodd : c.order ≠ 2)
    (hND : ∀ n, n < 5 * m →
        ¬ (c.order : ℤ) ∣ (gateLadder g n - 1) ∧ ¬ (c.order : ℤ) ∣ (gateLadder g n + 1)) :
    ∃ (gs : ∀ i, i < m → GateStep c (g i)) (P : ℕ → c.Point),
      (∀ i (hi : i < m), T = Point.some _ _ (gs i hi).hT)
        ∧ (∀ i (hi : i < m), P i = Point.some _ _ (gs i hi).a0)
        ∧ (∀ i (hi : i < m), P (i + 1) = Point.some _ _ (gs i hi).a5)
        ∧ P 0 = (2 : ℤ) • T := by
  -- Point congruence across equal coordinates (local analog of `Gate.EndoMul.some_congr`).
  have some_congr : ∀ {x x' y y' : F} (h : c.Nonsingular x y) (h' : c.Nonsingular x' y'),
      x = x' → y = y' → Point.some _ _ h = Point.some _ _ h' := by
    intro x x' y y' h h' hx hy; subst hx; subst hy; rfl
  -- coordinate threading: row `k`'s input column equals the accumulator at step `k`
  have haccP : ∀ k, k < m → (g k).x0 = accX g k ∧ (g k).y0 = accY g k := by
    intro k hk
    cases k with
    | zero => exact ⟨rfl, rfl⟩
    | succ j => exact hthread j hk
  -- per-step accumulator nonsingularity + point value + accumulated full `GateStep`
  have key : ∀ k, k ≤ m → ∃ hk : c.Nonsingular (accX g k) (accY g k),
      Point.some _ _ hk = gateLadder g (5 * k) • T ∧ (∀ i, i < k → GateStep c (g i)) := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨hP0ns, ?_, ?_⟩
      · change Point.some (g 0).x0 (g 0).y0 hP0ns = gateLadder g (5 * 0) • T
        rw [hP0]; simp only [Nat.mul_zero, gateLadder_zero]
      · intro i hi; omega
    | succ j ih =>
      intro hj1
      have hj' : j < m := by omega
      obtain ⟨hk, hPk, hGSk⟩ := ih (by omega)
      -- transport the base nonsingularity to row `j`
      obtain ⟨hbx, hby⟩ := hbase j hj'
      have hTns_j : c.Nonsingular (g j).xT (g j).yT := by rw [hbx, hby]; exact hTns
      have hTeq_j : T = Point.some _ _ hTns_j := by
        rw [hTeq]; exact some_congr hTns hTns_j hbx.symm hby.symm
      -- transport the threaded input accumulator to row `j`'s input column
      obtain ⟨hx0, hy0⟩ := haccP j hj'
      have ha0ns_j : c.Nonsingular (g j).x0 (g j).y0 := by rw [hx0, hy0]; exact hk
      have ha0_j : Point.some _ _ ha0ns_j = gateLadder g (5 * j) • T := by
        rw [some_congr ha0ns_j hk hx0 hy0]; exact hPk
      obtain ⟨nd, a1, a2, a3, a4, a5, ha5eq⟩ :=
        gate_block_full c g j h2 hTne hTns_j hTeq_j ha0ns_j (hholds j hj') ha0_j hodd
          (fun ℓ _ => hND (5 * j + ℓ) (by omega))
      -- the full per-row `GateStep` bundle at row `j`
      have hGSj : GateStep c (g j) :=
        ⟨ha0ns_j, a1, a2, a3, a4, a5, hTns_j, hholds j hj',
          nd.x0, nd.x1, nd.x2, nd.x3, nd.x4, nd.t0, nd.t1, nd.t2, nd.t3, nd.t4⟩
      -- `accX g (j+1) = (g j).x5` and `gateLadder g (5*(j+1)) = gateLadder g (5*j+5)` defeq
      refine ⟨a5, ?_, ?_⟩
      · rw [show 5 * (j + 1) = 5 * j + 5 from by ring]; exact ha5eq
      · intro i hi
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | h
        · exact hGSk i h
        · subst h; exact hGSj
  choose kf hkf using key
  -- kf : ∀ k, k ≤ m → c.Nonsingular (accX g k) (accY g k)
  -- hkf k hk : Point.some _ _ (kf k hk) = gateLadder g (5*k) • T ∧ (∀ i < k, GateStep c (g i))
  have gs := (hkf m le_rfl).2
  refine ⟨gs, fun k => if hk : k ≤ m then Point.some _ _ (kf k hk) else 0, ?_, ?_, ?_, ?_⟩
  · intro i hi
    exact hTeq.trans (some_congr hTns (gs i hi).hT (hbase i hi).1.symm (hbase i hi).2.symm)
  · intro i hi
    simp only [dif_pos (le_of_lt hi)]
    exact some_congr (kf i (le_of_lt hi)) (gs i hi).a0 (haccP i hi).1.symm (haccP i hi).2.symm
  · intro i hi
    simp only [dif_pos (Nat.succ_le_of_lt hi)]
    exact some_congr (kf (i + 1) (Nat.succ_le_of_lt hi)) (gs i hi).a5 rfl rfl
  · simp only [dif_pos (Nat.zero_le m)]
    rw [(hkf 0 (Nat.zero_le m)).1]; simp only [Nat.mul_zero, gateLadder_zero]

/-- **VarBaseMul correctness and soundness via the forbidden band.** For any witness satisfying the
    gate constraints (`Holds` per row) at the real init `P₀ = 2·T`, in the one-wrap regime, if the
    ladder top `s` avoids the forbidden band `forbiddenValues order`, the `m` rows compute the final
    accumulator `= s·T` and every row is `NonDegen`. The prover supplies only `Holds`, base,
    threading, and the initial accumulator; `gate_chain_produce` derives the accumulator
    nonsingularity. -/
theorem varBaseMul_forbidden_correct (c : WeierstrassCurve.Affine F)
    [Fact (c.a₁ = 0 ∧ c.a₂ = 0 ∧ c.a₃ = 0)] [Fact (Nat.Prime c.order)]
    (m : ℕ) (g : ℕ → Witness F) (T : c.Point) (s : ℤ) (hTne : T ≠ 0)
    (hholds : ∀ i, i < m → Holds (g i))
    (hTns : c.Nonsingular (g 0).xT (g 0).yT) (hTeq : T = Point.some _ _ hTns)
    (hbase : ∀ i, i < m → (g i).xT = (g 0).xT ∧ (g i).yT = (g 0).yT)
    (hthread : ∀ i, i + 1 < m → (g (i + 1)).x0 = (g i).x5 ∧ (g (i + 1)).y0 = (g i).y5)
    (hP0ns : c.Nonsingular (g 0).x0 (g 0).y0) (hP0 : Point.some _ _ hP0ns = (2 : ℤ) • T)
    (h2 : (2 : F) ≠ 0) (hodd : c.order ≠ 2)
    (hreg₁ : 2 ^ (5 * m - 1) < c.order) (hreg₂ : c.order < 2 ^ (5 * m))
    (hq4 : c.order % 4 = 1)
    (hs : s = gateLadder g (5 * m)) (hnf : s ∉ forbiddenValues c.order) :
    ∃ hfin : c.Nonsingular (accX g m) (accY g m),
      Point.some _ _ hfin = s • T ∧ ∀ i, i < m → NonDegen (g i) := by
  have hnf' : ∀ t ∈ Ladder.forbiddenResidues, ¬ (c.order : ℤ) ∣ (gateLadder g (5 * m) - t) := by
    intro t ht hdvd; exact hnf ⟨t, ht, by rw [hs]; exact hdvd⟩
  exact gate_chain_produce c m g T s hTne hholds hTns hTeq hbase hthread hP0ns hP0 h2 hodd
    (Ladder.ladder_nondegen_tight c.order (5 * m) (Fact.out : Nat.Prime c.order) hq4 hreg₁ hreg₂
      (gateLadder g) (gateBitSign g) (gateLadder_zero g) (fun j _ => gateBitSign_eq g j)
      (fun j _ => gateLadder_succ g j) hnf') hs

/-- **VarBaseMul correctness and soundness in the sub-wrap regime — no forbidden check.** When
    `3·2^(5m) ≤ order` the whole ladder fits below the order, so every row is `NonDegen`
    unconditionally. The prover supplies only `Holds`, base, threading, and the initial
    accumulator. -/
theorem varBaseMul_subwrap_correct (c : WeierstrassCurve.Affine F)
    [Fact (c.a₁ = 0 ∧ c.a₂ = 0 ∧ c.a₃ = 0)] [Fact (Nat.Prime c.order)]
    (m : ℕ) (g : ℕ → Witness F) (T : c.Point) (s : ℤ) (hTne : T ≠ 0)
    (hholds : ∀ i, i < m → Holds (g i))
    (hTns : c.Nonsingular (g 0).xT (g 0).yT) (hTeq : T = Point.some _ _ hTns)
    (hbase : ∀ i, i < m → (g i).xT = (g 0).xT ∧ (g i).yT = (g 0).yT)
    (hthread : ∀ i, i + 1 < m → (g (i + 1)).x0 = (g i).x5 ∧ (g (i + 1)).y0 = (g i).y5)
    (hP0ns : c.Nonsingular (g 0).x0 (g 0).y0) (hP0 : Point.some _ _ hP0ns = (2 : ℤ) • T)
    (h2 : (2 : F) ≠ 0) (hodd : c.order ≠ 2)
    (hsub : 3 * 2 ^ (5 * m) ≤ c.order) (hs : s = gateLadder g (5 * m)) :
    ∃ hfin : c.Nonsingular (accX g m) (accY g m),
      Point.some _ _ hfin = s • T ∧ ∀ i, i < m → NonDegen (g i) :=
  gate_chain_produce c m g T s hTne hholds hTns hTeq hbase hthread hP0ns hP0 h2 hodd
    (Ladder.ladder_subwrap_nondegen c.order (5 * m) hsub
      (gateLadder g) (gateBitSign g) (gateLadder_zero g) (fun j _ => gateBitSign_eq g j)
      (fun j _ => gateLadder_succ g j)) hs

end Kimchi.Gate.VarBaseMul

/-!
## The deployed circuit

Variable-base scalar multiplication, instantiated at the real Pasta curves. The supporting
development — the accumulator and register recurrence folds, the number-theoretic ladder kernel,
the group-order non-degeneracy toolkit, and the abstract soundness — is `§ Supporting
development` above.

The generic soundness theorems `varBaseMul_subwrap_correct` and `varBaseMul_forbidden_correct` are
proved over any `WeierstrassCurve.Affine` carrying the short-shape and prime-order `Fact`s, and are
`#print axioms`-clean. This module exposes the two directions the deployed circuit actually uses,
each at its concrete curve:

* `varBaseMul_scaleFast1` — `scaleFast1` / Type1 (Vesta): the scalar field is smaller
  than the circuit field, so there is no register range-check; soundness comes from the forbidden
  band (full width) or the sub-wrap regime (below it).
* `varBaseMul_scaleFast2` — `scaleFast2` / Type2 (Pallas): the caller splits the scalar and
  range-checks the high half, so soundness is the field-bound route.

A bare `varBaseMul` is never deployed on its own — only these two — so the field-bound Pallas
correctness is *inlined* into `scaleFast2`. The `Fact`s
are discharged from `Pasta`, the prime-order one through `pallas_card` / `vesta_card`. Those
are theorems, resting on CompElliptic's machine-checked point-count certificates rather than
on any axiom, and these corollaries are where that per-curve trust enters; the abstract
development is independent of it.
-/

namespace Kimchi.Gate.VarBaseMul

open CompElliptic.Curves.Pasta CompElliptic.Fields.Pasta CompElliptic.CurveForms.ShortWeierstrass
open Kimchi.Gate.VarBaseMul WeierstrassCurve.Affine Pasta.Shifted Pasta

/-! ## The run's bits as a list: the gadget-facing decode vocabulary

The circuit layer's law statements expose the wired bits as a LIST and speak about
its two folds: `bitsRegister` (the field-side scalar register the gadget pins) and
`bitsVal` (the exact ℤ-decode the forbidden-band condition prices through the Type1
unshift). The bridges identify them with the run-level `gateRegister` and the
register chain, so `varBaseMul_off`'s conclusion lands on list vocabulary. -/

section RunBits

variable {F : Type*} [Field F] [DecidableEq F]

/-- The run's bits, MSB-first: gate `i`'s five bits at positions `5i…5i+4`. -/
def runBits (g : ℕ → Witness F) (m : ℕ) : List F :=
  (List.range m).flatMap fun i => [(g i).b0, (g i).b1, (g i).b2, (g i).b3, (g i).b4]

/-- The base-2 field fold of a bit list, MSB-first — the scalar register the gadget
pins (`n' = 2·n + b` per bit). -/
def bitsRegister (bs : List F) : F := bs.foldl (fun a b => 2 * a + b) 0

/-- The exact ℤ-decode of a bit list (a bit counts iff it is `1`) — the shadow
`bitsRegister` casts on genuine bits, and what the forbidden-band condition speaks
about through the Type1 unshift. -/
def bitsVal (bs : List F) : ℤ := bs.foldl (fun a b => 2 * a + if b = 1 then 1 else 0) 0

theorem runBits_succ (g : ℕ → Witness F) (m : ℕ) :
    runBits g (m + 1) = runBits g m
      ++ [(g m).b0, (g m).b1, (g m).b2, (g m).b3, (g m).b4] := by
  unfold runBits
  rw [List.range_succ, List.flatMap_append]
  simp

theorem runBits_length (g : ℕ → Witness F) (m : ℕ) : (runBits g m).length = 5 * m := by
  induction m with
  | zero => rfl
  | succ k ih =>
    rw [runBits_succ, List.length_append, ih]
    simp
    omega

/-- The ladder's unsigned register is the ℤ-decode of the run's bits. -/
theorem gateRegister_eq_bitsVal (g : ℕ → Witness F) (m : ℕ) :
    gateRegister g (5 * m) = bitsVal (runBits g m) := by
  induction m with
  | zero => rfl
  | succ k ih =>
    have h0 : ubit g (5 * k) = (if (g k).b0 = 1 then (1 : ℤ) else 0) := by
      unfold ubit gateBit
      rw [show (5 * k) % 5 = 0 from by omega, show (5 * k) / 5 = k from by omega]
    have h1 : ubit g (5 * k + 1) = (if (g k).b1 = 1 then (1 : ℤ) else 0) := by
      unfold ubit gateBit
      rw [show (5 * k + 1) % 5 = 1 from by omega,
        show (5 * k + 1) / 5 = k from by omega]
    have h2 : ubit g (5 * k + 1 + 1) = (if (g k).b2 = 1 then (1 : ℤ) else 0) := by
      unfold ubit gateBit
      rw [show (5 * k + 1 + 1) % 5 = 2 from by omega,
        show (5 * k + 1 + 1) / 5 = k from by omega]
    have h3 : ubit g (5 * k + 1 + 1 + 1) = (if (g k).b3 = 1 then (1 : ℤ) else 0) := by
      unfold ubit gateBit
      rw [show (5 * k + 1 + 1 + 1) % 5 = 3 from by omega,
        show (5 * k + 1 + 1 + 1) / 5 = k from by omega]
    have h4 : ubit g (5 * k + 1 + 1 + 1 + 1)
        = (if (g k).b4 = 1 then (1 : ℤ) else 0) := by
      unfold ubit gateBit
      rw [show (5 * k + 1 + 1 + 1 + 1) % 5 = 4 from by omega,
        show (5 * k + 1 + 1 + 1 + 1) / 5 = k from by omega]
    rw [show 5 * (k + 1) = 5 * k + 1 + 1 + 1 + 1 + 1 from by ring]
    rw [gateRegister_succ, gateRegister_succ, gateRegister_succ, gateRegister_succ,
      gateRegister_succ, ih, runBits_succ]
    unfold bitsVal
    rw [List.foldl_append, h0, h1, h2, h3, h4]
    simp only [List.foldl_cons, List.foldl_nil]

/-- The register accumulator over a run: the seed, then each gate's output register. -/
def accN (g : ℕ → Witness F) : ℕ → F
  | 0 => (g 0).n
  | i + 1 => (g i).nPrime

/-- A run of `m` `varBaseMul` rows over the base `T`: every row satisfies the gate, every
    row reads `T`, the accumulator threads from row to row, and the run opens at `2·T` —
    what the gadget's doubled seed produces. The base is stated at `i ≤ m` so an empty run
    still names its base, which is where `T ≠ 0` comes from. -/
structure Run {F : Type*} [Field F] [DecidableEq F] (c : WeierstrassCurve.Affine F)
    (T : c.Point) (g : ℕ → Witness F) (m : ℕ) : Prop where
  /-- Every row of the run satisfies the gate. -/
  holds : ∀ i, i < m → Holds (g i)
  /-- Every row reads the base point. -/
  base : ∀ i, i ≤ m → Kimchi.Gate.AddComplete.IsPoint c (g i).xT (g i).yT T
  /-- Each row's output accumulator is the next row's input. -/
  thread : ∀ i, i + 1 < m → (g (i + 1)).x0 = (g i).x5 ∧ (g (i + 1)).y0 = (g i).y5
  /-- Each row's output register is the next row's input. -/
  regThread : ∀ i, i + 1 < m → (g (i + 1)).n = (g i).nPrime
  /-- The run opens at the doubled base. -/
  init : Kimchi.Gate.AddComplete.IsPoint c (g 0).x0 (g 0).y0 ((2 : ℤ) • T)

/-- The base is nonzero: row `0` names it. -/
theorem Run.base_ne {F : Type*} [Field F] [DecidableEq F] {c : WeierstrassCurve.Affine F}
    {T : c.Point} {g : ℕ → Witness F} {m : ℕ} (h : Run c T g m) : T ≠ 0 := by
  obtain ⟨n, rfl⟩ := h.base 0 (Nat.zero_le m)
  exact Point.some_ne_zero _

/-- **The register chain.** Threading the register through `m` held gates reads the
final register as the seed shifted up `5m` bits plus the base-2 fold of the run's
bits — the gadget's scalar pin, at the zero seed. -/
theorem chain_accN {c : WeierstrassCurve.Affine F} {T : c.Point} (m : ℕ)
    (g : ℕ → Witness F) (hrun : Run c T g m) :
    accN g m = 32 ^ m * accN g 0 + bitsRegister (runBits g m) := by
  obtain ⟨hholds, -, -, hthread, -⟩ := hrun
  induction m with
  | zero => simp [bitsRegister, runBits]
  | succ k ih =>
    have hreg : (g k).nPrime
        = (g k).b4 + 2 * ((g k).b3 + 2 * ((g k).b2 + 2 * ((g k).b1
            + 2 * ((g k).b0 + 2 * (g k).n)))) := by
      have hd := ((holds_iff (g k)).mp (hholds k (by omega))).1
      unfold decompHolds decompCons at hd
      linear_combination hd
    have hn : (g k).n = accN g k := by
      cases k with
      | zero => rfl
      | succ j => exact hthread j (by omega)
    have ihk := ih (fun i hi => hholds i (by omega)) (fun i hi => hthread i (by omega))
    show (g k).nPrime = _
    rw [hreg, hn, ihk, runBits_succ]
    unfold bitsRegister
    rw [List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil]
    ring

/-- `runBits` only reads the run below `m`. -/
theorem runBits_congr (g g' : ℕ → Witness F) (m : ℕ)
    (h : ∀ i, i < m → g i = g' i) : runBits g m = runBits g' m := by
  induction m with
  | zero => rfl
  | succ k ih =>
    rw [runBits_succ, runBits_succ, ih (fun i hi => h i (by omega)),
      h k (by omega)]

/-- The ℤ-decode of a boolean bit list is nonnegative and bounded by its width. -/
theorem bitsVal_lt (l : List F) (hb : ∀ b ∈ l, b = 0 ∨ b = 1) :
    bitsVal l < 2 ^ l.length ∧ 0 ≤ bitsVal l := by
  suffices h : ∀ z : ℤ, 0 ≤ z →
      l.foldl (fun a b => 2 * a + if b = 1 then 1 else 0) z
        < 2 ^ l.length * (z + 1) ∧
      z ≤ l.foldl (fun a b => 2 * a + if b = 1 then 1 else 0) z by
    obtain ⟨h1, h2⟩ := h 0 le_rfl
    exact ⟨by simpa [bitsVal] using h1, by simpa [bitsVal] using h2⟩
  induction l with
  | nil => intro z hz; simp
  | cons b t ih =>
    intro z hz
    have hbit : (if b = 1 then (1 : ℤ) else 0) ≤ 1
        ∧ 0 ≤ (if b = 1 then (1 : ℤ) else 0) := by
      split <;> norm_num
    have hz' : 0 ≤ 2 * z + if b = 1 then (1 : ℤ) else 0 := by omega
    obtain ⟨ih1, ih2⟩ := ih (fun x hx => hb x (List.mem_cons_of_mem _ hx))
      (2 * z + if b = 1 then 1 else 0) hz'
    simp only [List.foldl_cons, List.length_cons]
    constructor
    · calc List.foldl _ (2 * z + if b = 1 then 1 else 0) t
          < 2 ^ t.length * ((2 * z + if b = 1 then 1 else 0) + 1) := ih1
        _ ≤ 2 ^ (t.length + 1) * (z + 1) := by
            rw [pow_succ]
            nlinarith [hbit.1, hbit.2,
              pow_pos (show (0 : ℤ) < 2 by norm_num) t.length]
    · omega

/-- A zero prefix contributes nothing to the ℤ-decode. -/
theorem bitsVal_drop_of_zeros (l : List F) (k : ℕ)
    (hz : ∀ b ∈ l.take k, b = 0) : bitsVal l = bitsVal (l.drop k) := by
  induction k generalizing l with
  | zero => simp
  | succ j ih =>
    cases l with
    | nil => simp
    | cons b t =>
      have hb0 : b = 0 := hz b (by simp)
      have hrest : ∀ x ∈ t.take j, x = 0 := fun x hx =>
        hz x (by
          rw [List.take_succ_cons]
          exact List.mem_cons_of_mem _ hx)
      rw [List.drop_succ_cons, ← ih t hrest]
      subst hb0
      simp [bitsVal]

/-- On boolean bits the field fold is the cast of the ℤ-decode. -/
theorem bitsRegister_eq_cast (l : List F) (hb : ∀ b ∈ l, b = 0 ∨ b = 1) :
    bitsRegister l = ((bitsVal l : ℤ) : F) := by
  suffices h : ∀ z : ℤ,
      l.foldl (fun a b => 2 * a + b) ((z : ℤ) : F)
        = ((l.foldl (fun a b => 2 * a + if b = 1 then 1 else 0) z : ℤ) : F) by
    simpa [bitsRegister, bitsVal] using h 0
  induction l with
  | nil => intro z; simp
  | cons b t ih =>
    intro z
    have hb' : b = 0 ∨ b = 1 := hb b List.mem_cons_self
    simp only [List.foldl_cons]
    have hcast : 2 * ((z : ℤ) : F) + b
        = (((2 * z + if b = 1 then 1 else 0 : ℤ)) : F) := by
      rcases hb' with rfl | rfl
      · norm_num
      · push_cast
        norm_num
    rw [hcast]
    exact ih (fun x hx => hb x (List.mem_cons_of_mem _ hx)) _

/-- Every bit of a held run is boolean: each bit block's first constraint is
`b·b − b = 0`. -/
theorem runBits_bool (m : ℕ) (g : ℕ → Witness F)
    (hholds : ∀ i, i < m → Holds (g i)) :
    ∀ b ∈ runBits g m, b = 0 ∨ b = 1 := by
  induction m with
  | zero => simp [runBits]
  | succ k ih =>
    intro b hb
    rw [runBits_succ, List.mem_append] at hb
    rcases hb with hb | hb
    · exact ih (fun i hi => hholds i (by omega)) b hb
    · have h := (holds_iff (g k)).mp (hholds k (by omega))
      have hbool : ∀ x : F, x * x - x = 0 → x = 0 ∨ x = 1 := by
        intro x hx
        rcases mul_eq_zero.mp (show x * (x - 1) = 0 by linear_combination hx) with
          h0 | h1
        · exact Or.inl h0
        · exact Or.inr (by linear_combination h1)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl | rfl | rfl | rfl
      · exact hbool _ ((singleBitHolds_iff _ _ _ _ _ _ _ _).mp h.2.1).1
      · exact hbool _ ((singleBitHolds_iff _ _ _ _ _ _ _ _).mp h.2.2.1).1
      · exact hbool _ ((singleBitHolds_iff _ _ _ _ _ _ _ _).mp h.2.2.2.1).1
      · exact hbool _ ((singleBitHolds_iff _ _ _ _ _ _ _ _).mp h.2.2.2.2.1).1
      · exact hbool _ ((singleBitHolds_iff _ _ _ _ _ _ _ _).mp h.2.2.2.2.2).1

/-- The five-bit windows tile the flat stream: a `runBits`-shaped flatMap over rows
reads the same list as the plain range read. Element type is free — the gadget's
prover-side reading tiles variables, not just field values. -/
theorem flatMap_range_window {α : Type*} (bs : ℕ → α) (m : ℕ) :
    (List.range m).flatMap
        (fun i => [bs (5 * i), bs (5 * i + 1), bs (5 * i + 2), bs (5 * i + 3),
          bs (5 * i + 4)])
      = (List.range (5 * m)).map bs := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [List.range_succ, List.flatMap_append, ih,
      show 5 * (m + 1) = 5 * m + 5 from by ring, List.range_add, List.map_append,
      List.flatMap_cons, List.flatMap_nil]
    simp [show List.range 5 = [0, 1, 2, 3, 4] from by decide]

/-- The ℤ-decode reconstructs a bounded scalar from its MSB-first bit reads: position
`j` of the list carries `testBit (L − 1 − j)`. How the honest witness's register fold
recovers the scalar it unpacked. -/
theorem bitsVal_testBit (x L : ℕ) (hx : x < 2 ^ L) :
    bitsVal ((List.range L).map fun j => if x.testBit (L - 1 - j) then (1 : F) else 0)
      = (x : ℤ) := by
  induction L generalizing x with
  | zero =>
    have hx0 : x = 0 := by simpa using hx
    subst hx0
    rfl
  | succ L ih =>
    have hsplit : ((List.range (L + 1)).map
          fun j => if x.testBit (L + 1 - 1 - j) then (1 : F) else 0)
        = ((List.range L).map
            fun j => if (x / 2).testBit (L - 1 - j) then (1 : F) else 0)
          ++ [if x.testBit 0 then (1 : F) else 0] := by
      rw [List.range_succ, List.map_append]
      congr 1
      · apply List.map_congr_left
        intro j hj
        have hj' : j < L := List.mem_range.mp hj
        rw [show L + 1 - 1 - j = (L - 1 - j) + 1 from by omega, Nat.testBit_add_one]
      · simp
    have hfold : ∀ (l : List F) (b : F),
        bitsVal (l ++ [b]) = 2 * bitsVal l + (if b = 1 then 1 else 0) := by
      intro l b
      simp [bitsVal, List.foldl_append]
    rw [hsplit, hfold, ih (x / 2) (by omega)]
    have hbit0 : x.testBit 0 = decide (x % 2 = 1) := Nat.testBit_zero x
    rcases Nat.mod_two_eq_zero_or_one x with h | h
    · rw [show (if x.testBit 0 then (1 : F) else 0) = 0 from by rw [hbit0, h]; simp,
        if_neg (zero_ne_one (α := F))]
      omega
    · rw [show (if x.testBit 0 then (1 : F) else 0) = 1 from by rw [hbit0, h]; simp,
        if_pos rfl]
      omega

end RunBits

/-! ### A run given as a list

    A circuit builds its rows as a finite list, not as a function on `ℕ`; `Run.ofList` is
    that caller's constructor, and the identities below say what the run's bit stream and
    closing accumulators read as there. -/

/-- The run a caller holding a finite list of rows builds. -/
theorem Run.ofList {F : Type*} [Field F] [DecidableEq F] (c : WeierstrassCurve.Affine F)
    (T : c.Point) (l : List (Witness F)) (dflt : Witness F)
    (hholds : ∀ w ∈ l, Holds w)
    (hbase : ∀ w ∈ dflt :: l, Kimchi.Gate.AddComplete.IsPoint c w.xT w.yT T)
    (hthread : l.IsChain fun a b => (b.x0 = a.x5 ∧ b.y0 = a.y5) ∧ b.n = a.nPrime)
    (hinit : Kimchi.Gate.AddComplete.IsPoint c (l.getD 0 dflt).x0 (l.getD 0 dflt).y0
      ((2 : ℤ) • T)) :
    Run c T (fun i => l.getD i dflt) l.length := by
  have hget : ∀ i (hi : i < l.length), l.getD i dflt = l[i] :=
    fun i hi => List.getD_eq_getElem _ _ hi
  refine ⟨fun i hi => ?_, fun i hi => ?_, fun i hi => ?_, fun i hi => ?_, hinit⟩
  · rw [hget i hi]
    exact hholds _ (List.getElem_mem _)
  · rcases Nat.lt_or_ge i l.length with h | h
    · rw [hget i h]
      exact hbase _ (List.mem_cons_of_mem _ (List.getElem_mem _))
    · rw [List.getD_eq_default _ _ h]
      exact hbase _ (List.mem_cons_self ..)
  · rw [hget (i + 1) hi, hget i (by omega)]
    exact (hthread.getElem i hi).1
  · rw [hget (i + 1) hi, hget i (by omega)]
    exact (hthread.getElem i hi).2

/-- The bit stream of a run given as a list: its rows' five bits, concatenated. -/
theorem runBits_getD {F : Type*} [Field F] [DecidableEq F] (l : List (Witness F))
    (dflt : Witness F) :
    runBits (fun i => l.getD i dflt) l.length
      = l.flatMap fun w => [w.b0, w.b1, w.b2, w.b3, w.b4] := by
  rw [runBits, List.flatMap_def, List.flatMap_def]
  congr 1
  refine List.ext_getElem (by simp) fun i _ h2 => ?_
  simp only [List.getElem_map, List.getElem_range]
  rw [List.getD_eq_getElem _ _ (by simpa using h2)]

/-- A run given as a list closes at its last row's outputs. -/
theorem acc_getD_length {F : Type*} [Field F] [DecidableEq F] (l : List (Witness F))
    (hne : l ≠ []) (dflt : Witness F) :
    accX (fun i => l.getD i dflt) l.length = (l.getLast hne).x5
      ∧ accY (fun i => l.getD i dflt) l.length = (l.getLast hne).y5
      ∧ accN (fun i => l.getD i dflt) l.length = (l.getLast hne).nPrime := by
  obtain ⟨k, hk⟩ : ∃ k, l.length = k + 1 :=
    ⟨l.length - 1, by have := List.length_pos_iff.mpr hne; omega⟩
  have hlast : l.getD k dflt = l.getLast hne := by
    rw [List.getD_eq_getElem _ _ (by omega), List.getLast_eq_getElem]
    congr 1
    omega
  refine ⟨?_, ?_, ?_⟩ <;> rw [hk]
  · show (l.getD k dflt).x5 = _
    rw [hlast]
  · show (l.getD k dflt).y5 = _
    rw [hlast]
  · show (l.getD k dflt).nPrime = _
    rw [hlast]

/-- **The generic off-band entry point.** `varBaseMul_subwrap_correct` and
    `varBaseMul_forbidden_correct` behind one regime dichotomy, for generic (dictionary)
    callers: EITHER the whole ladder fits below the order (`3·2^(5m) ≤ order`, no
    condition on the scalar), OR the one-wrap band holds and the scalar's ladder decode
    avoids the forbidden residues. The deployed `varBaseMul_scaleFast{1,2}` below stay
    the per-curve certificates. -/
theorem varBaseMul_off {F : Type*} [Field F] [DecidableEq F]
    (c : WeierstrassCurve.Affine F)
    [Fact (c.a₁ = 0 ∧ c.a₂ = 0 ∧ c.a₃ = 0)] [Fact (Nat.Prime c.order)]
    (m : ℕ) (g : ℕ → Witness F) (T : c.Point) (s : ℤ) (hrun : Run c T g m)
    (h2 : (2 : F) ≠ 0) (hodd : c.order ≠ 2)
    (hs : s = gateLadder g (5 * m))
    (hregime : 3 * 2 ^ (5 * m) ≤ c.order ∨
      (2 ^ (5 * m - 1) < c.order ∧ c.order < 2 ^ (5 * m) ∧ c.order % 4 = 1 ∧
        s ∉ forbiddenValues c.order)) :
    ∃ hfin : c.Nonsingular (accX g m) (accY g m),
      Point.some _ _ hfin = s • T ∧ ∀ i, i < m → NonDegen (g i) := by
  obtain ⟨hTns, hTeq⟩ := hrun.base 0 (Nat.zero_le m)
  obtain ⟨hP0ns, hP0⟩ := hrun.init
  have hTne := hrun.base_ne
  have hholds := hrun.holds
  have hthread := hrun.thread
  have hbase : ∀ i, i < m → (g i).xT = (g 0).xT ∧ (g i).yT = (g 0).yT := fun i hi =>
    Kimchi.Gate.AddComplete.IsPoint.coords_eq (hrun.base i (le_of_lt hi))
      (hrun.base 0 (Nat.zero_le m))
  rcases hregime with hsub | ⟨hr1, hr2, hq4, hnf⟩
  · exact varBaseMul_subwrap_correct c m g T s hTne hholds hTns hTeq hbase hthread
      hP0ns hP0.symm h2 hodd hsub hs
  · exact varBaseMul_forbidden_correct c m g T s hTne hholds hTns hTeq hbase hthread
      hP0ns hP0.symm h2 hodd hr1 hr2 hq4 hs hnf

/-! ## The produce chain

The honest walk: `chainBuild` threads the gate's canonical row (`build`) from the doubled
init accumulator through a flat bit stream, five bits per row. `chain_complete` is its
conditional completeness — under either ladder regime, every generated row satisfies the
gate. The non-degeneracy is PRODUCED forward, not read off an accepted run: the
accumulator entering bit step `j` is the ladder multiple `[gateLadder g j]·T`, the regime
prices all four degeneracy residues at every step (`ladder_subwrap_nondegen` /
`ladder_nondegen_tight`), and each generated step's two secant denominators are derived
from those residues before the step is certified (`step_produce`). -/

variable {F : Type*} [Field F] [DecidableEq F]

/-- The honest rows: row `i` is `build` at the threaded accumulator and register,
consuming bits `5i … 5i+4` of the stream. -/
def chainBuild (xT yT x0 y0 n0 : F) (bs : ℕ → F) : ℕ → Witness F
  | 0 => build xT yT x0 y0 n0 (bs 0) (bs 1) (bs 2) (bs 3) (bs 4)
  | i + 1 =>
    build xT yT (chainBuild xT yT x0 y0 n0 bs i).x5 (chainBuild xT yT x0 y0 n0 bs i).y5
      (chainBuild xT yT x0 y0 n0 bs i).nPrime
      (bs (5 * (i + 1))) (bs (5 * (i + 1) + 1)) (bs (5 * (i + 1) + 2))
      (bs (5 * (i + 1) + 3)) (bs (5 * (i + 1) + 4))

omit [DecidableEq F] in
/-- The walk's gate bits ARE the stream it was built from: sub-step `j` reads `bs j`.
What lets the honest walk speak the sound side's ladder vocabulary (`gateLadder`)
rather than a second copy of it. -/
private lemma gateBit_chainBuild (xT yT x0 y0 n0 : F) (bs : ℕ → F) (j : ℕ) :
    gateBit (chainBuild xT yT x0 y0 n0 bs) j = bs j := by
  have h : j = 5 * (j / 5) + j % 5 := by omega
  have h5 : j % 5 < 5 := Nat.mod_lt _ (by omega)
  unfold gateBit
  interval_cases hm : (j % 5) <;> (conv_rhs => rw [h]) <;> cases (j / 5) <;> rfl

/-- Hence the walk's signed digit at sub-step `j` is the stream bit's sign. -/
private lemma gateBitSign_chainBuild (xT yT x0 y0 n0 : F) (bs : ℕ → F) (j : ℕ) :
    gateBitSign (chainBuild xT yT x0 y0 n0 bs) j = bitSign (bs j) := by
  unfold gateBitSign; rw [gateBit_chainBuild]

omit [DecidableEq F] in
/-- Every `chainBuild` row is `build` at its own threaded fields — the uniform
re-expression the produce induction rewrites with. -/
theorem chainBuild_eta (xT yT x0 y0 n0 : F) (bs : ℕ → F) (i : ℕ) :
    chainBuild xT yT x0 y0 n0 bs i
      = build xT yT (chainBuild xT yT x0 y0 n0 bs i).x0
          (chainBuild xT yT x0 y0 n0 bs i).y0 (chainBuild xT yT x0 y0 n0 bs i).n
          (bs (5 * i)) (bs (5 * i + 1)) (bs (5 * i + 2)) (bs (5 * i + 3))
          (bs (5 * i + 4)) := by
  cases i <;> rfl

omit [DecidableEq F] in
/-- The walk from row `1` on is the walk from row `0`'s outputs at the stream shifted
past row `0`'s five bits — what a caller reading the run off one round at a time needs
to step its induction. -/
theorem chainBuild_shift (xT yT x0 y0 n0 : F) (bs : ℕ → F) :
    ∀ j : ℕ, chainBuild xT yT x0 y0 n0 bs (j + 1)
      = chainBuild xT yT (chainBuild xT yT x0 y0 n0 bs 0).x5
          (chainBuild xT yT x0 y0 n0 bs 0).y5
          (chainBuild xT yT x0 y0 n0 bs 0).nPrime (fun n => bs (n + 5)) j
  | 0 => by
    show build xT yT _ _ _ (bs (5 * 1)) (bs (5 * 1 + 1)) (bs (5 * 1 + 2)) (bs (5 * 1 + 3))
      (bs (5 * 1 + 4)) = build xT yT _ _ _ (bs (0 + 5)) (bs (1 + 5)) (bs (2 + 5))
      (bs (3 + 5)) (bs (4 + 5))
    norm_num
  | j + 1 => by
    show build xT yT (chainBuild xT yT x0 y0 n0 bs (j + 1)).x5
      (chainBuild xT yT x0 y0 n0 bs (j + 1)).y5
      (chainBuild xT yT x0 y0 n0 bs (j + 1)).nPrime _ _ _ _ _ = _
    rw [chainBuild_shift xT yT x0 y0 n0 bs j]
    congr 1

/-! The walk's structural equations: how a row's input cells thread from the previous
row's outputs, and which of its cells are the arguments. The per-field equations of a
row itself belong to `build` (`Kimchi/Gate/VarBaseMul`), which the walk is built from
and `chainBuild_eta` re-expresses it as. -/

section ChainFields

variable (xT yT x0 y0 n0 : F) (bs : ℕ → F)

omit [DecidableEq F]

theorem chainBuild_succ_x0 (i : ℕ) :
    (chainBuild xT yT x0 y0 n0 bs (i + 1)).x0 = (chainBuild xT yT x0 y0 n0 bs i).x5 :=
  rfl

theorem chainBuild_succ_y0 (i : ℕ) :
    (chainBuild xT yT x0 y0 n0 bs (i + 1)).y0 = (chainBuild xT yT x0 y0 n0 bs i).y5 :=
  rfl

theorem chainBuild_succ_n (i : ℕ) :
    (chainBuild xT yT x0 y0 n0 bs (i + 1)).n
      = (chainBuild xT yT x0 y0 n0 bs i).nPrime :=
  rfl

/-- The row's fixed cells: the base is the argument and the five bits are the
stream's window `5m … 5m+4`. -/
theorem chainBuild_fields (m : ℕ) :
    (chainBuild xT yT x0 y0 n0 bs m).xT = xT
    ∧ (chainBuild xT yT x0 y0 n0 bs m).yT = yT
    ∧ (chainBuild xT yT x0 y0 n0 bs m).b0 = bs (5 * m)
    ∧ (chainBuild xT yT x0 y0 n0 bs m).b1 = bs (5 * m + 1)
    ∧ (chainBuild xT yT x0 y0 n0 bs m).b2 = bs (5 * m + 2)
    ∧ (chainBuild xT yT x0 y0 n0 bs m).b3 = bs (5 * m + 3)
    ∧ (chainBuild xT yT x0 y0 n0 bs m).b4 = bs (5 * m + 4) := by
  cases m <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem accX_chainBuild (m : ℕ) :
    accX (chainBuild xT yT x0 y0 n0 bs) m = (chainBuild xT yT x0 y0 n0 bs m).x0 := by
  cases m <;> rfl

theorem accY_chainBuild (m : ℕ) :
    accY (chainBuild xT yT x0 y0 n0 bs) m = (chainBuild xT yT x0 y0 n0 bs m).y0 := by
  cases m <;> rfl

theorem accN_chainBuild (m : ℕ) :
    accN (chainBuild xT yT x0 y0 n0 bs) m = (chainBuild xT yT x0 y0 n0 bs m).n := by
  cases m <;> rfl

end ChainFields

omit [DecidableEq F] in
/-- The walk's bit stream is the stream it was built from: row `i` carries `bs 5i … bs 5i+4`. -/
theorem runBits_chainBuild (xT yT x0 y0 n0 : F) (bs : ℕ → F) (m : ℕ) :
    runBits (chainBuild xT yT x0 y0 n0 bs) m = (List.range (5 * m)).map bs := by
  rw [← flatMap_range_window bs m, runBits]
  congr 1
  funext i
  obtain ⟨-, -, h0, h1, h2, h3, h4⟩ := chainBuild_fields xT yT x0 y0 n0 bs i
  rw [h0, h1, h2, h3, h4]

/-- One honest bit step: at an accumulator `[k]·T` whose four degeneracy residues the
regime has priced away, the generated `stepBit` values satisfy the bit block and the
output is the nonsingular `[2k + bitSign b]·T`. The two secant denominators are derived,
not assumed: `xi ≠ xT` from `k ≢ ±1`, and the second denominator from the intermediate
`I + Q ≠ ±I`, i.e. `2k ≢ ∓1` (stepped through in the body). -/
private lemma step_produce (c : WeierstrassCurve.Affine F)
    [Fact (c.a₁ = 0 ∧ c.a₂ = 0 ∧ c.a₃ = 0)] [Fact (Nat.Prime c.order)]
    (h2 : (2 : F) ≠ 0) (hodd : c.order ≠ 2)
    {xT yT b xi yi : F}
    (hTns : c.Nonsingular xT yT) (hTne : Point.some _ _ hTns ≠ 0)
    (hI : c.Nonsingular xi yi) (hbit : b = 0 ∨ b = 1)
    {k : ℤ} (hIk : Point.some _ _ hI = k • Point.some _ _ hTns)
    (hq1 : ¬((c.order : ℤ) ∣ (k - 1))) (hq2 : ¬((c.order : ℤ) ∣ (k + 1)))
    (hq3 : ¬((c.order : ℤ) ∣ (2 * k - 1))) (hq4 : ¬((c.order : ℤ) ∣ (2 * k + 1))) :
    singleBitHolds b xT yT (stepBit b xT yT xi yi).1 xi yi
        (stepBit b xT yT xi yi).2.1 (stepBit b xT yT xi yi).2.2
    ∧ ∃ hO : c.Nonsingular (stepBit b xT yT xi yi).2.1 (stepBit b xT yT xi yi).2.2,
        Point.some _ _ hO = (2 * k + bitSign b) • Point.some _ _ hTns := by
  have hshort : c.a₁ = 0 ∧ c.a₂ = 0 ∧ c.a₃ = 0 := Fact.out
  -- the sign-selected target `Q = ±T` and its scalar
  have hQ : c.Nonsingular xT ((2 * b - 1) * yT) := signed_target_nonsingular c hshort hTns hbit
  obtain ⟨e, heQ, -, hepm⟩ := signed_target c hshort hTns hQ hbit
  -- first denominator: `xi ≠ xT` from `k ≢ ±1`
  have hxne : xi ≠ xT := by
    apply x_ne_xT_of_ne_base c hI hTns
    · contrapose! hq1
      have hd : (k - 1) • Point.some _ _ hTns = 0 := by
        rw [sub_smul, one_smul, ← hIk, hq1, sub_self]
      exact (zsmul_eq_zero_iff_order_dvd c hTne _).1 hd
    · contrapose! hq2
      rw [← zsmul_eq_zero_iff_order_dvd c hTne, add_zsmul, one_zsmul, ← hIk, hq2,
        neg_add_cancel]
  -- the generated values, named
  set s1 : F := (yi - (2 * b - 1) * yT) / (xi - xT) with hs1
  set t : F := 2 * xi + xT - s1 * s1 with htdef
  have e1 : (stepBit b xT yT xi yi).1 = s1 := rfl
  -- the intermediate `M = I + Q = [k + e]·T` at the generated first slope
  obtain ⟨hM, hMadd⟩ := secant_add c hshort hI hQ hxne hs1
    (x3 := s1 * s1 - xi - xT) (y3 := s1 * (xi - (s1 * s1 - xi - xT)) - yi) rfl rfl
  have hMk : Point.some _ _ hM = (k + e) • Point.some _ _ hTns := by
    rw [← hMadd, hIk, heQ]; module
  -- second denominator: `M ≠ ±I` from `2k ≢ ∓1`, so `x_M ≠ xi` and `t = xi − x_M ≠ 0`
  have hMneI : Point.some _ _ hM ≠ Point.some _ _ hI := by
    intro h
    have he0 : e • Point.some _ _ hTns = 0 := by
      have h' : ((k + e) - k) • Point.some _ _ hTns = 0 := by
        rw [sub_smul, ← hMk, h, hIk, sub_self]
      simpa using h'
    rcases hepm with rfl | rfl
    · rw [one_zsmul] at he0; exact hTne he0
    · rw [neg_one_zsmul, neg_eq_zero] at he0; exact hTne he0
  have hMnegI : Point.some _ _ hM ≠ -Point.some _ _ hI := by
    intro h
    have hz : (2 * k + e) • Point.some _ _ hTns = 0 := by
      have h' : (k + e) • Point.some _ _ hTns + k • Point.some _ _ hTns = 0 := by
        rw [← hMk, ← hIk, h, neg_add_cancel]
      calc (2 * k + e) • Point.some _ _ hTns
          = (k + e) • Point.some _ _ hTns + k • Point.some _ _ hTns := by module
        _ = 0 := h'
    have hdvd := (zsmul_eq_zero_iff_order_dvd c hTne _).1 hz
    rcases hepm with rfl | rfl
    · exact hq4 hdvd
    · exact hq3 (by rwa [show 2 * k + (-1 : ℤ) = 2 * k - 1 from by ring] at hdvd)
  have hxMne : s1 * s1 - xi - xT ≠ xi := x_ne_xT_of_ne_base c hM hI hMneI hMnegI
  have htne : t ≠ 0 := by
    rw [htdef]
    intro h0
    exact hxMne (by linear_combination -h0)
  -- the generated block holds, and the sound step reads its output back
  have hbb : b * b - b = 0 := by rcases hbit with rfl | rfl <;> ring
  have hh := stepBit_holds b xT yT xi yi hbb (sub_ne_zero_of_ne hxne)
    (by rw [e1, ← htdef]; exact htne)
  obtain ⟨-, -, hO, e', hepm', heF', hOeq⟩ :=
    gate_step_advance' c h2 hodd hTns hI hQ hbit hTne k hIk hq1 hq2 hh
  exact ⟨hh, hO, by rw [hOeq, e_eq_bitSign hbit heF' hepm' h2]⟩

/-- One honest row: five `step_produce` steps threaded through `build`. The row's
constraints hold and the output accumulator is the nonsingular five-fold advance
`[k (j+5)]·T`, for any scalar sequence `k` satisfying the ladder recurrence on the
row's bits whose window `[j, j+5)` the regime has priced. -/
private lemma row_produce (c : WeierstrassCurve.Affine F)
    [Fact (c.a₁ = 0 ∧ c.a₂ = 0 ∧ c.a₃ = 0)] [Fact (Nat.Prime c.order)]
    (h2 : (2 : F) ≠ 0) (hodd : c.order ≠ 2)
    {xT yT : F} (hTns : c.Nonsingular xT yT) (hTne : Point.some _ _ hTns ≠ 0)
    {b0 b1 b2 b3 b4 x0 y0 : F} (n : F)
    (hb0 : b0 = 0 ∨ b0 = 1) (hb1 : b1 = 0 ∨ b1 = 1) (hb2 : b2 = 0 ∨ b2 = 1)
    (hb3 : b3 = 0 ∨ b3 = 1) (hb4 : b4 = 0 ∨ b4 = 1)
    (hI : c.Nonsingular x0 y0)
    {k : ℕ → ℤ} {j : ℕ}
    (hIk : Point.some _ _ hI = k j • Point.some _ _ hTns)
    (hk1 : k (j + 1) = 2 * k j + bitSign b0)
    (hk2 : k (j + 2) = 2 * k (j + 1) + bitSign b1)
    (hk3 : k (j + 3) = 2 * k (j + 2) + bitSign b2)
    (hk4 : k (j + 4) = 2 * k (j + 3) + bitSign b3)
    (hk5 : k (j + 5) = 2 * k (j + 4) + bitSign b4)
    (hq : ∀ l, j ≤ l → l < j + 5 →
      ¬((c.order : ℤ) ∣ (k l - 1)) ∧ ¬((c.order : ℤ) ∣ (k l + 1))
      ∧ ¬((c.order : ℤ) ∣ (2 * k l - 1)) ∧ ¬((c.order : ℤ) ∣ (2 * k l + 1))) :
    Holds (build xT yT x0 y0 n b0 b1 b2 b3 b4)
    ∧ ∃ h5 : c.Nonsingular (build xT yT x0 y0 n b0 b1 b2 b3 b4).x5
        (build xT yT x0 y0 n b0 b1 b2 b3 b4).y5,
        Point.some _ _ h5 = k (j + 5) • Point.some _ _ hTns := by
  obtain ⟨hd1, hd2, hd3, hd4⟩ := hq j le_rfl (by omega)
  obtain ⟨hh0, hO1, hP1⟩ := step_produce c h2 hodd hTns hTne hI hb0 hIk hd1 hd2 hd3 hd4
  rw [← hk1] at hP1
  obtain ⟨hd1, hd2, hd3, hd4⟩ := hq (j + 1) (by omega) (by omega)
  obtain ⟨hh1, hO2, hP2⟩ := step_produce c h2 hodd hTns hTne hO1 hb1 hP1 hd1 hd2 hd3 hd4
  rw [← hk2] at hP2
  obtain ⟨hd1, hd2, hd3, hd4⟩ := hq (j + 2) (by omega) (by omega)
  obtain ⟨hh2, hO3, hP3⟩ := step_produce c h2 hodd hTns hTne hO2 hb2 hP2 hd1 hd2 hd3 hd4
  rw [← hk3] at hP3
  obtain ⟨hd1, hd2, hd3, hd4⟩ := hq (j + 3) (by omega) (by omega)
  obtain ⟨hh3, hO4, hP4⟩ := step_produce c h2 hodd hTns hTne hO3 hb3 hP3 hd1 hd2 hd3 hd4
  rw [← hk4] at hP4
  obtain ⟨hd1, hd2, hd3, hd4⟩ := hq (j + 4) (by omega) (by omega)
  obtain ⟨hh4, hO5, hP5⟩ := step_produce c h2 hodd hTns hTne hO4 hb4 hP4 hd1 hd2 hd3 hd4
  rw [← hk5] at hP5
  exact ⟨(holds_iff _).mpr
    ⟨by simp only [decompHolds, decompCons, build]; ring, hh0, hh1, hh2, hh3, hh4⟩,
    hO5, hP5⟩

/-- **Completeness of the honest ladder.** From the doubled init `P₀ = [2]·T`, under
either ladder regime — subwrap (`3·2^(5m) ≤ order`, no condition on the bits) or the
one-wrap band with the walk's ladder value `gateLadder (chainBuild …) (5m)` avoiding
the forbidden residues — every generated row satisfies the gate. The regime dichotomy
is `varBaseMul_off`'s, at the honest values, and stated in its vocabulary: the walk's
gate bits are the stream (`gateBit_chainBuild`), so the sound side's `gateLadder` is
the honest ladder and `gateLadder_eq_register` is the decode a caller discharges the
band condition with. -/
theorem chain_complete (c : WeierstrassCurve.Affine F)
    [Fact (c.a₁ = 0 ∧ c.a₂ = 0 ∧ c.a₃ = 0)] [Fact (Nat.Prime c.order)]
    (h2 : (2 : F) ≠ 0) (hodd : c.order ≠ 2) (m : ℕ)
    {xT yT : F} (hTns : c.Nonsingular xT yT)
    (bs : ℕ → F) (hbs : ∀ j, j < 5 * m → bs j = 0 ∨ bs j = 1)
    {x0 y0 : F} (n0 : F) (hP0 : c.Nonsingular x0 y0)
    (hP0eq : Point.some _ _ hP0 = (2 : ℤ) • Point.some _ _ hTns)
    (hregime : 3 * 2 ^ (5 * m) ≤ c.order ∨
      (2 ^ (5 * m - 1) < c.order ∧ c.order < 2 ^ (5 * m) ∧ c.order % 4 = 1 ∧
        gateLadder (chainBuild xT yT x0 y0 n0 bs) (5 * m) ∉ forbiddenValues c.order)) :
    ∀ i, i < m → Holds (chainBuild xT yT x0 y0 n0 bs i) := by
  have hTne : Point.some _ _ hTns ≠ 0 := Point.some_ne_zero hTns
  set g := chainBuild xT yT x0 y0 n0 bs with hg
  -- the regime prices all four degeneracy residues at every bit step
  have hquad : ∀ j, j < 5 * m →
      ¬((c.order : ℤ) ∣ (gateLadder g j - 1)) ∧ ¬((c.order : ℤ) ∣ (gateLadder g j + 1))
      ∧ ¬((c.order : ℤ) ∣ (2 * gateLadder g j - 1))
      ∧ ¬((c.order : ℤ) ∣ (2 * gateLadder g j + 1)) := by
    rcases hregime with hsub | ⟨hr1, hr2, hq4, hnf⟩
    · exact Ladder.ladder_subwrap_nondegen c.order (5 * m) hsub (gateLadder g)
        (gateBitSign g) (gateLadder_zero g) (fun j _ => gateBitSign_eq g j)
        (fun j _ => gateLadder_succ g j)
    · refine Ladder.ladder_nondegen_tight c.order (5 * m)
        (Fact.out : Nat.Prime c.order) hq4 hr1 hr2 (gateLadder g)
        (gateBitSign g) (gateLadder_zero g) (fun j _ => gateBitSign_eq g j)
        (fun j _ => gateLadder_succ g j) ?_
      intro t ht hdvd
      exact hnf ⟨t, ht, hdvd⟩
  -- rows hold and the accumulator threads as the ladder multiple
  have main : ∀ i, i ≤ m →
      (∀ i', i' < i → Holds (chainBuild xT yT x0 y0 n0 bs i'))
      ∧ ∃ hIi : c.Nonsingular (chainBuild xT yT x0 y0 n0 bs i).x0
          (chainBuild xT yT x0 y0 n0 bs i).y0,
          Point.some _ _ hIi = gateLadder g (5 * i) • Point.some _ _ hTns := by
    intro i
    induction i with
    | zero =>
      intro _
      exact ⟨fun i' hi' => absurd hi' (Nat.not_lt_zero i'), hP0, by simpa using hP0eq⟩
    | succ i ih =>
      intro hi
      obtain ⟨hrows, hIi, hIeq⟩ := ih (by omega)
      obtain ⟨hrow, h5, h5eq⟩ := row_produce c h2 hodd hTns hTne
        (chainBuild xT yT x0 y0 n0 bs i).n
        (hbs (5 * i) (by omega)) (hbs (5 * i + 1) (by omega)) (hbs (5 * i + 2) (by omega))
        (hbs (5 * i + 3) (by omega)) (hbs (5 * i + 4) (by omega)) hIi
        (k := gateLadder g) (j := 5 * i) hIeq
        (by rw [gateLadder_succ, gateBitSign_chainBuild])
        (by rw [gateLadder_succ, gateBitSign_chainBuild])
        (by rw [gateLadder_succ, gateBitSign_chainBuild])
        (by rw [gateLadder_succ, gateBitSign_chainBuild])
        (by rw [gateLadder_succ, gateBitSign_chainBuild])
        (fun l hl hl' => hquad l (by omega))
      refine ⟨fun i' hi' => ?_, ?_⟩
      · rcases Nat.lt_or_ge i' i with h | h
        · exact hrows i' h
        · have : i' = i := by omega
          subst this
          rw [chainBuild_eta]
          exact hrow
      · show ∃ hIi : c.Nonsingular (chainBuild xT yT x0 y0 n0 bs i).x5
            (chainBuild xT yT x0 y0 n0 bs i).y5,
            Point.some _ _ hIi = gateLadder g (5 * (i + 1)) • Point.some _ _ hTns
        rw [chainBuild_eta xT yT x0 y0 n0 bs i,
          show (5 : ℕ) * (i + 1) = 5 * i + 5 from by ring]
        exact ⟨h5, h5eq⟩
  exact (main m le_rfl).1

/-! ## The `scaleFast1` / Type1 direction: soundness via the forbidden band (Vesta)

`scaleFast2` (the Pallas direction, below) range-checks the register, so its soundness is the
field-bound route (inlined into `varBaseMul_scaleFast2`). `scaleFast1` (the Vesta direction;
scalar field < circuit field) range-checks nothing and instead guards with a forbidden-value check.
Its soundness splits by chunk count `m` (`bitsUsed = 5m ≤ FieldSizeInBits = pastaFieldBits`): for
`m ≤ 50` the ladder fits below the order and every row is non-degenerate unconditionally
(`varBaseMul_subwrap_correct`); only the full width `m = 51` is the one-wrap case that needs the
forbidden band (`varBaseMul_forbidden_correct`).

The full-width `m = 51` case excludes the COMPLETE forbidden band, which is *stronger* than mina's
incomplete runtime guard; the faithfulness caveat is in `§ Soundness: avoiding `±T` makes
    every row non-degenerate`. -/

/-- **scaleFast1 / Type1 on the real Vesta curve: correct + sound for any chunk count `m ∈ 1..51`.**
    The single hypothesis on the bit count is `hbits : 5 * m ≤ pastaFieldBits`
    (`bitsUsed ≤ FieldSizeInBits`). The forbidden-band exclusion `hnf` is required **only at the
    full width** `5m = pastaFieldBits` — a conditional hypothesis — because every smaller chunk
    count is in the sub-wrap regime and is sound with no guard at all. The proof dispatches:
    `5m ≤ pastaFieldBits - 5` → `varBaseMul_subwrap_correct` (`3·2^(5m) ≤ PALLAS_BASE_CARD` by
    computation); `5m = pastaFieldBits` → `varBaseMul_forbidden_correct`
    (one-wrap, regime bounds + `order ≡ 1 mod 4` discharged from the cardinal). See
    `§ Soundness: avoiding `±T` makes every row non-degenerate` for the band-vs-deployed-check
    faithfulness caveat. -/
theorem varBaseMul_scaleFast1
    (m : ℕ) (g : ℕ → Witness Fq)
    (T : Vesta.curve.toAffine.Point) (s : ℤ) (hrun : Run Vesta.curve.toAffine T g m)
    (hbits : 5 * m ≤ pastaFieldBits)
    (hs : s = gateLadder g (5 * m))
    (hnf : 5 * m = pastaFieldBits → s ∉ forbiddenValues Vesta.curve.toAffine.order) :
    ∃ hfin : Vesta.curve.toAffine.Nonsingular (accX g m) (accY g m),
      Point.some _ _ hfin = s • T ∧ ∀ i, i < m → NonDegen (g i) := by
  obtain ⟨hTns, hTeq⟩ := hrun.base 0 (Nat.zero_le m)
  obtain ⟨hP0ns, hP0'⟩ := hrun.init
  have hP0 := hP0'.symm
  have hTne := hrun.base_ne
  have hholds := hrun.holds
  have hthread := hrun.thread
  have hbase : ∀ i, i < m → (g i).xT = (g 0).xT ∧ (g i).yT = (g 0).yT := fun i hi =>
    Kimchi.Gate.AddComplete.IsPoint.coords_eq (hrun.base i (le_of_lt hi))
      (hrun.base 0 (Nat.zero_le m))
  have hodd : Vesta.curve.toAffine.order ≠ 2 := by rw [Pasta.vesta_card]; decide
  rcases Nat.lt_or_ge (5 * m) pastaFieldBits with hlt | hge
  · -- sub-wrap: `5m` below `pastaFieldBits` with `5 ∣ 5m` ⟹ `5m ≤ pastaFieldBits - 5` ⟹ safe.
    refine varBaseMul_subwrap_correct Vesta.curve.toAffine m g T s hTne hholds hTns hTeq hbase
      hthread hP0ns hP0
      (by decide) hodd ?_ hs
    rw [Pasta.vesta_card]
    have hp : (2 : ℕ) ^ (5 * m) ≤ 2 ^ (pastaFieldBits - 5) :=
      Nat.pow_le_pow_right (by norm_num) (by have : pastaFieldBits = 255 := rfl; omega)
    have : (3 : ℕ) * 2 ^ (pastaFieldBits - 5) ≤ PALLAS_BASE_CARD := by norm_num [PALLAS_BASE_CARD]
    omega
  · -- one-wrap: `5m = pastaFieldBits` exactly.
    have hfull : 5 * m = pastaFieldBits := by omega
    exact varBaseMul_forbidden_correct Vesta.curve.toAffine m g T s hTne hholds hTns hTeq hbase
      hthread hP0ns hP0
      (by decide) hodd
      (by rw [Pasta.vesta_card, hfull]; norm_num [PALLAS_BASE_CARD])
      (by rw [Pasta.vesta_card, hfull]; norm_num [PALLAS_BASE_CARD])
      (by rw [Pasta.vesta_card]; norm_num [PALLAS_BASE_CARD])
      hs (hnf hfull)

/-! ## scaleFast2 / Type2: the parity-split entry point (Pallas direction)

`scaleFast2 base {sDiv2, sOdd}` does not call `varBaseMul` directly. It runs the inner
`varBaseMul base (Type1 sDiv2)`, asserts the high bits of the decomposition zero — forcing
`sDiv2 < 2^(pastaFieldBits-1)` — and applies the parity correction `if sOdd then g else g − base`.
So the inner register is `sDiv2 < 2^(pastaFieldBits-1) < p`, which discharges `hkL` via the
signed-ladder/register bridge (`gateLadder_eq_register`): no separate range hypothesis beyond
`sDiv2`'s bound. The field-bound non-degeneracy at Pallas is inlined below — a bare `varBaseMul` is
never a deployed entry point on its own. The split itself is modeled by `scalarMul_type2`. -/

/-- **scaleFast2 on the real Pallas curve.** The Type2 entry point: the scalar is split
    `s = 2·sDiv2 + sOdd`, the register `N` holds `sDiv2` (range-checked to
    `gateRegister g (5m) < 2^(pastaFieldBits-1)` — the deployed `sDiv2 < 2^(pastaFieldBits-1)`), and
    the `m` gates run the inner `varBaseMul`. The prover supplies only the gate `Holds` per row +
    base + threading + the initial accumulator + the parity bit `sOdd ∈ {0,1}`; the final
    accumulator `Point.some _ _ hfin` (its nonsingularity *derived*, like `endoMul`) and the scalar
    `n` are *exposed in the conclusion*. The parity correction is stated on that accumulator:
    `if sOdd then P m else P m − T = [n]·T`, with `(n : F) = unshiftType2 (5m) (N m) sOdd =
    2·(N m) + sOdd + 2^(5m)`. Non-degeneracy comes from the range-check
    (`sDiv2 < 2^(pastaFieldBits-1) ≤ p` ⟹ `hkL` via `gateLadder_eq_register`), feeding
    `gateStep_chain` for the derived `GateStep`s; `scalarMul_type2` then supplies the split +
    correction — matching the PureScript `scaleFast2` exactly. -/
theorem varBaseMul_scaleFast2
    (m : ℕ) (hm : 0 < m) (g : ℕ → Witness Fp)
    (T : Pallas.curve.toAffine.Point) (N : ℕ → Fp)
    (hrun : Run Pallas.curve.toAffine T g m)
    (hregIn : ∀ i, i < m → N i = (g i).n)
    (hregOut : ∀ i, i < m → N (i + 1) = (g i).nPrime)
    (hN0 : N 0 = 0)
    (hbits : 5 * m ≤ pastaFieldBits)
    (hsDiv2 : gateRegister g (5 * m) < 2 ^ (pastaFieldBits - 1))
    (sOdd : Fp) (hsOdd : sOdd = 0 ∨ sOdd = 1) :
    ∃ (hfin : Pallas.curve.toAffine.Nonsingular (accX g m) (accY g m)) (n : ℤ),
      (n : Fp) = unshiftType2 (5 * m) (N m) sOdd
        ∧ ((sOdd = 1 ∧ Point.some _ _ hfin = n • T)
            ∨ (sOdd = 0 ∧ Point.some _ _ hfin - T = n • T)) := by
  obtain ⟨hTns, hTeq⟩ := hrun.base 0 (Nat.zero_le m)
  obtain ⟨hP0ns, hP0'⟩ := hrun.init
  have hP0 := hP0'.symm
  have hTne := hrun.base_ne
  have hholds := hrun.holds
  have hthread := hrun.thread
  have hbase : ∀ i, i < m → (g i).xT = (g 0).xT ∧ (g i).yT = (g 0).yT := fun i hi =>
    Kimchi.Gate.AddComplete.IsPoint.coords_eq (hrun.base i (le_of_lt hi))
      (hrun.base 0 (Nat.zero_le m))
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
  have h2 : (2 : Fp) ≠ 0 := by decide
  have hodd : Pallas.curve.toAffine.order ≠ 2 := by rw [Pasta.pallas_card]; decide
  have hq : Pallas.curve.toAffine.order = PALLAS_SCALAR_CARD := Pasta.pallas_card
  have hcanon : gateLadder g (5 * (k + 1)) < 2 * (PALLAS_BASE_CARD : ℤ) + 2 ^ (5 * (k + 1)) := by
    rw [gateLadder_eq_register]
    have hp : (2 ^ (pastaFieldBits - 1) : ℤ) ≤ PALLAS_BASE_CARD := by
      exact_mod_cast two_pow_le_pallas_base
    linarith
  have hpow : (2 : ℕ) ^ (5 * (k + 1) - 1) ≤ 2 ^ (pastaFieldBits - 1) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have hND := Ladder.ladder_x_nondegen Pallas.curve.toAffine.order PALLAS_BASE_CARD (5 * (k + 1))
    (by rw [hq]; exact lt_of_le_of_lt hpow (by norm_num [PALLAS_SCALAR_CARD]))
    ((Fact.out : Nat.Prime Pallas.curve.toAffine.order).odd_of_ne_two hodd)
    (by rw [hq]; norm_num [PALLAS_SCALAR_CARD])
    (by rw [hq]
        have hc : PALLAS_BASE_CARD + 2 ^ (pastaFieldBits - 1) + 2 ≤ 2 * PALLAS_SCALAR_CARD := by
          norm_num [PALLAS_BASE_CARD, PALLAS_SCALAR_CARD]
        omega)
    (gateLadder g) (gateBitSign g) (gateLadder_zero g) (fun j _ => gateBitSign_eq g j)
    (fun j _ => gateLadder_succ g j) hcanon
  obtain ⟨gs, P, hTP, hin, hout, hP0P⟩ := gateStep_chain Pallas.curve.toAffine (k + 1) g T hTne
    hholds hTns hTeq hbase hthread hP0ns hP0 h2 hodd hND
  have hfin : Pallas.curve.toAffine.Nonsingular (accX g (k + 1)) (accY g (k + 1)) :=
    (gs k (by omega)).a5
  have hPm : P (k + 1) = Point.some _ _ hfin := hout k (by omega)
  obtain ⟨n, hnf, hcase⟩ := scalarMul_type2 Pallas.curve.toAffine ⟨rfl, rfl, rfl⟩ (k + 1) g T N P
    ⟨gs, hTP, hin, hout, hregIn, hregOut⟩ hP0P hN0 sOdd hsOdd
  refine ⟨hfin, n, hnf, ?_⟩
  rcases hcase with ⟨ho, hr⟩ | ⟨ho, hr⟩
  · exact Or.inl ⟨ho, by rw [← hPm]; exact hr⟩
  · exact Or.inr ⟨ho, by rw [← hPm]; exact hr⟩

end Kimchi.Gate.VarBaseMul
