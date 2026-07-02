import Kimchi.Curve

/-!
# The kimchi `CompleteAdd` gate

Complete elliptic-curve point addition: the gate's 7 constraints, and the theorem
that they implement Mathlib's affine group law.

Transcribed from proof-systems `.../complete_add.rs`: the column layout
(cols 0–10: x1 y1 x2 y2 x3 y3 inf sameX s infZ x21Inv) and the 7 `constraint_checks`.

The trusted ORACLE is Mathlib's affine elliptic-curve group law
(`WeierstrassCurve.Affine.slope / addX / addY`). With the Pasta-shape curve
(`a₁ = a₂ = a₃ = a₄ = 0`) Mathlib's formulas collapse to exactly the gate's identities:

    slope (doubling) = 3x₁²/(2y₁)      ← gate c3 doubling: 2·s·y₁ = 3x₁²
    addX             = ℓ² − x₁ − x₂     ← gate c4: x₁+x₂+x₃ = s²
    addY             = ℓ(x₁ − x₃) − y₁  ← gate c5: y₃ = s(x₁−x₃) − y₁

and the sum of two affine points has coordinates `(addX, addY)`
(`Point.add_some`), so matching those formulas = computing the group sum.

## Main results

The gate computes addition in Mathlib's proven elliptic-curve group `W.Point`:
* `sound` — SOUNDNESS, both cases in one statement: for a satisfying witness the
  sum `(x₁,y₁) + (x₂,y₂)` is the group element the gate encodes — `0` when `inf = 1`,
  else the affine output `(x₃, y₃)` — using that `inf` is boolean (`inf_boolean`). It
  splits into the per-case `sound_point_noninf` / `sound_point_inf`.
* `complete` — COMPLETENESS, both cases in one statement: for on-curve inputs (`y₁ ≠ 0`),
  an honest prover can fill a satisfying witness, casing internally on whether the sum is
  finite or `∞`. Splits into the per-case `complete_noninf` / `complete_inf`.
-/

namespace Kimchi.Gate.AddComplete

/-- The CompleteAdd witness columns (cols 0–10). -/
structure Witness (F : Type*) where
  x1 : F
  y1 : F
  x2 : F
  y2 : F
  x3 : F
  y3 : F
  inf : F
  sameX : F
  s : F
  infZ : F
  x21Inv : F
deriving Repr

variable {F : Type*}

/-- Map a function across every witness cell. Instantiating at a ring homomorphism moves a
    witness between rings — in particular between `Witness (Polynomial F)` (the column
    polynomials of the quotient layer) and `Witness F` (their values at a domain node). -/
def Witness.map {R S : Type*} (f : R → S) (w : Witness R) : Witness S where
  x1 := f w.x1
  y1 := f w.y1
  x2 := f w.x2
  y2 := f w.y2
  x3 := f w.x3
  y3 := f w.y3
  inf := f w.inf
  sameX := f w.sameX
  s := f w.s
  infZ := f w.infZ
  x21Inv := f w.x21Inv

/-! ## The 7 constraints, transcribed from `complete_add.rs`.

The constraint left-hand sides live here once, as ring elements (`constraints`); the
relational spec (`Holds`), the executable checker (`ok`), and the quotient layer's constraint
polynomials (which read the same list over `F[X]`) are all defined from them. `CommRing`
suffices — no division appears (the inverse is *witnessed* as `x21Inv`, the whole point of
the gate). -/

/-- The gate's 7 constraint expressions — the single transcription. -/
def constraints [CommRing F] (w : Witness F) : List F :=
  let x21  := w.x2 - w.x1
  let y21  := w.y2 - w.y1
  let x1sq := w.x1 * w.x1
  -- zero_check(x21, x21Inv, sameX): constrains `sameX = (x1 == x2)`
  [ w.x21Inv * x21 - (1 - w.sameX)                                             -- c1
  , w.sameX * x21                                                              -- c2
  -- slope: sameX ? (2·s·y₁ = 3x₁²)  :  ((x₂−x₁)·s = y₂−y₁)
  , w.sameX * (2 * w.s * w.y1 - 3 * x1sq)
      + (1 - w.sameX) * (x21 * w.s - y21)                                      -- c3
  , w.x1 + w.x2 + w.x3 - w.s * w.s                                             -- c4  (x₃)
  , w.s * (w.x1 - w.x3) - w.y1 - w.y3                                          -- c5  (y₃)
  -- inf = sameX ∧ (y₁ ≠ y₂):
  , y21 * (w.sameX - w.inf)                                                    -- c6
  , y21 * w.infZ - w.inf ]                                                     -- c7

/-- RELATIONAL spec: all 7 constraint expressions vanish. -/
def Holds [CommRing F] (w : Witness F) : Prop :=
  ∀ e ∈ constraints w, e = 0

/-- EXECUTABLE checker — runnable on a concrete witness. -/
def ok [CommRing F] [DecidableEq F] (w : Witness F) : Bool :=
  (constraints w).all (· == 0)

/-- Reflection: the checker faithfully decides the relational constraints. -/
theorem ok_iff [CommRing F] [DecidableEq F] (w : Witness F) :
    ok w = true ↔ Holds w := by
  simp only [ok, Holds, List.all_eq_true, beq_iff_eq]

/-- `Holds` as the readable 7-conjunction (what the faithfulness proofs destructure). -/
theorem holds_iff [CommRing F] (w : Witness F) :
    Holds w ↔
      (w.x21Inv * (w.x2 - w.x1) - (1 - w.sameX) = 0)                           -- c1
      ∧ (w.sameX * (w.x2 - w.x1) = 0)                                          -- c2
      ∧ (w.sameX * (2 * w.s * w.y1 - 3 * (w.x1 * w.x1))
           + (1 - w.sameX) * ((w.x2 - w.x1) * w.s - (w.y2 - w.y1)) = 0)        -- c3
      ∧ (w.x1 + w.x2 + w.x3 - w.s * w.s = 0)                                   -- c4
      ∧ (w.s * (w.x1 - w.x3) - w.y1 - w.y3 = 0)                                -- c5
      ∧ ((w.y2 - w.y1) * (w.sameX - w.inf) = 0)                                -- c6
      ∧ ((w.y2 - w.y1) * w.infZ - w.inf = 0) := by                             -- c7
  simp only [Holds, constraints, List.forall_mem_cons, List.not_mem_nil, false_implies,
    implies_true, and_true]

/-- The constraint expressions commute with ring homomorphisms (applied cellwise via
    `Witness.map`). At `f = eval (ω^i) : F[X] →+* F` this turns the quotient layer's
    constraint polynomials' values at a domain node into the gate constraints of that
    node's row witness. -/
theorem constraints_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (w : Witness R) :
    (constraints w).map f = constraints (w.map f) := by
  simp [constraints, Witness.map, map_ofNat]

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

/-- COMPLETENESS: the honest prover can always fill in the witness. For on-curve
    inputs whose sum is finite, there exists a satisfying witness, and its output
    is the Mathlib affine sum. -/
theorem complete_noninf
    (W : WeierstrassCurve.Affine F)
    (ha : W.a₁ = 0 ∧ W.a₂ = 0 ∧ W.a₃ = 0 ∧ W.a₄ = 0)
    (x1 y1 x2 y2 : F)
    (hon1 : W.Equation x1 y1) (hon2 : W.Equation x2 y2)
    (hfin : ¬ (x1 = x2 ∧ y1 = W.negY x2 y2))
    (hy1 : y1 ≠ 0) (h2 : (2 : F) ≠ 0) :
    ∃ w : Witness F,
      w.x1 = x1 ∧ w.y1 = y1 ∧ w.x2 = x2 ∧ w.y2 = y2 ∧ w.inf = 0
      ∧ Holds w
      ∧ w.x3 = W.addX x1 x2 (W.slope x1 x2 y1 y2)
      ∧ w.y3 = W.addY x1 x2 y1 (W.slope x1 x2 y1 y2) := by
  obtain ⟨ha1, ha2, ha3, ha4⟩ := ha
  by_cases hx : x1 = x2
  · -- doubling branch: sameX = 1, x21Inv = 0
    have hy : y1 ≠ W.negY x2 y2 := fun h => hfin ⟨hx, h⟩
    have hnegYx1 : W.negY x1 y1 = -y1 := by simp [WeierstrassCurve.Affine.negY, ha1, ha3]
    have hyy : y1 + y1 ≠ 0 := by rw [← two_mul]; exact mul_ne_zero h2 hy1
    have hyeq : y1 = y2 := WeierstrassCurve.Affine.Y_eq_of_Y_ne hon1 hon2 hx hy
    refine ⟨{ x1 := x1, y1 := y1, x2 := x2, y2 := y2
            , x3 := W.addX x1 x2 (W.slope x1 x2 y1 y2)
            , y3 := W.addY x1 x2 y1 (W.slope x1 x2 y1 y2)
            , inf := 0, sameX := 1, s := W.slope x1 x2 y1 y2
            , infZ := 0, x21Inv := 0 },
          rfl, rfl, rfl, rfl, rfl, ?_, rfl, rfl⟩
    rw [holds_iff]
    refine ⟨by ring, by rw [hx]; ring, ?_, ?_, ?_, by rw [← hyeq]; ring, by ring⟩
    · -- c3: 2·s·y₁ = 3x₁²  (via slope = 3x₁²/(2y₁), cleared with eq_div_iff)
      have hs : W.slope x1 x2 y1 y2 = 3 * x1 ^ 2 / (y1 + y1) := by
        rw [WeierstrassCurve.Affine.slope_of_Y_ne hx hy, hnegYx1, sub_neg_eq_add]
        simp only [ha1, ha2, ha4]; ring
      have key : W.slope x1 x2 y1 y2 * (y1 + y1) = 3 * x1 ^ 2 := (eq_div_iff hyy).mp hs
      linear_combination key
    · simp only [WeierstrassCurve.Affine.addX, ha1, ha2]; ring
    · simp only [WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negY,
        WeierstrassCurve.Affine.negAddY, WeierstrassCurve.Affine.addX, ha1, ha2, ha3]; ring
  · -- addition branch: sameX = 0, x21Inv = (x₂−x₁)⁻¹
    have hx21 : x2 - x1 ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
    refine ⟨{ x1 := x1, y1 := y1, x2 := x2, y2 := y2
            , x3 := W.addX x1 x2 (W.slope x1 x2 y1 y2)
            , y3 := W.addY x1 x2 y1 (W.slope x1 x2 y1 y2)
            , inf := 0, sameX := 0, s := W.slope x1 x2 y1 y2
            , infZ := 0, x21Inv := (x2 - x1)⁻¹ },
          rfl, rfl, rfl, rfl, rfl, ?_, rfl, rfl⟩
    rw [holds_iff]
    refine ⟨?_, by ring, ?_, ?_, ?_, by ring, by ring⟩
    · -- c1: (x₂−x₁)⁻¹·(x₂−x₁) − 1 = 0
      rw [inv_mul_cancel₀ hx21]; ring
    · -- c3: (x₂−x₁)·s = y₂−y₁  (slope identity in multiplied-out form)
      have hx12 : x1 - x2 ≠ 0 := sub_ne_zero.mpr hx
      have key : W.slope x1 x2 y1 y2 * (x1 - x2) = y1 - y2 := by
        rw [WeierstrassCurve.Affine.slope_of_X_ne hx]; field_simp
      linear_combination -key
    · simp only [WeierstrassCurve.Affine.addX, ha1, ha2]; ring
    · simp only [WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negY,
        WeierstrassCurve.Affine.negAddY, WeierstrassCurve.Affine.addX, ha1, ha2, ha3]; ring

omit [DecidableEq F] in
/-- COMPLETENESS, infinity case. When the inputs sum to `∞` — `x₁ = x₂` and
    `y₁ = negY x₂ y₂`, i.e. `P₂ = -P₁` — the honest prover can fill a satisfying witness
    with `inf = 1`. The output columns carry the (unused) doubling slope `s = 3x₁²/(2y₁)`
    so the `sameX = 1` slope constraint still holds; `infZ = 1/(y₂−y₁)` witnesses `inf`.
    The companion to `complete_noninf`, closing completeness over both cases. -/
theorem complete_inf
    (W : WeierstrassCurve.Affine F)
    (ha : W.a₁ = 0 ∧ W.a₂ = 0 ∧ W.a₃ = 0 ∧ W.a₄ = 0)
    (x1 y1 x2 y2 : F)
    (_hon1 : W.Equation x1 y1) (_hon2 : W.Equation x2 y2)
    (hinf : x1 = x2 ∧ y1 = W.negY x2 y2)
    (hy1 : y1 ≠ 0) (h2 : (2 : F) ≠ 0) :
    ∃ w : Witness F,
      w.x1 = x1 ∧ w.y1 = y1 ∧ w.x2 = x2 ∧ w.y2 = y2 ∧ w.inf = 1 ∧ Holds w := by
  obtain ⟨ha1, -, ha3, -⟩ := ha
  obtain ⟨hxe, hye⟩ := hinf
  have hnegY2 : W.negY x2 y2 = -y2 := by simp [WeierstrassCurve.Affine.negY, ha1, ha3]
  rw [hnegY2] at hye
  have hy2 : y2 = -y1 := by linear_combination hye
  have hden : (2 : F) * y1 ≠ 0 := mul_ne_zero h2 hy1
  have hy21ne : y2 - y1 ≠ 0 := by
    rw [hy2]; intro h; exact hden (by linear_combination -h)
  set s : F := 3 * x1 ^ 2 / (2 * y1) with hsdef
  refine ⟨{ x1 := x1, y1 := y1, x2 := x2, y2 := y2, x3 := s ^ 2 - x1 - x2,
            y3 := s * (x1 - (s ^ 2 - x1 - x2)) - y1, inf := 1, sameX := 1, s := s,
            infZ := 1 / (y2 - y1), x21Inv := 0 }, rfl, rfl, rfl, rfl, rfl, ?_⟩
  rw [holds_iff]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · ring
  · rw [hxe]; ring
  · rw [hsdef]; field_simp; ring
  · ring
  · ring
  · ring
  · rw [mul_one_div, div_self hy21ne, sub_self]

/-- COMPLETENESS, both cases in one statement. For any on-curve inputs with `y₁ ≠ 0`, an
    honest prover can fill a satisfying witness — casing internally on whether the sum is
    `∞` (`x₁=x₂ ∧ y₁ = negY x₂ y₂` → `complete_inf`, `inf=1`) or finite (`complete_noninf`,
    `inf=0`). The single-theorem companion to `sound`. (`y₁ ≠ 0` excludes 2-torsion,
    which the prime-order kimchi curves don't have — so it is no real restriction there.) -/
theorem complete
    (W : WeierstrassCurve.Affine F)
    (ha : W.a₁ = 0 ∧ W.a₂ = 0 ∧ W.a₃ = 0 ∧ W.a₄ = 0)
    (x1 y1 x2 y2 : F)
    (hon1 : W.Equation x1 y1) (hon2 : W.Equation x2 y2)
    (hy1 : y1 ≠ 0) (h2 : (2 : F) ≠ 0) :
    ∃ w : Witness F, w.x1 = x1 ∧ w.y1 = y1 ∧ w.x2 = x2 ∧ w.y2 = y2 ∧ Holds w := by
  by_cases hd : x1 = x2 ∧ y1 = W.negY x2 y2
  · obtain ⟨w, e1, e2, e3, e4, _, hcons⟩ :=
      complete_inf W ha x1 y1 x2 y2 hon1 hon2 hd hy1 h2
    exact ⟨w, e1, e2, e3, e4, hcons⟩
  · obtain ⟨w, e1, e2, e3, e4, _, hcons, _, _⟩ :=
      complete_noninf W ha x1 y1 x2 y2 hon1 hon2 hd hy1 h2
    exact ⟨w, e1, e2, e3, e4, hcons⟩

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

def egDouble : Witness (ZMod 17) :=
  { x1 := 0, y1 := 2, x2 := 0, y2 := 2, x3 := 0, y3 := 15
  , inf := 0, sameX := 1, s := 0, infZ := 0, x21Inv := 0 }

#eval ok egDouble   -- expect true

example : Holds egDouble := by
  rw [← ok_iff]; rfl

end Kimchi.Gate.AddComplete
