import Kimchi.Gate.EndoMul
import Kimchi.Gate.Semantics.EndoScalar
import Kimchi.Gate.Semantics.VarBaseMul
import Pasta.Endo

/-! # EndoMul gate & circuit semantics: one row computes the GLV combination
    `4·P + c₁·T + c₂·φ(T)` (soundness/completeness), and the multi-row chain
    proves the endomorphism-accelerated scalar multiplication `endoMul`. -/

namespace Kimchi.Gate.EndoMul

open WeierstrassCurve.Affine

variable {F : Type*} [Field F] [DecidableEq F]

omit [DecidableEq F] in
/-- Booleanity: the constraint `b·(b−1) = 0` forces `b ∈ {0,1}` (field = domain). -/
private theorem bool_of_mul {b : F} (h : b * (b - 1) = 0) : b = 0 ∨ b = 1 := by
  rcases mul_eq_zero.mp h with h | h
  · exact Or.inl h
  · exact Or.inr (by linear_combination h)

omit [DecidableEq F] in
/-- The distinct-point check discharges the non-degeneracy both windows need:
    `(xP − xR)·(xR − xS)·inv = 1` makes both factors units, so `xP ≠ xR` (first
    window, `R ≠ −P`) and `xR ≠ xS` (second window, `S ≠ −R`). -/
private theorem distinctPoints (endo : F) (w : Witness F) (h : Holds endo w) :
    w.xP ≠ w.xR ∧ w.xR ≠ w.xS := by
  rw [holds_iff] at h
  have hinv := h.2.2.2.2.2.2.1
  refine ⟨fun hc => ?_, fun hc => ?_⟩
  · rw [hc, sub_self, zero_mul, zero_mul] at hinv; exact one_ne_zero hinv.symm
  · rw [hc, sub_self, mul_zero, zero_mul] at hinv; exact one_ne_zero hinv.symm

omit [DecidableEq F] in
/-- `Point.some` congruence over *both* coordinates: equal `x` and `y` values give
    equal points (the nonsingularity proofs are irrelevant). A small extension of
    `Kimchi.some_eq_some`, used to transport a target point along an `x`-coordinate
    identity that holds only `by ring`. -/
theorem some_congr (W : WeierstrassCurve.Affine F) {x x' y y' : F}
    (h : W.Nonsingular x y) (h' : W.Nonsingular x' y') (hx : x = x') (hy : y = y') :
    Point.some _ _ h = Point.some _ _ h' := by
  subst hx; subst hy; rfl

/-- GLV target selection. A window's target
    `Q = ((1 + (endo−1)·b₁)·xT, (2·b₂−1)·yT)` with `b₁, b₂ ∈ {0,1}` is `±T` (when
    `b₁ = 0`, so `xq = xT`) or `±φ(T)` (when `b₁ = 1`, so `xq = endo·xT`), where
    `φ(T) = (endo·xT, yT)`. Reuses `Kimchi.signed_target` with base `T` or `φ(T)`. -/
private theorem selectQ (W : WeierstrassCurve.Affine F) (ha : (W.a₁ = 0 ∧ W.a₂ = 0 ∧ W.a₃ = 0))
    {endo b1 b2 xT yT : F}
    (hT : W.Nonsingular xT yT) (hφT : W.Nonsingular (endo * xT) yT)
    (hQ : W.Nonsingular ((1 + (endo - 1) * b1) * xT) ((2 * b2 - 1) * yT))
    (hb1 : b1 = 0 ∨ b1 = 1) (hb2 : b2 = 0 ∨ b2 = 1) :
    (∃ e : ℤ, Point.some _ _ hQ = e • Point.some _ _ hT ∧ (e : F) = 2 * b2 - 1)
      ∨ (∃ e : ℤ, Point.some _ _ hQ = e • Point.some _ _ hφT ∧ (e : F) = 2 * b2 - 1) := by
  rcases hb1 with rfl | rfl
  · -- `b₁ = 0`: the `x`-coordinate `(1 + (endo-1)*0)*xT` collapses to `xT`,
    -- so `Q = ±T` via `signed_target` with base `T`.
    left
    have hx : (1 + (endo - 1) * 0) * xT = xT := by ring
    obtain ⟨e, he, hef, _⟩ := Kimchi.Gate.VarBaseMul.signed_target W ha hT (hx ▸ hQ) hb2
    exact ⟨e, (some_congr W hQ (hx ▸ hQ) hx rfl).trans he, hef⟩
  · -- `b₁ = 1`: the `x`-coordinate `(1 + (endo-1)*1)*xT` collapses to `endo*xT`,
    -- so `Q = ±φ(T)` via `signed_target` with base `φ(T)`.
    right
    have hx : (1 + (endo - 1) * 1) * xT = endo * xT := by ring
    obtain ⟨e, he, hef, _⟩ := Kimchi.Gate.VarBaseMul.signed_target W ha hφT (hx ▸ hQ) hb2
    exact ⟨e, (some_congr W hQ (hx ▸ hQ) hx rfl).trans he, hef⟩

omit [DecidableEq F] in
/-- A window target `Q = ((1 + (endo−1)·b₁)·xT, (2·b₂−1)·yT)` is nonsingular whenever the base
    `T` and its endo-image `φ(T) = (endo·xT, yT)` are: `b₁` selects the base, `b₂` the sign. So
    the target's nonsingularity need never be assumed — it follows from `hT`/`hφT` and the bits'
    booleanity (the EndoMul analog of VarBaseMul's `signed_target_nonsingular`). -/
private theorem target_nonsingular (W : WeierstrassCurve.Affine F)
    (ha : (W.a₁ = 0 ∧ W.a₂ = 0 ∧ W.a₃ = 0))
    {endo b1 b2 xT yT : F} (hT : W.Nonsingular xT yT) (hφT : W.Nonsingular (endo * xT) yT)
    (hb1 : b1 = 0 ∨ b1 = 1) (hb2 : b2 = 0 ∨ b2 = 1) :
    W.Nonsingular ((1 + (endo - 1) * b1) * xT) ((2 * b2 - 1) * yT) := by
  rcases hb1 with rfl | rfl
  · rw [show (1 + (endo - 1) * 0) * xT = xT by ring]
    exact Kimchi.Gate.VarBaseMul.signed_target_nonsingular W ha hT hb2
  · rw [show (1 + (endo - 1) * 1) * xT = endo * xT by ring]
    exact Kimchi.Gate.VarBaseMul.signed_target_nonsingular W ha hφT hb2

omit [DecidableEq F] in
/-- Both window targets are nonsingular, read off the bases `hT`/`hφT` and the four bits'
    booleanity in `Holds` — so a row's targets are derived, not assumed. -/
private theorem targets_nonsingular (W : WeierstrassCurve.Affine F)
    (ha : (W.a₁ = 0 ∧ W.a₂ = 0 ∧ W.a₃ = 0))
    (endo : F) (w : Witness F) (h : Holds endo w)
    (hT : W.Nonsingular w.xT w.yT) (hφT : W.Nonsingular (endo * w.xT) w.yT) :
    W.Nonsingular ((1 + (endo - 1) * w.b1) * w.xT) ((2 * w.b2 - 1) * w.yT)
      ∧ W.Nonsingular ((1 + (endo - 1) * w.b3) * w.xT) ((2 * w.b4 - 1) * w.yT) := by
  rw [holds_iff] at h
  obtain ⟨_, _, _, _, _, _, _, hb1, hb2, hb3, hb4, _⟩ := h
  exact ⟨target_nonsingular W ha hT hφT (bool_of_mul hb1) (bool_of_mul hb2),
         target_nonsingular W ha hT hφT (bool_of_mul hb3) (bool_of_mul hb4)⟩

/-- One window's `(P + Q) + P` double-and-add. The three EC constraints — the
    first-addition slope `s` and the `xR`/`yR` relations — together with the
    non-degeneracy `xP ≠ xq` (first slope), `2·xP − s² + xq ≠ 0` (second addition
    `M + P`, `M = P + Q`), and `xR ≠ xP` force `R = (P + Q) + P`. General in `Q`, so
    it serves both windows of the row. Closes with `Kimchi.secant_add` twice,
    recovering the eliminated intermediate `M` (cf. VarBaseMul's `singleBit_sound`).

    `xR ≠ xP` is essential: `hc2` and `hc3` share a `(xP − xR)` factor, so without
    it they also admit the spurious `R = −P` (`xR = xP`, `yR = −yP`) — e.g. on
    `y² = x³ + 1`, `P=(0,1)`, `Q=(2,3)`, `s=1` satisfies every constraint yet
    `(P+Q)+P = (2,−3) ≠ (0,−1)`. The gate's distinct-point constraint supplies it
    (via `distinctPoints`); it is a per-window parameter here because the two
    windows need `xR ≠ xP` and `xS ≠ xR` respectively. -/
private theorem block_sound (W : WeierstrassCurve.Affine F) (ha : (W.a₁ = 0 ∧ W.a₂ = 0 ∧ W.a₃ = 0))
    {xq yq xP yP s xR yR : F}
    (hP : W.Nonsingular xP yP) (hQ : W.Nonsingular xq yq) (hR : W.Nonsingular xR yR)
    (hxne : xP ≠ xq) (htne : 2 * xP - s ^ 2 + xq ≠ 0) (hxRne : xR ≠ xP)
    (hs : (xq - xP) * s = yq - yP)
    (hc2 : (2 * xP - s ^ 2 + xq) * ((xP - xR) * s + yR + yP) = (xP - xR) * (2 * yP))
    (hc3 : (yR + yP) ^ 2 = (xP - xR) ^ 2 * (s ^ 2 - xq + xR)) :
    Point.some _ _ hR = (Point.some _ _ hP + Point.some _ _ hQ) + Point.some _ _ hP := by
  obtain ⟨ha1, ha2, ha3⟩ := ha
  have hdiff1 : xP - xq ≠ 0 := sub_ne_zero.mpr hxne
  have hxRne0 : xP - xR ≠ 0 := sub_ne_zero.mpr (Ne.symm hxRne)
  -- first addition `P + Q` has slope `s`
  have hl1 : s = (yP - yq) / (xP - xq) := by
    rw [eq_div_iff hdiff1]; linear_combination -hs
  -- intermediate `M = (Mx, My) = P + Q`
  set Mx : F := s * s - xP - xq with hMx
  set My : F := s * (xP - Mx) - yP with hMy
  set s2 : F := (My - yP) / (Mx - xP) with hs2
  clear_value s2 My Mx
  have htval : xP - Mx = 2 * xP - s ^ 2 + xq := by rw [hMx]; ring
  have htt : xP - Mx ≠ 0 := by rw [htval]; exact htne
  have hMxne : Mx ≠ xP := by intro hc; exact htt (by rw [hc]; ring)
  have hxine : Mx - xP ≠ 0 := sub_ne_zero.mpr hMxne
  -- first addition `P + Q = M`
  obtain ⟨hM, hAdd1⟩ :=
    Kimchi.Gate.VarBaseMul.secant_add W ⟨ha1, ha2, ha3⟩ hP hQ hxne hl1 hMx hMy
  -- `s2` is genuinely `(My - yP)/(Mx - xP)`
  have hsr : s2 * (Mx - xP) = My - yP := by
    rw [hs2, div_mul_cancel₀]; exact hxine
  -- the cleared `hc2` says `yR + yP = (xP - xR) * s2`
  have key1' : (yR + yP) * (Mx - xP) = (xP - xR) * (My - yP) := by
    linear_combination -hc2 - (xP - xR) * hMy - ((xP - xR) * s + yR + yP) * htval
  have hcancel : (yR + yP) * (Mx - xP) = ((xP - xR) * s2) * (Mx - xP) := by
    rw [key1']; linear_combination -(xP - xR) * hsr
  have key1div : yR + yP = (xP - xR) * s2 := mul_right_cancel₀ hxine hcancel
  -- the second slope satisfies `s2² = s² - xq + xR` (from `hc3`, dividing by `(xP-xR)²`)
  have hs2sq : s2 * s2 = s ^ 2 - xq + xR := by
    have hkey3 : (xP - xR) ^ 2 * (s2 * s2) = (xP - xR) ^ 2 * (s ^ 2 - xq + xR) := by
      rw [← hc3]
      linear_combination -((yR + yP) + (xP - xR) * s2) * key1div
    exact mul_left_cancel₀ (pow_ne_zero 2 hxRne0) hkey3
  -- the second addition's output coordinates
  have hxR_eq : xR = s2 * s2 - Mx - xP := by rw [hs2sq, hMx]; ring
  have hyR_eq : yR = s2 * (Mx - xR) - My := by
    have hyR' : yR = (xP - xR) * s2 - yP := by linear_combination key1div
    rw [hyR']; linear_combination -hsr
  -- second addition `M + P = R`
  obtain ⟨hR', hAdd2⟩ :=
    Kimchi.Gate.VarBaseMul.secant_add W ⟨ha1, ha2, ha3⟩ hM hP hMxne hs2 hxR_eq hyR_eq
  rw [hAdd1, hAdd2]

/-- Per-row soundness: a satisfying row's two windows compute the double-and-add
    chain `R = (P + Q₁) + P` then `S = (R + Q₂) + R`, where `Q₁, Q₂` are the gate's
    endo-and-sign-selected targets. The distinct-point constraint (via
    `distinctPoints`) supplies each window's `xR ≠ xP` / `xS ≠ xR`; the per-slope
    non-degeneracies `xP ≠ xq` and `2·xP − s² + xq ≠ 0` are the remaining honest-
    witness conditions (as in VarBaseMul). Identify `Q₁, Q₂` as `±T` / `±φ(T)` with
    `selectQ` to feed the GLV accumulation. -/
private theorem row_sound (W : WeierstrassCurve.Affine F) (ha : (W.a₁ = 0 ∧ W.a₂ = 0 ∧ W.a₃ = 0))
    (endo : F) (w : Witness F) (h : Holds endo w)
    (hP : W.Nonsingular w.xP w.yP) (hR : W.Nonsingular w.xR w.yR)
    (hS : W.Nonsingular w.xS w.yS)
    (hQ1 : W.Nonsingular ((1 + (endo - 1) * w.b1) * w.xT) ((2 * w.b2 - 1) * w.yT))
    (hQ2 : W.Nonsingular ((1 + (endo - 1) * w.b3) * w.xT) ((2 * w.b4 - 1) * w.yT))
    (hxne1 : w.xP ≠ (1 + (endo - 1) * w.b1) * w.xT)
    (htne1 : 2 * w.xP - w.s1 ^ 2 + (1 + (endo - 1) * w.b1) * w.xT ≠ 0)
    (hxne2 : w.xR ≠ (1 + (endo - 1) * w.b3) * w.xT)
    (htne2 : 2 * w.xR - w.s3 ^ 2 + (1 + (endo - 1) * w.b3) * w.xT ≠ 0) :
    Point.some _ _ hR = (Point.some _ _ hP + Point.some _ _ hQ1) + Point.some _ _ hP
      ∧ Point.some _ _ hS = (Point.some _ _ hR + Point.some _ _ hQ2) + Point.some _ _ hR := by
  obtain ⟨hxPxR, hxRxS⟩ := distinctPoints endo w h
  rw [holds_iff] at h
  obtain ⟨hs1, hc2_1, hc3_1, hs2, hc2_2, hc3_2, _, _, _, _, _, _⟩ := h
  exact ⟨block_sound W ha hP hQ1 hR hxne1 htne1 (Ne.symm hxPxR) hs1 hc2_1 hc3_1,
         block_sound W ha hR hQ2 hS hxne2 htne2 (Ne.symm hxRxS) hs2 hc2_2 hc3_2⟩

/-- The per-row GLV contribution, as integer scalar multiples of the two bases.
    Folding `row_sound`'s `S = (R+Q₂)+R`, `R = (P+Q₁)+P` gives `S = 4·P + 2·Q₁ + Q₂`;
    `selectQ` makes each `Qⱼ` a signed `T` or `φ(T)`, so `S = 4·P + c₁·T + c₂·φ(T)`
    for integers `c₁, c₂` (the gate's exposed interface, consumed by the chain). -/
theorem sound (W : WeierstrassCurve.Affine F) (ha : (W.a₁ = 0 ∧ W.a₂ = 0 ∧ W.a₃ = 0))
    (endo : F) (w : Witness F) (h : Holds endo w)
    (hT : W.Nonsingular w.xT w.yT) (hφT : W.Nonsingular (endo * w.xT) w.yT)
    (hP : W.Nonsingular w.xP w.yP) (hR : W.Nonsingular w.xR w.yR)
    (hS : W.Nonsingular w.xS w.yS)
    (hQ1 : W.Nonsingular ((1 + (endo - 1) * w.b1) * w.xT) ((2 * w.b2 - 1) * w.yT))
    (hQ2 : W.Nonsingular ((1 + (endo - 1) * w.b3) * w.xT) ((2 * w.b4 - 1) * w.yT))
    (hxne1 : w.xP ≠ (1 + (endo - 1) * w.b1) * w.xT)
    (htne1 : 2 * w.xP - w.s1 ^ 2 + (1 + (endo - 1) * w.b1) * w.xT ≠ 0)
    (hxne2 : w.xR ≠ (1 + (endo - 1) * w.b3) * w.xT)
    (htne2 : 2 * w.xR - w.s3 ^ 2 + (1 + (endo - 1) * w.b3) * w.xT ≠ 0) :
    ∃ c1 c2 : ℤ, Point.some _ _ hS
      = (4 : ℤ) • Point.some _ _ hP + c1 • Point.some _ _ hT + c2 • Point.some _ _ hφT := by
  obtain ⟨hReq, hSeq⟩ :=
    row_sound W ha endo w h hP hR hS hQ1 hQ2 hxne1 htne1 hxne2 htne2
  have hb := h
  rw [holds_iff] at hb
  obtain ⟨_, _, _, _, _, _, _, hb1c, hb2c, hb3c, hb4c, _⟩ := hb
  have hb1 := bool_of_mul hb1c
  have hb2 := bool_of_mul hb2c
  have hb3 := bool_of_mul hb3c
  have hb4 := bool_of_mul hb4c
  rcases selectQ W ha hT hφT hQ1 hb1 hb2 with ⟨e1, hQ1e, _⟩ | ⟨e1, hQ1e, _⟩
  · rcases selectQ W ha hT hφT hQ2 hb3 hb4 with ⟨e2, hQ2e, _⟩ | ⟨e2, hQ2e, _⟩
    · exact ⟨2 * e1 + e2, 0, by rw [hSeq, hReq, hQ1e, hQ2e]; module⟩
    · exact ⟨2 * e1, e2, by rw [hSeq, hReq, hQ1e, hQ2e]; module⟩
  · rcases selectQ W ha hT hφT hQ2 hb3 hb4 with ⟨e2, hQ2e, _⟩ | ⟨e2, hQ2e, _⟩
    · exact ⟨e2, 2 * e1, by rw [hSeq, hReq, hQ1e, hQ2e]; module⟩
    · exact ⟨0, 2 * e1 + e2, by rw [hSeq, hReq, hQ1e, hQ2e]; module⟩

/-! ## Completeness: the witness generator satisfies the constraints

`sound` shows a satisfying row computes the GLV double-and-add. Completeness is the converse —
the honest computation yields a satisfying witness: the generated row (`build`) satisfies `Holds`,
under the same per-window non-degeneracy `sound` needs (`xP ≠ xq`, `t ≠ 0`) plus the distinct-point
conditions `xP ≠ xR`, `xR ≠ xS` that supply the gate's `inv` witness. Purely algebraic — no curve
membership. Each window is the same `(P+Q)+P` step as VarBaseMul's `singleBit`. -/

omit [DecidableEq F] in
/-- One window's two cleared EC constraints (the `xR`/`yR` relations) hold for any
    `(s1, s2, xR, yR)` linked by the generation relations — slopes in multiplicative form, so it
    is pure polynomial algebra. -/
private theorem window_holds (xq xP yP s1 s2 xR yR : F)
    (hs2 : (2 * xP - s1 ^ 2 + xq) * s2 = 2 * yP - (2 * xP - s1 ^ 2 + xq) * s1)
    (hxR : xR = s2 ^ 2 - s1 ^ 2 + xq)
    (hyR : yR = (xP - xR) * s2 - yP) :
    (2 * xP - s1 ^ 2 + xq) * ((xP - xR) * s1 + yR + yP) = (xP - xR) * (2 * yP)
      ∧ (yR + yP) ^ 2 = (xP - xR) ^ 2 * (s1 ^ 2 - xq + xR) := by
  refine ⟨?_, ?_⟩
  · subst hyR; linear_combination (xP - xR) * hs2
  · subst hxR hyR; ring

omit [DecidableEq F] in
/-- The generated window step `(s1, xR, yR)` for `R = (P + Q) + P`, `Q = (xq, yq)`. -/
private def stepWindow (xq yq xP yP : F) : F × F × F :=
  let s1 := (yq - yP) / (xq - xP)
  let s2 := 2 * yP / (2 * xP - s1 ^ 2 + xq) - s1
  let xR := s2 ^ 2 - s1 ^ 2 + xq
  (s1, xR, (xP - xR) * s2 - yP)

omit [DecidableEq F] in
/-- The generated window satisfies the window's slope + `xR` + `yR` constraints, given the two
    non-degeneracy conditions (`xP ≠ xq` and `t ≠ 0`) — the denominators in `stepWindow`. -/
private theorem stepWindow_holds (xq yq xP yP : F) (hxne : xP ≠ xq)
    (htne : 2 * xP - (stepWindow xq yq xP yP).1 ^ 2 + xq ≠ 0) :
    ((xq - xP) * (stepWindow xq yq xP yP).1 = yq - yP)
      ∧ (2 * xP - (stepWindow xq yq xP yP).1 ^ 2 + xq)
            * ((xP - (stepWindow xq yq xP yP).2.1) * (stepWindow xq yq xP yP).1
               + (stepWindow xq yq xP yP).2.2 + yP)
          = (xP - (stepWindow xq yq xP yP).2.1) * (2 * yP)
      ∧ ((stepWindow xq yq xP yP).2.2 + yP) ^ 2
          = (xP - (stepWindow xq yq xP yP).2.1) ^ 2
              * ((stepWindow xq yq xP yP).1 ^ 2 - xq + (stepWindow xq yq xP yP).2.1) := by
  have hd : xq - xP ≠ 0 := sub_ne_zero.mpr (Ne.symm hxne)
  set s1 := (yq - yP) / (xq - xP) with hs1
  have e1 : (stepWindow xq yq xP yP).1 = s1 := rfl
  set s2 := 2 * yP / (2 * xP - s1 ^ 2 + xq) - s1 with hs2d
  have e2 : (stepWindow xq yq xP yP).2.1 = s2 ^ 2 - s1 ^ 2 + xq := rfl
  have e3 : (stepWindow xq yq xP yP).2.2 = (xP - (s2 ^ 2 - s1 ^ 2 + xq)) * s2 - yP := rfl
  rw [e1] at htne ⊢
  rw [e2, e3]
  have hC1 : (xq - xP) * s1 = yq - yP := by rw [hs1]; field_simp
  have hs2m : (2 * xP - s1 ^ 2 + xq) * s2 = 2 * yP - (2 * xP - s1 ^ 2 + xq) * s1 := by
    rw [hs2d]; field_simp
  exact ⟨hC1, window_holds xq xP yP s1 s2 (s2 ^ 2 - s1 ^ 2 + xq)
    ((xP - (s2 ^ 2 - s1 ^ 2 + xq)) * s2 - yP) hs2m rfl rfl⟩

omit [DecidableEq F] in
/-- Build the canonical satisfying row from the base `T = (xT, yT)`, input accumulator
    `P = (xP, yP)`, scalar register `n`, the four bits, and the endomorphism coefficient. The two
    windows are generated by `stepWindow`; `inv` witnesses the distinct-point product. -/
def build (endo xT yT xP yP n b1 b2 b3 b4 : F) : Witness F :=
  let w1 := stepWindow ((1 + (endo - 1) * b1) * xT) ((2 * b2 - 1) * yT) xP yP
  let w2 := stepWindow ((1 + (endo - 1) * b3) * xT) ((2 * b4 - 1) * yT) w1.2.1 w1.2.2
  { xT, yT, xP, yP, n
  , nPrime := 16 * n + 8 * b1 + 4 * b2 + 2 * b3 + b4
  , b1, b2, b3, b4
  , s1 := w1.1, xR := w1.2.1, yR := w1.2.2
  , s3 := w2.1, xS := w2.2.1, yS := w2.2.2
  , inv := 1 / ((xP - w1.2.1) * (w1.2.1 - w2.2.1)) }

omit [DecidableEq F] in
/-- **Completeness of the EndoMul gate.** The witness the honest prover constructs (`build`)
    satisfies all 12 constraints (`Holds`), given booleanity of the four bits and the per-window
    non-degeneracy (`xP ≠ xq`, `t ≠ 0` for each window) plus the distinct-point conditions
    (`xP ≠ xR`, `xR ≠ xS`) that the `inv` constraint encodes. Conditional, as expected for an
    incomplete-addition gate; the scalar-register constraint holds by construction. -/
theorem complete (endo xT yT xP yP n b1 b2 b3 b4 : F)
    (w : Witness F) (hw : w = build endo xT yT xP yP n b1 b2 b3 b4)
    (hb1 : b1 * (b1 - 1) = 0) (hb2 : b2 * (b2 - 1) = 0)
    (hb3 : b3 * (b3 - 1) = 0) (hb4 : b4 * (b4 - 1) = 0)
    (hxne1 : w.xP ≠ (1 + (endo - 1) * w.b1) * w.xT)
    (htne1 : 2 * w.xP - w.s1 ^ 2 + (1 + (endo - 1) * w.b1) * w.xT ≠ 0)
    (hxne2 : w.xR ≠ (1 + (endo - 1) * w.b3) * w.xT)
    (htne2 : 2 * w.xR - w.s3 ^ 2 + (1 + (endo - 1) * w.b3) * w.xT ≠ 0)
    (hxPR : w.xP ≠ w.xR) (hxRS : w.xR ≠ w.xS) :
    Holds endo w := by
  subst hw
  obtain ⟨h1, h2, h3⟩ :=
    stepWindow_holds ((1 + (endo - 1) * b1) * xT) ((2 * b2 - 1) * yT) xP yP hxne1 htne1
  obtain ⟨h4, h5, h6⟩ :=
    stepWindow_holds ((1 + (endo - 1) * b3) * xT) ((2 * b4 - 1) * yT)
      (build endo xT yT xP yP n b1 b2 b3 b4).xR (build endo xT yT xP yP n b1 b2 b3 b4).yR
      hxne2 htne2
  refine (holds_iff _ _).mpr ⟨h1, h2, h3, h4, h5, h6, ?_, hb1, hb2, hb3, hb4, rfl⟩
  have hd : (xP - (build endo xT yT xP yP n b1 b2 b3 b4).xR)
      * ((build endo xT yT xP yP n b1 b2 b3 b4).xR
         - (build endo xT yT xP yP n b1 b2 b3 b4).xS) ≠ 0 :=
    mul_ne_zero (sub_ne_zero.mpr hxPR) (sub_ne_zero.mpr hxRS)
  show (xP - (build endo xT yT xP yP n b1 b2 b3 b4).xR)
      * ((build endo xT yT xP yP n b1 b2 b3 b4).xR
         - (build endo xT yT xP yP n b1 b2 b3 b4).xS)
      * (1 / ((xP - (build endo xT yT xP yP n b1 b2 b3 b4).xR)
          * ((build endo xT yT xP yP n b1 b2 b3 b4).xR
             - (build endo xT yT xP yP n b1 b2 b3 b4).xS))) = 1
  rw [mul_one_div, div_self hd]

end Kimchi.Gate.EndoMul

/-! ## GLV scalar-mul chain: supporting development (folded from
    `Circuit/EndoMul/Internal`). -/


/-!
# The `EndoMul` circuit: supporting development

Endomorphism-optimized (GLV) scalar multiplication composes `Kimchi.Gate.EndoMul` rows into a
full scalar multiplication of the base point. Each row contributes `S = 4·P + c₁·T + c₂·φ(T)` (the
gate's `sound`), so chaining `m` rows folds into `P_m = 4^m·P₀ + k₁·T + k₂·φ(T)`; on the Pasta
endomorphism `φ(T) = [λ]·T` this collapses to a single scalar multiple of `T`. This module collects
the definitions and lemmas on which the curve-specialized entry points (`{pallas,vesta}_endoMul`,
in `Kimchi.Gate.EndoMul`) rest, together with the generic capstone `endoMul`.

The circuit is stated so the prover supplies only

* `Holds endo (g i)` at every step (the gate constraint),
* the **base** nonsingularity `hT`/`hφT` (one-time, row 0 — genuinely external),
* the **initial** accumulator `P₀ = 2(T + φT)` (one-time),
* the **threading** of columns (`(g (i+1)).xP = (g i).xS`, base shared).

Every intermediate accumulator's nonsingularity is *derived* — the gate's secant additions hand
back the output point on-curve (`gate_advance`), threaded through the chain — so there is no
per-row hypothesis bundle, only a coordinate side-condition `hxne` discharged at the curve layer.

## The `EndoMul ∘ EndoScalar` recoding kernel

EndoMul's per-window GLV digits coincide with EndoScalar's Algorithm-2 `cPoly`/`dPoly` digits over
the shared challenge crumbs. This is the technical bridge between the two gates — pure digit/crumb
bookkeeping, independent of the GLV point-fold.

* `recoding_digit` — the per-window correspondence: an `EndoMul` window's bits map to the
  `EndoScalar` crumb on which `cPoly`/`dPoly` reproduce the GLV window digit.
* `sum_reindex` — the row↔crumb reindexing lifting the per-window identity to the fold.
* `aDigit` / `bDigit` — the `cPoly` / `dPoly` digit of crumb `j` built from the rows.
* `crumbList` / `decompose_crumbList` — the `2m`-crumb list the rows feed to `EndoScalar`, and the
  init-aligned bridge to its `decomposeA`/`decomposeB`.

## Non-degeneracy

The per-row non-degeneracy facts the soundness needs, generic over the curve:

* `block_tne` — each `(P+Q)+P` block's *second*-addition condition `htne ≠ 0` is self-enforced by
  the gate constraints (the EndoMul analog of VarBaseMul's `tne_of_holds`).
* `combo_off_targets` — the geometric core of the *first*-addition condition `hxne`: a bounded
  two-base combination `[a]·T + [b]·φT` avoids `±T`/`±φT`.
* `selectQ'` — a bounded variant of `Gate.EndoMul.selectQ` that also returns the sign `e = ±1`.

## The GLV scalar-multiplication chain

The point-level fold and the capstone:

* `chain_endo` — the two-base group fold (pure group algebra).
* `gate_advance` — one `EndoMul` row, with the output point's nonsingularity *produced*, not given.
* `endoMul_ab` — the GLV-recoding chain: the coefficients `(k₂, k₁)` are `EndoScalar`'s `a`, `b`.
* `endoMul` — the capstone: the rows compute `[s]·T`, `s = EndoScalar.toField (crumbList g m) λ`.
* `accumulator_chain` — discharges the per-row `hxne` from the GLV short-basis bound.
-/
namespace Kimchi.Gate.EndoMul

open Kimchi.Gate.EndoMul WeierstrassCurve.Affine
open Kimchi.Gate.EndoScalar (cPoly dPoly)

variable {F : Type*} [Field F] [DecidableEq F]

/-! ## The `EndoMul ∘ EndoScalar` recoding kernel -/

omit [DecidableEq F] in
open Kimchi.Gate.EndoScalar in
/-- The recoding correspondence (per window). An `EndoMul` window's bits `(b₁, b₂)`
    map to the `EndoScalar` crumb `x = b₂ + 2·b₁` (the crumb's `bitEven`/`bitOdd` are
    the sign/base-selector — `EndoScalar`'s nybble is `bitEven + 2·bitOdd`). On it,
    `EndoScalar`'s Algorithm-2 digit polynomials equal `EndoMul`'s GLV window digit:

        cPoly x = (2·b₂ − 1)·b₁          dPoly x = (2·b₂ − 1)·(1 − b₁)

    where `2·b₂ − 1` is the sign (as in `selectQ`) and `b₁` selects the base — so
    `cPoly` lands on the `φ(T)`/λ component (`EndoScalar`'s `a`, `EndoMul`'s `k₂`)
    and `dPoly` on the `T`/1 component (`EndoScalar`'s `b`, `EndoMul`'s `k₁`). This
    is the heart of `EndoMul ∘ EndoScalar`: the two gates assign the SAME signed
    base to each 2-bit window. Folding these matched digits — with `EndoMul`'s ×4
    per row = ×2 per window matching `EndoScalar`'s ×2 per crumb, and the inits
    aligned (`EndoMul`'s `4^m·P₀` carry ↔ `EndoScalar`'s `a=b=2`) — yields
    `(k₂, k₁) = (a, b)`, i.e. `endoMul`'s scalar equals
    `EndoScalar.toField challenge λ`. -/
private theorem recoding_digit (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) {b1 b2 : F}
    (hb1 : b1 = 0 ∨ b1 = 1) (hb2 : b2 = 0 ∨ b2 = 1) :
    cPoly (b2 + 2 * b1) = (2 * b2 - 1) * b1
      ∧ dPoly (b2 + 2 * b1) = (2 * b2 - 1) * (1 - b1) := by
  obtain ⟨c0, c1, c2, c3⟩ := cPoly_table h2 h3
  obtain ⟨d0, d1, d2, d3⟩ := dPoly_table h2 h3
  rcases hb1 with rfl | rfl <;> rcases hb2 with rfl | rfl
  · exact ⟨by rw [show (0:F) + 2 * 0 = 0 by ring, c0]; ring,
           by rw [show (0:F) + 2 * 0 = 0 by ring, d0]; ring⟩
  · exact ⟨by rw [show (1:F) + 2 * 0 = 1 by ring, c1]; ring,
           by rw [show (1:F) + 2 * 0 = 1 by ring, d1]; ring⟩
  · exact ⟨by rw [show (0:F) + 2 * 1 = 2 by ring, c2]; ring,
           by rw [show (0:F) + 2 * 1 = 2 by ring, d2]; ring⟩
  · exact ⟨by rw [show (1:F) + 2 * 1 = 3 by ring, c3]; ring,
           by rw [show (1:F) + 2 * 1 = 3 by ring, d3]; ring⟩

/-- The row↔crumb sum reindexing — the structural core of the fold-level recoding.
    `EndoMul`'s `m` rows weight each row's 2-crumb contribution `2·g(2i) + g(2i+1)`
    by `4^(m-1-i)`; flattening to `EndoScalar`'s `2m` crumbs weights crumb `j` by
    `2^(2m-1-j)`. The two agree (the row's `×4 = ×2` twice splits across its two
    crumbs). Over any `CommRing` — used at `ℤ` (the GLV coefficients) and `F` (the
    `cPoly`/`dPoly` digits). -/
private theorem sum_reindex {R : Type*} [CommRing R] (m : ℕ) (g : ℕ → R) :
    ∑ i ∈ Finset.range m, (4 : R) ^ (m - 1 - i) * (2 * g (2 * i) + g (2 * i + 1))
      = ∑ j ∈ Finset.range (2 * m), (2 : R) ^ (2 * m - 1 - j) * g j := by
  induction m with
  | zero => simp
  | succ m ih =>
    have e1 : ∀ i ∈ Finset.range m, (4 : R) ^ (m + 1 - 1 - i) * (2 * g (2 * i) + g (2 * i + 1))
        = 4 * ((4 : R) ^ (m - 1 - i) * (2 * g (2 * i) + g (2 * i + 1))) := by
      intro i hi
      have : i < m := Finset.mem_range.mp hi
      rw [show m + 1 - 1 - i = (m - 1 - i) + 1 by omega, pow_succ]; ring
    have e2 : ∀ j ∈ Finset.range (2 * m), (2 : R) ^ (2 * m + 1 + 1 - 1 - j) * g j
        = 4 * ((2 : R) ^ (2 * m - 1 - j) * g j) := by
      intro j hj
      have : j < 2 * m := Finset.mem_range.mp hj
      rw [show 2 * m + 1 + 1 - 1 - j = (2 * m - 1 - j) + 2 by omega, pow_add]; ring
    rw [Finset.sum_range_succ, Finset.sum_congr rfl e1, ← Finset.mul_sum, ih,
      show 2 * (m + 1) = 2 * m + 1 + 1 by ring, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_congr rfl e2, ← Finset.mul_sum,
      show m + 1 - 1 - m = 0 by omega, show 2 * m + 1 + 1 - 1 - (2 * m) = 1 by omega,
      show 2 * m + 1 + 1 - 1 - (2 * m + 1) = 0 by omega]
    ring

open Kimchi.Gate.EndoScalar (cPoly) in
/-- `EndoScalar`'s `a`-digit (`cPoly`, the `φ(T)`/λ component) of crumb `j` built from
    the rows `g`: crumb `2i` is row `i`'s first window `(b₂,b₁)`, crumb `2i+1` its
    second `(b₄,b₃)`. -/
private def aDigit (g : ℕ → Witness F) (j : ℕ) : F :=
  if j % 2 = 0 then cPoly ((g (j / 2)).b2 + 2 * (g (j / 2)).b1)
  else cPoly ((g (j / 2)).b4 + 2 * (g (j / 2)).b3)

open Kimchi.Gate.EndoScalar (dPoly) in
/-- `EndoScalar`'s `b`-digit (`dPoly`, the `T`/1 component) of crumb `j`. -/
private def bDigit (g : ℕ → Witness F) (j : ℕ) : F :=
  if j % 2 = 0 then dPoly ((g (j / 2)).b2 + 2 * (g (j / 2)).b1)
  else dPoly ((g (j / 2)).b4 + 2 * (g (j / 2)).b3)

/-- The `2m`-crumb list the rows feed to `EndoScalar`: row `i` contributes its two
    windows `[b₂+2·b₁, b₄+2·b₃]` in order, so `crumbList[2i] = aDigit/bDigit`'s crumb
    `2i` and `crumbList[2i+1]` crumb `2i+1`. -/
def crumbList (g : ℕ → Witness F) (m : ℕ) : List F :=
  (List.range m).flatMap fun i => [(g i).b2 + 2 * (g i).b1, (g i).b4 + 2 * (g i).b3]

omit [DecidableEq F] in
/-- Each additional row appends its two window crumbs to the crumb list. -/
private theorem crumbList_succ (g : ℕ → Witness F) (m : ℕ) :
    crumbList g (m + 1)
      = crumbList g m ++ [(g m).b2 + 2 * (g m).b1, (g m).b4 + 2 * (g m).b3] := by
  simp [crumbList, List.range_succ, List.flatMap_append]

omit [DecidableEq F] in
/-- The init bridge: `EndoScalar`'s `decomposeA`/`decomposeB` over the crumb
    list (folded from the `a = b = 2` init) is its `2·4^m` carry plus the
    Algorithm-2 digit sums — exactly `endoMul_ab`'s `(k₂:F)` / `(k₁:F)`. By induction
    on `m` (each row appends 2 crumbs; `List.foldl_append`). -/
private theorem decompose_crumbList (g : ℕ → Witness F) (m : ℕ) :
    Kimchi.Gate.EndoScalar.decomposeA (crumbList g m)
        = 2 * (4 : F) ^ m + ∑ j ∈ Finset.range (2 * m), (2 : F) ^ (2 * m - 1 - j) * aDigit g j
      ∧ Kimchi.Gate.EndoScalar.decomposeB (crumbList g m)
        = 2 * (4 : F) ^ m + ∑ j ∈ Finset.range (2 * m), (2 : F) ^ (2 * m - 1 - j) * bDigit g j := by
  induction' m with m ih <;> simp_all +decide [ Nat.mul_succ, Finset.sum_range_succ ];
  · exact ⟨ rfl, rfl ⟩;
  · rw [ crumbList_succ, EndoScalar.decomposeA_append, EndoScalar.decomposeB_append ];
    simp_all +decide [ aDigit, bDigit ];
    norm_num [ Nat.add_div ] ; ring_nf ;
    constructor <;> rw [ Finset.sum_mul _ _ _ ] <;>
      rw [ Finset.sum_congr rfl fun x hx => ?_ ] <;> ring;
    · split_ifs <;>
        rw [ show 1 + m * 2 - x = (m * 2 - 1 - x) + 2 by
              have := Finset.mem_range.mp hx; omega ] <;> ring;
    · split_ifs <;>
        rw [ show 1 + m * 2 - x = (m * 2 - 1 - x) + 2 by
              have := Finset.mem_range.mp hx; omega ] <;> ring

/-! ## Non-degeneracy

The first-addition condition `hxne` is `Pᵢ ∉ {±T, ±φT}` (same `x` ⟺ `±` point). Writing the
accumulator as `[a]·T + [b]·φT` and collapsing with the eigenvalue `φT = [λ]·T`, this reduces to
`a + b·λ ≢ {±1, ±λ} (mod order)` — four "no short relation" facts, supplied for the small
accumulator coefficients by the GLV bound (`Pasta.pallas_glv_no_short_relation`). The
second-addition condition is self-enforced by the gate constraints. -/

/-- One block's second-addition non-degeneracy, self-enforced. If `2·xI − s² + xq = 0`, the
    block constraint `(2·xI − s² + xq)·(…) = (xI − xO)·(2·yI)` gives `(xI − xO)·(2·yI) = 0`;
    with `xI ≠ xO` and char ≠ 2 this forces `yI = 0`, making `I` 2-torsion — ruled out on an
    odd-prime-order group. (The EndoMul analog of VarBaseMul's `tne_of_holds`.) -/
private theorem block_tne (W : WeierstrassCurve.Affine F) [Fact (Nat.Prime W.order)]
    (ha : W.a₁ = 0 ∧ W.a₂ = 0 ∧ W.a₃ = 0) (h2 : (2 : F) ≠ 0) (hodd : W.order ≠ 2)
    {xI yI xO yO s xq : F} (hI : W.Nonsingular xI yI) (hxne : xI ≠ xO)
    (hc : (2 * xI - s ^ 2 + xq) * ((xI - xO) * s + yO + yI) = (xI - xO) * (2 * yI)) :
    2 * xI - s ^ 2 + xq ≠ 0 := by
  haveI : Fact (W.a₁ = 0 ∧ W.a₂ = 0 ∧ W.a₃ = 0) := ⟨ha⟩
  intro ht
  rw [ht, zero_mul] at hc
  have hyI : yI = 0 := by
    rcases mul_eq_zero.mp hc.symm with h | h
    · exact absurd h (sub_ne_zero_of_ne hxne)
    · exact (mul_eq_zero.mp h).resolve_left h2
  obtain ⟨ha1, -, ha3⟩ := ha
  have hneg : W.negY xI yI = yI := by simp [WeierstrassCurve.Affine.negY, ha1, ha3, hyI]
  have hself : -(Point.some _ _ hI) = Point.some _ _ hI := by
    rw [Point.neg_some]; exact some_congr W _ hI rfl hneg
  have hPne : Point.some _ _ hI ≠ 0 := Point.some_ne_zero hI
  have h2P : (2 : ℤ) • Point.some _ _ hI = 0 := by
    rw [two_zsmul]; nth_rewrite 2 [← hself]; rw [add_neg_cancel]
  have hlt : (2 : ℤ) < (W.order : ℤ) := by
    have : (2 : ℕ) < W.order :=
      lt_of_le_of_ne (Fact.out : Nat.Prime W.order).two_le (Ne.symm hodd)
    exact_mod_cast this
  exact Kimchi.Gate.VarBaseMul.smul_ne_zero_of_lt W hPne (by norm_num) hlt h2P

/-- **GLV off-targets.** With the eigenvalue `φT = [λ]·T` and the four no-short-relation facts
    for the accumulator's offset coefficients, the two-base combination `[a]·T + [b]·φT` is none
    of `±T`, `±φT`. The geometric core of `hxne`. -/
private theorem combo_off_targets (W : WeierstrassCurve.Affine F)
    [Fact (W.a₁ = 0 ∧ W.a₂ = 0 ∧ W.a₃ = 0)] [Fact (Nat.Prime W.order)]
    {T φT : W.Point} (hTne : T ≠ 0) {lam : ℤ} (heig : φT = lam • T) {a b : ℤ}
    (h1 : ¬ (W.order : ℤ) ∣ (a - 1 + b * lam))
    (h2 : ¬ (W.order : ℤ) ∣ (a + 1 + b * lam))
    (h3 : ¬ (W.order : ℤ) ∣ (a + (b - 1) * lam))
    (h4 : ¬ (W.order : ℤ) ∣ (a + (b + 1) * lam)) :
    a • T + b • φT ≠ T ∧ a • T + b • φT ≠ -T
      ∧ a • T + b • φT ≠ φT ∧ a • T + b • φT ≠ -φT := by
  have combo : ∀ c : ℤ, a • T + b • φT = c • T ↔ (W.order : ℤ) ∣ (a + b * lam - c) := by
    intro c
    have e : a • T + b • φT - c • T = (a + b * lam - c) • T := by rw [heig]; module
    rw [← sub_eq_zero, e, Kimchi.Gate.VarBaseMul.zsmul_eq_zero_iff_order_dvd W hTne]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hP
    exact h1 (by have := (combo 1).mp (hP.trans (one_zsmul T).symm)
                 rwa [show a + b * lam - 1 = a - 1 + b * lam by ring] at this)
  · intro hP
    exact h2 (by have := (combo (-1)).mp (hP.trans (neg_one_zsmul T).symm)
                 rwa [show a + b * lam - (-1) = a + 1 + b * lam by ring] at this)
  · intro hP
    exact h3 (by have := (combo lam).mp (hP.trans (by rw [heig]))
                 rwa [show a + b * lam - lam = a + (b - 1) * lam by ring] at this)
  · intro hP
    exact h4 (by have := (combo (-lam)).mp (hP.trans (by rw [heig]; simp))
                 rwa [show a + b * lam - -lam = a + (b + 1) * lam by ring] at this)

/-- A bounded variant of `Gate.EndoMul.selectQ` that additionally returns the integer fact
    `e = 1 ∨ e = -1` (the sign), which `selectQ` discards. Same case split, threading the fourth
    component of `Kimchi.Gate.VarBaseMul.signed_target`. -/
private theorem selectQ' (W : WeierstrassCurve.Affine F) (ha : (W.a₁ = 0 ∧ W.a₂ = 0 ∧ W.a₃ = 0))
    {endo b1 b2 xT yT : F}
    (hT : W.Nonsingular xT yT) (hφT : W.Nonsingular (endo * xT) yT)
    (hQ : W.Nonsingular ((1 + (endo - 1) * b1) * xT) ((2 * b2 - 1) * yT))
    (hb1 : b1 = 0 ∨ b1 = 1) (hb2 : b2 = 0 ∨ b2 = 1) :
    (∃ e : ℤ, Point.some _ _ hQ = e • Point.some _ _ hT ∧ (e = 1 ∨ e = -1))
      ∨ (∃ e : ℤ, Point.some _ _ hQ = e • Point.some _ _ hφT ∧ (e = 1 ∨ e = -1)) := by
  rcases hb1 with rfl | rfl
  · left
    have hx : (1 + (endo - 1) * 0) * xT = xT := by ring
    obtain ⟨e, he, _, hpm⟩ := Kimchi.Gate.VarBaseMul.signed_target W ha hT (hx ▸ hQ) hb2
    exact ⟨e, (some_congr W hQ (hx ▸ hQ) hx rfl).trans he, hpm⟩
  · right
    have hx : (1 + (endo - 1) * 1) * xT = endo * xT := by ring
    obtain ⟨e, he, _, hpm⟩ := Kimchi.Gate.VarBaseMul.signed_target W ha hφT (hx ▸ hQ) hb2
    exact ⟨e, (some_congr W hQ (hx ▸ hQ) hx rfl).trans he, hpm⟩

/-! ## The GLV scalar-multiplication chain -/

/-- The two-base GLV fold: chaining `P_{i+1} = 4·P_i + c₁ᵢ·T + c₂ᵢ·φT` over `m` rows
    gives `P_m = 4^m·P₀ + (∑ 4^(m-1-i)·c₁ᵢ)·T + (∑ 4^(m-1-i)·c₂ᵢ)·φT`. Pure group
    algebra (cf. VarBaseMul's `chain_scalarMul`, here with a second base). -/
private theorem chain_endo (W : WeierstrassCurve.Affine F)
    (m : ℕ) (P : ℕ → W.Point) (T φT : W.Point) (c1 c2 : ℕ → ℤ)
    (hstep : ∀ i, i < m → P (i + 1) = (4 : ℤ) • P i + c1 i • T + c2 i • φT) :
    P m = (4 : ℤ) ^ m • P 0
        + (∑ i ∈ Finset.range m, (4 : ℤ) ^ (m - 1 - i) * c1 i) • T
        + (∑ i ∈ Finset.range m, (4 : ℤ) ^ (m - 1 - i) * c2 i) • φT := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hs : P (m + 1) = (4 : ℤ) • P m + c1 m • T + c2 m • φT :=
      hstep m (Nat.lt_succ_self m)
    have ih' := ih (fun i hi => hstep i (Nat.lt_succ_of_lt hi))
    have hsum : ∀ c : ℕ → ℤ,
        (∑ i ∈ Finset.range (m + 1), (4 : ℤ) ^ (m + 1 - 1 - i) * c i)
          = (4 : ℤ) * (∑ i ∈ Finset.range m, (4 : ℤ) ^ (m - 1 - i) * c i) + c m := by
      intro c
      rw [Finset.sum_range_succ, Finset.mul_sum]
      simp only [Nat.add_sub_cancel, Nat.sub_self, pow_zero, one_mul]
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      have hi' : m - i = (m - 1 - i) + 1 := by
        have := Finset.mem_range.mp hi; omega
      rw [hi', pow_succ]; ring
    rw [hs, ih', hsum c1, hsum c2, pow_succ']
    module

/-- Output-accumulator coordinates after `k` rows: row 0's input `xP`/`yP` when `k = 0`, else
    row `(k-1)`'s output `xS`/`yS` (so `accX g m` is the final accumulator's `x`). -/
def accX (g : ℕ → Witness F) : ℕ → F
  | 0 => (g 0).xP
  | k + 1 => (g k).xS

/-- The `y`-companion of `accX`: row 0's input `yP` when `k = 0`, else row `(k-1)`'s
    output `yS`. -/
def accY (g : ℕ → Witness F) : ℕ → F
  | 0 => (g 0).yP
  | k + 1 => (g k).yS

/-- **Producing variant of `Gate.EndoMul.block_sound`.** Same `(P+Q)+P` window algebra, but the
    output accumulator's nonsingularity (`hR`) is *produced* (existential) via `secant_add`,
    rather than consumed as a hypothesis. This is the producer that `gate_advance` / the chain
    proofs call to derive per-row nonsingularity. -/
private theorem block_produce (W : WeierstrassCurve.Affine F) (ha : W.a₁ = 0 ∧ W.a₂ = 0 ∧ W.a₃ = 0)
    {xq yq xP yP s xR yR : F}
    (hP : W.Nonsingular xP yP) (hQ : W.Nonsingular xq yq)
    (hxne : xP ≠ xq) (htne : 2 * xP - s ^ 2 + xq ≠ 0) (hxRne : xR ≠ xP)
    (hs : (xq - xP) * s = yq - yP)
    (hc2 : (2 * xP - s ^ 2 + xq) * ((xP - xR) * s + yR + yP) = (xP - xR) * (2 * yP))
    (hc3 : (yR + yP) ^ 2 = (xP - xR) ^ 2 * (s ^ 2 - xq + xR)) :
    ∃ hR : W.Nonsingular xR yR,
      Point.some _ _ hR = (Point.some _ _ hP + Point.some _ _ hQ) + Point.some _ _ hP := by
  obtain ⟨ha1, ha2, ha3⟩ := ha
  have hdiff1 : xP - xq ≠ 0 := sub_ne_zero.mpr hxne
  have hxRne0 : xP - xR ≠ 0 := sub_ne_zero.mpr (Ne.symm hxRne)
  have hl1 : s = (yP - yq) / (xP - xq) := by
    rw [eq_div_iff hdiff1]; linear_combination -hs
  set Mx : F := s * s - xP - xq with hMx
  set My : F := s * (xP - Mx) - yP with hMy
  set s2 : F := (My - yP) / (Mx - xP) with hs2
  clear_value s2 My Mx
  have htval : xP - Mx = 2 * xP - s ^ 2 + xq := by rw [hMx]; ring
  have htt : xP - Mx ≠ 0 := by rw [htval]; exact htne
  have hMxne : Mx ≠ xP := by intro hc; exact htt (by rw [hc]; ring)
  have hxine : Mx - xP ≠ 0 := sub_ne_zero.mpr hMxne
  obtain ⟨hM, hAdd1⟩ :=
    Kimchi.Gate.VarBaseMul.secant_add W ⟨ha1, ha2, ha3⟩ hP hQ hxne hl1 hMx hMy
  have hsr : s2 * (Mx - xP) = My - yP := by rw [hs2, div_mul_cancel₀]; exact hxine
  have key1' : (yR + yP) * (Mx - xP) = (xP - xR) * (My - yP) := by
    linear_combination -hc2 - (xP - xR) * hMy - ((xP - xR) * s + yR + yP) * htval
  have hcancel : (yR + yP) * (Mx - xP) = ((xP - xR) * s2) * (Mx - xP) := by
    rw [key1']; linear_combination -(xP - xR) * hsr
  have key1div : yR + yP = (xP - xR) * s2 := mul_right_cancel₀ hxine hcancel
  have hs2sq : s2 * s2 = s ^ 2 - xq + xR := by
    have hkey3 : (xP - xR) ^ 2 * (s2 * s2) = (xP - xR) ^ 2 * (s ^ 2 - xq + xR) := by
      rw [← hc3]
      linear_combination -((yR + yP) + (xP - xR) * s2) * key1div
    exact mul_left_cancel₀ (pow_ne_zero 2 hxRne0) hkey3
  have hxR_eq : xR = s2 * s2 - Mx - xP := by rw [hs2sq, hMx]; ring
  have hyR_eq : yR = s2 * (Mx - xR) - My := by
    have hyR' : yR = (xP - xR) * s2 - yP := by linear_combination key1div
    rw [hyR']; linear_combination -hsr
  obtain ⟨hR', hAdd2⟩ :=
    Kimchi.Gate.VarBaseMul.secant_add W ⟨ha1, ha2, ha3⟩ hM hP hMxne hs2 hxR_eq hyR_eq
  exact ⟨hR', by rw [hAdd1, hAdd2]⟩

/-- **The producing gate step.** Given the input accumulator on-curve (`hP`), the base
    (`hT`/`hφT`), the row constraints (`Holds`), and the two first-addition non-degeneracies
    (`hxne1`/`hxne2` — the second-addition `htne`s are self-enforced via `htne_of_holds`), the
    gate *produces* the output point on-curve (`hS`, existential — via the secant additions, not
    assumed) together with the GLV contribution. The `(c1, c2)` digit identities are the GLV
    window digits, plus the `|·| ≤ 3` bound used by the accumulator invariant. -/
private theorem gate_advance (W : WeierstrassCurve.Affine F) [Fact (Nat.Prime W.order)]
    (ha : W.a₁ = 0 ∧ W.a₂ = 0 ∧ W.a₃ = 0)
    (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (hodd : W.order ≠ 2)
    (endo : F) (w : Witness F) (h : Holds endo w)
    (hT : W.Nonsingular w.xT w.yT) (hφT : W.Nonsingular (endo * w.xT) w.yT)
    (hP : W.Nonsingular w.xP w.yP)
    (hxne1 : w.xP ≠ (1 + (endo - 1) * w.b1) * w.xT)
    (hxne2 : w.xR ≠ (1 + (endo - 1) * w.b3) * w.xT) :
    ∃ (hS : W.Nonsingular w.xS w.yS) (c1 c2 : ℤ),
      Point.some _ _ hS = (4 : ℤ) • Point.some _ _ hP
          + c1 • Point.some _ _ hT + c2 • Point.some _ _ hφT
        ∧ (c1 : F) = 2 * dPoly (w.b2 + 2 * w.b1) + dPoly (w.b4 + 2 * w.b3)
        ∧ (c2 : F) = 2 * cPoly (w.b2 + 2 * w.b1) + cPoly (w.b4 + 2 * w.b3)
        ∧ |c1| ≤ 3 ∧ |c2| ≤ 3 := by
  -- distinct-point facts and target nonsingularities
  obtain ⟨hxPxR, hxRxS⟩ := distinctPoints endo w h
  obtain ⟨hQ1, hQ2⟩ := targets_nonsingular W ha endo w h hT hφT
  -- the gate constraints
  have hb := h
  rw [holds_iff] at hb
  obtain ⟨hs1, hc2_1, hc3_1, hs3, hc2_2, hc3_2, _, hb1c, hb2c, hb3c, hb4c, _⟩ := hb
  have hb1 := bool_of_mul hb1c
  have hb2 := bool_of_mul hb2c
  have hb3 := bool_of_mul hb3c
  have hb4 := bool_of_mul hb4c
  -- window 1: produce `hR` (the self-enforced second-addition non-degeneracy via `block_tne`)
  have htne1 := block_tne W ha h2 hodd hP hxPxR hc2_1
  obtain ⟨hR, hReq⟩ :=
    block_produce W ha hP hQ1 hxne1 htne1 (Ne.symm hxPxR) hs1 hc2_1 hc3_1
  -- window 2: produce `hS`
  have htne2 := block_tne W ha h2 hodd hR hxRxS hc2_2
  obtain ⟨hS, hSeq⟩ :=
    block_produce W ha hR hQ2 hxne2 htne2 (Ne.symm hxRxS) hs3 hc2_2 hc3_2
  refine ⟨hS, ?_⟩
  -- recoding digit identities
  obtain ⟨hcP1, hdP1⟩ := recoding_digit h2 h3 hb1 hb2
  obtain ⟨hcP2, hdP2⟩ := recoding_digit h2 h3 hb3 hb4
  rcases hb1 with hb1' | hb1' <;> rcases hb3 with hb3' | hb3'
  · -- b1 = 0 (Q₁ = ±T), b3 = 0 (Q₂ = ±T)
    have hxc1 : (1 + (endo - 1) * w.b1) * w.xT = w.xT := by rw [hb1']; ring
    obtain ⟨e1, he1, he1f, he1pm⟩ :=
      Kimchi.Gate.VarBaseMul.signed_target W ha hT (hxc1 ▸ hQ1) hb2
    have hQ1e : Point.some _ _ hQ1 = e1 • Point.some _ _ hT :=
      (some_congr W hQ1 (hxc1 ▸ hQ1) hxc1 rfl).trans he1
    have hxc2 : (1 + (endo - 1) * w.b3) * w.xT = w.xT := by rw [hb3']; ring
    obtain ⟨e2, he2, he2f, he2pm⟩ :=
      Kimchi.Gate.VarBaseMul.signed_target W ha hT (hxc2 ▸ hQ2) hb4
    have hQ2e : Point.some _ _ hQ2 = e2 • Point.some _ _ hT :=
      (some_congr W hQ2 (hxc2 ▸ hQ2) hxc2 rfl).trans he2
    refine ⟨2 * e1 + e2, 0, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hSeq, hReq, hQ1e, hQ2e]; module
    · rw [hdP1, hdP2]; push_cast [he1f, he2f]; rw [hb1', hb3']; ring
    · rw [hcP1, hcP2]; push_cast [he1f, he2f]; rw [hb1', hb3']; ring
    · rcases he1pm with rfl | rfl <;> rcases he2pm with rfl | rfl <;> decide
    · rcases he1pm with rfl | rfl <;> rcases he2pm with rfl | rfl <;> decide
  · -- b1 = 0 (Q₁ = ±T), b3 = 1 (Q₂ = ±φT)
    have hxc1 : (1 + (endo - 1) * w.b1) * w.xT = w.xT := by rw [hb1']; ring
    obtain ⟨e1, he1, he1f, he1pm⟩ :=
      Kimchi.Gate.VarBaseMul.signed_target W ha hT (hxc1 ▸ hQ1) hb2
    have hQ1e : Point.some _ _ hQ1 = e1 • Point.some _ _ hT :=
      (some_congr W hQ1 (hxc1 ▸ hQ1) hxc1 rfl).trans he1
    have hxc2 : (1 + (endo - 1) * w.b3) * w.xT = endo * w.xT := by rw [hb3']; ring
    obtain ⟨e2, he2, he2f, he2pm⟩ :=
      Kimchi.Gate.VarBaseMul.signed_target W ha hφT (hxc2 ▸ hQ2) hb4
    have hQ2e : Point.some _ _ hQ2 = e2 • Point.some _ _ hφT :=
      (some_congr W hQ2 (hxc2 ▸ hQ2) hxc2 rfl).trans he2
    refine ⟨2 * e1, e2, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hSeq, hReq, hQ1e, hQ2e]; module
    · rw [hdP1, hdP2]; push_cast [he1f, he2f]; rw [hb1', hb3']; ring
    · rw [hcP1, hcP2]; push_cast [he1f, he2f]; rw [hb1', hb3']; ring
    · rcases he1pm with rfl | rfl <;> rcases he2pm with rfl | rfl <;> decide
    · rcases he1pm with rfl | rfl <;> rcases he2pm with rfl | rfl <;> decide
  · -- b1 = 1 (Q₁ = ±φT), b3 = 0 (Q₂ = ±T)
    have hxc1 : (1 + (endo - 1) * w.b1) * w.xT = endo * w.xT := by rw [hb1']; ring
    obtain ⟨e1, he1, he1f, he1pm⟩ :=
      Kimchi.Gate.VarBaseMul.signed_target W ha hφT (hxc1 ▸ hQ1) hb2
    have hQ1e : Point.some _ _ hQ1 = e1 • Point.some _ _ hφT :=
      (some_congr W hQ1 (hxc1 ▸ hQ1) hxc1 rfl).trans he1
    have hxc2 : (1 + (endo - 1) * w.b3) * w.xT = w.xT := by rw [hb3']; ring
    obtain ⟨e2, he2, he2f, he2pm⟩ :=
      Kimchi.Gate.VarBaseMul.signed_target W ha hT (hxc2 ▸ hQ2) hb4
    have hQ2e : Point.some _ _ hQ2 = e2 • Point.some _ _ hT :=
      (some_congr W hQ2 (hxc2 ▸ hQ2) hxc2 rfl).trans he2
    refine ⟨e2, 2 * e1, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hSeq, hReq, hQ1e, hQ2e]; module
    · rw [hdP1, hdP2]; push_cast [he1f, he2f]; rw [hb1', hb3']; ring
    · rw [hcP1, hcP2]; push_cast [he1f, he2f]; rw [hb1', hb3']; ring
    · rcases he1pm with rfl | rfl <;> rcases he2pm with rfl | rfl <;> decide
    · rcases he1pm with rfl | rfl <;> rcases he2pm with rfl | rfl <;> decide
  · -- b1 = 1 (Q₁ = ±φT), b3 = 1 (Q₂ = ±φT)
    have hxc1 : (1 + (endo - 1) * w.b1) * w.xT = endo * w.xT := by rw [hb1']; ring
    obtain ⟨e1, he1, he1f, he1pm⟩ :=
      Kimchi.Gate.VarBaseMul.signed_target W ha hφT (hxc1 ▸ hQ1) hb2
    have hQ1e : Point.some _ _ hQ1 = e1 • Point.some _ _ hφT :=
      (some_congr W hQ1 (hxc1 ▸ hQ1) hxc1 rfl).trans he1
    have hxc2 : (1 + (endo - 1) * w.b3) * w.xT = endo * w.xT := by rw [hb3']; ring
    obtain ⟨e2, he2, he2f, he2pm⟩ :=
      Kimchi.Gate.VarBaseMul.signed_target W ha hφT (hxc2 ▸ hQ2) hb4
    have hQ2e : Point.some _ _ hQ2 = e2 • Point.some _ _ hφT :=
      (some_congr W hQ2 (hxc2 ▸ hQ2) hxc2 rfl).trans he2
    refine ⟨0, 2 * e1 + e2, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hSeq, hReq, hQ1e, hQ2e]; module
    · rw [hdP1, hdP2]; push_cast [he1f, he2f]; rw [hb1', hb3']; ring
    · rw [hcP1, hcP2]; push_cast [he1f, he2f]; rw [hb1', hb3']; ring
    · rcases he1pm with rfl | rfl <;> rcases he2pm with rfl | rfl <;> decide
    · rcases he1pm with rfl | rfl <;> rcases he2pm with rfl | rfl <;> decide

/-- **The GLV-recoding chain.** `m` `EndoMul` rows over `Holds` (with base + threading + initial +
    the per-row `hxne`) compute the final accumulator `= 4^m·P₀ + k₁·T + k₂·φT`; the field casts of
    the GLV coefficients `(k₂, k₁)` are exactly `EndoScalar`'s Algorithm-2 `a`, `b` digit-sums over
    the shared crumbs. Every intermediate accumulator's nonsingularity is *derived* via
    `gate_advance`, so the prover supplies only `Holds`. -/
private theorem endoMul_ab (W : WeierstrassCurve.Affine F) [Fact (Nat.Prime W.order)]
    (ha : W.a₁ = 0 ∧ W.a₂ = 0 ∧ W.a₃ = 0)
    (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (hodd : W.order ≠ 2) (endo : F)
    (m : ℕ) (g : ℕ → Witness F) (hholds : ∀ i, i < m → Holds endo (g i))
    (T φT : W.Point)
    (hTns : W.Nonsingular (g 0).xT (g 0).yT) (hTeq : T = Point.some _ _ hTns)
    (hφTns : W.Nonsingular (endo * (g 0).xT) (g 0).yT) (hφTeq : φT = Point.some _ _ hφTns)
    (hbase : ∀ i, i < m → (g i).xT = (g 0).xT ∧ (g i).yT = (g 0).yT)
    (hthread : ∀ i, i + 1 < m → (g (i + 1)).xP = (g i).xS ∧ (g (i + 1)).yP = (g i).yS)
    (hP0ns : W.Nonsingular (g 0).xP (g 0).yP)
    (hxne : ∀ i, i < m → (g i).xP ≠ (1 + (endo - 1) * (g i).b1) * (g i).xT
                        ∧ (g i).xR ≠ (1 + (endo - 1) * (g i).b3) * (g i).xT) :
    ∃ (hfin : W.Nonsingular (accX g m) (accY g m)) (k1 k2 : ℤ),
      Point.some _ _ hfin = (4 : ℤ) ^ m • Point.some _ _ hP0ns + k1 • T + k2 • φT
        ∧ (k2 : F) = ∑ j ∈ Finset.range (2 * m), (2 : F) ^ (2 * m - 1 - j) * aDigit g j
        ∧ (k1 : F) = ∑ j ∈ Finset.range (2 * m), (2 : F) ^ (2 * m - 1 - j) * bDigit g j := by
  -- coordinate threading: row `i`'s input column equals the accumulator at step `i`
  have haccP : ∀ k, k < m → (g k).xP = accX g k ∧ (g k).yP = accY g k := by
    intro k hk
    cases k with
    | zero => exact ⟨rfl, rfl⟩
    | succ j => exact hthread j hk
  -- per-step accumulator nonsingularity, derived by threading `gate_advance`
  have key : ∀ k, k ≤ m → W.Nonsingular (accX g k) (accY g k) := by
    intro k
    induction k with
    | zero => intro _; exact hP0ns
    | succ j ih =>
      intro hj
      have hj' : j < m := by omega
      obtain ⟨hxP, hyP⟩ := haccP j hj'
      have hPj : W.Nonsingular (g j).xP (g j).yP := by rw [hxP, hyP]; exact ih (by omega)
      have hTj : W.Nonsingular (g j).xT (g j).yT := by
        obtain ⟨hx, hy⟩ := hbase j hj'; rw [hx, hy]; exact hTns
      have hφTj : W.Nonsingular (endo * (g j).xT) (g j).yT := by
        obtain ⟨hx, hy⟩ := hbase j hj'; rw [hx, hy]; exact hφTns
      obtain ⟨hxn1, hxn2⟩ := hxne j hj'
      obtain ⟨hSj, -⟩ :=
        gate_advance W ha h2 h3 hodd endo (g j) (hholds j hj') hTj hφTj hPj hxn1 hxn2
      exact hSj
  -- the accumulator chain as a point function over the derived per-step nonsingularity
  set P : ℕ → W.Point := fun k => if hk : k ≤ m then Point.some _ _ (key k hk) else 0 with hPdef
  have hPval : ∀ k (hk : k ≤ m), P k = Point.some _ _ (key k hk) := by
    intro k hk; rw [hPdef]; exact dif_pos hk
  -- per-row GLV contribution, read straight off `gate_advance` (no bundle, no `endoMul`)
  have hrow : ∀ i, i < m → ∃ c1 c2 : ℤ,
      P (i + 1) = (4 : ℤ) • P i + c1 • T + c2 • φT
        ∧ (c1 : F) = 2 * dPoly ((g i).b2 + 2 * (g i).b1) + dPoly ((g i).b4 + 2 * (g i).b3)
        ∧ (c2 : F) = 2 * cPoly ((g i).b2 + 2 * (g i).b1) + cPoly ((g i).b4 + 2 * (g i).b3) := by
    intro i hi
    obtain ⟨hxP, hyP⟩ := haccP i hi
    have hPi : W.Nonsingular (g i).xP (g i).yP := by rw [hxP, hyP]; exact key i (le_of_lt hi)
    have hTi : W.Nonsingular (g i).xT (g i).yT := by
      obtain ⟨hx, hy⟩ := hbase i hi; rw [hx, hy]; exact hTns
    have hφTi : W.Nonsingular (endo * (g i).xT) (g i).yT := by
      obtain ⟨hx, hy⟩ := hbase i hi; rw [hx, hy]; exact hφTns
    obtain ⟨hxn1, hxn2⟩ := hxne i hi
    obtain ⟨hS, c1, c2, hrel, hd1, hd2, -, -⟩ :=
      gate_advance W ha h2 h3 hodd endo (g i) (hholds i hi) hTi hφTi hPi hxn1 hxn2
    refine ⟨c1, c2, ?_, hd1, hd2⟩
    rw [hPval (i + 1) hi, hPval i (le_of_lt hi),
      some_congr W (key (i + 1) hi) hS rfl rfl,
      some_congr W (key i (le_of_lt hi)) hPi hxP.symm hyP.symm, hTeq,
      some_congr W hTns hTi (hbase i hi).1.symm (hbase i hi).2.symm, hφTeq,
      some_congr W hφTns hφTi (by rw [(hbase i hi).1]) (hbase i hi).2.symm]
    exact hrel
  choose! c1 c2 hc using hrow
  have hstep : ∀ i, i < m → P (i + 1) = (4 : ℤ) • P i + c1 i • T + c2 i • φT :=
    fun i hi => (hc i hi).1
  -- fold the chain and identify the scalar with `EndoScalar.toField` (cf. the old `endoMul_ab`)
  set k1 := ∑ i ∈ Finset.range m, (4 : ℤ) ^ (m - 1 - i) * c1 i with hk1def
  set k2 := ∑ i ∈ Finset.range m, (4 : ℤ) ^ (m - 1 - i) * c2 i with hk2def
  have hPm : P m = (4 : ℤ) ^ m • P 0 + k1 • T + k2 • φT := chain_endo W m P T φT c1 c2 hstep
  have hk2 : (k2 : F) = ∑ j ∈ Finset.range (2 * m), (2 : F) ^ (2 * m - 1 - j) * aDigit g j := by
    rw [hk2def, ← sum_reindex m (aDigit g)]; push_cast
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' : i < m := Finset.mem_range.mp hi
    have e1 : (2 * i) % 2 = 0 := by omega
    have e2 : (2 * i) / 2 = i := by omega
    have e3 : (2 * i + 1) % 2 = 1 := by omega
    have e4 : (2 * i + 1) / 2 = i := by omega
    have haE : aDigit g (2 * i) = cPoly ((g i).b2 + 2 * (g i).b1) := by simp [aDigit, e1, e2]
    have haO : aDigit g (2 * i + 1) = cPoly ((g i).b4 + 2 * (g i).b3) := by simp [aDigit, e3, e4]
    rw [haE, haO, ← (hc i hi').2.2]
  have hk1 : (k1 : F) = ∑ j ∈ Finset.range (2 * m), (2 : F) ^ (2 * m - 1 - j) * bDigit g j := by
    rw [hk1def, ← sum_reindex m (bDigit g)]; push_cast
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' : i < m := Finset.mem_range.mp hi
    have e1 : (2 * i) % 2 = 0 := by omega
    have e2 : (2 * i) / 2 = i := by omega
    have e3 : (2 * i + 1) % 2 = 1 := by omega
    have e4 : (2 * i + 1) / 2 = i := by omega
    have hbE : bDigit g (2 * i) = dPoly ((g i).b2 + 2 * (g i).b1) := by simp [bDigit, e1, e2]
    have hbO : bDigit g (2 * i + 1) = dPoly ((g i).b4 + 2 * (g i).b3) := by simp [bDigit, e3, e4]
    rw [hbE, hbO, ← (hc i hi').2.1]
  refine ⟨key m (le_refl m), k1, k2, ?_, hk2, hk1⟩
  rw [← hPval m (le_refl m), hPm, hPval 0 (Nat.zero_le m),
    some_congr W (key 0 (Nat.zero_le m)) hP0ns rfl rfl]

/-- **EndoMul — the capstone.** At the real init `P₀ = 2(T + φT)` and eigenvalue `φT = [λ]·T`, the
    rows compute the final accumulator `= [s]·T` with `s = EndoScalar.toField (crumbList g m) λ`:
    EndoMul multiplies the base by exactly the scalar EndoScalar decodes. The prover supplies only
    `Holds` per row + base + threading + initial; the intermediate nonsingularity is derived and
    `hxne` is the lone coordinate side-condition (the curve layer discharges it via
    `accumulator_chain`). Specializes to the curves as `{pallas,vesta}_endoMul`. -/
theorem endoMul (W : WeierstrassCurve.Affine F) [Fact (Nat.Prime W.order)]
    (ha : W.a₁ = 0 ∧ W.a₂ = 0 ∧ W.a₃ = 0)
    (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (hodd : W.order ≠ 2) (endo : F)
    (m : ℕ) (g : ℕ → Witness F) (hholds : ∀ i, i < m → Holds endo (g i))
    (T φT : W.Point)
    (hTns : W.Nonsingular (g 0).xT (g 0).yT) (hTeq : T = Point.some _ _ hTns)
    (hφTns : W.Nonsingular (endo * (g 0).xT) (g 0).yT) (hφTeq : φT = Point.some _ _ hφTns)
    (hbase : ∀ i, i < m → (g i).xT = (g 0).xT ∧ (g i).yT = (g 0).yT)
    (hthread : ∀ i, i + 1 < m → (g (i + 1)).xP = (g i).xS ∧ (g (i + 1)).yP = (g i).yS)
    (hP0ns : W.Nonsingular (g 0).xP (g 0).yP)
    (hP0 : Point.some _ _ hP0ns = (2 : ℤ) • T + (2 : ℤ) • φT)
    (hxne : ∀ i, i < m → (g i).xP ≠ (1 + (endo - 1) * (g i).b1) * (g i).xT
                        ∧ (g i).xR ≠ (1 + (endo - 1) * (g i).b3) * (g i).xT)
    (lam : ℤ) (heig : φT = lam • T) :
    ∃ (hfin : W.Nonsingular (accX g m) (accY g m)) (s : ℤ),
      Point.some _ _ hfin = s • T
        ∧ (s : F) = Kimchi.Gate.EndoScalar.toField (crumbList g m) (lam : F) := by
  obtain ⟨hfin, k1, k2, hPm, hk2, hk1⟩ :=
    endoMul_ab W ha h2 h3 hodd endo m g hholds T φT hTns hTeq hφTns hφTeq hbase hthread hP0ns hxne
  refine ⟨hfin, 2 * 4 ^ m + k1 + (2 * 4 ^ m + k2) * lam, ?_, ?_⟩
  · rw [hPm, hP0, heig]; module
  · simp +decide [EndoScalar.toField, hk1, hk2]
    rw [decompose_crumbList g m |>.1, decompose_crumbList g m |>.2]; ring

/-- **Producing variant of `one_window`.** Given the bounded input accumulator form `[a]·T + [b]·φT`
    and a window's constraints, derives the window's first-addition non-degeneracy `hxne` and
    advances to the next bounded form, handing back the on-curve output point — the output
    accumulator's nonsingularity `hO` is *produced* (via `block_produce`) rather than consumed. -/
private theorem one_window_produce (W : WeierstrassCurve.Affine F)
    [Fact (W.a₁ = 0 ∧ W.a₂ = 0 ∧ W.a₃ = 0)] [Fact (Nat.Prime W.order)]
    (T φT : W.Point)
    (off : ∀ a b : ℤ, a ≠ 0 → b ≠ 0 → |a| < 2 ^ 126 → |b| < 2 ^ 126 →
      a • T + b • φT ≠ T ∧ a • T + b • φT ≠ -T
        ∧ a • T + b • φT ≠ φT ∧ a • T + b • φT ≠ -φT)
    {endo bf bs xT yT : F} (hT : W.Nonsingular xT yT) (hφT : W.Nonsingular (endo * xT) yT)
    (hTeq : T = Point.some _ _ hT) (hφTeq : φT = Point.some _ _ hφT)
    (hbf : bf = 0 ∨ bf = 1) (hbs : bs = 0 ∨ bs = 1)
    {xI yI xO yO s : F} (hI : W.Nonsingular xI yI)
    (a b : ℤ) (hIeq : Point.some _ _ hI = a • T + b • φT)
    (ha2 : 2 ≤ a) (haH : a < 2 ^ 126) (hb2 : 2 ≤ b) (hbH : b < 2 ^ 126)
    (hxIO : xO ≠ xI)
    (htne : 2 * xI - s ^ 2 + (1 + (endo - 1) * bf) * xT ≠ 0)
    (hs : ((1 + (endo - 1) * bf) * xT - xI) * s = (2 * bs - 1) * yT - yI)
    (hc2 : (2 * xI - s ^ 2 + (1 + (endo - 1) * bf) * xT) * ((xI - xO) * s + yO + yI)
        = (xI - xO) * (2 * yI))
    (hc3 : (yO + yI) ^ 2 = (xI - xO) ^ 2 * (s ^ 2 - (1 + (endo - 1) * bf) * xT + xO)) :
    xI ≠ (1 + (endo - 1) * bf) * xT
      ∧ ∃ (hO : W.Nonsingular xO yO) (a' b' : ℤ), Point.some _ _ hO = a' • T + b' • φT
          ∧ 2 * a - 1 ≤ a' ∧ a' ≤ 2 * a + 1 ∧ 2 * b - 1 ≤ b' ∧ b' ≤ 2 * b + 1 := by
  have ha' : W.a₁ = 0 ∧ W.a₂ = 0 ∧ W.a₃ = 0 := Fact.out
  have hQ := Kimchi.Gate.EndoMul.target_nonsingular W ha' hT hφT hbf hbs
  have hsel := selectQ' W ha' hT hφT hQ hbf hbs
  have ha0 : a ≠ 0 := by omega
  have hb0 : b ≠ 0 := by omega
  have haabs : |a| < 2 ^ 126 := by rw [abs_of_pos (by omega : (0 : ℤ) < a)]; exact haH
  have hbabs : |b| < 2 ^ 126 := by rw [abs_of_pos (by omega : (0 : ℤ) < b)]; exact hbH
  have hoff := off a b ha0 hb0 haabs hbabs
  have hxne : xI ≠ (1 + (endo - 1) * bf) * xT := by
    rcases hsel with ⟨e, hQe, he⟩ | ⟨e, hQe, he⟩ <;> rcases he with rfl | rfl <;>
      refine Kimchi.Gate.VarBaseMul.x_ne_xT_of_ne_base W hI hQ ?_ ?_ <;>
      simp only [hIeq, hQe, ← hTeq, ← hφTeq, one_zsmul, neg_one_zsmul, neg_neg] <;>
      first
        | exact hoff.1 | exact hoff.2.1 | exact hoff.2.2.1 | exact hoff.2.2.2
  refine ⟨hxne, ?_⟩
  obtain ⟨hO, hO_eq⟩ := block_produce W ha' hI hQ hxne htne hxIO hs hc2 hc3
  refine ⟨hO, ?_⟩
  rcases hsel with ⟨e, hQe, he⟩ | ⟨e, hQe, he⟩
  · rcases he with rfl | rfl
    · exact ⟨2 * a + 1, 2 * b, by rw [hO_eq, hIeq, hQe, ← hTeq]; module,
        by omega, by omega, by omega, by omega⟩
    · exact ⟨2 * a - 1, 2 * b, by rw [hO_eq, hIeq, hQe, ← hTeq]; module,
        by omega, by omega, by omega, by omega⟩
  · rcases he with rfl | rfl
    · exact ⟨2 * a, 2 * b + 1, by rw [hO_eq, hIeq, hQe, ← hφTeq]; module,
        by omega, by omega, by omega, by omega⟩
    · exact ⟨2 * a, 2 * b - 1, by rw [hO_eq, hIeq, hQe, ← hφTeq]; module,
        by omega, by omega, by omega, by omega⟩

/-- **Deriving `hxne` from the GLV bound.** The fused induction: from the leaner hypotheses + the
    GLV off-targets fact `off` (`= combo_off_targets`), each accumulator point is `[A]·T + [B]·φT`
    with `A, B ∈ [4ⁱ+1, 3·4ⁱ−1]` (so `< 2¹²⁶`), which yields the per-row first-addition
    non-degeneracy `hxne`. The nonsingularity is derived inside the same induction (via
    `gate_advance`), not consumed from a bundle. -/
private theorem accumulator_chain (W : WeierstrassCurve.Affine F)
    [Fact (W.a₁ = 0 ∧ W.a₂ = 0 ∧ W.a₃ = 0)] [Fact (Nat.Prime W.order)]
    (h2 : (2 : F) ≠ 0) (hodd : W.order ≠ 2) (endo : F)
    (T φT : W.Point)
    (off : ∀ a b : ℤ, a ≠ 0 → b ≠ 0 → |a| < 2 ^ 126 → |b| < 2 ^ 126 →
      a • T + b • φT ≠ T ∧ a • T + b • φT ≠ -T
        ∧ a • T + b • φT ≠ φT ∧ a • T + b • φT ≠ -φT)
    (m : ℕ) (hbits : 4 * m ≤ 244) (g : ℕ → Witness F)
    (hholds : ∀ i, i < m → Holds endo (g i))
    (hTns : W.Nonsingular (g 0).xT (g 0).yT) (hTeq : T = Point.some _ _ hTns)
    (hφTns : W.Nonsingular (endo * (g 0).xT) (g 0).yT) (hφTeq : φT = Point.some _ _ hφTns)
    (hbase : ∀ i, i < m → (g i).xT = (g 0).xT ∧ (g i).yT = (g 0).yT)
    (hthread : ∀ i, i + 1 < m → (g (i + 1)).xP = (g i).xS ∧ (g (i + 1)).yP = (g i).yS)
    (hP0ns : W.Nonsingular (g 0).xP (g 0).yP)
    (hP0 : Point.some _ _ hP0ns = (2 : ℤ) • T + (2 : ℤ) • φT) :
    ∀ i, i < m → (g i).xP ≠ (1 + (endo - 1) * (g i).b1) * (g i).xT
                ∧ (g i).xR ≠ (1 + (endo - 1) * (g i).b3) * (g i).xT := by
  have ha' : W.a₁ = 0 ∧ W.a₂ = 0 ∧ W.a₃ = 0 := Fact.out
  -- coordinate threading: row `i`'s input column equals the accumulator at step `i`
  have haccP : ∀ k, k < m → (g k).xP = accX g k ∧ (g k).yP = accY g k := by
    intro k hk
    cases k with
    | zero => exact ⟨rfl, rfl⟩
    | succ j => exact hthread j hk
  -- the fused invariant: each step's accumulator is `[A]·T + [B]·φT`, bounded; nonsingularity
  -- is produced (`one_window_produce`) rather than consumed from a bundle.
  have inv : ∀ i, i ≤ m → ∃ (hPi : W.Nonsingular (accX g i) (accY g i)) (A B : ℤ),
      Point.some _ _ hPi = A • T + B • φT
        ∧ (4 : ℤ) ^ i + 1 ≤ A ∧ A ≤ 3 * 4 ^ i - 1
        ∧ (4 : ℤ) ^ i + 1 ≤ B ∧ B ≤ 3 * 4 ^ i - 1 := by
    intro i
    induction i with
    | zero =>
      intro _
      exact ⟨hP0ns, 2, 2, hP0, by norm_num, by norm_num, by norm_num, by norm_num⟩
    | succ i ih =>
      intro hi
      have hi' : i < m := by omega
      obtain ⟨hPi', A, B, hPeq, hAlo, hAhi, hBlo, hBhi⟩ := ih (by omega)
      -- power bookkeeping (verbatim from `accumulator_invariant`)
      have h2i : 2 * i ≤ 120 := by omega
      have h4i : (4 : ℤ) ^ i ≤ 2 ^ 120 := by
        calc (4 : ℤ) ^ i = 2 ^ (2 * i) := by rw [pow_mul]; norm_num
          _ ≤ 2 ^ 120 := pow_le_pow_right₀ (by norm_num) h2i
      have h4ipos : (1 : ℤ) ≤ 4 ^ i := one_le_pow₀ (by norm_num)
      have hsucc : (4 : ℤ) ^ (i + 1) = 4 * 4 ^ i := by rw [pow_succ]; ring
      have hp125 : (3 : ℤ) * 2 ^ 120 < 2 ^ 126 := by norm_num
      have hp126 : (6 : ℤ) * 2 ^ 120 < 2 ^ 126 := by norm_num
      have hAlo2 : (2 : ℤ) ≤ A := by omega
      have hBlo2 : (2 : ℤ) ≤ B := by omega
      have hAlt : A < 2 ^ 126 := by omega
      have hBlt : B < 2 ^ 126 := by omega
      -- transport the input accumulator to row `i`'s column coordinates
      obtain ⟨hxP, hyP⟩ := haccP i hi'
      have hPi : W.Nonsingular (g i).xP (g i).yP := by rw [hxP, hyP]; exact hPi'
      have hIeq : Point.some _ _ hPi = A • T + B • φT :=
        (some_congr W hPi hPi' hxP hyP).trans hPeq
      -- per-row base nonsingularity and `T`/`φT` identification (base shared via `hbase`)
      have hTi : W.Nonsingular (g i).xT (g i).yT := by
        obtain ⟨hx, hy⟩ := hbase i hi'; rw [hx, hy]; exact hTns
      have hφTi : W.Nonsingular (endo * (g i).xT) (g i).yT := by
        obtain ⟨hx, hy⟩ := hbase i hi'; rw [hx, hy]; exact hφTns
      have hTeqi : T = Point.some _ _ hTi :=
        hTeq.trans (some_congr W hTns hTi (hbase i hi').1.symm (hbase i hi').2.symm)
      have hφTeqi : φT = Point.some _ _ hφTi :=
        hφTeq.trans (some_congr W hφTns hφTi (by rw [(hbase i hi').1]) (hbase i hi').2.symm)
      -- per-row constraints
      obtain ⟨hxPxR, hxRxS⟩ := distinctPoints endo (g i) (hholds i hi')
      have hcon := hholds i hi'
      rw [holds_iff] at hcon
      obtain ⟨hs1, hc2_1, hc3_1, hs3, hc2_3, hc3_3, _, hb1c, hb2c, hb3c, hb4c, _⟩ := hcon
      have hb1 := bool_of_mul hb1c
      have hb2 := bool_of_mul hb2c
      have hb3 := bool_of_mul hb3c
      have hb4 := bool_of_mul hb4c
      -- window 1: P → R
      have htne1 := block_tne W ha' h2 hodd hPi hxPxR hc2_1
      obtain ⟨_, hR, AR, BR, hReq, hARlo, hARhi, hBRlo, hBRhi⟩ :=
        one_window_produce W T φT off hTi hφTi hTeqi hφTeqi hb1 hb2 hPi A B hIeq
          hAlo2 hAlt hBlo2 hBlt (Ne.symm hxPxR) htne1 hs1 hc2_1 hc3_1
      have hARlo2 : (2 : ℤ) ≤ AR := by omega
      have hBRlo2 : (2 : ℤ) ≤ BR := by omega
      have hARlt : AR < 2 ^ 126 := by omega
      have hBRlt : BR < 2 ^ 126 := by omega
      -- window 2: R → S
      have htne2 := block_tne W ha' h2 hodd hR hxRxS hc2_3
      obtain ⟨_, hS, AS, BS, hSeq, hASlo, hAShi, hBSlo, hBShi⟩ :=
        one_window_produce W T φT off hTi hφTi hTeqi hφTeqi hb3 hb4 hR AR BR hReq
          hARlo2 hARlt hBRlo2 hBRlt (Ne.symm hxRxS) htne2 hs3 hc2_3 hc3_3
      exact ⟨hS, AS, BS, hSeq, by rw [hsucc]; omega, by rw [hsucc]; omega,
        by rw [hsucc]; omega, by rw [hsucc]; omega⟩
  -- read off each row's first-addition non-degeneracy from the invariant
  intro i hi
  obtain ⟨hPi', A, B, hPeq, hAlo, hAhi, hBlo, hBhi⟩ := inv i (le_of_lt hi)
  have h2i : 2 * i ≤ 120 := by omega
  have h4i : (4 : ℤ) ^ i ≤ 2 ^ 120 := by
    calc (4 : ℤ) ^ i = 2 ^ (2 * i) := by rw [pow_mul]; norm_num
      _ ≤ 2 ^ 120 := pow_le_pow_right₀ (by norm_num) h2i
  have h4ipos : (1 : ℤ) ≤ 4 ^ i := one_le_pow₀ (by norm_num)
  have hp126 : (6 : ℤ) * 2 ^ 120 < 2 ^ 126 := by norm_num
  have hAlo2 : (2 : ℤ) ≤ A := by omega
  have hBlo2 : (2 : ℤ) ≤ B := by omega
  have hAlt : A < 2 ^ 126 := by omega
  have hBlt : B < 2 ^ 126 := by omega
  obtain ⟨hxP, hyP⟩ := haccP i hi
  have hPi : W.Nonsingular (g i).xP (g i).yP := by rw [hxP, hyP]; exact hPi'
  have hIeq : Point.some _ _ hPi = A • T + B • φT := (some_congr W hPi hPi' hxP hyP).trans hPeq
  have hTi : W.Nonsingular (g i).xT (g i).yT := by
    obtain ⟨hx, hy⟩ := hbase i hi; rw [hx, hy]; exact hTns
  have hφTi : W.Nonsingular (endo * (g i).xT) (g i).yT := by
    obtain ⟨hx, hy⟩ := hbase i hi; rw [hx, hy]; exact hφTns
  have hTeqi : T = Point.some _ _ hTi :=
    hTeq.trans (some_congr W hTns hTi (hbase i hi).1.symm (hbase i hi).2.symm)
  have hφTeqi : φT = Point.some _ _ hφTi :=
    hφTeq.trans (some_congr W hφTns hφTi (by rw [(hbase i hi).1]) (hbase i hi).2.symm)
  obtain ⟨hxPxR, hxRxS⟩ := distinctPoints endo (g i) (hholds i hi)
  have hcon := hholds i hi
  rw [holds_iff] at hcon
  obtain ⟨hs1, hc2_1, hc3_1, hs3, hc2_3, hc3_3, _, hb1c, hb2c, hb3c, hb4c, _⟩ := hcon
  have hb1 := bool_of_mul hb1c
  have hb2 := bool_of_mul hb2c
  have hb3 := bool_of_mul hb3c
  have hb4 := bool_of_mul hb4c
  -- window 1 derives the first conjunct (and hands back `R`)
  have htne1 := block_tne W ha' h2 hodd hPi hxPxR hc2_1
  obtain ⟨hxne1, hR, AR, BR, hReq, hARlo, hARhi, hBRlo, hBRhi⟩ :=
    one_window_produce W T φT off hTi hφTi hTeqi hφTeqi hb1 hb2 hPi A B hIeq
      hAlo2 hAlt hBlo2 hBlt (Ne.symm hxPxR) htne1 hs1 hc2_1 hc3_1
  have hARlo2 : (2 : ℤ) ≤ AR := by omega
  have hBRlo2 : (2 : ℤ) ≤ BR := by omega
  have hARlt : AR < 2 ^ 126 := by omega
  have hBRlt : BR < 2 ^ 126 := by omega
  -- window 2 derives the second conjunct
  have htne2 := block_tne W ha' h2 hodd hR hxRxS hc2_3
  obtain ⟨hxne2, _⟩ :=
    one_window_produce W T φT off hTi hφTi hTeqi hφTeqi hb3 hb4 hR AR BR hReq
      hARlo2 hARlt hBRlo2 hBRlt (Ne.symm hxRxS) htne2 hs3 hc2_3 hc3_3
  exact ⟨hxne1, hxne2⟩

end Kimchi.Gate.EndoMul

/-! ## GLV scalar-mul chain: `endoMul` at the Pasta curves (folded from
    `Circuit/EndoMul`). -/


/-!
# The `EndoMul` circuit

Endomorphism-optimized (GLV) scalar multiplication, instantiated at the real Pasta curves (the
analog of `VarBaseMul`'s `scaleFast` entry points). A run of `Kimchi.Gate.EndoMul` rows over a base
point `T` computes `[s]·T`, where `s` is the scalar `EndoScalar` decodes from the row crumbs. The
generic capstone `Kimchi.Gate.EndoMul.endoMul` and its supporting development — the GLV point
fold, the `EndoMul ∘ EndoScalar` recoding kernel, and the non-degeneracy lemmas — live in
`Kimchi.Gate.EndoMul.Internal`.

This module exposes the deployed entry points at each concrete curve. The prover supplies only the
gate constraint `Holds` per row, the base nonsingularity (row 0 — genuinely external), the column
threading, and the initial accumulator `P₀ = 2(T + φT)`. Every intermediate accumulator's
nonsingularity is *derived* (`endoMul`), and the per-row first-addition non-degeneracy `hxne` is
*derived* — not assumed — from the GLV short-basis bound. The prime-order / `hodd` / short-shape
facts come from `Pasta`, and the eigenvalue `φT = [λ]·T` is discharged by the curve's CM
axiom (`{pallas,vesta}_eigen`).

## Main results

* `{pallas,vesta}_combo_off_targets` — the GLV off-targets fact (the `hxne` core): a bounded
  nonzero two-base accumulator `[a]·T + [b]·φT` avoids `±T`, `±φT`.
* `{pallas,vesta}_endoMul` — the capstone at each curve: a run of valid (`Holds`) rows computes the
  final accumulator `= [s]·T` with `s = EndoScalar.toField (crumbList g m) λ`.
-/

namespace Kimchi.Gate.EndoMul

open Kimchi.Gate.EndoMul Pasta WeierstrassCurve.Affine
open CompElliptic.Curves.Pasta CompElliptic.Fields.Pasta

/-! ## GLV non-degeneracy: the two-base accumulator avoids the targets

A two-base combination `[a]·T + [b]·φT` with coefficients inside the GLV bound (`< 2¹²⁶`,
comfortably above any `4^m` a `< 254`-bit challenge reaches) and nonzero is none of `±T`, `±φT`.
This is the consumer of `*_glv_no_short_relation` — the geometric core that, threaded through the
per-row accumulators (`accumulator_chain`), discharges the per-row `hxne`. -/

/-- `|x| < 2¹²⁶` keeps the offsets `x ∓ 1` inside the GLV bound `2¹²⁶`. -/
private lemma abs_offset_lt {x : ℤ} (hx : |x| < 2 ^ 126) :
    |x - 1| ≤ 2 ^ 126 ∧ |x + 1| ≤ 2 ^ 126 := by
  rw [abs_lt] at hx
  exact ⟨by rw [abs_le]; omega, by rw [abs_le]; omega⟩

/-- **GLV off-targets at Pallas.** A bounded nonzero two-base accumulator avoids `±T`, `±φT`. -/
theorem pallas_combo_off_targets {a b : ℤ} (ha : a ≠ 0) (hb : b ≠ 0)
    (hba : |a| < 2 ^ 126) (hbb : |b| < 2 ^ 126)
    {T φT : Pallas.curve.toAffine.Point} (hTne : T ≠ 0) (heig : φT = pallasLam • T) :
    a • T + b • φT ≠ T ∧ a • T + b • φT ≠ -T
      ∧ a • T + b • φT ≠ φT ∧ a • T + b • φT ≠ -φT := by
  obtain ⟨ha1, ha1'⟩ := abs_offset_lt hba
  obtain ⟨hb1, hb1'⟩ := abs_offset_lt hbb
  exact combo_off_targets Pallas.curve.toAffine hTne heig
    (pallas_glv_no_short_relation (Or.inr hb) ha1 hbb.le)
    (pallas_glv_no_short_relation (Or.inr hb) ha1' hbb.le)
    (pallas_glv_no_short_relation (Or.inl ha) hba.le hb1)
    (pallas_glv_no_short_relation (Or.inl ha) hba.le hb1')

/-- **GLV off-targets at Vesta** — the other half of the 2-cycle. -/
theorem vesta_combo_off_targets {a b : ℤ} (ha : a ≠ 0) (hb : b ≠ 0)
    (hba : |a| < 2 ^ 126) (hbb : |b| < 2 ^ 126)
    {T φT : Vesta.curve.toAffine.Point} (hTne : T ≠ 0) (heig : φT = vestaLam • T) :
    a • T + b • φT ≠ T ∧ a • T + b • φT ≠ -T
      ∧ a • T + b • φT ≠ φT ∧ a • T + b • φT ≠ -φT := by
  obtain ⟨ha1, ha1'⟩ := abs_offset_lt hba
  obtain ⟨hb1, hb1'⟩ := abs_offset_lt hbb
  exact combo_off_targets Vesta.curve.toAffine hTne heig
    (vesta_glv_no_short_relation (Or.inr hb) ha1 hbb.le)
    (vesta_glv_no_short_relation (Or.inr hb) ha1' hbb.le)
    (vesta_glv_no_short_relation (Or.inl ha) hba.le hb1)
    (vesta_glv_no_short_relation (Or.inl ha) hba.le hb1')

/-! ## `endoMul` at the curves

The deployed entry points: a run of valid (`Holds`) rows + base + threading + initial `P₀`
computes `[s]·T`. The per-row `hxne` is discharged internally from the GLV bound
(`accumulator_chain`); the intermediate-point nonsingularity is derived (`endoMul`). -/

/-- **EndoMul at Pallas.** A run of `m ≥ 1` `EndoMul` rows over Pallas, threaded from the init
    `P₀ = 2(T + φT)`, computes the final accumulator `= [s]·T` with
    `s = EndoScalar.toField (crumbList g m) λ`. The prover supplies only the gate constraint
    `Holds` per row, the base nonsingularity `hT`/`hφT` (row 0 — genuinely external), the column
    threading, the initial `P₀`, and the bit bound `4·m ≤ 244` (the deployed 128-bit challenge is
    `m = 32`, far under). Every intermediate accumulator's nonsingularity is *derived*
    (`endoMul`), the per-row `hxne` from the GLV short-basis bound (`accumulator_chain`,
    `off := pallas_combo_off_targets`), the eigenvalue from `pallas_eigen`, and the
    odd-prime-order conditions from `Pasta`. -/
theorem pallas_endoMul (m : ℕ) (hbits : 4 * m ≤ 244)
    (g : ℕ → Witness Fp)
    (hholds : ∀ i, i < m → Holds pallasEndo (g i))
    (T φT : Pallas.curve.toAffine.Point)
    (hTns : Pallas.curve.toAffine.Nonsingular (g 0).xT (g 0).yT) (hTeq : T = Point.some _ _ hTns)
    (hφTns : Pallas.curve.toAffine.Nonsingular (pallasEndo * (g 0).xT) (g 0).yT)
    (hφTeq : φT = Point.some _ _ hφTns)
    (hbase : ∀ i, i < m → (g i).xT = (g 0).xT ∧ (g i).yT = (g 0).yT)
    (hthread : ∀ i, i + 1 < m → (g (i + 1)).xP = (g i).xS ∧ (g (i + 1)).yP = (g i).yS)
    (hP0ns : Pallas.curve.toAffine.Nonsingular (g 0).xP (g 0).yP)
    (hP0 : Point.some _ _ hP0ns = (2 : ℤ) • T + (2 : ℤ) • φT) :
    ∃ (hfin : Pallas.curve.toAffine.Nonsingular (accX g m) (accY g m)) (s : ℤ),
      Point.some _ _ hfin = s • T
        ∧ (s : Fp)
            = Kimchi.Gate.EndoScalar.toField (crumbList g m) (pallasLam : Fp) := by
  have ha : Pallas.curve.toAffine.a₁ = 0 ∧ Pallas.curve.toAffine.a₂ = 0
      ∧ Pallas.curve.toAffine.a₃ = 0 := ⟨rfl, rfl, rfl⟩
  haveI : Fact (Pallas.curve.toAffine.a₁ = 0 ∧ Pallas.curve.toAffine.a₂ = 0
      ∧ Pallas.curve.toAffine.a₃ = 0) := ⟨ha⟩
  have h2 : (2 : Fp) ≠ 0 := by decide
  have h3 : (3 : Fp) ≠ 0 := by decide
  have hodd : Pallas.curve.toAffine.order ≠ 2 := by rw [pallas_card]; decide
  have hTne : T ≠ 0 := by rw [hTeq]; exact Point.some_ne_zero _
  have heig : φT = pallasLam • T := by rw [hφTeq, hTeq]; exact pallas_eigen hTns
  have off : ∀ a b : ℤ, a ≠ 0 → b ≠ 0 → |a| < 2 ^ 126 → |b| < 2 ^ 126 →
      a • T + b • φT ≠ T ∧ a • T + b • φT ≠ -T
        ∧ a • T + b • φT ≠ φT ∧ a • T + b • φT ≠ -φT :=
    fun a b ha' hb hba hbb => pallas_combo_off_targets ha' hb hba hbb hTne heig
  have hxne := accumulator_chain Pallas.curve.toAffine h2 hodd pallasEndo T φT off m hbits
    g hholds hTns hTeq hφTns hφTeq hbase hthread hP0ns hP0
  exact endoMul Pallas.curve.toAffine ha h2 h3 hodd pallasEndo m g hholds T φT
    hTns hTeq hφTns hφTeq hbase hthread hP0ns hP0 hxne pallasLam heig

/-- **EndoMul at Vesta** — the other half of the 2-cycle, identical modulo `vesta_*`. -/
theorem vesta_endoMul (m : ℕ) (hbits : 4 * m ≤ 244)
    (g : ℕ → Witness Fq)
    (hholds : ∀ i, i < m → Holds vestaEndo (g i))
    (T φT : Vesta.curve.toAffine.Point)
    (hTns : Vesta.curve.toAffine.Nonsingular (g 0).xT (g 0).yT) (hTeq : T = Point.some _ _ hTns)
    (hφTns : Vesta.curve.toAffine.Nonsingular (vestaEndo * (g 0).xT) (g 0).yT)
    (hφTeq : φT = Point.some _ _ hφTns)
    (hbase : ∀ i, i < m → (g i).xT = (g 0).xT ∧ (g i).yT = (g 0).yT)
    (hthread : ∀ i, i + 1 < m → (g (i + 1)).xP = (g i).xS ∧ (g (i + 1)).yP = (g i).yS)
    (hP0ns : Vesta.curve.toAffine.Nonsingular (g 0).xP (g 0).yP)
    (hP0 : Point.some _ _ hP0ns = (2 : ℤ) • T + (2 : ℤ) • φT) :
    ∃ (hfin : Vesta.curve.toAffine.Nonsingular (accX g m) (accY g m)) (s : ℤ),
      Point.some _ _ hfin = s • T
        ∧ (s : Fq)
            = Kimchi.Gate.EndoScalar.toField (crumbList g m) (vestaLam : Fq) := by
  have ha : Vesta.curve.toAffine.a₁ = 0 ∧ Vesta.curve.toAffine.a₂ = 0
      ∧ Vesta.curve.toAffine.a₃ = 0 := ⟨rfl, rfl, rfl⟩
  haveI : Fact (Vesta.curve.toAffine.a₁ = 0 ∧ Vesta.curve.toAffine.a₂ = 0
      ∧ Vesta.curve.toAffine.a₃ = 0) := ⟨ha⟩
  have h2 : (2 : Fq) ≠ 0 := by decide
  have h3 : (3 : Fq) ≠ 0 := by decide
  have hodd : Vesta.curve.toAffine.order ≠ 2 := by rw [vesta_card]; decide
  have hTne : T ≠ 0 := by rw [hTeq]; exact Point.some_ne_zero _
  have heig : φT = vestaLam • T := by rw [hφTeq, hTeq]; exact vesta_eigen hTns
  have off : ∀ a b : ℤ, a ≠ 0 → b ≠ 0 → |a| < 2 ^ 126 → |b| < 2 ^ 126 →
      a • T + b • φT ≠ T ∧ a • T + b • φT ≠ -T
        ∧ a • T + b • φT ≠ φT ∧ a • T + b • φT ≠ -φT :=
    fun a b ha' hb hba hbb => vesta_combo_off_targets ha' hb hba hbb hTne heig
  have hxne := accumulator_chain Vesta.curve.toAffine h2 hodd vestaEndo T φT off m hbits
    g hholds hTns hTeq hφTns hφTeq hbase hthread hP0ns hP0
  exact endoMul Vesta.curve.toAffine ha h2 h3 hodd vestaEndo m g hholds T φT
    hTns hTeq hφTns hφTeq hbase hthread hP0ns hP0 hxne vestaLam heig

end Kimchi.Gate.EndoMul
