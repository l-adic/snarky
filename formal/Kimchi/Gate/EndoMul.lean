import Kimchi.Gate.VarBaseMul

/-!
# The kimchi `EndoMul` gate

The endomorphism-optimized variable-base scalar-multiplication gate, transcribed
from proof-systems `kimchi/src/circuits/polynomials/endosclmul.rs` (the
`EC_endoscale` point constraint) and the PureScript `Snarky.Circuit.Kimchi.EndoMul`.

It is VarBaseMul's `(P + Q) + P` double-and-add, but each 2-bit window selects `Q`
from `{T, −T, φ(T), −φ(T)}` — the GLV optimization — using the curve endomorphism

      φ(x, y) = (endo · x, y)      (endo a primitive cube root of unity, φ(T) = [λ]T)

so that `[k]T = [k₁]T + [k₂]·φ(T)` with `k₁, k₂` half-width. Each row processes 4
bits = two windows `P → R → S`:

* `Q₁ = (xq₁, yq₁)`, `xq₁ = (1 + (endo−1)·b₁)·xT` (= `xT` or `endo·xT`),
  `yq₁ = (2·b₂ − 1)·yT` (sign) — so `b₁` picks `T` vs `φ(T)`, `b₂` the sign.
* `Q₂ = (xq₂, yq₂)` likewise from `(b₃, b₄)`.

The register threads `n' = 16·n + 8·b₁ + 4·b₂ + 2·b₃ + b₄`, and the accumulator is
initialized to `2·(T + φ(T))` to dodge the point at infinity.

We model the UPSTREAM-FIXED gate: 12 constraints, including the distinct-point check
`(xP − xR)·(xR − xS)·inv = 1` (o1-labs/proof-systems@64129ce4) which pins the
accumulator away from `−P` / `−R`. The pre-fix gate without it is underconstrained
(it admits the spurious `R = −P`) — see `block_sound` / `distinctPoints`.

The EC core (`(P + Q) + P` per window) reuses `Kimchi.Gate.VarBaseMul`'s
`secant_add` (general affine addition) and `signed_target` (the `±` selection); the
new ingredients are the endomorphism base-choice and the GLV `[k₁]T + [k₂]φ(T)`
accumulation.

## Main results

* `selectQ` — GLV target selection: a window's `Q` is `±T` (when `b₁ = 0`) or
  `±φ(T)` (when `b₁ = 1`), via `Kimchi.signed_target` with base `T` or `φ(T)`.
* `block_sound` — one window's `(P + Q) + P` double-and-add, via `Kimchi.secant_add`
  twice (general in `Q`; carries the `xR ≠ xP` non-degeneracy the modeled gate
  revision needs — see its docstring + the upstream fix it references).

## Supporting development

The constraint model `Witness` / `Holds`, the booleanity helper `bool_of_mul`, the
distinct-point lemma `distinctPoints` (which discharges `block_sound`'s
non-degeneracy at the row level), and the `some_congr` point congruence. Still to
come: threading these through `Holds` per row, the GLV `[k₁]T + [k₂]·φ(T)`
accumulation, and the `φ(T) = [λ]T` eigenvalue collapse (a hypothesis/axiom)
composing with EndoScalar's `a·λ + b`.
-/

namespace Kimchi.Gate.EndoMul

open WeierstrassCurve.Affine

variable {F : Type*} [Field F] [DecidableEq F]

/-- One `EndoMul` row: base `T`, input accumulator `P`, the scalar register
    `n → n'`, the four bits, the two window slopes `s1`/`s3`, and the intermediate
    `R` and output `S` accumulator points. -/
structure Witness (F : Type*) where
  xT : F
  yT : F
  xP : F
  yP : F
  n : F
  nPrime : F
  b1 : F
  b2 : F
  b3 : F
  b4 : F
  s1 : F
  xR : F
  yR : F
  s3 : F
  xS : F
  yS : F
  inv : F

/-- The 12 gate constraints: two `(P+Q)+P` blocks (3 each, with `Q` the endo-and-
    sign-selected target), the distinct-point check, 4 booleanity checks, and the
    scalar-register decomposition. `endo` is the base-field endomorphism coefficient.
    (The distinct-point check is the upstream fix o1-labs/proof-systems@64129ce4 — see
    `block_sound` / `distinctPoints`; the pre-fix gate without it is underconstrained.) -/
def Holds (endo : F) (w : Witness F) : Prop :=
  let xq1 := (1 + (endo - 1) * w.b1) * w.xT
  let yq1 := (2 * w.b2 - 1) * w.yT
  let xq2 := (1 + (endo - 1) * w.b3) * w.xT
  let yq2 := (2 * w.b4 - 1) * w.yT
  -- first window `P → R`, slope `s1`
  ((xq1 - w.xP) * w.s1 = yq1 - w.yP)
    ∧ ((2 * w.xP - w.s1 ^ 2 + xq1) * ((w.xP - w.xR) * w.s1 + w.yR + w.yP)
        = (w.xP - w.xR) * (2 * w.yP))
    ∧ ((w.yR + w.yP) ^ 2 = (w.xP - w.xR) ^ 2 * (w.s1 ^ 2 - xq1 + w.xR))
    -- second window `R → S`, slope `s3`
    ∧ ((xq2 - w.xR) * w.s3 = yq2 - w.yR)
    ∧ ((2 * w.xR - w.s3 ^ 2 + xq2) * ((w.xR - w.xS) * w.s3 + w.yS + w.yR)
        = (w.xR - w.xS) * (2 * w.yR))
    ∧ ((w.yS + w.yR) ^ 2 = (w.xR - w.xS) ^ 2 * (w.s3 ^ 2 - xq2 + w.xS))
    -- distinct-point check (upstream fix): `inv` witnesses `(xP−xR)·(xR−xS)` is a
    -- unit, forcing `xP ≠ xR` and `xR ≠ xS` (no degenerate `R = −P` / `S = −R`)
    ∧ ((w.xP - w.xR) * (w.xR - w.xS) * w.inv = 1)
    -- booleanity of the four bits
    ∧ (w.b1 * (w.b1 - 1) = 0)
    ∧ (w.b2 * (w.b2 - 1) = 0)
    ∧ (w.b3 * (w.b3 - 1) = 0)
    ∧ (w.b4 * (w.b4 - 1) = 0)
    -- scalar register
    ∧ (w.nPrime = 16 * w.n + 8 * w.b1 + 4 * w.b2 + 2 * w.b3 + w.b4)

omit [DecidableEq F] in
/-- Booleanity: the constraint `b·(b−1) = 0` forces `b ∈ {0,1}` (field = domain). -/
theorem bool_of_mul {b : F} (h : b * (b - 1) = 0) : b = 0 ∨ b = 1 := by
  rcases mul_eq_zero.mp h with h | h
  · exact Or.inl h
  · exact Or.inr (by linear_combination h)

omit [DecidableEq F] in
/-- The distinct-point check discharges the non-degeneracy both windows need:
    `(xP − xR)·(xR − xS)·inv = 1` makes both factors units, so `xP ≠ xR` (first
    window, `R ≠ −P`) and `xR ≠ xS` (second window, `S ≠ −R`). -/
theorem distinctPoints (endo : F) (w : Witness F) (h : Holds endo w) :
    w.xP ≠ w.xR ∧ w.xR ≠ w.xS := by
  simp only [Holds] at h
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
    Point.some h = Point.some h' := by
  subst hx; subst hy; rfl

/-- GLV target selection. A window's target
    `Q = ((1 + (endo−1)·b₁)·xT, (2·b₂−1)·yT)` with `b₁, b₂ ∈ {0,1}` is `±T` (when
    `b₁ = 0`, so `xq = xT`) or `±φ(T)` (when `b₁ = 1`, so `xq = endo·xT`), where
    `φ(T) = (endo·xT, yT)`. Reuses `Kimchi.signed_target` with base `T` or `φ(T)`. -/
theorem selectQ (W : WeierstrassCurve.Affine F) (ha : IsShortShape W)
    {endo b1 b2 xT yT : F}
    (hT : W.Nonsingular xT yT) (hφT : W.Nonsingular (endo * xT) yT)
    (hQ : W.Nonsingular ((1 + (endo - 1) * b1) * xT) ((2 * b2 - 1) * yT))
    (hb1 : b1 = 0 ∨ b1 = 1) (hb2 : b2 = 0 ∨ b2 = 1) :
    (∃ e : ℤ, Point.some hQ = e • Point.some hT)
      ∨ (∃ e : ℤ, Point.some hQ = e • Point.some hφT) := by
  rcases hb1 with rfl | rfl
  · -- `b₁ = 0`: the `x`-coordinate `(1 + (endo-1)*0)*xT` collapses to `xT`,
    -- so `Q = ±T` via `signed_target` with base `T`.
    left
    have hx : (1 + (endo - 1) * 0) * xT = xT := by ring
    obtain ⟨e, he, _⟩ := signed_target W ha hT (hx ▸ hQ) hb2
    exact ⟨e, (some_congr W hQ (hx ▸ hQ) hx rfl).trans he⟩
  · -- `b₁ = 1`: the `x`-coordinate `(1 + (endo-1)*1)*xT` collapses to `endo*xT`,
    -- so `Q = ±φ(T)` via `signed_target` with base `φ(T)`.
    right
    have hx : (1 + (endo - 1) * 1) * xT = endo * xT := by ring
    obtain ⟨e, he, _⟩ := signed_target W ha hφT (hx ▸ hQ) hb2
    exact ⟨e, (some_congr W hQ (hx ▸ hQ) hx rfl).trans he⟩

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
theorem block_sound (W : WeierstrassCurve.Affine F) (ha : IsShortShape W)
    {xq yq xP yP s xR yR : F}
    (hP : W.Nonsingular xP yP) (hQ : W.Nonsingular xq yq) (hR : W.Nonsingular xR yR)
    (hxne : xP ≠ xq) (htne : 2 * xP - s ^ 2 + xq ≠ 0) (hxRne : xR ≠ xP)
    (hs : (xq - xP) * s = yq - yP)
    (hc2 : (2 * xP - s ^ 2 + xq) * ((xP - xR) * s + yR + yP) = (xP - xR) * (2 * yP))
    (hc3 : (yR + yP) ^ 2 = (xP - xR) ^ 2 * (s ^ 2 - xq + xR)) :
    Point.some hR = (Point.some hP + Point.some hQ) + Point.some hP := by
  obtain ⟨ha1, ha2, ha3, ha4⟩ := ha
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
    secant_add W ⟨ha1, ha2, ha3, ha4⟩ hP hQ hxne hl1 hMx hMy
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
    secant_add W ⟨ha1, ha2, ha3, ha4⟩ hM hP hMxne hs2 hxR_eq hyR_eq
  rw [hAdd1, hAdd2]

/-- Per-row soundness: a satisfying row's two windows compute the double-and-add
    chain `R = (P + Q₁) + P` then `S = (R + Q₂) + R`, where `Q₁, Q₂` are the gate's
    endo-and-sign-selected targets. The distinct-point constraint (via
    `distinctPoints`) supplies each window's `xR ≠ xP` / `xS ≠ xR`; the per-slope
    non-degeneracies `xP ≠ xq` and `2·xP − s² + xq ≠ 0` are the remaining honest-
    witness conditions (as in VarBaseMul). Identify `Q₁, Q₂` as `±T` / `±φ(T)` with
    `selectQ` to feed the GLV accumulation. -/
theorem row_sound (W : WeierstrassCurve.Affine F) (ha : IsShortShape W)
    (endo : F) (w : Witness F) (h : Holds endo w)
    (hP : W.Nonsingular w.xP w.yP) (hR : W.Nonsingular w.xR w.yR)
    (hS : W.Nonsingular w.xS w.yS)
    (hQ1 : W.Nonsingular ((1 + (endo - 1) * w.b1) * w.xT) ((2 * w.b2 - 1) * w.yT))
    (hQ2 : W.Nonsingular ((1 + (endo - 1) * w.b3) * w.xT) ((2 * w.b4 - 1) * w.yT))
    (hxne1 : w.xP ≠ (1 + (endo - 1) * w.b1) * w.xT)
    (htne1 : 2 * w.xP - w.s1 ^ 2 + (1 + (endo - 1) * w.b1) * w.xT ≠ 0)
    (hxne2 : w.xR ≠ (1 + (endo - 1) * w.b3) * w.xT)
    (htne2 : 2 * w.xR - w.s3 ^ 2 + (1 + (endo - 1) * w.b3) * w.xT ≠ 0) :
    Point.some hR = (Point.some hP + Point.some hQ1) + Point.some hP
      ∧ Point.some hS = (Point.some hR + Point.some hQ2) + Point.some hR := by
  obtain ⟨hxPxR, hxRxS⟩ := distinctPoints endo w h
  simp only [Holds] at h
  obtain ⟨hs1, hc2_1, hc3_1, hs2, hc2_2, hc3_2, _, _, _, _, _, _⟩ := h
  exact ⟨block_sound W ha hP hQ1 hR hxne1 htne1 (Ne.symm hxPxR) hs1 hc2_1 hc3_1,
         block_sound W ha hR hQ2 hS hxne2 htne2 (Ne.symm hxRxS) hs2 hc2_2 hc3_2⟩

end Kimchi.Gate.EndoMul
