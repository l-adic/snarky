import Kimchi.Gate.EndoMul
import Kimchi.Gate.EndoScalar
import Kimchi.Circuit.EndoScalar

/-!
# The `EndoMul` circuit: GLV scalar multiplication

Composition of `Kimchi.Gate.EndoMul` rows into the full endomorphism-optimized
scalar multiplication. Each row contributes `S = 4·P + c₁·T + c₂·φ(T)` (the gate's
`row_int`), so chaining `m` rows folds into

    P_m = 4^m · P₀ + k₁ · T + k₂ · φ(T)

with `k₁, k₂` the GLV scalar halves. This is VarBaseMul's `chain_scalarMul` over
TWO bases (`T` and `φ(T)`).

## Main results

* `chain_endo` — the abstract two-base recurrence fold.
* `endoMul` — `m` chained rows compute `∃ k₁ k₂, P_m = 4^m·P₀ + k₁·T + k₂·φ(T)`.
* `endoMul_scalar` — with the eigenvalue `φ(T) = [λ]·T` (a hypothesis), this
  collapses to a single scalar multiple `P_m = 4^m·P₀ + k·T`, `k = k₁ + k₂·λ` — the
  endo-scalar form `EndoScalar.toField` computes.
* `recoding_digit` — the `EndoMul ∘ EndoScalar` recoding correspondence (per
  window): `EndoScalar`'s `cPoly`/`dPoly` digits equal `EndoMul`'s GLV window digit.
* `sum_reindex` / `recode_fold` — that correspondence lifted to the fold (the
  row↔crumb reindexing + the coefficient identity).
* `endoMul_ab` — THE FULL RESULT: `m` chained rows give `P_m = 4^m·P₀ + k₁·T + k₂·φ(T)`
  with `(k₂:F) = ∑ 2^(2m-1-j)·aDigit g j` and `(k₁:F) = ∑ 2^(2m-1-j)·bDigit g j` —
  EndoMul's GLV coefficients ARE `EndoScalar`'s Algorithm-2 `a`, `b` accumulations
  over the shared crumbs. With `φ(T)=[λ]·T` this is `[b + a·λ]·T = [toField]·T`.
-/

namespace Kimchi.Circuit.EndoMul

open Kimchi.Gate.EndoMul WeierstrassCurve.Affine

variable {F : Type*} [Field F] [DecidableEq F]

/-- The two-base GLV fold: chaining `P_{i+1} = 4·P_i + c₁ᵢ·T + c₂ᵢ·φT` over `m` rows
    gives `P_m = 4^m·P₀ + (∑ 4^(m-1-i)·c₁ᵢ)·T + (∑ 4^(m-1-i)·c₂ᵢ)·φT`. Pure group
    algebra (cf. VarBaseMul's `chain_scalarMul`, here with a second base). -/
theorem chain_endo (W : WeierstrassCurve.Affine F)
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

/-- The per-row hypotheses `row_int` needs, bundled (over a shared base `T` whose
    coordinates are the row's `xT`/`yT`): the base/endo/accumulator/target
    nonsingularities, the two per-slope non-degeneracies per window, and the 12
    constraints `holds`. -/
structure EndoStep (W : WeierstrassCurve.Affine F) (endo : F) (g : Witness F) : Prop where
  hT : W.Nonsingular g.xT g.yT
  hφT : W.Nonsingular (endo * g.xT) g.yT
  hP : W.Nonsingular g.xP g.yP
  hR : W.Nonsingular g.xR g.yR
  hS : W.Nonsingular g.xS g.yS
  hQ1 : W.Nonsingular ((1 + (endo - 1) * g.b1) * g.xT) ((2 * g.b2 - 1) * g.yT)
  hQ2 : W.Nonsingular ((1 + (endo - 1) * g.b3) * g.xT) ((2 * g.b4 - 1) * g.yT)
  hxne1 : g.xP ≠ (1 + (endo - 1) * g.b1) * g.xT
  htne1 : 2 * g.xP - g.s1 ^ 2 + (1 + (endo - 1) * g.b1) * g.xT ≠ 0
  hxne2 : g.xR ≠ (1 + (endo - 1) * g.b3) * g.xT
  htne2 : 2 * g.xR - g.s3 ^ 2 + (1 + (endo - 1) * g.b3) * g.xT ≠ 0
  holds : Holds endo g

/-! ## Main theorem: GLV scalar multiplication -/

/-- `m` chained `EndoMul` rows compute GLV scalar multiplication. Given `m` valid
    rows over a shared base `T` and its endomorphism image `φ(T)`, whose accumulator
    points form a chain `P` (row `i`'s input is `P i`, output is `P (i+1)`), the
    final accumulator is `P m = 4^m·P₀ + k₁·T + k₂·φ(T)` for integers `k₁, k₂`. The
    proof reads each row's contribution `c₁ᵢ·T + c₂ᵢ·φ(T)` off `row_int` and folds
    them with `chain_endo`. -/
theorem endoMul (W : WeierstrassCurve.Affine F) (ha : IsShortShape W) (endo : F)
    (m : ℕ) (g : ℕ → Witness F) (gs : ∀ i, i < m → EndoStep W endo (g i))
    (P : ℕ → W.Point) (T φT : W.Point)
    (hT : ∀ i (hi : i < m), T = Point.some (gs i hi).hT)
    (hφT : ∀ i (hi : i < m), φT = Point.some (gs i hi).hφT)
    (hin : ∀ i (hi : i < m), P i = Point.some (gs i hi).hP)
    (hout : ∀ i (hi : i < m), P (i + 1) = Point.some (gs i hi).hS) :
    ∃ k1 k2 : ℤ, P m = (4 : ℤ) ^ m • P 0 + k1 • T + k2 • φT := by
  obtain ⟨c1, c2, hc⟩ : ∃ c1 c2 : ℕ → ℤ, ∀ i, i < m →
      P (i + 1) = (4 : ℤ) • P i + c1 i • T + c2 i • φT := by
    choose! c1 c2 hc using fun i (hi : i < m) =>
      row_int W ha endo (g i) (gs i hi).holds (gs i hi).hT (gs i hi).hφT (gs i hi).hP
        (gs i hi).hR (gs i hi).hS (gs i hi).hQ1 (gs i hi).hQ2 (gs i hi).hxne1
        (gs i hi).htne1 (gs i hi).hxne2 (gs i hi).htne2
    refine ⟨c1, c2, fun i hi => ?_⟩
    rw [hout i hi, hin i hi, hT i hi, hφT i hi]
    exact hc i hi
  exact ⟨_, _, chain_endo W m P T φT c1 c2 hc⟩

/-- The GLV eigenvalue collapse → genuine scalar multiplication. The curve
    endomorphism satisfies `φ(T) = [λ]·T` (its defining property — a hypothesis
    here, NOT provable in Mathlib for an abstract `WeierstrassCurve`; on the Pasta
    curves `λ` is the scalar-field `endo_scalar`). With it, the two-base GLV result
    becomes a single scalar multiple of the base:

        P_m = 4^m·P₀ + k·T,   k = k₁ + k₂·λ.

    The scalar `k = k₁ + k₂·λ` has exactly the endo-scalar form `a·λ + b` that
    `Kimchi.Circuit.EndoScalar.toField` computes from the challenge (with `a = k₂`,
    `b = k₁`) — so on a joint witness (the same challenge bits fed to both gates),
    EndoMul's point is `[toField challenge λ]·T`. `recoding_digit` proves the
    per-window heart of `k₂ = a`, `k₁ = b`: the two gates assign the same signed base
    to each 2-bit window (the full fold-level identity is then summing the matched
    digits with the inits aligned). -/
theorem endoMul_scalar (W : WeierstrassCurve.Affine F) (ha : IsShortShape W)
    (endo : F) (m : ℕ) (g : ℕ → Witness F) (gs : ∀ i, i < m → EndoStep W endo (g i))
    (P : ℕ → W.Point) (T φT : W.Point)
    (hT : ∀ i (hi : i < m), T = Point.some (gs i hi).hT)
    (hφT : ∀ i (hi : i < m), φT = Point.some (gs i hi).hφT)
    (hin : ∀ i (hi : i < m), P i = Point.some (gs i hi).hP)
    (hout : ∀ i (hi : i < m), P (i + 1) = Point.some (gs i hi).hS)
    (lam : ℤ) (heig : φT = lam • T) :
    ∃ k : ℤ, P m = (4 : ℤ) ^ m • P 0 + k • T := by
  obtain ⟨k1, k2, hk⟩ := endoMul W ha endo m g gs P T φT hT hφT hin hout
  exact ⟨k1 + k2 * lam, by rw [hk, heig]; module⟩

/-! ## The recoding correspondence with `EndoScalar`. -/

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
    `(k₂, k₁) = (a, b)`, i.e. `endoMul_scalar`'s scalar equals
    `EndoScalar.toField challenge λ`. -/
theorem recoding_digit (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) {b1 b2 : F}
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
theorem sum_reindex {R : Type*} [CommRing R] (m : ℕ) (g : ℕ → R) :
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

omit [DecidableEq F] in
/-- Fold-level recoding (coefficient level). Given the per-row digit equations
    `(c₂ᵢ : F) = 2·g(2i) + g(2i+1)` — `EndoMul`'s integer row contribution casts to
    `EndoScalar`'s two `cPoly`-digits, supplied by `row_int` + `recoding_digit` (so
    `g j` is crumb `j`'s `cPoly` digit) — the field cast of `EndoMul`'s GLV
    `φ(T)`-coefficient `∑ 4^(m-1-i)·c₂ᵢ` equals `EndoScalar`'s Algorithm-2 digit sum
    `∑_{j<2m} 2^(2m-1-j)·g(j)` that `a` accumulates. (The same holds for the
    `T`-coefficient `k₁` / `b` with the `dPoly` digits.) This is `sum_reindex` over
    `F` after pushing the cast through and substituting each row's digits. -/
theorem recode_fold (m : ℕ) (c2 : ℕ → ℤ) (g : ℕ → F)
    (hrow : ∀ i, ((c2 i : ℤ) : F) = 2 * g (2 * i) + g (2 * i + 1)) :
    (((∑ i ∈ Finset.range m, (4 : ℤ) ^ (m - 1 - i) * c2 i : ℤ)) : F)
      = ∑ j ∈ Finset.range (2 * m), (2 : F) ^ (2 * m - 1 - j) * g j := by
  rw [← sum_reindex m g]
  push_cast
  exact Finset.sum_congr rfl fun i _ => by rw [hrow i]

open Kimchi.Gate.EndoScalar (cPoly dPoly cPoly_table dPoly_table) in
/-- The per-row digit equations — the gate-side source of `recode_fold`'s
    hypothesis. A satisfying row's GLV contribution `S = 4·P + c₁·T + c₂·φ(T)` has its
    integers pinned to `EndoScalar`'s digits: `(c₁ : F) = 2·dPoly(crumb₁) + dPoly(crumb₂)`
    (the `T`/`b` digits) and `(c₂ : F) = 2·cPoly(crumb₁) + cPoly(crumb₂)` (the `φ(T)`/`a`
    digits), where `crumbⱼ = b₂ⱼ + 2·b₂ⱼ₋₁` is window `j`'s `EndoScalar` crumb. (`row_int`
    with the field digits read off the strengthened `selectQ` + `recoding_digit`.) -/
theorem row_digit (W : WeierstrassCurve.Affine F) (ha : IsShortShape W)
    (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (endo : F) (w : Witness F) (h : Holds endo w)
    (hT : W.Nonsingular w.xT w.yT) (hφT : W.Nonsingular (endo * w.xT) w.yT)
    (hP : W.Nonsingular w.xP w.yP) (hR : W.Nonsingular w.xR w.yR)
    (hS : W.Nonsingular w.xS w.yS)
    (hQ1 : W.Nonsingular ((1 + (endo - 1) * w.b1) * w.xT) ((2 * w.b2 - 1) * w.yT))
    (hQ2 : W.Nonsingular ((1 + (endo - 1) * w.b3) * w.xT) ((2 * w.b4 - 1) * w.yT))
    (hxne1 : w.xP ≠ (1 + (endo - 1) * w.b1) * w.xT)
    (htne1 : 2 * w.xP - w.s1 ^ 2 + (1 + (endo - 1) * w.b1) * w.xT ≠ 0)
    (hxne2 : w.xR ≠ (1 + (endo - 1) * w.b3) * w.xT)
    (htne2 : 2 * w.xR - w.s3 ^ 2 + (1 + (endo - 1) * w.b3) * w.xT ≠ 0) :
    ∃ c1 c2 : ℤ,
      Point.some hS = (4 : ℤ) • Point.some hP + c1 • Point.some hT + c2 • Point.some hφT
        ∧ (c1 : F) = 2 * dPoly (w.b2 + 2 * w.b1) + dPoly (w.b4 + 2 * w.b3)
        ∧ (c2 : F) = 2 * cPoly (w.b2 + 2 * w.b1) + cPoly (w.b4 + 2 * w.b3) := by
  obtain ⟨hReq, hSeq⟩ :=
    row_sound W ha endo w h hP hR hS hQ1 hQ2 hxne1 htne1 hxne2 htne2
  have hb := h
  simp only [Holds] at hb
  obtain ⟨_, _, _, _, _, _, _, hb1c, hb2c, hb3c, hb4c, _⟩ := hb
  have hb1 := bool_of_mul hb1c
  have hb2 := bool_of_mul hb2c
  have hb3 := bool_of_mul hb3c
  have hb4 := bool_of_mul hb4c
  obtain ⟨hcP1, hdP1⟩ := recoding_digit h2 h3 hb1 hb2
  obtain ⟨hcP2, hdP2⟩ := recoding_digit h2 h3 hb3 hb4
  rcases hb1 with hb1' | hb1' <;> rcases hb3 with hb3' | hb3'
  · -- b1 = 0 (Q₁ = ±T), b3 = 0 (Q₂ = ±T)
    have hxc1 : (1 + (endo - 1) * w.b1) * w.xT = w.xT := by rw [hb1']; ring
    obtain ⟨e1, he1, he1f⟩ := signed_target W ha hT (hxc1 ▸ hQ1) hb2
    have hQ1e : Point.some hQ1 = e1 • Point.some hT :=
      (some_congr W hQ1 (hxc1 ▸ hQ1) hxc1 rfl).trans he1
    have hxc2 : (1 + (endo - 1) * w.b3) * w.xT = w.xT := by rw [hb3']; ring
    obtain ⟨e2, he2, he2f⟩ := signed_target W ha hT (hxc2 ▸ hQ2) hb4
    have hQ2e : Point.some hQ2 = e2 • Point.some hT :=
      (some_congr W hQ2 (hxc2 ▸ hQ2) hxc2 rfl).trans he2
    refine ⟨2 * e1 + e2, 0, ?_, ?_, ?_⟩
    · rw [hSeq, hReq, hQ1e, hQ2e]; module
    · rw [hdP1, hdP2]; push_cast [he1f, he2f]; rw [hb1', hb3']; ring
    · rw [hcP1, hcP2]; push_cast [he1f, he2f]; rw [hb1', hb3']; ring
  · -- b1 = 0 (Q₁ = ±T), b3 = 1 (Q₂ = ±φT)
    have hxc1 : (1 + (endo - 1) * w.b1) * w.xT = w.xT := by rw [hb1']; ring
    obtain ⟨e1, he1, he1f⟩ := signed_target W ha hT (hxc1 ▸ hQ1) hb2
    have hQ1e : Point.some hQ1 = e1 • Point.some hT :=
      (some_congr W hQ1 (hxc1 ▸ hQ1) hxc1 rfl).trans he1
    have hxc2 : (1 + (endo - 1) * w.b3) * w.xT = endo * w.xT := by rw [hb3']; ring
    obtain ⟨e2, he2, he2f⟩ := signed_target W ha hφT (hxc2 ▸ hQ2) hb4
    have hQ2e : Point.some hQ2 = e2 • Point.some hφT :=
      (some_congr W hQ2 (hxc2 ▸ hQ2) hxc2 rfl).trans he2
    refine ⟨2 * e1, e2, ?_, ?_, ?_⟩
    · rw [hSeq, hReq, hQ1e, hQ2e]; module
    · rw [hdP1, hdP2]; push_cast [he1f, he2f]; rw [hb1', hb3']; ring
    · rw [hcP1, hcP2]; push_cast [he1f, he2f]; rw [hb1', hb3']; ring
  · -- b1 = 1 (Q₁ = ±φT), b3 = 0 (Q₂ = ±T)
    have hxc1 : (1 + (endo - 1) * w.b1) * w.xT = endo * w.xT := by rw [hb1']; ring
    obtain ⟨e1, he1, he1f⟩ := signed_target W ha hφT (hxc1 ▸ hQ1) hb2
    have hQ1e : Point.some hQ1 = e1 • Point.some hφT :=
      (some_congr W hQ1 (hxc1 ▸ hQ1) hxc1 rfl).trans he1
    have hxc2 : (1 + (endo - 1) * w.b3) * w.xT = w.xT := by rw [hb3']; ring
    obtain ⟨e2, he2, he2f⟩ := signed_target W ha hT (hxc2 ▸ hQ2) hb4
    have hQ2e : Point.some hQ2 = e2 • Point.some hT :=
      (some_congr W hQ2 (hxc2 ▸ hQ2) hxc2 rfl).trans he2
    refine ⟨e2, 2 * e1, ?_, ?_, ?_⟩
    · rw [hSeq, hReq, hQ1e, hQ2e]; module
    · rw [hdP1, hdP2]; push_cast [he1f, he2f]; rw [hb1', hb3']; ring
    · rw [hcP1, hcP2]; push_cast [he1f, he2f]; rw [hb1', hb3']; ring
  · -- b1 = 1 (Q₁ = ±φT), b3 = 1 (Q₂ = ±φT)
    have hxc1 : (1 + (endo - 1) * w.b1) * w.xT = endo * w.xT := by rw [hb1']; ring
    obtain ⟨e1, he1, he1f⟩ := signed_target W ha hφT (hxc1 ▸ hQ1) hb2
    have hQ1e : Point.some hQ1 = e1 • Point.some hφT :=
      (some_congr W hQ1 (hxc1 ▸ hQ1) hxc1 rfl).trans he1
    have hxc2 : (1 + (endo - 1) * w.b3) * w.xT = endo * w.xT := by rw [hb3']; ring
    obtain ⟨e2, he2, he2f⟩ := signed_target W ha hφT (hxc2 ▸ hQ2) hb4
    have hQ2e : Point.some hQ2 = e2 • Point.some hφT :=
      (some_congr W hQ2 (hxc2 ▸ hQ2) hxc2 rfl).trans he2
    refine ⟨0, 2 * e1 + e2, ?_, ?_, ?_⟩
    · rw [hSeq, hReq, hQ1e, hQ2e]; module
    · rw [hdP1, hdP2]; push_cast [he1f, he2f]; rw [hb1', hb3']; ring
    · rw [hcP1, hcP2]; push_cast [he1f, he2f]; rw [hb1', hb3']; ring

open Kimchi.Gate.EndoScalar (cPoly) in
/-- `EndoScalar`'s `a`-digit (`cPoly`, the `φ(T)`/λ component) of crumb `j` built from
    the rows `g`: crumb `2i` is row `i`'s first window `(b₂,b₁)`, crumb `2i+1` its
    second `(b₄,b₃)`. -/
def aDigit (g : ℕ → Witness F) (j : ℕ) : F :=
  if j % 2 = 0 then cPoly ((g (j / 2)).b2 + 2 * (g (j / 2)).b1)
  else cPoly ((g (j / 2)).b4 + 2 * (g (j / 2)).b3)

open Kimchi.Gate.EndoScalar (dPoly) in
/-- `EndoScalar`'s `b`-digit (`dPoly`, the `T`/1 component) of crumb `j`. -/
def bDigit (g : ℕ → Witness F) (j : ℕ) : F :=
  if j % 2 = 0 then dPoly ((g (j / 2)).b2 + 2 * (g (j / 2)).b1)
  else dPoly ((g (j / 2)).b4 + 2 * (g (j / 2)).b3)

open Kimchi.Gate.EndoScalar (cPoly dPoly) in
/-- THE FULL RECODING RESULT: EndoMul's GLV coefficients are EndoScalar's
    `a`, `b`. `m` chained rows compute `P_m = 4^m·P₀ + k₁·T + k₂·φ(T)` where the field
    casts of `k₂` (the `φ(T)` coefficient) and `k₁` (the `T` coefficient) are exactly
    `EndoScalar`'s Algorithm-2 accumulations over the `2m` crumbs:

        (k₂ : F) = ∑_{j<2m} 2^(2m-1-j)·aDigit g j    (= `a`, the λ component)
        (k₁ : F) = ∑_{j<2m} 2^(2m-1-j)·bDigit g j    (= `b`, the 1 component)

    Folds `row_digit` (per-row digits) through `chain_endo` and `recode_fold` (the
    `aDigit (2i) = cPoly(window-1 crumb)`, `aDigit (2i+1) = cPoly(window-2 crumb)`
    pairing reindexes the rows to crumbs). With `φ(T) = [λ]·T` and `P₀ = 2(T+φ(T))`
    this gives `P_m = [b + a·λ]·T = [EndoScalar.toField]·T`. -/
theorem endoMul_ab (W : WeierstrassCurve.Affine F) (ha : IsShortShape W)
    (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (endo : F)
    (m : ℕ) (g : ℕ → Witness F) (gs : ∀ i, i < m → EndoStep W endo (g i))
    (P : ℕ → W.Point) (T φT : W.Point)
    (hT : ∀ i (hi : i < m), T = Point.some (gs i hi).hT)
    (hφT : ∀ i (hi : i < m), φT = Point.some (gs i hi).hφT)
    (hin : ∀ i (hi : i < m), P i = Point.some (gs i hi).hP)
    (hout : ∀ i (hi : i < m), P (i + 1) = Point.some (gs i hi).hS) :
    ∃ k1 k2 : ℤ, P m = (4 : ℤ) ^ m • P 0 + k1 • T + k2 • φT
      ∧ (k2 : F) = ∑ j ∈ Finset.range (2 * m), (2 : F) ^ (2 * m - 1 - j) * aDigit g j
      ∧ (k1 : F) = ∑ j ∈ Finset.range (2 * m), (2 : F) ^ (2 * m - 1 - j) * bDigit g j := by
  choose! c1 c2 hc using fun i (hi : i < m) =>
    row_digit W ha h2 h3 endo (g i) (gs i hi).holds (gs i hi).hT (gs i hi).hφT
      (gs i hi).hP (gs i hi).hR (gs i hi).hS (gs i hi).hQ1 (gs i hi).hQ2
      (gs i hi).hxne1 (gs i hi).htne1 (gs i hi).hxne2 (gs i hi).htne2
  have hstep : ∀ i, i < m → P (i + 1) = (4 : ℤ) • P i + c1 i • T + c2 i • φT := by
    intro i hi
    rw [hout i hi, hin i hi, hT i hi, hφT i hi]
    exact (hc i hi).1
  refine ⟨∑ i ∈ Finset.range m, (4 : ℤ) ^ (m - 1 - i) * c1 i,
          ∑ i ∈ Finset.range m, (4 : ℤ) ^ (m - 1 - i) * c2 i, ?_, ?_, ?_⟩
  · exact chain_endo W m P T φT c1 c2 hstep
  · rw [← sum_reindex m (aDigit g)]
    push_cast
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' : i < m := Finset.mem_range.mp hi
    have e1 : (2 * i) % 2 = 0 := by omega
    have e2 : (2 * i) / 2 = i := by omega
    have e3 : (2 * i + 1) % 2 = 1 := by omega
    have e4 : (2 * i + 1) / 2 = i := by omega
    have haE : aDigit g (2 * i) = cPoly ((g i).b2 + 2 * (g i).b1) := by
      simp [aDigit, e1, e2]
    have haO : aDigit g (2 * i + 1) = cPoly ((g i).b4 + 2 * (g i).b3) := by
      simp [aDigit, e3, e4]
    rw [haE, haO, ← (hc i hi').2.2]
  · rw [← sum_reindex m (bDigit g)]
    push_cast
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' : i < m := Finset.mem_range.mp hi
    have e1 : (2 * i) % 2 = 0 := by omega
    have e2 : (2 * i) / 2 = i := by omega
    have e3 : (2 * i + 1) % 2 = 1 := by omega
    have e4 : (2 * i + 1) / 2 = i := by omega
    have hbE : bDigit g (2 * i) = dPoly ((g i).b2 + 2 * (g i).b1) := by
      simp [bDigit, e1, e2]
    have hbO : bDigit g (2 * i + 1) = dPoly ((g i).b4 + 2 * (g i).b3) := by
      simp [bDigit, e3, e4]
    rw [hbE, hbO, ← (hc i hi').2.1]

/-! ## Top level: EndoMul computes `[EndoScalar.toField]·T`. -/

/-- The `2m`-crumb list the rows feed to `EndoScalar`: row `i` contributes its two
    windows `[b₂+2·b₁, b₄+2·b₃]` in order, so `crumbList[2i] = aDigit/bDigit`'s crumb
    `2i` and `crumbList[2i+1]` crumb `2i+1`. -/
def crumbList (g : ℕ → Witness F) (m : ℕ) : List F :=
  (List.range m).flatMap fun i => [(g i).b2 + 2 * (g i).b1, (g i).b4 + 2 * (g i).b3]

omit [DecidableEq F] in
/-- Each additional row appends its two window crumbs to the crumb list. -/
theorem crumbList_succ (g : ℕ → Witness F) (m : ℕ) :
    crumbList g (m + 1)
      = crumbList g m ++ [(g m).b2 + 2 * (g m).b1, (g m).b4 + 2 * (g m).b3] := by
  simp [crumbList, List.range_succ, List.flatMap_append]

omit [DecidableEq F] in
/-- The init bridge: `EndoScalar`'s `decomposeA`/`decomposeB` over the crumb
    list (folded from the `a = b = 2` init) is its `2·4^m` carry plus the
    Algorithm-2 digit sums — exactly `endoMul_ab`'s `(k₂:F)` / `(k₁:F)`. By induction
    on `m` (each row appends 2 crumbs; `List.foldl_append`). -/
theorem decompose_crumbList (g : ℕ → Witness F) (m : ℕ) :
    Kimchi.Circuit.EndoScalar.decomposeA (crumbList g m)
        = 2 * (4 : F) ^ m + ∑ j ∈ Finset.range (2 * m), (2 : F) ^ (2 * m - 1 - j) * aDigit g j
      ∧ Kimchi.Circuit.EndoScalar.decomposeB (crumbList g m)
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

/-- THE TOP-LEVEL STATEMENT: EndoMul computes scalar multiplication by exactly
    the scalar EndoScalar decodes. At the real init (`P₀ = 2·(T + φ(T))`) and with the
    eigenvalue `φ(T) = [λ]·T`, the `m` rows produce `P_m = s·T` where `s` is the
    `EndoScalar.toField` of the shared challenge crumbs:

        (s : F) = decomposeA(crumbs)·λ + decomposeB(crumbs) = toField crumbs λ.

    This closes `EndoMul ∘ EndoScalar`: EndoScalar decodes the scalar into the
    eigenvalue basis `a·λ + b`, and EndoMul multiplies the base by exactly that
    scalar. Assembles `endoMul_ab` (k₂,k₁ = the a,b digit-sums) with
    `decompose_crumbList` (the `a=b=2` ↔ `4^m·P₀` init alignment), the init `hP₀`,
    and the eigenvalue `heig`. -/
theorem endoMul_toField (W : WeierstrassCurve.Affine F) (ha : IsShortShape W)
    (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (endo : F)
    (m : ℕ) (g : ℕ → Witness F) (gs : ∀ i, i < m → EndoStep W endo (g i))
    (P : ℕ → W.Point) (T φT : W.Point)
    (hT : ∀ i (hi : i < m), T = Point.some (gs i hi).hT)
    (hφT : ∀ i (hi : i < m), φT = Point.some (gs i hi).hφT)
    (hin : ∀ i (hi : i < m), P i = Point.some (gs i hi).hP)
    (hout : ∀ i (hi : i < m), P (i + 1) = Point.some (gs i hi).hS)
    (hP0 : P 0 = (2 : ℤ) • T + (2 : ℤ) • φT) (lam : ℤ) (heig : φT = lam • T) :
    ∃ s : ℤ, P m = s • T
      ∧ (s : F) = Kimchi.Circuit.EndoScalar.toField (crumbList g m) (lam : F) := by
  obtain ⟨ k1, k2, hPm, hk2, hk1 ⟩ := endoMul_ab W ha h2 h3 endo m g gs P T φT hT hφT hin hout;
  refine' ⟨ 2 * 4 ^ m + k1 + ( 2 * 4 ^ m + k2 ) * lam, _, _ ⟩;
  · rw [ hPm, hP0, heig ];
    module;
  · simp +decide [ EndoScalar.toField, hk1, hk2 ];
    rw [ decompose_crumbList g m |>.1, decompose_crumbList g m |>.2 ] ; ring

end Kimchi.Circuit.EndoMul
