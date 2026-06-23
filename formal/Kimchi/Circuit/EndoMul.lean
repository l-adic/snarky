import Kimchi.Gate.EndoMul
import Kimchi.Gate.EndoScalar

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
* `recoding_digit` — the `EndoMul ∘ EndoScalar` recoding correspondence: per 2-bit
  window, `EndoScalar`'s `cPoly`/`dPoly` digits equal `EndoMul`'s GLV window digit,
  so the two gates assign the same signed base to each window.
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

end Kimchi.Circuit.EndoMul
