import Kimchi.Gate.EndoMul
import Kimchi.Gate.EndoScalar
import Kimchi.Circuit.EndoScalar
import Kimchi.Circuit.EndoMul.Recoding
import Kimchi.Circuit.EndoMul.NonDegen

/-!
# The `EndoMul` circuit: GLV scalar multiplication

Composition of `Kimchi.Gate.EndoMul` rows into the full endomorphism-optimized
scalar multiplication. Each row contributes `S = 4·P + c₁·T + c₂·φ(T)` (the gate's
`sound`), so chaining `m` rows folds into

    P_m = 4^m · P₀ + k₁ · T + k₂ · φ(T)

with `k₁, k₂` the GLV scalar halves; on the Pasta endomorphism `φ(T) = [λ]·T` this
collapses to a single scalar multiple of `T`. This is VarBaseMul's `chain_scalarMul`
over TWO bases (`T` and `φ(T)`).

## Main results

* `endoMul_ab` — the recoding result: the GLV coefficients `(k₂, k₁)` cast to `F` are
  exactly `EndoScalar`'s Algorithm-2 `a`, `b` digit-sums over the shared crumbs.
* `endoMul` — THE CAPSTONE (and the only result the deployed `endo` circuit
  needs): at the real init `P₀ = 2(T+φT)` and the eigenvalue `φ(T) = [λ]·T`, the `m`
  rows give `P_m = [s]·T` with `(s:F) = EndoScalar.toField (crumbList g m) λ` — EndoMul
  multiplies the base by exactly the scalar EndoScalar decodes.

`chain_endo` (the two-base group fold) and `EndoStep` (the per-row hypothesis bundle) are
the supporting structures; the `EndoMul ∘ EndoScalar` recoding kernel (`recoding_digit`,
`sum_reindex`, `row_digit`, `aDigit`/`bDigit`, `crumbList`/`decompose_crumbList`) lives in
`Kimchi.Circuit.EndoMul.Recoding`.
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

/-- The per-row hypotheses `sound` needs, bundled (over a shared base `T` whose
    coordinates are the row's `xT`/`yT`): the base/endo/accumulator nonsingularities, the two
    per-window *first*-addition non-degeneracies `hxne`, and the 12 constraints `holds`. The
    window targets' nonsingularity and the *second*-addition non-degeneracies are *derived*
    (`Gate.EndoMul.targets_nonsingular` / `htne_of_holds`), not assumed — leaving only `hxne`
    (the accumulator avoiding `±T`/`±φT`) for the Pasta-layer global argument. -/
structure EndoStep (W : WeierstrassCurve.Affine F) (endo : F) (g : Witness F) : Prop where
  hT : W.Nonsingular g.xT g.yT
  hφT : W.Nonsingular (endo * g.xT) g.yT
  hP : W.Nonsingular g.xP g.yP
  hR : W.Nonsingular g.xR g.yR
  hS : W.Nonsingular g.xS g.yS
  hxne1 : g.xP ≠ (1 + (endo - 1) * g.b1) * g.xT
  hxne2 : g.xR ≠ (1 + (endo - 1) * g.b3) * g.xT
  holds : Holds endo g

/-! ## The recoding result: GLV coefficients are `EndoScalar`'s `a`, `b`. -/

open Kimchi.Gate.EndoScalar (cPoly dPoly) in
/-- THE FULL RECODING RESULT: EndoMul's GLV coefficients are EndoScalar's
    `a`, `b`. `m` chained rows compute `P_m = 4^m·P₀ + k₁·T + k₂·φ(T)` where the field
    casts of `k₂` (the `φ(T)` coefficient) and `k₁` (the `T` coefficient) are exactly
    `EndoScalar`'s Algorithm-2 accumulations over the `2m` crumbs:

        (k₂ : F) = ∑_{j<2m} 2^(2m-1-j)·aDigit g j    (= `a`, the λ component)
        (k₁ : F) = ∑_{j<2m} 2^(2m-1-j)·bDigit g j    (= `b`, the 1 component)

    Folds `row_digit` (per-row digits) through `chain_endo` and `sum_reindex` (the
    `aDigit (2i) = cPoly(window-1 crumb)`, `aDigit (2i+1) = cPoly(window-2 crumb)`
    pairing reindexes the rows to crumbs). With `φ(T) = [λ]·T` and `P₀ = 2(T+φ(T))`
    this gives `P_m = [b + a·λ]·T = [EndoScalar.toField]·T`. -/
theorem endoMul_ab (W : WeierstrassCurve.Affine F) [Fact (Nat.Prime W.order)]
    (ha : (W.a₁ = 0 ∧ W.a₂ = 0 ∧ W.a₃ = 0))
    (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (hodd : W.order ≠ 2) (endo : F)
    (m : ℕ) (g : ℕ → Witness F) (gs : ∀ i, i < m → EndoStep W endo (g i))
    (P : ℕ → W.Point) (T φT : W.Point)
    (hT : ∀ i (hi : i < m), T = Point.some _ _ (gs i hi).hT)
    (hφT : ∀ i (hi : i < m), φT = Point.some _ _ (gs i hi).hφT)
    (hin : ∀ i (hi : i < m), P i = Point.some _ _ (gs i hi).hP)
    (hout : ∀ i (hi : i < m), P (i + 1) = Point.some _ _ (gs i hi).hS) :
    ∃ k1 k2 : ℤ, P m = (4 : ℤ) ^ m • P 0 + k1 • T + k2 • φT
      ∧ (k2 : F) = ∑ j ∈ Finset.range (2 * m), (2 : F) ^ (2 * m - 1 - j) * aDigit g j
      ∧ (k1 : F) = ∑ j ∈ Finset.range (2 * m), (2 : F) ^ (2 * m - 1 - j) * bDigit g j := by
  choose! c1 c2 hc using fun i (hi : i < m) =>
    row_digit W ha h2 h3 endo (g i) (gs i hi).holds (gs i hi).hT (gs i hi).hφT
      (gs i hi).hP (gs i hi).hR (gs i hi).hS
      (targets_nonsingular W ha endo (g i) (gs i hi).holds (gs i hi).hT (gs i hi).hφT).1
      (targets_nonsingular W ha endo (g i) (gs i hi).holds (gs i hi).hT (gs i hi).hφT).2
      (gs i hi).hxne1
      (htne_of_holds W ha h2 hodd endo (g i) (gs i hi).holds (gs i hi).hP (gs i hi).hR).1
      (gs i hi).hxne2
      (htne_of_holds W ha h2 hodd endo (g i) (gs i hi).holds (gs i hi).hP (gs i hi).hR).2
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

/-- THE TOP-LEVEL STATEMENT: EndoMul computes scalar multiplication by exactly
    the scalar EndoScalar decodes. At the real init (`P₀ = 2·(T + φ(T))`) and with the
    eigenvalue `φ(T) = [λ]·T`, the `m` rows produce `P_m = s·T` where `s` is the
    `EndoScalar.toField` of the shared challenge crumbs:

        (s : F) = decomposeA(crumbs)·λ + decomposeB(crumbs) = toField crumbs λ.

    This closes `EndoMul ∘ EndoScalar`: EndoScalar decodes the scalar into the
    eigenvalue basis `a·λ + b`, and EndoMul multiplies the base by exactly that
    scalar. Assembles `endoMul_ab` (k₂,k₁ = the a,b digit-sums) with
    `decompose_crumbList` (the `a=b=2` ↔ `4^m·P₀` init alignment), the init `hP₀`,
    and the eigenvalue `heig`. Over a curve of odd prime order (`Fact (Prime W.order)` +
    `hodd : W.order ≠ 2`), which self-enforces each block's second-addition non-degeneracy
    (`htne_of_holds`), so `EndoStep` need only carry the first-addition `hxne`. -/
theorem endoMul (W : WeierstrassCurve.Affine F) [Fact (Nat.Prime W.order)]
    (ha : (W.a₁ = 0 ∧ W.a₂ = 0 ∧ W.a₃ = 0))
    (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (hodd : W.order ≠ 2) (endo : F)
    (m : ℕ) (g : ℕ → Witness F) (gs : ∀ i, i < m → EndoStep W endo (g i))
    (P : ℕ → W.Point) (T φT : W.Point)
    (hT : ∀ i (hi : i < m), T = Point.some _ _ (gs i hi).hT)
    (hφT : ∀ i (hi : i < m), φT = Point.some _ _ (gs i hi).hφT)
    (hin : ∀ i (hi : i < m), P i = Point.some _ _ (gs i hi).hP)
    (hout : ∀ i (hi : i < m), P (i + 1) = Point.some _ _ (gs i hi).hS)
    (hP0 : P 0 = (2 : ℤ) • T + (2 : ℤ) • φT) (lam : ℤ) (heig : φT = lam • T) :
    ∃ s : ℤ, P m = s • T
      ∧ (s : F) = Kimchi.Circuit.EndoScalar.toField (crumbList g m) (lam : F) := by
  obtain ⟨ k1, k2, hPm, hk2, hk1 ⟩ :=
    endoMul_ab W ha h2 h3 hodd endo m g gs P T φT hT hφT hin hout;
  refine' ⟨ 2 * 4 ^ m + k1 + ( 2 * 4 ^ m + k2 ) * lam, _, _ ⟩;
  · rw [ hPm, hP0, heig ];
    module;
  · simp +decide [ EndoScalar.toField, hk1, hk2 ];
    rw [ decompose_crumbList g m |>.1, decompose_crumbList g m |>.2 ] ; ring

end Kimchi.Circuit.EndoMul
