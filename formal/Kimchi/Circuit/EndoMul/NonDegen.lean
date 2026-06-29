import Kimchi.Gate.EndoMul
import Kimchi.Circuit.VarBaseMul.NonDegen
import Kimchi.Circuit.VarBaseMul.Soundness

/-!
# EndoMul non-degeneracy lemmas

The per-row non-degeneracy facts the EndoMul soundness needs, generic over the curve:

* `block_tne` — each `(P+Q)+P` block's *second*-addition condition `htne ≠ 0` is self-enforced by
  the gate constraints (the EndoMul analog of VarBaseMul's `tne_of_holds`): were it to fail, the
  block constraint plus the built-in distinct-point check would force the accumulator to be
  2-torsion — impossible on an odd-prime-order group (`smul_ne_zero_of_lt`).
* `combo_off_targets` — the *first*-addition condition `hxne` is NOT self-enforced; its geometric
  core is that a bounded two-base combination `[a]·T + [b]·φT` avoids `±T`/`±φT` (eigenvalue
  `φT = [λ]·T` + four "no short relation" facts). The Pasta GLV bound supplies those, threaded
  through `accumulator_chain`.
* `selectQ'` — a bounded variant of `Gate.EndoMul.selectQ` that also returns the sign `e = ±1`.
-/
namespace Kimchi.Circuit.EndoMul

open Kimchi.Gate.EndoMul WeierstrassCurve.Affine

variable {F : Type*} [Field F] [DecidableEq F]

/-- One block's second-addition non-degeneracy, self-enforced. If `2·xI − s² + xq = 0`, the
    block constraint `(2·xI − s² + xq)·(…) = (xI − xO)·(2·yI)` gives `(xI − xO)·(2·yI) = 0`;
    with `xI ≠ xO` and char ≠ 2 this forces `yI = 0`, making `I` 2-torsion — ruled out on an
    odd-prime-order group. (EndoMul's `tne_of_holds`.) -/
theorem block_tne (W : WeierstrassCurve.Affine F) [Fact (Nat.Prime W.order)]
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
    have : (2 : ℕ) < W.order := lt_of_le_of_ne W.order_prime.two_le (Ne.symm hodd)
    exact_mod_cast this
  exact Kimchi.Circuit.VarBaseMul.smul_ne_zero_of_lt W hPne (by norm_num) hlt h2P

/-! ## The GLV non-degeneracy: the two-base accumulator avoids the targets.

    The first-addition condition `hxne` is `Pᵢ ∉ {±T, ±φT}` (same `x` ⟺ `±` point). Writing the
    accumulator as `[a]·T + [b]·φT` and collapsing with the eigenvalue `φT = [λ]·T`, this reduces
    to `a + b·λ ≢ {±1, ±λ} (mod order)` — four "no short relation" facts, supplied for the small
    accumulator coefficients by the GLV bound (`Kimchi.Pasta.pallas_glv_no_short_relation`). -/

/-- **GLV off-targets.** With the eigenvalue `φT = [λ]·T` and the four no-short-relation facts
    for the accumulator's offset coefficients, the two-base combination `[a]·T + [b]·φT` is none
    of `±T`, `±φT`. The geometric core of `hxne`. -/
theorem combo_off_targets (W : WeierstrassCurve.Affine F)
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
    rw [← sub_eq_zero, e, Kimchi.Circuit.VarBaseMul.zsmul_eq_zero_iff_order_dvd W hTne]
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
theorem selectQ' (W : WeierstrassCurve.Affine F) (ha : (W.a₁ = 0 ∧ W.a₂ = 0 ∧ W.a₃ = 0))
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

end Kimchi.Circuit.EndoMul
