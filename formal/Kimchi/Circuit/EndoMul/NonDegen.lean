import Kimchi.Gate.EndoMul
import Kimchi.Circuit.VarBaseMul.NonDegen
import Kimchi.Circuit.VarBaseMul.Soundness

/-!
# EndoMul non-degeneracy: the second-addition condition is self-enforced

Stage 2a of discharging `EndoStep`'s per-row non-degeneracies. The *second*-addition
condition of each `(P+Q)+P` block — `htne = 2·xI − s² + xq ≠ 0` — is forced by the gate
constraints themselves: it is the EndoMul analog of VarBaseMul's `tne_of_holds`, and EndoMul's
built-in distinct-point check supplies the `xI ≠ xO` it needs.

If `htne = 0`, block constraint #2/#5 collapses to `(xI − xO)·(2·yI) = 0`; with `xI ≠ xO`
(`distinctPoints`) and char ≠ 2 this forces `yI = 0`, so `I` is 2-torsion — impossible on an
odd-prime-order group (`smul_ne_zero_of_lt`). So the gate never needs `htne` assumed.

The *first*-addition condition `hxne` is NOT self-enforced — it needs the global
accumulator-avoids-`±T`/`±φT` argument, deferred to the Pasta instantiation.
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

/-- Both blocks' second-addition non-degeneracies, read off `Holds` and the distinct-point
    check (`distinctPoints` supplies `xP ≠ xR`, `xR ≠ xS`). These are the `htne1`/`htne2` that
    `EndoStep` previously assumed — now derived. -/
theorem htne_of_holds (W : WeierstrassCurve.Affine F) [Fact (Nat.Prime W.order)]
    (ha : W.a₁ = 0 ∧ W.a₂ = 0 ∧ W.a₃ = 0) (h2 : (2 : F) ≠ 0) (hodd : W.order ≠ 2)
    (endo : F) (w : Witness F) (h : Holds endo w)
    (hP : W.Nonsingular w.xP w.yP) (hR : W.Nonsingular w.xR w.yR) :
    2 * w.xP - w.s1 ^ 2 + (1 + (endo - 1) * w.b1) * w.xT ≠ 0
      ∧ 2 * w.xR - w.s3 ^ 2 + (1 + (endo - 1) * w.b3) * w.xT ≠ 0 := by
  obtain ⟨hxPxR, hxRxS⟩ := distinctPoints endo w h
  simp only [Holds] at h
  obtain ⟨_, hc1, _, _, hc2, _, _, _, _, _, _, _⟩ := h
  exact ⟨block_tne W ha h2 hodd hP hxPxR hc1, block_tne W ha h2 hodd hR hxRxS hc2⟩

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

end Kimchi.Circuit.EndoMul
