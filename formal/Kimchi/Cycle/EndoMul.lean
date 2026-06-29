import Kimchi.Circuit.EndoMul
import Kimchi.Pasta

/-!
# `EndoMul` at the Pasta curves

The Cycle-layer instantiation of `Kimchi.Circuit.EndoMul.endoMul` at the real Pallas and Vesta
curves. The abstract `endoMul` is stated over any short-Weierstrass curve of odd prime order
with the eigenvalue `φ(T) = [λ]·T` taken as a hypothesis; here the prime-order/`hodd`/short-shape
facts come from `Kimchi.Pasta`, and `heig` is discharged by the curve's CM axiom (`pallas_eigen`
/ `vesta_eigen`). So `pallas_endoMul` / `vesta_endoMul` need neither the eigenvalue data nor the
order conditions — only the per-row `EndoStep` witnesses and the threaded point chain.

The per-row first-addition non-degeneracy (`EndoStep.hxne`) is still carried; discharging it from
the GLV short-basis bound (`pallas_glv_no_short_relation`) is the remaining Stage-3b step.
-/

namespace Kimchi.Cycle.EndoMul

open Kimchi.Circuit.EndoMul Kimchi.Gate.EndoMul Kimchi.Pasta WeierstrassCurve.Affine
open CompElliptic.Curves.Pasta CompElliptic.Fields.Pasta

/-- `|x| < 2¹²⁶` keeps the offsets `x ∓ 1` inside the GLV bound `2¹²⁷`. -/
private lemma abs_offset_lt {x : ℤ} (hx : |x| < 2 ^ 126) :
    |x - 1| < 2 ^ 127 ∧ |x + 1| < 2 ^ 127 := by
  rw [abs_lt] at hx
  have hp : (2 : ℤ) ^ 126 < 2 ^ 127 := by norm_num
  exact ⟨by rw [abs_lt]; omega, by rw [abs_lt]; omega⟩

/-- **EndoMul at Pallas.** A run of `m ≥ 1` valid `EndoMul` rows over the Pallas curve, threaded
    from the init `P₀ = 2(T + φT)`, computes `P_m = [s]·T` where `s` is the `EndoScalar`-decoded
    scalar `toField (crumbList g m) λ`. The eigenvalue `heig` is supplied by `pallas_eigen`; the
    odd-prime-order conditions by `Kimchi.Pasta`. -/
theorem pallas_endoMul (m : ℕ) (hm : 0 < m) (g : ℕ → Witness PallasBaseField)
    (gs : ∀ i, i < m → EndoStep Pallas.curve.toAffine pallas_endo (g i))
    (P : ℕ → Pallas.curve.toAffine.Point) (T φT : Pallas.curve.toAffine.Point)
    (hT : ∀ i (hi : i < m), T = Point.some _ _ (gs i hi).hT)
    (hφT : ∀ i (hi : i < m), φT = Point.some _ _ (gs i hi).hφT)
    (hin : ∀ i (hi : i < m), P i = Point.some _ _ (gs i hi).hP)
    (hout : ∀ i (hi : i < m), P (i + 1) = Point.some _ _ (gs i hi).hS)
    (hP0 : P 0 = (2 : ℤ) • T + (2 : ℤ) • φT) :
    ∃ s : ℤ, P m = s • T
      ∧ (s : PallasBaseField)
          = Kimchi.Circuit.EndoScalar.toField (crumbList g m) (pallas_lam : PallasBaseField) := by
  have h2 : (2 : PallasBaseField) ≠ 0 := by decide
  have h3 : (3 : PallasBaseField) ≠ 0 := by decide
  have hodd : Pallas.curve.toAffine.order ≠ 2 := by rw [pallas_card]; decide
  have heig : φT = pallas_lam • T := by
    rw [hφT 0 hm, hT 0 hm]; exact pallas_eigen (gs 0 hm).hT (gs 0 hm).hφT
  exact endoMul Pallas.curve.toAffine ⟨rfl, rfl, rfl⟩ h2 h3 hodd pallas_endo m g gs P T φT
    hT hφT hin hout hP0 pallas_lam heig

/-- **EndoMul at Vesta** — the other half of the 2-cycle, identical modulo `vesta_*`. -/
theorem vesta_endoMul (m : ℕ) (hm : 0 < m) (g : ℕ → Witness VestaBaseField)
    (gs : ∀ i, i < m → EndoStep Vesta.curve.toAffine vesta_endo (g i))
    (P : ℕ → Vesta.curve.toAffine.Point) (T φT : Vesta.curve.toAffine.Point)
    (hT : ∀ i (hi : i < m), T = Point.some _ _ (gs i hi).hT)
    (hφT : ∀ i (hi : i < m), φT = Point.some _ _ (gs i hi).hφT)
    (hin : ∀ i (hi : i < m), P i = Point.some _ _ (gs i hi).hP)
    (hout : ∀ i (hi : i < m), P (i + 1) = Point.some _ _ (gs i hi).hS)
    (hP0 : P 0 = (2 : ℤ) • T + (2 : ℤ) • φT) :
    ∃ s : ℤ, P m = s • T
      ∧ (s : VestaBaseField)
          = Kimchi.Circuit.EndoScalar.toField (crumbList g m) (vesta_lam : VestaBaseField) := by
  have h2 : (2 : VestaBaseField) ≠ 0 := by decide
  have h3 : (3 : VestaBaseField) ≠ 0 := by decide
  have hodd : Vesta.curve.toAffine.order ≠ 2 := by rw [vesta_card]; decide
  have heig : φT = vesta_lam • T := by
    rw [hφT 0 hm, hT 0 hm]; exact vesta_eigen (gs 0 hm).hT (gs 0 hm).hφT
  exact endoMul Vesta.curve.toAffine ⟨rfl, rfl, rfl⟩ h2 h3 hodd vesta_endo m g gs P T φT
    hT hφT hin hout hP0 vesta_lam heig

/-! ## GLV non-degeneracy at the Pasta curves

The `hxne` accumulator-off-targets fact for `EndoMul`, discharged from the GLV short-basis bound.
A two-base combination `[a]·T + [b]·φT` with coefficients inside the bound (`< 2¹²⁶`, comfortably
above any `4^m` reached by a `< 254`-bit challenge) and nonzero is none of `±T`, `±φT`. This is
the consumer of `*_glv_no_short_relation`; threading it through the per-row accumulators to drop
`EndoStep.hxne` is the remaining integration. -/

/-- **GLV off-targets at Pallas.** A bounded nonzero two-base accumulator avoids `±T`, `±φT`. -/
theorem pallas_combo_off_targets {a b : ℤ} (ha : a ≠ 0) (hb : b ≠ 0)
    (hba : |a| < 2 ^ 126) (hbb : |b| < 2 ^ 126)
    {T φT : Pallas.curve.toAffine.Point} (hTne : T ≠ 0) (heig : φT = pallas_lam • T) :
    a • T + b • φT ≠ T ∧ a • T + b • φT ≠ -T
      ∧ a • T + b • φT ≠ φT ∧ a • T + b • φT ≠ -φT := by
  obtain ⟨ha1, ha1'⟩ := abs_offset_lt hba
  obtain ⟨hb1, hb1'⟩ := abs_offset_lt hbb
  have ha127 : |a| < 2 ^ 127 := lt_trans hba (by norm_num)
  have hb127 : |b| < 2 ^ 127 := lt_trans hbb (by norm_num)
  exact combo_off_targets Pallas.curve.toAffine hTne heig
    (pallas_glv_no_short_relation (Or.inr hb) ha1 hb127)
    (pallas_glv_no_short_relation (Or.inr hb) ha1' hb127)
    (pallas_glv_no_short_relation (Or.inl ha) ha127 hb1)
    (pallas_glv_no_short_relation (Or.inl ha) ha127 hb1')

/-- **GLV off-targets at Vesta** — the other half of the 2-cycle. -/
theorem vesta_combo_off_targets {a b : ℤ} (ha : a ≠ 0) (hb : b ≠ 0)
    (hba : |a| < 2 ^ 126) (hbb : |b| < 2 ^ 126)
    {T φT : Vesta.curve.toAffine.Point} (hTne : T ≠ 0) (heig : φT = vesta_lam • T) :
    a • T + b • φT ≠ T ∧ a • T + b • φT ≠ -T
      ∧ a • T + b • φT ≠ φT ∧ a • T + b • φT ≠ -φT := by
  obtain ⟨ha1, ha1'⟩ := abs_offset_lt hba
  obtain ⟨hb1, hb1'⟩ := abs_offset_lt hbb
  have ha127 : |a| < 2 ^ 127 := lt_trans hba (by norm_num)
  have hb127 : |b| < 2 ^ 127 := lt_trans hbb (by norm_num)
  exact combo_off_targets Vesta.curve.toAffine hTne heig
    (vesta_glv_no_short_relation (Or.inr hb) ha1 hb127)
    (vesta_glv_no_short_relation (Or.inr hb) ha1' hb127)
    (vesta_glv_no_short_relation (Or.inl ha) ha127 hb1)
    (vesta_glv_no_short_relation (Or.inl ha) ha127 hb1')

end Kimchi.Cycle.EndoMul
