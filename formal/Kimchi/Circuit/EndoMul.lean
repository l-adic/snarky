import Kimchi.Circuit.EndoMul.Internal
import Kimchi.Pasta

/-!
# The `EndoMul` circuit

Endomorphism-optimized (GLV) scalar multiplication, instantiated at the real Pasta curves (the
analog of `VarBaseMul`'s `scaleFast` entry points). A run of `Kimchi.Gate.EndoMul` rows over a base
point `T` computes `[s]·T`, where `s` is the scalar `EndoScalar` decodes from the row crumbs. The
generic capstone `Kimchi.Circuit.EndoMul.endoMul` and its supporting development — the GLV point
fold, the `EndoMul ∘ EndoScalar` recoding kernel, and the non-degeneracy lemmas — live in
`Kimchi.Circuit.EndoMul.Internal`.

This module exposes the deployed entry points at each concrete curve. The prover supplies only the
gate constraint `Holds` per row, the base nonsingularity (row 0 — genuinely external), the column
threading, and the initial accumulator `P₀ = 2(T + φT)`. Every intermediate accumulator's
nonsingularity is *derived* (`endoMul`), and the per-row first-addition non-degeneracy `hxne` is
*derived* — not assumed — from the GLV short-basis bound. The prime-order / `hodd` / short-shape
facts come from `Kimchi.Pasta`, and the eigenvalue `φT = [λ]·T` is discharged by the curve's CM
axiom (`{pallas,vesta}_eigen`).

## Main results

* `{pallas,vesta}_combo_off_targets` — the GLV off-targets fact (the `hxne` core): a bounded
  nonzero two-base accumulator `[a]·T + [b]·φT` avoids `±T`, `±φT`.
* `{pallas,vesta}_endoMul` — the capstone at each curve: a run of valid (`Holds`) rows computes the
  final accumulator `= [s]·T` with `s = EndoScalar.toField (crumbList g m) λ`.
-/

namespace Kimchi.Circuit.EndoMul

open Kimchi.Gate.EndoMul Kimchi.Pasta WeierstrassCurve.Affine
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
    {T φT : Pallas.curve.toAffine.Point} (hTne : T ≠ 0) (heig : φT = pallas_lam • T) :
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
    {T φT : Vesta.curve.toAffine.Point} (hTne : T ≠ 0) (heig : φT = vesta_lam • T) :
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
    odd-prime-order conditions from `Kimchi.Pasta`. -/
theorem pallas_endoMul (m : ℕ) (hbits : 4 * m ≤ 244)
    (g : ℕ → Witness PallasBaseField)
    (hholds : ∀ i, i < m → Holds pallas_endo (g i))
    (T φT : Pallas.curve.toAffine.Point)
    (hTns : Pallas.curve.toAffine.Nonsingular (g 0).xT (g 0).yT) (hTeq : T = Point.some _ _ hTns)
    (hφTns : Pallas.curve.toAffine.Nonsingular (pallas_endo * (g 0).xT) (g 0).yT)
    (hφTeq : φT = Point.some _ _ hφTns)
    (hbase : ∀ i, i < m → (g i).xT = (g 0).xT ∧ (g i).yT = (g 0).yT)
    (hthread : ∀ i, i + 1 < m → (g (i + 1)).xP = (g i).xS ∧ (g (i + 1)).yP = (g i).yS)
    (hP0ns : Pallas.curve.toAffine.Nonsingular (g 0).xP (g 0).yP)
    (hP0 : Point.some _ _ hP0ns = (2 : ℤ) • T + (2 : ℤ) • φT) :
    ∃ (hfin : Pallas.curve.toAffine.Nonsingular (accX g m) (accY g m)) (s : ℤ),
      Point.some _ _ hfin = s • T
        ∧ (s : PallasBaseField)
            = Kimchi.Circuit.EndoScalar.toField (crumbList g m) (pallas_lam : PallasBaseField) := by
  have ha : Pallas.curve.toAffine.a₁ = 0 ∧ Pallas.curve.toAffine.a₂ = 0
      ∧ Pallas.curve.toAffine.a₃ = 0 := ⟨rfl, rfl, rfl⟩
  haveI : Fact (Pallas.curve.toAffine.a₁ = 0 ∧ Pallas.curve.toAffine.a₂ = 0
      ∧ Pallas.curve.toAffine.a₃ = 0) := ⟨ha⟩
  have h2 : (2 : PallasBaseField) ≠ 0 := by decide
  have h3 : (3 : PallasBaseField) ≠ 0 := by decide
  have hodd : Pallas.curve.toAffine.order ≠ 2 := by rw [pallas_card]; decide
  have hTne : T ≠ 0 := by rw [hTeq]; exact Point.some_ne_zero _
  have heig : φT = pallas_lam • T := by rw [hφTeq, hTeq]; exact pallas_eigen hTns hφTns
  have off : ∀ a b : ℤ, a ≠ 0 → b ≠ 0 → |a| < 2 ^ 126 → |b| < 2 ^ 126 →
      a • T + b • φT ≠ T ∧ a • T + b • φT ≠ -T
        ∧ a • T + b • φT ≠ φT ∧ a • T + b • φT ≠ -φT :=
    fun a b ha' hb hba hbb => pallas_combo_off_targets ha' hb hba hbb hTne heig
  have hxne := accumulator_chain Pallas.curve.toAffine h2 hodd pallas_endo T φT off m hbits
    g hholds hTns hTeq hφTns hφTeq hbase hthread hP0ns hP0
  exact endoMul Pallas.curve.toAffine ha h2 h3 hodd pallas_endo m g hholds T φT
    hTns hTeq hφTns hφTeq hbase hthread hP0ns hP0 hxne pallas_lam heig

/-- **EndoMul at Vesta** — the other half of the 2-cycle, identical modulo `vesta_*`. -/
theorem vesta_endoMul (m : ℕ) (hbits : 4 * m ≤ 244)
    (g : ℕ → Witness VestaBaseField)
    (hholds : ∀ i, i < m → Holds vesta_endo (g i))
    (T φT : Vesta.curve.toAffine.Point)
    (hTns : Vesta.curve.toAffine.Nonsingular (g 0).xT (g 0).yT) (hTeq : T = Point.some _ _ hTns)
    (hφTns : Vesta.curve.toAffine.Nonsingular (vesta_endo * (g 0).xT) (g 0).yT)
    (hφTeq : φT = Point.some _ _ hφTns)
    (hbase : ∀ i, i < m → (g i).xT = (g 0).xT ∧ (g i).yT = (g 0).yT)
    (hthread : ∀ i, i + 1 < m → (g (i + 1)).xP = (g i).xS ∧ (g (i + 1)).yP = (g i).yS)
    (hP0ns : Vesta.curve.toAffine.Nonsingular (g 0).xP (g 0).yP)
    (hP0 : Point.some _ _ hP0ns = (2 : ℤ) • T + (2 : ℤ) • φT) :
    ∃ (hfin : Vesta.curve.toAffine.Nonsingular (accX g m) (accY g m)) (s : ℤ),
      Point.some _ _ hfin = s • T
        ∧ (s : VestaBaseField)
            = Kimchi.Circuit.EndoScalar.toField (crumbList g m) (vesta_lam : VestaBaseField) := by
  have ha : Vesta.curve.toAffine.a₁ = 0 ∧ Vesta.curve.toAffine.a₂ = 0
      ∧ Vesta.curve.toAffine.a₃ = 0 := ⟨rfl, rfl, rfl⟩
  haveI : Fact (Vesta.curve.toAffine.a₁ = 0 ∧ Vesta.curve.toAffine.a₂ = 0
      ∧ Vesta.curve.toAffine.a₃ = 0) := ⟨ha⟩
  have h2 : (2 : VestaBaseField) ≠ 0 := by decide
  have h3 : (3 : VestaBaseField) ≠ 0 := by decide
  have hodd : Vesta.curve.toAffine.order ≠ 2 := by rw [vesta_card]; decide
  have hTne : T ≠ 0 := by rw [hTeq]; exact Point.some_ne_zero _
  have heig : φT = vesta_lam • T := by rw [hφTeq, hTeq]; exact vesta_eigen hTns hφTns
  have off : ∀ a b : ℤ, a ≠ 0 → b ≠ 0 → |a| < 2 ^ 126 → |b| < 2 ^ 126 →
      a • T + b • φT ≠ T ∧ a • T + b • φT ≠ -T
        ∧ a • T + b • φT ≠ φT ∧ a • T + b • φT ≠ -φT :=
    fun a b ha' hb hba hbb => vesta_combo_off_targets ha' hb hba hbb hTne heig
  have hxne := accumulator_chain Vesta.curve.toAffine h2 hodd vesta_endo T φT off m hbits
    g hholds hTns hTeq hφTns hφTeq hbase hthread hP0ns hP0
  exact endoMul Vesta.curve.toAffine ha h2 h3 hodd vesta_endo m g hholds T φT
    hTns hTeq hφTns hφTeq hbase hthread hP0ns hP0 hxne vesta_lam heig

end Kimchi.Circuit.EndoMul
