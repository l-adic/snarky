import Kimchi.Gate.Semantics.VarBaseMul
import Pasta.Endo

/-!
# The curve dictionaries the circuit laws close over

The deep embedding's rendering of the PureScript typeclass dictionaries: a structure passed
explicitly rather than a class, since the formal tree threads theorem content by argument.
Generic circuit laws take one of these and compose over an abstract field the way the
PureScript pickles circuits do; the deployed values discharge it, mirroring the
instantiation at wrap and step main.

They live here rather than in the gadget module that happens to use them first. `HasCurve`
is what the `VarBaseMul` ladder closes over and `HasEndo` what `EndoMul` closes over, but
both are statements about a curve, not about a gate, and both deployed pairs belong beside
their structures rather than scattered across `VarBaseMul`, `Point` and `EndoMul`.

## Main definitions

* `HasCurve` — the curve, its short shape, and the group facts the ladder consumes.
* `HasEndo` — `HasCurve` with the endomorphism coefficient, its eigenvalue and the GLV
  facts. The wire twin is `Pasta.EndoSpec`.
* `HasCurve.vesta`, `HasCurve.pallas`, `HasEndo.vesta`, `HasEndo.pallas` — the four
  deployed dictionaries.
-/

namespace Snarky.Kimchi

open WeierstrassCurve.Affine

variable {F : Type}

/-- The curve dictionary the `VarBaseMul` laws close over (the PureScript ambient
`WeierstrassCurve` class): the curve, its Pasta short shape, and the group facts the
ladder's gate-semantics theorems consume. -/
structure HasCurve (F : Type) [Field F] [DecidableEq F] where
  /-- The curve the base point and accumulators live on. -/
  W : WeierstrassCurve.Affine F
  /-- The Pasta short-Weierstrass shape. -/
  short : W.a₁ = 0 ∧ W.a₂ = 0 ∧ W.a₃ = 0 ∧ W.a₄ = 0
  /-- The group order is prime. -/
  prime : Nat.Prime W.order
  /-- The group order is not `2` — with `prime`, the group has no 2-torsion. -/
  odd : W.order ≠ 2
  /-- The field does not have characteristic `2`. -/
  two_ne : (2 : F) ≠ 0

/-- The regime the ladder's non-degeneracy pricing needs, at `L` bits over the
dictionary's order: EITHER the whole ladder fits below the order (subwrap — no
condition on the scalar), OR the one-wrap band holds and the scalar's Type1 decode
`z` avoids the forbidden residues. `varBaseMul_off`'s dichotomy, at the law's
list-level decode. -/
def HasCurve.LadderRegime [Field F] [DecidableEq F] (d : HasCurve F) (L : ℕ)
    (z : ℤ) : Prop :=
  3 * 2 ^ L ≤ d.W.order ∨
    (2 ^ (L - 1) < d.W.order ∧ d.W.order < 2 ^ L ∧ d.W.order % 4 = 1 ∧
      z ∉ Kimchi.Gate.VarBaseMul.forbiddenValues d.W.order)

open WeierstrassCurve.Affine in
/-- No point of the group is 2-torsion: the order is an odd prime, so doubling kills only
zero. What the addition gadget asks of the base it doubles. -/
theorem HasCurve.two_torsion_free [Field F] [DecidableEq F] (d : HasCurve F)
    (P : d.W.Point) (hne : P ≠ 0) : P + P ≠ 0 := by
  haveI : Fact (Nat.Prime d.W.order) := ⟨d.prime⟩
  haveI : Fact (d.W.a₁ = 0 ∧ d.W.a₂ = 0 ∧ d.W.a₃ = 0) :=
    ⟨⟨d.short.1, d.short.2.1, d.short.2.2.1⟩⟩
  have hlt : (2 : ℤ) < (d.W.order : ℤ) := by
    have h2 := (Fact.out : Nat.Prime d.W.order).two_le
    have h3 : 3 ≤ d.W.order := by
      rcases Nat.lt_or_ge d.W.order 3 with h | h
      · exact absurd (by omega : d.W.order = 2) d.odd
      · exact h
    exact_mod_cast h3
  intro hzero
  exact _root_.Pasta.smul_ne_zero_of_lt d.W hne (by norm_num) hlt
    (by rw [two_zsmul, hzero])

/-- The dictionary the `EndoMul` laws close over: a `HasCurve` with the endomorphism
coefficient, its scalar eigenvalue, and every curve-level fact the `endoMul` law pair
consumes. The wire twin is `Pasta.EndoSpec`, which carries the same mathematics without
the circuit layer's extra characteristic and order facts. -/
structure HasEndo (F : Type) [Field F] [DecidableEq F] extends HasCurve F where
  /-- The endomorphism coefficient `β`: `φ(x, y) = (β·x, y)`. -/
  endo : F
  /-- The scalar eigenvalue `λ` of the endomorphism: `φ(T) = [λ]·T`. -/
  lam : ℤ
  /-- The curve is smooth, so an on-curve point is nonsingular
  (`equation_iff_nonsingular_of_Δ_ne_zero`). -/
  delta_ne : W.Δ ≠ 0
  /-- The field does not have characteristic `3`. -/
  three_ne : (3 : F) ≠ 0
  /-- The eigenvalue relation `φ(T) = [λ]·T` at every on-curve point. -/
  eigen : ∀ {x y : F} (hT : W.Nonsingular x y) (hφT : W.Nonsingular (endo * x) y),
    Point.some _ _ hφT = lam • Point.some _ _ hT
  /-- The endomorphism maps the curve to itself. -/
  endo_nonsingular : ∀ {x y : F}, W.Nonsingular x y → W.Nonsingular (endo * x) y
  /-- The GLV off-targets fact: a bounded nonzero two-base combination avoids `±T`,
  `±φT` (`Pasta.{pallas,vesta}_combo_off_targets`'s shape). -/
  off_targets : ∀ {a b : ℤ}, a ≠ 0 → b ≠ 0 → |a| < 2 ^ 126 → |b| < 2 ^ 126 →
    ∀ {T φT : W.Point}, T ≠ 0 → φT = lam • T →
      a • T + b • φT ≠ T ∧ a • T + b • φT ≠ -T ∧
      a • T + b • φT ≠ φT ∧ a • T + b • φT ≠ -φT
  /-- `[1 + λ]` does not kill a nonzero point — the init sum `T + φT` is finite. -/
  lam_succ_smul : ∀ T : W.Point, T ≠ 0 → (1 + lam) • T ≠ 0
  /-- The order is not `3` either: with `odd`, both `2` and `3` are units in
  `ZMod order`, which lets the decompose tables be read in the scalar field. -/
  order_ne_three : W.order ≠ 3
  /-- The char window: integers below `2^127` in magnitude embed injectively in `F`,
  so bounded fold values with equal `F`-images are equal integers. -/
  char_big : ∀ z : ℤ, |z| < 2 ^ 127 → (z : F) = 0 → z = 0

/-! ## The deployed dictionaries -/

open CompElliptic.Curves.Pasta CompElliptic.Fields.Pasta Pasta in
/-- The curve dictionary at deployed Vesta — the curve the Schnorr statement's points live
on and the ladder's base group. -/
@[reducible] def HasCurve.vesta : HasCurve Fq where
  W := Vesta.curve.toAffine
  short := ⟨rfl, rfl, rfl, rfl⟩
  prime := Fact.out
  odd := by rw [vesta_card]; decide
  two_ne := by decide

open CompElliptic.Curves.Pasta CompElliptic.Fields.Pasta Pasta in
/-- The curve dictionary at deployed Pallas, the step side's base group. -/
@[reducible] def HasCurve.pallas : HasCurve Fp where
  W := Pallas.curve.toAffine
  short := ⟨rfl, rfl, rfl, rfl⟩
  prime := Fact.out
  odd := by rw [pallas_card]; decide
  two_ne := by decide

open CompElliptic.Curves.Pasta CompElliptic.Fields.Pasta Pasta in
/-- The endomorphism dictionary at deployed Pallas: `pallasEndo`/`pallasLam`, the facts
from `Pasta` (`pallas_eigen`, `pallas_endo_nonsingular`, `pallas_card`) and the GLV
off-targets fact. -/
def HasEndo.pallas : HasEndo Fp where
  W := Pallas.curve.toAffine
  endo := pallasEndo
  lam := pallasLam
  short := ⟨rfl, rfl, rfl, rfl⟩
  delta_ne := by decide
  prime := Fact.out
  odd := by rw [pallas_card]; decide
  two_ne := by decide
  three_ne := by decide
  eigen := fun hT _ => pallas_eigen hT
  endo_nonsingular := fun h => pallas_endo_nonsingular h
  off_targets := fun {a b} ha hb hba hbb {T φT} hTne heig =>
    _root_.Pasta.pallas_combo_off_targets ha hb hba hbb hTne heig
  lam_succ_smul := fun T hTne => by
    haveI : Fact (Pallas.curve.toAffine.a₁ = 0 ∧ Pallas.curve.toAffine.a₂ = 0
        ∧ Pallas.curve.toAffine.a₃ = 0) := ⟨rfl, rfl, rfl⟩
    exact _root_.Pasta.smul_ne_zero_of_lt Pallas.curve.toAffine hTne
      (by norm_num [pallasLam])
      (by rw [pallas_card]; norm_num [pallasLam])
  order_ne_three := by rw [pallas_card]; decide
  char_big := fun z hz h0 => by
    have hdvd : ((PALLAS_BASE_CARD : ℕ) : ℤ) ∣ z :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd z _).mp h0
    exact Int.eq_zero_of_abs_lt_dvd hdvd (hz.trans (by norm_num))

open CompElliptic.Curves.Pasta CompElliptic.Fields.Pasta Pasta in
/-- The endomorphism dictionary at deployed Vesta — the other half of the 2-cycle. -/
@[reducible] def HasEndo.vesta : HasEndo Fq where
  W := Vesta.curve.toAffine
  endo := vestaEndo
  lam := vestaLam
  short := ⟨rfl, rfl, rfl, rfl⟩
  delta_ne := by decide
  prime := Fact.out
  odd := by rw [vesta_card]; decide
  two_ne := by decide
  three_ne := by decide
  eigen := fun hT _ => vesta_eigen hT
  endo_nonsingular := fun h => vesta_endo_nonsingular h
  off_targets := fun {a b} ha hb hba hbb {T φT} hTne heig =>
    _root_.Pasta.vesta_combo_off_targets ha hb hba hbb hTne heig
  lam_succ_smul := fun T hTne => by
    haveI : Fact (Vesta.curve.toAffine.a₁ = 0 ∧ Vesta.curve.toAffine.a₂ = 0
        ∧ Vesta.curve.toAffine.a₃ = 0) := ⟨rfl, rfl, rfl⟩
    exact _root_.Pasta.smul_ne_zero_of_lt Vesta.curve.toAffine hTne
      (by norm_num [vestaLam])
      (by rw [vesta_card]; norm_num [vestaLam])
  order_ne_three := by rw [vesta_card]; decide
  char_big := fun z hz h0 => by
    have hdvd : ((PALLAS_SCALAR_CARD : ℕ) : ℤ) ∣ z :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd z _).mp h0
    exact Int.eq_zero_of_abs_lt_dvd hdvd (hz.trans (by norm_num))

end Snarky.Kimchi
