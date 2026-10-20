import Kimchi.Gate.Semantics.VarBaseMul
import Pasta.Endo
import Bulletproof.Wire

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
open CompElliptic.CurveForms.ShortWeierstrass Bulletproof.Ipa

variable {F : Type}

/-- The curve dictionary the `VarBaseMul` laws close over: the curve, its Pasta short
shape, and the group facts the ladder's gate-semantics theorems consume. -/
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

/-- The gadget layer's curve dictionary of a commitment curve: the affine form of `C.E`, short
by `C.a_zero`, of prime order by `C.card`, and off characteristic `2` and 2-torsion by the
bounds `hbase` and `hscalar`.

Reducible, and a structure literal: consumers state premises over `HasCurve.W`, and instance
search runs at reducible transparency, so that projection must reduce to `C.E.toAffine`
there, by iota on the literal, without forcing the proof fields. -/
@[reducible] def HasCurve.ofCommitmentCurve
    (C : CommitmentCurve) (hbase : 2 < C.base) (hscalar : 2 < C.scalar) :
    HasCurve C.BaseField where
  W := C.E.toAffine
  short := ⟨rfl, rfl, rfl, C.a_zero⟩
  prime := C.order_eq ▸ Fact.out
  odd := by rw [C.order_eq]; omega
  two_ne := by
    haveI : NeZero C.base := ⟨by omega⟩
    intro h
    have h2 : ((2 : ℕ) : ZMod C.base) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at h2
    exact absurd (Nat.le_of_dvd (by norm_num) h2) (by omega)

/-- The regime in which a ladder over `L` bits computes its scalar, for the scalar's Type1
decode `z`: the whole ladder fits below the order (subwrap), or the top is below `4q - 4` over
an order `q` above `2^(L-1)`, where no accumulator meets `±T`. Every Pasta ladder is below the
bound: a pinned one tops out under `2^(L+1)`, an unpinned one reads a field element.
`varBaseMul_off`'s cases, at the law's list-level decode. -/
def HasCurve.LadderRegime [Field F] [DecidableEq F] (d : HasCurve F) (L : ℕ)
    (z : ℤ) : Prop :=
  3 * 2 ^ L ≤ d.W.order ∨ (2 ^ (L - 1) < d.W.order ∧ 3 < d.W.order ∧ z < 4 * d.W.order - 4)

/-- The regime in which the honest ladder over `L` bits has a satisfying witness: subwrap, or
the soundness bound over an order `q` in `(2^(L-1), 2^L)` with `3q < 2^(L+1)` and the top off
the three values `2q - 1`, `2q + 1`, `3q` at which an accumulator reaches `O`.
`chain_complete`'s cases. -/
def HasCurve.LadderCompleteRegime [Field F] [DecidableEq F] (d : HasCurve F) (L : ℕ)
    (z : ℤ) : Prop :=
  3 * 2 ^ L ≤ d.W.order ∨
    (3 ≤ L ∧ 2 ^ (L - 1) < d.W.order ∧ d.W.order < 2 ^ L ∧ 3 * d.W.order < 2 ^ (L + 1) ∧
      3 < d.W.order ∧ z < 4 * d.W.order - 4 ∧
      z ≠ 2 * d.W.order - 1 ∧ z ≠ 2 * d.W.order + 1 ∧ z ≠ 3 * d.W.order)

/-- A ladder that is satisfiable honestly also computes its scalar. -/
theorem HasCurve.LadderCompleteRegime.toLadderRegime [Field F] [DecidableEq F] {d : HasCurve F}
    {L : ℕ} {z : ℤ} (h : d.LadderCompleteRegime L z) : d.LadderRegime L z := by
  rcases h with h | ⟨-, h1, -, -, h3, hz, -⟩
  · exact Or.inl h
  · exact Or.inr ⟨h1, h3, hz⟩

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

/-- The dictionary the `EndoMul` laws close over: a `HasCurve` carrying the curve's GLV
endomorphism, together with the further field and order facts the `endoMul` law pair
consumes. The endomorphism itself is the wire's own record, `Pasta.EndoSpec`, rather than
a second copy of its coefficient, eigenvalue and GLV facts; `HasEndo.endo`, `HasEndo.lam`
and the three theorems below project them out under the names the laws use. -/
structure HasEndo (F : Type) [Field F] [DecidableEq F] extends HasCurve F where
  /-- The curve's GLV endomorphism, as the wire states it. -/
  spec : Pasta.EndoSpec W
  /-- The curve is smooth, so an on-curve point is nonsingular
  (`equation_iff_nonsingular_of_Δ_ne_zero`). -/
  delta_ne : W.Δ ≠ 0
  /-- The field does not have characteristic `3`. -/
  three_ne : (3 : F) ≠ 0
  /-- The order is not `3` either: with `odd`, both `2` and `3` are units in
  `ZMod order`, which lets the decompose tables be read in the scalar field. -/
  order_ne_three : W.order ≠ 3
  /-- The char window: integers below `2^127` in magnitude embed injectively in `F`,
  so bounded fold values with equal `F`-images are equal integers. -/
  char_big : ∀ z : ℤ, |z| < 2 ^ 127 → (z : F) = 0 → z = 0

/-- The gadget endomorphism dictionary of a Kimchi curve: its own curve and `EndoSpec`, with
the field and order bounds needed by the GLV laws. -/
@[reducible] def HasEndo.ofKimchiCurve (C : KimchiCurve)
    (hbase : 2 ^ 127 < C.base) (hscalar : 3 < C.scalar) : HasEndo C.BaseField where
  toHasCurve := HasCurve.ofCommitmentCurve C.toCommitmentCurve
    (lt_trans (by norm_num) hbase) (lt_trans (by norm_num) hscalar)
  spec := C.endo
  delta_ne := by
    show WeierstrassCurve.Δ (toW C.E.A C.E.B) ≠ 0
    rw [toW_Δ]
    exact C.E.IsElliptic.ne_zero
  three_ne := by
    haveI : Fact (Nat.Prime C.base) := C.primeBase
    intro h
    have h3 : ((3 : ℕ) : ZMod C.base) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at h3
    have := Nat.le_of_dvd (by norm_num) h3
    have : 3 < C.base := lt_trans (by norm_num) hbase
    omega
  order_ne_three := by rw [C.order_eq]; omega
  char_big := fun z hz h0 => by
    have hdvd : ((C.base : ℕ) : ℤ) ∣ z := (ZMod.intCast_zmod_eq_zero_iff_dvd z _).mp h0
    refine Int.eq_zero_of_abs_lt_dvd hdvd (lt_of_lt_of_le hz ?_)
    exact_mod_cast hbase.le

variable [Field F] [DecidableEq F]

/-- The endomorphism coefficient `β`: `φ(x, y) = (β·x, y)`. -/
@[reducible] def HasEndo.endo (d : HasEndo F) : F := d.spec.coeff

/-- The scalar eigenvalue `λ` of the endomorphism: `φ(T) = [λ]·T`. -/
@[reducible] def HasEndo.lam (d : HasEndo F) : ℤ := d.spec.lam

/-- The endomorphism maps the curve to itself. -/
theorem HasEndo.endo_nonsingular (d : HasEndo F) {x y : F} (h : d.W.Nonsingular x y) :
    d.W.Nonsingular (d.endo * x) y := d.spec.endo_nonsingular h

/-- The eigenvalue relation `φ(T) = [λ]·T` at every on-curve point. -/
theorem HasEndo.eigen (d : HasEndo F) {x y : F} (hT : d.W.Nonsingular x y)
    (hφT : d.W.Nonsingular (d.endo * x) y) :
    Point.some _ _ hφT = d.lam • Point.some _ _ hT := d.spec.eigen hT

/-- The GLV off-targets fact: a bounded nonzero two-base combination avoids `±T`, `±φT`. -/
theorem HasEndo.off_targets (d : HasEndo F) {a b : ℤ} (ha : a ≠ 0) (hb : b ≠ 0)
    (hba : |a| < 2 ^ 126) (hbb : |b| < 2 ^ 126) {T φT : d.W.Point} (hTne : T ≠ 0)
    (heig : φT = d.lam • T) :
    a • T + b • φT ≠ T ∧ a • T + b • φT ≠ -T ∧
      a • T + b • φT ≠ φT ∧ a • T + b • φT ≠ -φT :=
  d.spec.off_targets ha hb hba hbb hTne heig

/-- `[1 + λ]` does not kill a nonzero point — the init sum `T + φT` is finite. -/
theorem HasEndo.lam_succ_smul (d : HasEndo F) (T : d.W.Point) (hne : T ≠ 0) :
    (1 + d.lam) • T ≠ 0 := d.spec.lam_succ_smul T hne

/-! ## The deployed dictionaries -/

open CompElliptic.Curves.Pasta CompElliptic.Fields.Pasta Pasta in
/-- The curve dictionary at deployed Vesta — the curve the Schnorr statement's points live
on and the ladder's base group. -/
@[reducible] def HasCurve.vesta : HasCurve Fq :=
  HasCurve.ofCommitmentCurve Bulletproof.IpaVesta.curve.toCommitmentCurve (by decide) (by decide)

open CompElliptic.Curves.Pasta CompElliptic.Fields.Pasta Pasta in
/-- The curve dictionary at deployed Pallas, the step side's base group. -/
@[reducible] def HasCurve.pallas : HasCurve Fp :=
  HasCurve.ofCommitmentCurve Bulletproof.IpaPallas.curve.toCommitmentCurve (by decide) (by decide)

open CompElliptic.Fields.Pasta in
/-- At Vesta, every 255-bit ladder below `4·|Vesta| - 4` computes its scalar. -/
theorem HasCurve.vesta_ladderRegime (z : ℤ) (hz : z < 4 * PALLAS_BASE_CARD - 4) :
    HasCurve.vesta.LadderRegime 255 z := by
  have hOv : HasCurve.vesta.W.order = PALLAS_BASE_CARD := Pasta.vesta_card
  refine Or.inr ⟨?_, ?_, ?_⟩ <;> rw [hOv] <;> first | decide | exact hz

open CompElliptic.Fields.Pasta in
/-- At Pallas, likewise. -/
theorem HasCurve.pallas_ladderRegime (z : ℤ) (hz : z < 4 * PALLAS_SCALAR_CARD - 4) :
    HasCurve.pallas.LadderRegime 255 z := by
  have hOv : HasCurve.pallas.W.order = PALLAS_SCALAR_CARD := Pasta.pallas_card
  refine Or.inr ⟨?_, ?_, ?_⟩ <;> rw [hOv] <;> first | decide | exact hz

open CompElliptic.Curves.Pasta CompElliptic.Fields.Pasta Pasta in
/-- The endomorphism dictionary at deployed Pallas: `Pasta.pallasEndoSpec` over
`HasCurve.pallas`, and the field and order facts on top of it. -/
def HasEndo.pallas : HasEndo Fp :=
  HasEndo.ofKimchiCurve Bulletproof.IpaPallas.curve (by decide) (by decide)

open CompElliptic.Curves.Pasta CompElliptic.Fields.Pasta Pasta in
/-- The endomorphism dictionary at deployed Vesta — the other half of the 2-cycle. -/
@[reducible] def HasEndo.vesta : HasEndo Fq :=
  HasEndo.ofKimchiCurve Bulletproof.IpaVesta.curve (by decide) (by decide)

end Snarky.Kimchi
