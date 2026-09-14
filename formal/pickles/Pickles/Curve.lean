import Snarky.Kimchi.Circuit.VarBaseMul
import Bulletproof.Wire
import Pasta.Basic

/-!
# The gadget layer's curve dictionary of a commitment curve

The gadget theorems (`Snarky.Kimchi.*`) are stated over `HasCurve F`, a Mathlib affine curve
with the four facts the gate semantics consume; the wire verifier is stated over
`CommitmentCurve`, CompElliptic's `SWCurve` with its scalar order. The two describe one curve:
`C.E.toAffine` is the affine form and `SWPoint.equivPoint` the group isomorphism. This module
is the map from the second to the first, so an assembly stated over a `CommitmentCurve` derives
its gadget dictionary instead of asking for the coupling as fields.

## Main definitions

* `HasCurve.ofCommitmentCurve` — the dictionary of a commitment curve, at the bounds `2 < base`
  and `2 < scalar` that rule out characteristic `2` and a 2-torsion group.
* `PastaShape` — the deployed shape of a commitment curve, and `PastaShape.d` its dictionary.
  `pastaShapeVesta` and `pastaShapePallas` are the two witnesses.

## Main results

* `CommitmentCurve.order_eq` — the affine group's order is the scalar cardinality.
* `CommitmentCurve.affine_card_nsmul` — the scalar order kills the affine group.
-/

namespace Pickles

open CompElliptic.CurveForms.ShortWeierstrass Bulletproof.Ipa Snarky.Kimchi
open CompElliptic.Fields.Pasta

/-- The affine group's order is the wire's scalar cardinality. -/
theorem _root_.Bulletproof.Ipa.CommitmentCurve.order_eq (C : CommitmentCurve) :
    C.E.toAffine.order = C.scalar :=
  (SWPoint.card_eq_point C.E).symm.trans C.card

/-- The scalar order kills the affine group (Lagrange). -/
theorem _root_.Bulletproof.Ipa.CommitmentCurve.affine_card_nsmul (C : CommitmentCurve)
    (X : C.E.toAffine.Point) : C.scalar • X = 0 := by
  rw [← C.order_eq]; exact card_nsmul_eq_zero'

/-- The gadget layer's curve dictionary of a commitment curve: the affine form of `C.E`, short
by `C.a_zero`, of prime order by `C.card`, and off characteristic `2` and 2-torsion by the two
bounds.

Reducible, and a structure literal: consumers state their premises over `d.W`, and instance
search runs at reducible transparency, so `d.W` has to reduce to `C.E.toAffine` there. The
projection is iota on the literal, so the proof fields are never forced. -/
@[reducible] noncomputable def _root_.Snarky.Kimchi.HasCurve.ofCommitmentCurve
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

/-- The deployed shape of a commitment curve: the base field's width, and the scalar order's —
255 bits, below `2^254 + 2^253`, and `1 mod 4`. Facts about `C` alone, so the sides of the
cycle state them once here rather than each restating them. Not fields of `CommitmentCurve`:
a commitment curve in general has no 255-bit scalar order, and the wire package is generic
over any of them. -/
structure PastaShape (C : CommitmentCurve) : Prop where
  /-- The base field has more than 254 bits: a `2^254`-bounded integer casts faithfully. -/
  base_big : 2 ^ 254 < C.base
  /-- The scalar order has 255 bits. -/
  scalar_lo : 2 ^ 254 < C.scalar
  /-- The scalar order is below `2^254 + 2^253`: the pinned full ladder wraps exactly twice. -/
  scalar_hi : C.scalar < 2 ^ 254 + 2 ^ 253
  /-- The scalar order is `1 mod 4`, as the one-wrap ladder regime asks. -/
  scalar_mod : C.scalar % 4 = 1

/-- The gadget dictionary at a shaped curve: the 254-bit bounds weakened to the `2 <` ones
`HasCurve.ofCommitmentCurve` asks for. -/
@[reducible] noncomputable def PastaShape.d {C : CommitmentCurve} (s : PastaShape C) :
    HasCurve C.BaseField :=
  HasCurve.ofCommitmentCurve C (lt_trans (by norm_num) s.base_big)
    (lt_trans (by norm_num) s.scalar_lo)

/-- Vesta has the shape: base `PALLAS_SCALAR_CARD`, scalar order `PALLAS_BASE_CARD`. -/
theorem pastaShapeVesta : PastaShape Bulletproof.IpaVesta.curve where
  base_big := by norm_num [PALLAS_SCALAR_CARD]
  scalar_lo := by norm_num [PALLAS_BASE_CARD]
  scalar_hi := by norm_num [PALLAS_BASE_CARD]
  scalar_mod := by norm_num [PALLAS_BASE_CARD]

/-- Pallas has the shape: base `PALLAS_BASE_CARD`, scalar order `PALLAS_SCALAR_CARD`. -/
theorem pastaShapePallas : PastaShape Bulletproof.IpaPallas.curve where
  base_big := by norm_num [PALLAS_BASE_CARD]
  scalar_lo := by norm_num [PALLAS_SCALAR_CARD]
  scalar_hi := by norm_num [PALLAS_SCALAR_CARD]
  scalar_mod := by norm_num [PALLAS_SCALAR_CARD]

end Pickles
