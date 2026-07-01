/-
Copyright (c) 2025 O(1) Labs. Released under Apache 2.0 license.
-/
import Kimchi.Commitment.IPA.Correctness
import Kimchi.Commitment.IPA.Binding
import Kimchi.Pasta

/-!
# The IPA Polynomial Commitment over the Pasta Curves

This top module instantiates the generic IPA scheme of `Kimchi.Commitment.IPA.Basic`
at the two Pasta curves, Pallas and Vesta. The generic development is parametric over
an additive commitment group `G` with scalar field `F`; here `G` is a Pasta curve's
group of rational points (`Pallas.curve.toAffine.Point` / `Vesta.curve.toAffine.Point`,
the Mathlib affine point group supplied by CompElliptic) and `F` is the corresponding
scalar field (`PallasScalarField` / `VestaScalarField`). Nothing new is proved beyond
transporting the generic results across the instantiation.

## Layout

* `pallasPointModule` / `vestaPointModule` — the scalar-field module structure on each
  Pasta point group, built from `AddCommGroup.zmodModule` and the trusted point counts
  (`pallas_card` / `vesta_card`) via `order_smul`.
* `ipaPallas` / `ipaVesta` — the `Commitment.Scheme` instances.
* `ipaPallas_correctness` / `ipaVesta_correctness` — perfect completeness, specialized.
* `ipaPallas_binding` / `ipaVesta_binding` — evaluation binding, specialized.

## References

* [Halo] Bowe, Grigg, Hopwood, *Recursive Proof Composition without a Trusted Setup*, §3.
-/

namespace Kimchi.Commitment.IPA

open Commitment OracleSpec OracleComp ProtocolSpec
open CompElliptic.Curves.Pasta CompElliptic.Fields.Pasta
open Kimchi.Pasta
open scoped NNReal ENNReal

/-! ## The point group as a scalar-field module -/

/-- Every Pallas point is annihilated by `q = PALLAS_SCALAR_CARD`: `[q]P = O`. This is
the curve's generic `order_smul` fact specialized through the trusted Pallas point count
`pallas_card`, converting the integer scalar to a natural-number scalar. -/
lemma pallas_torsion (P : Pallas.curve.toAffine.Point) :
    (PALLAS_SCALAR_CARD : ℕ) • P = 0 := by
  have h := Pallas.curve.toAffine.order_smul P
  rw [pallas_card] at h
  rwa [natCast_zsmul] at h

/-- The Pallas point group carries a module structure over the Pallas scalar field
`ℤ/q = PallasScalarField`. Because the group has order `q` (the trusted point count
`pallas_card`), every point is `q`-torsion, and the canonical `ZMod q`-module structure
on an abelian group of exponent dividing `q` (`AddCommGroup.zmodModule`) supplies the
scalar action used by the Pedersen commitment. -/
noncomputable instance pallasPointModule :
    Module PallasScalarField Pallas.curve.toAffine.Point :=
  AddCommGroup.zmodModule (n := PALLAS_SCALAR_CARD) pallas_torsion

/-- Every Vesta point is annihilated by `p = PALLAS_BASE_CARD`: `[p]P = O`, by the
identical construction to `pallas_torsion`, using the trusted Vesta point count
`vesta_card`. -/
lemma vesta_torsion (P : Vesta.curve.toAffine.Point) :
    (PALLAS_BASE_CARD : ℕ) • P = 0 := by
  have h := Vesta.curve.toAffine.order_smul P
  rw [vesta_card] at h
  rwa [natCast_zsmul] at h

/-- The Vesta point group carries a module structure over the Vesta scalar field
`ℤ/p = VestaScalarField` (`= PallasBaseField`), by the identical construction to
`pallasPointModule`: the trusted point count `vesta_card` gives `[p]P = O`, whence the
canonical `ZMod p`-module structure of `AddCommGroup.zmodModule`. -/
noncomputable instance vestaPointModule :
    Module VestaScalarField Vesta.curve.toAffine.Point :=
  AddCommGroup.zmodModule (n := PALLAS_BASE_CARD) vesta_torsion

/-! ## The Pasta scheme instances -/

section Scheme

variable {d k : ℕ}

/-- Local oracle interface evaluating a coefficient vector as a polynomial: the query is a
point `z ∈ F`, and the answer is `p(z) = ∑ᵢ aᵢ zⁱ`. Declared here (defeq to the matching
instances in `Basic`/`Correctness`/`Binding`) so the specialized scheme and security
statements typecheck with the same `OracleInterface` that `ipa` carries. -/
local instance evalOracleInst {F : Type} [Field F] {d : ℕ} :
    OracleInterface (Fin d → F) where
  Query := F
  toOC.spec := F →ₒ F
  toOC.impl z := do
    let a ← read
    return ∑ i, a i * z ^ (i : ℕ)

/-- The IPA commitment scheme over the **Pallas** curve: the generic scheme `ipa` with
the commitment group `G` taken to be the Pallas point group and the scalar field `F`
taken to be the Pallas scalar field. Key generation samples the SRS generators uniformly
from the point group, so the instantiation carries `[SampleableType Pallas.curve.toAffine.Point]`
as a hypothesis (building the finite enumeration of curve points is curve infrastructure
beyond this development). The type (a `Commitment.Scheme` over the Pallas data) is inherited
from `ipa`, including the coefficient-vector evaluation `OracleInterface`. -/
noncomputable def ipaPallas [SampleableType Pallas.curve.toAffine.Point] :=
  ipa (F := PallasScalarField) (G := Pallas.curve.toAffine.Point) (d := d) (k := k)

/-- The IPA commitment scheme over the **Vesta** curve: the generic scheme `ipa` with the
commitment group `G` the Vesta point group and the scalar field `F` the Vesta scalar
field. Carries `[SampleableType Vesta.curve.toAffine.Point]` as a hypothesis, exactly as
for Pallas; the type is inherited from `ipa`. -/
noncomputable def ipaVesta [SampleableType Vesta.curve.toAffine.Point] :=
  ipa (F := VestaScalarField) (G := Vesta.curve.toAffine.Point) (d := d) (k := k)

/-! ## Security at the Pasta curves -/

/-- **Perfect completeness over Pallas** (Halo, §3, Theorem 1). The Pallas IPA scheme of
`ipaPallas` satisfies `Commitment.perfectCorrectness`. Specializes the generic
`ipa_correctness` at the Pallas point group and scalar field; the body is `sorry` at this
scaffold stage. -/
theorem ipaPallas_correctness [SampleableType Pallas.curve.toAffine.Point]
    [[(pSpec PallasScalarField Pallas.curve.toAffine.Point k).Challenge]ₒ.Inhabited]
    [[(pSpec PallasScalarField Pallas.curve.toAffine.Point k).Challenge]ₒ.Fintype]
    [∀ i, VCVCompatible
      ((pSpec PallasScalarField Pallas.curve.toAffine.Point k).Challenge i)]
    [∀ i, SampleableType
      ((pSpec PallasScalarField Pallas.curve.toAffine.Point k).Challenge i)]
    (hd : d = 2 ^ k) :
    Commitment.perfectCorrectness (init := pure ∅) (impl := randomOracle)
      (ipaPallas (d := d) (k := k)) :=
  Correctness.ipa_correctness (F := PallasScalarField)
    (G := Pallas.curve.toAffine.Point) (d := d) (k := k) hd

/-- **Evaluation binding over Pallas** (Halo, §3, Theorem 1). The Pallas IPA scheme of
`ipaPallas` satisfies `Commitment.binding` with error `dlError`, provided the discrete
log relation assumption holds with that error. Specializes the generic `ipa_binding`; the
body is `sorry` at this scaffold stage. -/
theorem ipaPallas_binding [SampleableType Pallas.curve.toAffine.Point]
    [∀ i, VCVCompatible
      ((pSpec PallasScalarField Pallas.curve.toAffine.Point k).Challenge i)]
    [∀ i, SampleableType
      ((pSpec PallasScalarField Pallas.curve.toAffine.Point k).Challenge i)]
    [[(pSpec PallasScalarField Pallas.curve.toAffine.Point k).Challenge]ₒ.Inhabited]
    [[(pSpec PallasScalarField Pallas.curve.toAffine.Point k).Challenge]ₒ.Fintype]
    (dlError : ℝ≥0)
    (hdl : Binding.dlRelationAssumption
      (F := PallasScalarField) (G := Pallas.curve.toAffine.Point) d dlError) :
    Commitment.binding (init := pure ∅) (impl := randomOracle)
      (ipaPallas (d := d) (k := k)) dlError :=
  Binding.ipa_binding (F := PallasScalarField)
    (G := Pallas.curve.toAffine.Point) (d := d) (k := k) dlError hdl

/-- **Perfect completeness over Vesta** (Halo, §3, Theorem 1). Identical to the Pallas
case, specializing the generic `ipa_correctness` at the Vesta point group and scalar
field; the body is `sorry` at this scaffold stage. -/
theorem ipaVesta_correctness [SampleableType Vesta.curve.toAffine.Point]
    [[(pSpec VestaScalarField Vesta.curve.toAffine.Point k).Challenge]ₒ.Inhabited]
    [[(pSpec VestaScalarField Vesta.curve.toAffine.Point k).Challenge]ₒ.Fintype]
    [∀ i, VCVCompatible
      ((pSpec VestaScalarField Vesta.curve.toAffine.Point k).Challenge i)]
    [∀ i, SampleableType
      ((pSpec VestaScalarField Vesta.curve.toAffine.Point k).Challenge i)]
    (hd : d = 2 ^ k) :
    Commitment.perfectCorrectness (init := pure ∅) (impl := randomOracle)
      (ipaVesta (d := d) (k := k)) :=
  Correctness.ipa_correctness (F := VestaScalarField)
    (G := Vesta.curve.toAffine.Point) (d := d) (k := k) hd

/-- **Evaluation binding over Vesta** (Halo, §3, Theorem 1). Identical to the Pallas case,
specializing the generic `ipa_binding` at the Vesta point group and scalar field; the body
is `sorry` at this scaffold stage. -/
theorem ipaVesta_binding [SampleableType Vesta.curve.toAffine.Point]
    [∀ i, VCVCompatible
      ((pSpec VestaScalarField Vesta.curve.toAffine.Point k).Challenge i)]
    [∀ i, SampleableType
      ((pSpec VestaScalarField Vesta.curve.toAffine.Point k).Challenge i)]
    [[(pSpec VestaScalarField Vesta.curve.toAffine.Point k).Challenge]ₒ.Inhabited]
    [[(pSpec VestaScalarField Vesta.curve.toAffine.Point k).Challenge]ₒ.Fintype]
    (dlError : ℝ≥0)
    (hdl : Binding.dlRelationAssumption
      (F := VestaScalarField) (G := Vesta.curve.toAffine.Point) d dlError) :
    Commitment.binding (init := pure ∅) (impl := randomOracle)
      (ipaVesta (d := d) (k := k)) dlError :=
  Binding.ipa_binding (F := VestaScalarField)
    (G := Vesta.curve.toAffine.Point) (d := d) (k := k) dlError hdl

end Scheme

end Kimchi.Commitment.IPA
