import Pasta.Basic

/-!
# The scalar action on the Pasta point groups

Each Pasta point group is a module over its scalar field: the group is prime-order
(its cardinality is the scalar-field cardinality, under the Hasse axiom), so it is
torsion at that prime and `AddCommGroup.zmodModule` equips it with the `ZMod`-module
structure. The action is definitionally the ℕ-action at the canonical representative
(`{vesta,pallas}_smul_val` — `rfl`), which is the form the executable verifiers
compute with.
-/

namespace Pasta

open CompElliptic.CurveForms.ShortWeierstrass CompElliptic.Curves.Pasta
open CompElliptic.Curves.Pasta.Vesta renaming curve → vestaCurve
open CompElliptic.Curves.Pasta.Pallas renaming curve → pallasCurve
open CompElliptic.Fields.Pasta

/-- The Vesta point group is `PALLAS_BASE_CARD`-torsion (its group order, under the Hasse
axiom), hence a module over its scalar field. The action is definitionally `z.val • _`. -/
instance vestaPointModule : Module Fp (SWPoint vestaCurve) :=
  AddCommGroup.zmodModule fun P => by
    rw [← Vesta.card_eq Pasta.vesta_hasse]
    exact card_nsmul_eq_zero'

/-- The Pallas point group is `PALLAS_SCALAR_CARD`-torsion (its group order, under the
Hasse axiom), hence a module over its scalar field. -/
instance pallasPointModule : Module Fq (SWPoint pallasCurve) :=
  AddCommGroup.zmodModule fun P => by
    rw [← Pallas.card_eq Pasta.pallas_hasse]
    exact card_nsmul_eq_zero'

/-- The module action is the ℕ-action at the canonical representative — the form the
executable verifiers compute with. -/
theorem vesta_smul_val (z : Fp) (P : SWPoint vestaCurve) : z • P = z.val • P :=
  rfl

theorem pallas_smul_val (z : Fq) (P : SWPoint pallasCurve) : z • P = z.val • P :=
  rfl

end Pasta
