/-
Axiom-closure gate for the Pasta trust base. This package DECLARES the curve axioms
(`Pasta.{pallas,vesta}_hasse`, `Pasta.{pallas,vesta}_eigen`); the gate checks that every
theorem DERIVED here reduces to the standard logical axioms + the Hasse bounds + the
CompElliptic point-count certificates and nothing else — in particular the eigen (CM)
axioms are consumed only downstream (kimchi's EndoMul), never by this package's own
derivations.

Run from `formal/pasta/`:  lake env lean scripts/check_axioms.lean
(or from `formal/`:        lake env lean pasta/scripts/check_axioms.lean)
-/
import Pasta
import Lean.Elab.Command

open Lean Lean.Elab.Command

namespace Pasta.CheckAxioms

/-- The derived trust-base theorems. -/
def roots : List Name :=
  [ `Pasta.pallas_card, `Pasta.vesta_card,
    `Pasta.pallas_order_prime, `Pasta.vesta_order_prime,
    `Pasta.pallas_glv_no_short_relation, `Pasta.vesta_glv_no_short_relation,
    `Pasta.vesta_smul_val, `Pasta.pallas_smul_val,
    `Pasta.Shifted.unshiftType1_shiftType1, `Pasta.Shifted.shiftType1_unshiftType1,
    `Pasta.Shifted.shiftType2_unshiftType2,
    `WeierstrassCurve.Affine.zsmul_mod, `WeierstrassCurve.Affine.order_smul ]

/-- Standard logical axioms, the Hasse bounds (declared here), and `Lean.ofReduceBool`
    (inherited from CompElliptic's `native_decide` order witnesses). NO eigen. -/
def allowed : List Name :=
  [ `propext, `Classical.choice, `Quot.sound, `Lean.ofReduceBool,
    `Pasta.pallas_hasse, `Pasta.vesta_hasse ]

/-- A CompElliptic `native_decide` point-count witness (trusted; see kimchi's gate). -/
def isTrustedNativeDecide (ax : Name) : Bool :=
  let s := ax.toString
  "CompElliptic.".isPrefixOf s && (s.splitOn "native_decide").length > 1

def isAllowed (ax : Name) : Bool := allowed.contains ax || isTrustedNativeDecide ax

end Pasta.CheckAxioms

run_cmd do
  let env ← getEnv
  let mut bad : Array (Name × Name) := #[]
  for root in Pasta.CheckAxioms.roots do
    unless env.contains root do
      throwError "axiom-check root not in environment: {root}"
    for ax in (← liftCoreM <| Lean.collectAxioms root) do
      unless Pasta.CheckAxioms.isAllowed ax do
        bad := bad.push (root, ax)
  if bad.isEmpty then
    IO.println s!"✓ all {Pasta.CheckAxioms.roots.length} Pasta roots reduce to the standard \
      axioms + the Hasse bounds + CompElliptic certificates (no eigen)"
  else
    for (r, a) in bad do
      IO.eprintln s!"::error::{r} depends on disallowed axiom {a}"
    throwError "disallowed axioms found ({bad.size})"
