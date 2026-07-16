/-
Axiom-closure gate for the Pasta trust base. This package DECLARES the curve axioms
(`Pasta.{pallas,vesta}_hasse`); the gate checks that every
theorem DERIVED here reduces to the standard logical axioms + the Hasse bounds + the
trusted `native_decide` certificates and nothing else — the CM eigenvalue relations
(`pallas_eigen`/`vesta_eigen`) are THEOREMS here, not axioms.

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
    `WeierstrassCurve.Affine.order_smul,
    `Pasta.pallas_eigen, `Pasta.vesta_eigen ]

/-- Standard logical axioms, the Hasse bounds (declared here), and `Lean.ofReduceBool`
    (the `native_decide` witnesses: CompElliptic's order counts + this package's two
    eigenvalue anchors). NO eigen. -/
def allowed : List Name :=
  [ `propext, `Classical.choice, `Quot.sound, `Lean.ofReduceBool,
    `Pasta.pallas_hasse, `Pasta.vesta_hasse ]

/-- A trusted `native_decide` certificate: CompElliptic's point-count witnesses, or this
    package's two eigenvalue anchors (`Pasta.{pallas,vesta}_lam_nsmul_Gpt` in
    `Pasta/Endo.lean`) — exactly those declarations, by name. Any other `native_decide`
    in our tree is still rejected. -/
def isTrustedNativeDecide (ax : Name) : Bool :=
  let s := ax.toString
  (s.splitOn "native_decide").length > 1 &&
    ("CompElliptic.".isPrefixOf s
      || "Pasta.pallas_lam_nsmul_Gpt.".isPrefixOf s
      || "Pasta.vesta_lam_nsmul_Gpt.".isPrefixOf s)

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
      axioms + the Hasse bounds + trusted native_decide certificates (no eigen)"
  else
    for (r, a) in bad do
      IO.eprintln s!"::error::{r} depends on disallowed axiom {a}"
    throwError "disallowed axioms found ({bad.size})"
