/-
Axiom-closure gate for the Kimchi formalization.

`lake build` succeeds even with `sorry` (it is only a warning), so this script gates the headline
theorems explicitly: it collects the full axiom closure of each root and fails unless every axiom
is in the allowlist below — the three standard logical axioms plus the two trusted Pasta
point-count axioms (`Kimchi.Pasta.{pallas_card, vesta_card}`). This subsumes the old `sorryAx`
grep: a `sorry` shows up as `sorryAx`, which is not in the allowlist, and any *other* stray axiom
that slips into a proof is caught too.

Run from `formal/`:  lake env lean scripts/check_axioms.lean   (or: scripts/check_axioms.sh)
-/
import Kimchi

open Lean Lean.Elab.Command

namespace Kimchi.CheckAxioms

/-- The headline theorems whose axiom closure must stay clean. -/
def roots : List Name :=
  [ `Kimchi.Gate.Generic.sound, `Kimchi.Gate.Generic.complete,
    `Kimchi.Gate.AddComplete.sound_noninf, `Kimchi.Gate.AddComplete.complete_noninf,
    `Kimchi.Gate.AddComplete.sound_point_noninf, `Kimchi.Gate.AddComplete.sound_point_inf,
    `Kimchi.Gate.AddComplete.ok_iff, `Kimchi.Gate.AddComplete.inf_boolean,
    `Kimchi.Gate.AddComplete.complete_inf, `Kimchi.Gate.AddComplete.complete,
    `Kimchi.Gate.AddComplete.sound,
    `Kimchi.Gate.VarBaseMul.sound, `Kimchi.Gate.VarBaseMul.complete,
    `WeierstrassCurve.Affine.zsmul_mod, `WeierstrassCurve.Affine.order_smul,
    `Kimchi.Circuit.VarBaseMul.varBaseMul_deployed_correct,
    `Kimchi.Circuit.VarBaseMul.varBaseMul_forbidden_correct,
    `Kimchi.Circuit.VarBaseMul.varBaseMul_subwrap_correct,
    `Kimchi.Circuit.VarBaseMul.varBaseMul_scaleFast1,
    `Kimchi.Circuit.VarBaseMul.varBaseMul_scaleFast2,
    `Kimchi.Gate.EndoScalar.sound, `Kimchi.Gate.EndoScalar.complete,
    `Kimchi.Circuit.EndoScalar.chain_toField,
    `Kimchi.Circuit.EndoScalar.chain_complete,
    `Kimchi.Circuit.EndoScalar.endoScalar_unique,
    `Kimchi.Gate.EndoMul.sound, `Kimchi.Gate.EndoMul.complete,
    `Kimchi.Circuit.EndoMul.endoMul,
    `Kimchi.Circuit.EndoMul.pallas_endoMul, `Kimchi.Circuit.EndoMul.vesta_endoMul,
    `Kimchi.Circuit.EndoMul.pallas_combo_off_targets,
    `Kimchi.Circuit.EndoMul.vesta_combo_off_targets ]

/-- The only axioms the roots may depend on: the standard logical axioms, the trusted Pasta
    point counts, and the Pasta GLV endomorphism inputs (`β`, `λ`, the CM eigenvalue relation,
    and the GLV short-basis bound). -/
def allowed : List Name :=
  [ `propext, `Classical.choice, `Quot.sound,
    `Kimchi.Pasta.pallas_card, `Kimchi.Pasta.vesta_card,
    `Kimchi.Pasta.pallas_endo, `Kimchi.Pasta.pallas_lam, `Kimchi.Pasta.pallas_eigen,
    `Kimchi.Pasta.pallas_glv_no_short_relation,
    `Kimchi.Pasta.vesta_endo, `Kimchi.Pasta.vesta_lam, `Kimchi.Pasta.vesta_eigen,
    `Kimchi.Pasta.vesta_glv_no_short_relation ]

end Kimchi.CheckAxioms

run_cmd do
  let env ← getEnv
  let mut bad : Array (Name × Name) := #[]
  for root in Kimchi.CheckAxioms.roots do
    unless env.contains root do
      throwError "axiom-check root not in environment: {root}"
    for ax in (← liftCoreM <| Lean.collectAxioms root) do
      unless Kimchi.CheckAxioms.allowed.contains ax do
        bad := bad.push (root, ax)
  if bad.isEmpty then
    IO.println s!"✓ all {Kimchi.CheckAxioms.roots.length} roots reduce to the allowed axiom set \
      {Kimchi.CheckAxioms.allowed}"
  else
    for (r, a) in bad do
      IO.eprintln s!"::error::{r} depends on disallowed axiom {a}"
    throwError "disallowed axioms found ({bad.size})"
