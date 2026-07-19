/-
No-op gate for the Circuit module refactor: dumps each check-axioms root's TYPE and full axiom
closure, one stable line per root. Capture before a refactor, re-run after, and diff: identical
output (plus a green build) means the restructure changed no statement and no proof's trusted base.

Run from `formal/`:  lake env lean scripts/refactor_baseline.lean
-/
import Kimchi
open Lean Lean.Elab.Command

namespace Kimchi.RefactorBaseline

def roots : List Name :=
  [ `Kimchi.Gate.Generic.sound, `Kimchi.Gate.Generic.complete,
    `Kimchi.Gate.AddComplete.sound_noninf, `Kimchi.Gate.AddComplete.complete_noninf,
    `Kimchi.Gate.AddComplete.sound_point_noninf, `Kimchi.Gate.AddComplete.sound_point_inf,
    `Kimchi.Gate.AddComplete.ok_iff, `Kimchi.Gate.AddComplete.inf_boolean,
    `Kimchi.Gate.AddComplete.complete_inf, `Kimchi.Gate.AddComplete.complete,
    `Kimchi.Gate.AddComplete.sound,
    `Kimchi.Gate.VarBaseMul.sound, `Kimchi.Gate.VarBaseMul.complete,
    `Kimchi.Gate.VarBaseMul.varBaseMul_forbidden_correct,
    `Kimchi.Gate.VarBaseMul.varBaseMul_subwrap_correct,
    `Kimchi.Gate.VarBaseMul.varBaseMul_scaleFast1,
    `Kimchi.Gate.VarBaseMul.varBaseMul_scaleFast2,
    `Kimchi.Gate.EndoScalar.sound, `Kimchi.Gate.EndoScalar.complete,
    `Kimchi.Gate.EndoScalar.chain_toField,
    `Kimchi.Gate.EndoScalar.chain_complete,
    `Kimchi.Gate.EndoScalar.endoScalar_unique,
    `Kimchi.Gate.EndoMul.sound, `Kimchi.Gate.EndoMul.complete,
    `Kimchi.Gate.EndoMul.endoMul,
    `Kimchi.Gate.EndoMul.pallas_endoMul, `Kimchi.Gate.EndoMul.vesta_endoMul,
    `Kimchi.Gate.EndoMul.pallas_combo_off_targets,
    `Kimchi.Gate.EndoMul.vesta_combo_off_targets ]

end Kimchi.RefactorBaseline

run_cmd do
  let env ← getEnv
  for root in Kimchi.RefactorBaseline.roots do
    let some ci := env.find? root | throwError "baseline root not in environment: {root}"
    let typeStr ← liftTermElabM do
      let fmt ← Lean.Meta.ppExpr ci.type
      pure ((toString fmt).replace "\n" " ")
    let axs ← liftCoreM <| Lean.collectAxioms root
    let axStr := String.intercalate "," ((axs.qsort (·.lt ·)).toList.map toString)
    IO.println s!"{root} :: {typeStr} :: [{axStr}]"
