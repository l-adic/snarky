/-
Axiom-closure gate for the Snarky DSL library: the interpreter laws must be proved from
the standard logical axioms alone — the deep embedding is pure core Lean, so nothing else
(no `sorryAx`, no `native_decide`, no curve axioms) may appear in their closures.

Run from `formal/snarky/`:  lake env lean scripts/check_axioms.lean
-/
import Snarky
import Lean.Elab.Command

open Lean Lean.Elab.Command

namespace Snarky.CheckAxioms

/-- The headline interpreter laws (see `Snarky/Laws.lean`). -/
def roots : List Name :=
  [ `Snarky.build_eraseWitness,
    `Snarky.prove_assignments_le,
    `Snarky.prove_build_agrees,
    `Snarky.prove_sound,
    `Snarky.CVar.eval_le ]

/-- Pure core Lean: only the three standard logical axioms are permitted. -/
def allowed : List Name := [`propext, `Classical.choice, `Quot.sound]

end Snarky.CheckAxioms

run_cmd do
  let env ← getEnv
  let mut bad : Array (Name × Name) := #[]
  for root in Snarky.CheckAxioms.roots do
    unless env.contains root do
      throwError "axiom-check root not in environment: {root}"
    for ax in (← liftCoreM <| Lean.collectAxioms root) do
      unless Snarky.CheckAxioms.allowed.contains ax do
        bad := bad.push (root, ax)
  if bad.isEmpty then
    IO.println s!"✓ all {Snarky.CheckAxioms.roots.length} Snarky roots reduce to \
      {Snarky.CheckAxioms.allowed}"
  else
    for (r, a) in bad do
      IO.eprintln s!"::error::{r} depends on disallowed axiom {a}"
    throwError "disallowed axioms found ({bad.size})"
