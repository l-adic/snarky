/-
Axiom-closure gate for the Snarky DSL library: the interpreter laws must be proved from
the standard logical axioms alone — the deep embedding is pure core Lean, so nothing else
(no `sorryAx`, no `native_decide`, no curve axioms) may appear in their closures.

The root list is a deletion guard as well as an axiom guard: a name absent from the environment
fails with `axiom-check root not in environment`, so removing a listed declaration — even
together with its `roots.txt` line — cannot pass silently.

Run from `formal/snarky/`:  lake env lean scripts/check_axioms.lean
-/
import Snarky
import Lean.Elab.Command

open Lean Lean.Elab.Command

namespace Snarky.CheckAxioms

/-- The headline interpreter and gadget laws (beside their interpreters and gadgets). -/
def roots : List Name :=
  [ `Snarky.build_eraseWitness,
    `Snarky.prove_assignments_le,
    `Snarky.prove_build_agrees,
    `Snarky.prove_complete,
    `Snarky.CVar.eval_le,
    `Snarky.build_bind,
    `Snarky.prove_bind,
    `Snarky.equals_sound,
    `Snarky.equals_complete,
    `Snarky.mul_sound,
    `Snarky.mul_complete,
    `Snarky.inv_sound,
    `Snarky.inv_complete,
    `Snarky.inv_spec,
    `Snarky.inv_complete_spec,
    `Snarky.square_sound,
    `Snarky.square_complete,
    `Snarky.div_sound,
    `Snarky.div_complete,
    `Snarky.pow_sound,
    `Snarky.pow_complete,
    `Snarky.sum_eval,
    `Snarky.not_eval,
    `Snarky.neq_sound,
    `Snarky.neq_complete,
    `Snarky.and_sound,
    `Snarky.and_complete,
    `Snarky.or_sound,
    `Snarky.or_complete,
    `Snarky.xor_sound,
    `Snarky.xor_complete,
    `Snarky.select_sound,
    `Snarky.select_complete,
    `Snarky.assertEqual_spec,
    `Snarky.assertEqual_complete_spec,
    `Snarky.assertNonZero_spec,
    `Snarky.assertNonZero_complete_spec,
    `Snarky.assertNotEqual_spec,
    `Snarky.assertNotEqual_complete_spec,
    `Snarky.assertSquare_spec,
    `Snarky.assertSquare_complete_spec,
    `Snarky.assert_spec,
    `Snarky.assert_complete_spec,
    `Snarky.pack_eval,
    `Snarky.packPure_unpackPure,
    `Snarky.unpack_sound,
    `Snarky.unpack_complete,
    `Snarky.solve_complete,
    `Snarky.readVar_le,
    `Snarky.CVar.reduce_eval,
    `Snarky.fvar_value_roundTrip,
    `Snarky.fvar_var_roundTrip,
    `Snarky.boolVar_value_roundTrip,
    `Snarky.boolVar_var_roundTrip,
    `Snarky.build_eq_of_eraseWitness,
    `Snarky.CircuitM.instLawfulMonad ]

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
