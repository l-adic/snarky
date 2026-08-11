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
    `Snarky.equals_spec,
    `Snarky.equals_complete_spec,
    `Snarky.mul_spec,
    `Snarky.mul_complete_spec,
    `Snarky.inv_spec,
    `Snarky.inv_complete_spec,
    `Snarky.div_spec,
    `Snarky.div_complete_spec,
    `Snarky.square_spec,
    `Snarky.square_complete_spec,
    `Snarky.pow_spec,
    `Snarky.pow_complete_spec,
    `Snarky.sum_eval,
    `Snarky.not_eval,
    `Snarky.neq_spec,
    `Snarky.neq_complete_spec,
    `Snarky.and_spec,
    `Snarky.and_complete_spec,
    `Snarky.or_spec,
    `Snarky.or_complete_spec,
    `Snarky.xor_spec,
    `Snarky.xor_complete_spec,
    `Snarky.select_spec,
    `Snarky.select_complete_spec,
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
    `Snarky.invCore_spec,
    `Snarky.any_spec,
    `Snarky.any_complete_spec,
    `Snarky.all_spec,
    `Snarky.all_complete_spec,
    `Snarky.allBools_spec,
    `Snarky.allBools_complete_spec,
    `Snarky.assertAny_spec,
    `Snarky.assertAny_complete_spec,
    `Snarky.assertAll_spec,
    `Snarky.assertAll_complete_spec,
    `Snarky.assertExactlyOne_spec,
    `Snarky.assertExactlyOne_complete_spec,
    `Snarky.pack_eval,
    `Snarky.packPure_unpackPure,
    `Snarky.unpack_spec,
    `Snarky.unpack_complete_spec,
    `Snarky.post_of_prove,
    `Snarky.mul_agrees,
    `Snarky.inv_agrees,
    `Snarky.div_agrees,
    `Snarky.square_agrees,
    `Snarky.pow_agrees,
    `Snarky.equals_agrees,
    `Snarky.neq_agrees,
    `Snarky.xor_agrees,
    `Snarky.select_agrees,
    `Snarky.unpack_agrees,
    `Snarky.assertEqual_agrees,
    `Snarky.assertNonZero_agrees,
    `Snarky.addConstraint_spec,
    `Snarky.addConstraint_complete_spec,
    `Snarky.witnessBool_spec,
    `Snarky.witnessBool_complete_spec,
    `Snarky.generateVec_spec,
    `Snarky.generateVec_complete_spec,
    `Snarky.Example.cubic_spec,
    `Snarky.Example.cubic_complete_spec,
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
