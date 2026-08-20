/-
Axiom-closure gate for the schnorr exemplar: every root reduces to the three standard
axioms (`propext`, `Classical.choice`, `Quot.sound`). Run from `schnorr/`:

  lake env lean scripts/check_axioms.lean

A removed or renamed root fails loudly (`axiom-check root not in environment`).
-/
import Schnorr
import Lean.Elab.Command

open Lean Lean.Elab.Command

namespace Schnorr.CheckAxioms

/-- The exemplar's audited surface. -/
def roots : List Name :=
  [ `Schnorr.gen,
    `Schnorr.squeezeFieldElement,
    `Schnorr.preChallenge,
    `Schnorr.verify,
    `Schnorr.verifyRelaxed,
    `Schnorr.verify_imp_verifyRelaxed,
    `Schnorr.squeezeFieldElement_eq,
    `Schnorr.verifyCircuit,
    `Schnorr.squeezeTranscript_spec,
    `Schnorr.squeezeTranscript_complete_spec ]

/-- The allowed axioms. -/
def allowed : List Name := [`propext, `Classical.choice, `Quot.sound]

end Schnorr.CheckAxioms

run_cmd do
  let env ← getEnv
  let mut bad : Array (Name × Name) := #[]
  for root in Schnorr.CheckAxioms.roots do
    unless env.contains root do
      throwError "axiom-check root not in environment: {root}"
    for ax in (← liftCoreM <| Lean.collectAxioms root) do
      unless Schnorr.CheckAxioms.allowed.contains ax do
        bad := bad.push (root, ax)
  if bad.isEmpty then
    IO.println s!"✓ all {Schnorr.CheckAxioms.roots.length} Schnorr roots reduce to \
      {Schnorr.CheckAxioms.allowed}"
  else
    for (r, a) in bad do
      IO.eprintln s!"::error::{r} depends on disallowed axiom {a}"
    throwError "disallowed axioms found ({bad.size})"
