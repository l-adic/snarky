/-
Axiom-closure gate for the schnorr exemplar: every root reduces to the three standard
axioms (`propext`, `Classical.choice`, `Quot.sound`), except the deployed endpoint
laws, which may additionally carry the certified `native_decide` witnesses of the
Pasta trust base. Run from `schnorr/`:

  lake env lean scripts/check_axioms.lean

A removed or renamed root fails loudly (`axiom-check root not in environment`).
-/
import Schnorr
import Lean.Elab.Command

open Lean Lean.Elab.Command

namespace Schnorr.CheckAxioms

/-- The exemplar's audited surface: the wire protocol, and the canonical decomposition's
law pairs. -/
def roots : List Name :=
  [ `Schnorr.gen,
    `Schnorr.transcriptHash,
    `Schnorr.preChallenge,
    `Schnorr.verify,
    `Schnorr.challenge,
    `Schnorr.verify_iff,
    `Schnorr.completeness,
    `Schnorr.ltBitstringValue_spec,
    `Schnorr.ltBitstringValue_complete,
    `Schnorr.assertBitsBelow_spec,
    `Schnorr.assertBitsBelow_complete,
    `Schnorr.unpackFull_spec,
    `Schnorr.unpackFull_complete,
    `Schnorr.verifyCircuit_spec,
    `Schnorr.verifyCircuit_complete,
    `Schnorr.verifyCircuit_compile_sound,
    `Schnorr.verifyCircuit_solve_complete ]

/-- The allowed axioms. -/
def allowed : List Name := [`propext, `Classical.choice, `Quot.sound]

/-- The verifier acts by `Fp`-scalars through the point group's module structure,
    which rests on the certified Vesta order; the endpoint laws concretize at the
    deployed Pasta dictionaries. Their closures carry the certified `native_decide`
    witnesses (orders and eigenvalue anchors). Everything else stays pure core Lean. -/
def deployedRoots : List Name :=
  [ `Schnorr.verify,
    `Schnorr.verify_iff,
    `Schnorr.completeness,
    `Schnorr.verifyCircuit_spec,
    `Schnorr.verifyCircuit_complete,
    `Schnorr.verifyCircuit_compile_sound,
    `Schnorr.verifyCircuit_solve_complete ]

/-- A trusted `native_decide` certificate, discriminated by DEFINING MODULE rather
    than by name prefix (the snarky gate's convention): an upstream CompElliptic
    module, or `Pasta/Endo.lean` — the one tree file declared to hold the two GLV
    eigenvalue anchors. -/
def isTrustedNativeDecide (env : Environment) (ax : Name) : Bool :=
  (ax.toString.splitOn "native_decide").length > 1 &&
    match env.getModuleFor? ax with
    | some m => (`CompElliptic).isPrefixOf m || m == `Pasta.Endo
    | none => false

end Schnorr.CheckAxioms

run_cmd do
  let env ← getEnv
  let mut bad : Array (Name × Name) := #[]
  for root in Schnorr.CheckAxioms.roots do
    unless env.contains root do
      throwError "axiom-check root not in environment: {root}"
    for ax in (← liftCoreM <| Lean.collectAxioms root) do
      unless Schnorr.CheckAxioms.allowed.contains ax ||
          (Schnorr.CheckAxioms.deployedRoots.contains root &&
            Schnorr.CheckAxioms.isTrustedNativeDecide env ax) do
        bad := bad.push (root, ax)
  if bad.isEmpty then
    IO.println s!"✓ all {Schnorr.CheckAxioms.roots.length} Schnorr roots reduce to \
      {Schnorr.CheckAxioms.allowed} (deployed endpoint + certified native_decide)"
  else
    for (r, a) in bad do
      IO.eprintln s!"::error::{r} depends on disallowed axiom {a}"
    throwError "disallowed axioms found ({bad.size})"
