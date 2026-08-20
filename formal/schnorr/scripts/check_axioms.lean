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

/-- The exemplar's audited surface. -/
def roots : List Name :=
  [ `Schnorr.gen,
    `Schnorr.transcriptHash,
    `Schnorr.preChallenge,
    `Schnorr.verify,
    `Schnorr.verifyRelaxed,
    `Schnorr.verify_imp_verifyRelaxed,
    `Schnorr.verifyCircuit,
    `Schnorr.verifyCircuit_spec,
    `Schnorr.verifyCircuit_complete_spec ]

/-- The allowed axioms. -/
def allowed : List Name := [`propext, `Classical.choice, `Quot.sound]

/-- The endpoint laws concretize the snarky gadget laws at the DEPLOYED Pasta
    dictionaries (`HasEndo.vesta`, `HasCurve.vesta`), so their closures carry the
    certified `native_decide` witnesses those dictionaries' curve facts rest on —
    the certified orders and eigenvalue anchors. Everything else stays pure core
    Lean. -/
def deployedRoots : List Name :=
  [ `Schnorr.verifyCircuit_spec,
    `Schnorr.verifyCircuit_complete_spec ]

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
