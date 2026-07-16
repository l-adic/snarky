/-
Axiom-closure gate for the bulletproof PCS. This package DECLARES the Fiat-Shamir axioms
(`Bulletproof.poseidon_fiat_shamir_{vesta,pallas}` — the Poseidon sponge, from the
`poseidon` package, provides a valid Fiat-Shamir transform); the gate checks that the
soundness surface reduces to the standard logical axioms + those FS axioms + the Pasta
trust base (Hasse bounds, CompElliptic certificates) and nothing else. DL-binding is a
hypothesis throughout, never an axiom.

Run from `formal/bulletproof-pcs/`:  lake env lean scripts/check_axioms.lean
(or from `formal/`:                  lake env lean bulletproof-pcs/scripts/check_axioms.lean)
-/
import Bulletproof
import Lean.Elab.Command

open Lean Lean.Elab.Command

namespace Bulletproof.CheckAxioms

/-- The PCS soundness surface. -/
def roots : List Name :=
  [ `Bulletproof.ipa_soundness,
    `Bulletproof.commitmentBinding_iff_no_relation,
    `Bulletproof.ipaRelation_unique,
    `Bulletproof.vandermondeN,
    `Bulletproof.batch_soundness,
    `Bulletproof.chunked_ipa_soundness,
    `Bulletproof.chunked_batch_soundness,
    `Bulletproof.verify_reflects,
    `Bulletproof.ipaVesta_sound,
    `Bulletproof.ipaPallas_sound ]

/-- Standard logical axioms; the FS axioms declared here; the Pasta Hasse bounds;
    `Lean.ofReduceBool` (CompElliptic's `native_decide` witnesses). -/
def allowed : List Name :=
  [ `propext, `Classical.choice, `Quot.sound, `Lean.ofReduceBool,
    `Bulletproof.poseidon_fiat_shamir_vesta, `Bulletproof.poseidon_fiat_shamir_pallas,
    `Pasta.pallas_hasse, `Pasta.vesta_hasse ]

/-- A CompElliptic `native_decide` point-count witness (trusted; see kimchi's gate). -/
def isTrustedNativeDecide (ax : Name) : Bool :=
  let s := ax.toString
  "CompElliptic.".isPrefixOf s && (s.splitOn "native_decide").length > 1

def isAllowed (ax : Name) : Bool := allowed.contains ax || isTrustedNativeDecide ax

end Bulletproof.CheckAxioms

run_cmd do
  let env ← getEnv
  let mut bad : Array (Name × Name) := #[]
  for root in Bulletproof.CheckAxioms.roots do
    unless env.contains root do
      throwError "axiom-check root not in environment: {root}"
    for ax in (← liftCoreM <| Lean.collectAxioms root) do
      unless Bulletproof.CheckAxioms.isAllowed ax do
        bad := bad.push (root, ax)
  if bad.isEmpty then
    IO.println s!"✓ all {Bulletproof.CheckAxioms.roots.length} Bulletproof roots reduce to \
      the standard axioms + the declared FS axioms + the Pasta trust base"
  else
    for (r, a) in bad do
      IO.eprintln s!"::error::{r} depends on disallowed axiom {a}"
    throwError "disallowed axioms found ({bad.size})"
