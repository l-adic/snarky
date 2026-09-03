import Pickles.Reflect.Soundness
import Lean.Elab.Command

/-! Gate the pickles linearization results' axiom closure.

The roots are the results this package stands behind: the two circuit theorems, one per
side of the cycle, and the two reflection endpoints they rest on. Everything else the
package proves — the machine's simulation laws, the environment's compatibility, the
transport lemmas, the decided α-bound — is in their dependency closure, and
`collectAxioms` walks the closure, so a stray axiom anywhere beneath them is caught here
without being named.

`Pickles/Reflect/Certificate.lean` is the ONLY module in this tree permitted to decide by
`native_decide`: the two reflection certificates and the α-table bound of the closed
streams. Every root rests on it, so every root may carry that module's certificates and
nothing else; the rest of the closure must reduce to the standard logical axioms alone,
since its content is ordinary proof and a certificate appearing there would mean a
computation had leaked into a law.

The discriminator is the DEFINING MODULE rather than a name prefix, following the kimchi
gate: an axiom's name is forgeable from inside a matching `namespace` block, its defining
module is not.
-/

open Lean Lean.Elab.Command

namespace Pickles.CheckAxioms

/-- Every result this package stands behind. -/
def roots : List Name :=
  [ `Pickles.Reflect.circuit_gateLinearization_fp,
    `Pickles.Reflect.circuit_gateLinearization_fq,
    `Pickles.Reflect.evaluate_fpTokens,
    `Pickles.Reflect.evaluate_fqTokens ]

/-- The standard logical axioms, permitted everywhere. -/
def allowed : List Name := [ `propext, `Classical.choice, `Quot.sound ]

/-- The roots allowed to carry a certified `native_decide` witness: all of them, each
resting on `Certificate.lean`'s decisions — the polynomial identity for the endpoints, and
that plus the α-table bound for the circuit theorems. -/
def deployedRoots : List Name := roots

/-- A trusted `native_decide` certificate: an upstream CompElliptic module (the Pasta field
and curve certificates), `Pasta/Endo.lean` (the two declared GLV eigenvalue anchors), or
`Pickles/Reflect/Certificate.lean` (the two linearization certificates). -/
def isTrustedNativeDecide (env : Environment) (ax : Name) : Bool :=
  (ax.toString.splitOn "native_decide").length > 1 &&
    match env.getModuleFor? ax with
    | some m =>
      (`CompElliptic).isPrefixOf m || m == `Pasta.Endo || m == `Pickles.Reflect.Certificate
    | none => false

end Pickles.CheckAxioms

run_cmd do
  let env ← getEnv
  let mut bad : Array (Name × Name) := #[]
  for root in Pickles.CheckAxioms.roots do
    unless env.contains root do
      throwError "axiom-check root not in environment: {root}"
    for ax in (← liftCoreM <| Lean.collectAxioms root) do
      unless Pickles.CheckAxioms.allowed.contains ax ||
          (Pickles.CheckAxioms.deployedRoots.contains root &&
            Pickles.CheckAxioms.isTrustedNativeDecide env ax) do
        bad := bad.push (root, ax)
  if bad.isEmpty then
    IO.println s!"✓ all {Pickles.CheckAxioms.roots.length} Pickles roots reduce to \
      {Pickles.CheckAxioms.allowed} (+ the declared Certificate.lean decisions)"
  else
    for (r, a) in bad do
      IO.eprintln s!"::error::{r} depends on disallowed axiom {a}"
    throwError "disallowed axioms found ({bad.size})"
