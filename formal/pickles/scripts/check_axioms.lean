import Pickles.Reflect.Certificate
import Lean.Elab.Command

/-! Gate the pickles linearization results' axiom closure.

The two reflection endpoints are the ONLY declarations in this tree permitted a
`native_decide` certificate, and only one from `Pickles/Reflect/Certificate.lean` — the
module declared to hold them. Everything else, the transport lemmas included, must reduce
to the standard logical axioms alone: their content is ordinary proof, and a certificate
appearing there would mean a computation had leaked into a law.

The discriminator is the DEFINING MODULE rather than a name prefix, following the kimchi
gate: an axiom's name is forgeable from inside a matching `namespace` block, its defining
module is not.
-/

open Lean Lean.Elab.Command

namespace Pickles.CheckAxioms

/-- Every result this package stands behind. -/
def roots : List Name :=
  [ `Pickles.Reflect.evaluate_fpTokens,
    `Pickles.Reflect.evaluate_fqTokens,
    `Pickles.Linearization.evaluate_map,
    `Kimchi.Protocol.Linearization.toEnv_compatible,
    `Kimchi.Protocol.Linearization.gateLinearization_map ]

/-- The standard logical axioms, permitted everywhere. -/
def allowed : List Name := [ `propext, `Classical.choice, `Quot.sound ]

/-- The roots allowed to additionally carry a certified `native_decide` witness: the two
reflection endpoints, which rest on the polynomial identity decided by compilation. -/
def deployedRoots : List Name :=
  [ `Pickles.Reflect.evaluate_fpTokens,
    `Pickles.Reflect.evaluate_fqTokens ]

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
      {Pickles.CheckAxioms.allowed} (+ the two declared linearization certificates)"
  else
    for (r, a) in bad do
      IO.eprintln s!"::error::{r} depends on disallowed axiom {a}"
    throwError "disallowed axioms found ({bad.size})"
