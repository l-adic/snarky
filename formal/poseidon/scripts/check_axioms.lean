/-
Axiom-closure gate for the poseidon package — the Poseidon permutation, the duplex sponge,
the curve-generic Fq-sponge consumer layer, and the SvdW map-to-curve. This is the object
the whole random-oracle idealisation concerns (the game's uniform table is identified with
THESE reads by `FSFaithful`), so its surface gets its own gate rather than being audited
only where a kimchi or bulletproof root happens to reach it (external-audit finding A-5).

Everything here is executable specification; the gate pins existence and that no axiom —
in particular no `sorryAx` and no tree-local `native_decide` — enters the closures. The
map-to-curve reaches CompElliptic's certified curve constants, so upstream `native_decide`
certificates are permitted by defining module, exactly as in the other packages' gates.

That existence pin makes the root list a deletion guard: a name absent from the environment
fails with `axiom-check root not in environment`, so removing a listed declaration — even
together with its `roots.txt` line — cannot pass silently.

Run from `formal/poseidon/`:  lake env lean scripts/check_axioms.lean
(or from `formal/`:           lake env lean poseidon/scripts/check_axioms.lean)
-/
import Poseidon
import Lean.Elab.Command

open Lean Lean.Elab.Command

namespace Poseidon.CheckAxioms

/-- The sponge-layer surface: the duplex automaton, the production parameter tables, the
    Fq-sponge ops the Fiat–Shamir faithfulness layer is stated over, the per-curve specs,
    and the SvdW map-to-curve. -/
def roots : List Name :=
  [ `Poseidon.init, `Poseidon.absorb, `Poseidon.squeeze, `Poseidon.squeezeN,
    `Poseidon.fqParams, `Poseidon.fpParams,
    `Poseidon.FqSponge.init, `Poseidon.FqSponge.absorbFq, `Poseidon.FqSponge.absorbG,
    `Poseidon.FqSponge.absorbFr, `Poseidon.FqSponge.challenge,
    `Poseidon.FqSponge.challengeFq, `Poseidon.FqSponge.challengeNat,
    `Poseidon.FqSponge.squeezeChallenge, `Poseidon.FqSponge.endoExpand,
    `Poseidon.FqVesta.spec, `Poseidon.FqPallas.spec,
    `Poseidon.GroupMapVesta.toGroup, `Poseidon.GroupMapPallas.toGroup ]

/-- The standard logical axioms. (`native_decide` certificates are permitted separately,
    by defining module — see `isTrustedNativeDecide`.) -/
def allowed : List Name := [`propext, `Classical.choice, `Quot.sound]

/-- A trusted `native_decide` certificate, discriminated by DEFINING MODULE rather than by
    name prefix (the name is forgeable from inside a `namespace CompElliptic` block in this
    tree; the module is not — tree files keep their own module names regardless of the
    namespaces they open). Trusted: any `native_decide` axiom whose defining module is
    upstream CompElliptic's, or pasta's two declared eigenvalue anchors in `Pasta/Endo.lean`. -/
def isTrustedNativeDecide (env : Environment) (ax : Name) : Bool :=
  (ax.toString.splitOn "native_decide").length > 1 &&
    match env.getModuleFor? ax with
    | some m => (`CompElliptic).isPrefixOf m || m == `Pasta.Endo
    | none => false

def isAllowed (env : Environment) (ax : Name) : Bool :=
  allowed.contains ax || isTrustedNativeDecide env ax

end Poseidon.CheckAxioms

run_cmd do
  let env ← getEnv
  let mut bad : Array (Name × Name) := #[]
  for root in Poseidon.CheckAxioms.roots do
    unless env.contains root do
      throwError "axiom-check root not in environment: {root}"
    for ax in (← liftCoreM <| Lean.collectAxioms root) do
      unless Poseidon.CheckAxioms.isAllowed env ax do
        bad := bad.push (root, ax)
  if bad.isEmpty then
    IO.println s!"✓ all {Poseidon.CheckAxioms.roots.length} Poseidon roots reduce to the \
      standard axioms (+ certified upstream native_decide only)"
  else
    for (r, a) in bad do
      IO.eprintln s!"::error::{r} depends on disallowed axiom {a}"
    throwError "disallowed axioms found ({bad.size})"
