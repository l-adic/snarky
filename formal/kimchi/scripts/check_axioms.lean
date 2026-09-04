/-
Axiom-closure gate for the Kimchi formalization.

`lake build` succeeds even with `sorry` (it is only a warning), so this script gates the headline
theorems explicitly: it collects the full axiom closure of each root and fails unless every axiom
is in the allowlist below — the three standard logical axioms and the trusted `native_decide`
certificates (the Pasta group orders are *unconditional*, derived via
CompElliptic's fibre-bound argument). `Lean.ofReduceBool` is deliberately absent — it is not
what `native_decide` produces on this toolchain. This subsumes the old `sorryAx` grep: a
`sorry` shows up as
`sorryAx`, which is not in the allowlist, and any *other* stray axiom that slips in is caught too.

The root list is a deletion guard as well as an axiom guard: a name absent from the environment
fails with `axiom-check root not in environment`, so removing a listed declaration — even
together with its `roots.txt` line — cannot pass silently.

Run from `formal/kimchi/`:  lake env lean scripts/check_axioms.lean
(or from `formal/`:         lake env lean kimchi/scripts/check_axioms.lean)
-/
import Kimchi

open Lean Lean.Elab.Command

namespace Kimchi.CheckAxioms

/-- The headline theorems whose axiom closure must stay clean — plus the executable
    verifier and wire-parse defs from `roots.txt`, audited so no stray axiom
    (a `native_decide` outside the trusted certificates, say) hides in the
    executable path. -/
def roots : List Name :=
  [ `Kimchi.Gate.Generic.sound, `Kimchi.Gate.Generic.complete,
    `Kimchi.Gate.AddComplete.sound_noninf, `Kimchi.Gate.AddComplete.complete_build,
    `Kimchi.Gate.AddComplete.sound_point_noninf, `Kimchi.Gate.AddComplete.sound_point_inf,
    `Kimchi.Gate.AddComplete.ok_iff, `Kimchi.Gate.AddComplete.inf_boolean,
    `Kimchi.Gate.AddComplete.complete,
    `Kimchi.Gate.AddComplete.sound,
    `Kimchi.Gate.VarBaseMul.sound, `Kimchi.Gate.VarBaseMul.complete,
    `Kimchi.Gate.VarBaseMul.varBaseMul_forbidden_correct,
    `Kimchi.Gate.VarBaseMul.varBaseMul_subwrap_correct,
    `Kimchi.Gate.VarBaseMul.varBaseMul_off,
    `Kimchi.Gate.VarBaseMul.chain_complete,
    `Kimchi.Gate.VarBaseMul.varBaseMul_scaleFast1,
    `Kimchi.Gate.VarBaseMul.varBaseMul_scaleFast2,
    `Kimchi.Gate.EndoScalar.sound, `Kimchi.Gate.EndoScalar.complete,
    `Kimchi.Gate.EndoScalar.chain_toField,
    `Kimchi.Gate.EndoScalar.chain_complete,
    `Kimchi.Gate.EndoScalar.endoScalar_unique,
    -- the 128-bit range check the same gate implements (`RangeCheck.purs`)
    `Kimchi.Gate.EndoScalar.chain_range,
    `Kimchi.Gate.EndoScalar.chain_range_128,
    `Kimchi.Gate.EndoScalar.chain_range_unique,
    `Kimchi.Gate.EndoScalar.range_complete,
    `Kimchi.Gate.EndoScalar.chain_range_complete,
    `Kimchi.Gate.EndoScalar.chain_range_complete_128,
    -- the packaged eight-row shape (`RangeCheck.purs`'s `rangeCheck128`) and its deployed
    -- per-field entry points, every field hypothesis discharged
    `Kimchi.Gate.EndoScalar.Chain128,
    `Kimchi.Gate.EndoScalar.Chain128.range,
    `Kimchi.Gate.EndoScalar.Chain128.exists_of_lt,
    `Kimchi.Gate.EndoScalar.fp_rangeCheck128_sound,
    `Kimchi.Gate.EndoScalar.fp_rangeCheck128_complete,
    `Kimchi.Gate.EndoScalar.fq_rangeCheck128_sound,
    `Kimchi.Gate.EndoScalar.fq_rangeCheck128_complete,
    `Kimchi.Gate.EndoMul.sound, `Kimchi.Gate.EndoMul.complete,
    `Kimchi.Gate.EndoMul.endoMul,
    `Kimchi.Gate.EndoMul.pallas_endoMul, `Kimchi.Gate.EndoMul.vesta_endoMul,
    `Kimchi.Gate.EndoMul.chain_complete,
    `Kimchi.Gate.EndoMul.pallas_chain_complete, `Kimchi.Gate.EndoMul.vesta_chain_complete,
    `Kimchi.zH_dvd_iff,
    `Kimchi.dvd_separation,
    `Kimchi.Gate.Poseidon.sound, `Kimchi.Gate.Poseidon.complete,
    -- the gate-to-sponge faithfulness layer: the eleven-row chain computes
    -- `Poseidon.blockCipher`, the fixture-validated `mina_poseidon` permutation, rather than
    -- the `perm` the gate file defines for itself. Every public declaration of
    -- `Gate/Semantics/Poseidon.lean`'s sponge development is pinned, terminals and plumbing
    -- alike, so a `sorry` anywhere in the chain cannot hide behind a reachable terminal.
    `Kimchi.Gate.Poseidon.rounds,
    `Kimchi.Gate.Poseidon.rounds_congr,
    `Kimchi.Gate.Poseidon.rounds_add,
    `Kimchi.Gate.Poseidon.perm_eq_rounds,
    `Kimchi.Gate.Poseidon.mdsOfParams,
    `Kimchi.Gate.Poseidon.round_eq_fullRound,
    `Kimchi.Gate.Poseidon.paramsRc,
    `Kimchi.Gate.Poseidon.blockCipher_eq_rounds,
    `Kimchi.Gate.Poseidon.Chain,
    `Kimchi.Gate.Poseidon.Chain.mono,
    `Kimchi.Gate.Poseidon.chain_rounds,
    `Kimchi.Gate.Poseidon.chain_blockCipher,
    `Kimchi.Gate.Poseidon.buildChain,
    `Kimchi.Gate.Poseidon.buildChain_s0,
    `Kimchi.Gate.Poseidon.buildChain_chain,
    `Kimchi.Gate.Poseidon.buildChain_blockCipher,
    `Kimchi.Gate.Poseidon.fqParams_size,
    `Kimchi.Gate.Poseidon.fpParams_size,
    `Kimchi.Gate.Poseidon.fq_poseidonChain_blockCipher,
    `Kimchi.Gate.Poseidon.fp_poseidonChain_blockCipher,
    `Kimchi.Gate.Poseidon.fq_poseidonChain_complete,
    `Kimchi.Gate.Poseidon.fp_poseidonChain_complete,
    `Kimchi.Lift.Argument.bridge,
    `Kimchi.Index.Satisfies,
    `Kimchi.Index.satisfies_iff_fullFamily_dvd,
    `Kimchi.Index.copy_soundness_of_dvd,
    `Kimchi.Verifier.kimchiVerify,
    `Kimchi.Verifier.frOracles_eq_frPrechallenges,
    `Kimchi.Verifier.fqOracles_eq_fqPrechallenges,
    `Kimchi.Verifier.low128_of_decomp,
    `Kimchi.Verifier.Wire.KimchiProof.check,
    `Kimchi.Verifier.Wire.KimchiVK.check ]

/-- The only axioms the roots may depend on: the standard logical axioms. The pasta
    package declares NO axioms — the group orders are unconditional (CompElliptic's
    fibre-bound argument) and the CM eigenvalue relations are THEOREMS (homomorphism +
    prime-order cyclicity + `native_decide` anchors at the generators). The
    `native_decide` certificates — CompElliptic's primality, point-count, sqrt-order and
    eigen-anchor witnesses plus pasta's two declared anchors, each trusting the compiler
    through `Lean.trustCompiler` — are permitted separately by `isTrustedNativeDecide`.
    (`Lean.ofReduceBool` is *not* produced by `native_decide` on this toolchain and is
    deliberately absent.) -/
def allowed : List Name :=
  [ `propext, `Classical.choice, `Quot.sound ]

/-- A trusted `native_decide` certificate, discriminated by DEFINING MODULE rather than
    by name prefix (external-audit A-8: the name is forgeable from inside a
    `namespace CompElliptic` block in this tree — and this tree does author declarations
    in that namespace — while the defining module is not: tree files keep their own
    module names regardless of the namespaces they open). Trusted: any `native_decide`
    axiom defined in an upstream CompElliptic module, or in `Pasta/Endo.lean` — the one
    tree file declared to hold the two GLV eigenvalue anchors. -/
def isTrustedNativeDecide (env : Environment) (ax : Name) : Bool :=
  (ax.toString.splitOn "native_decide").length > 1 &&
    match env.getModuleFor? ax with
    | some m => (`CompElliptic).isPrefixOf m || m == `Pasta.Endo
    | none => false

/-- An axiom is permitted if it is in the explicit allowlist or is a certified
    `native_decide` witness. -/
def isAllowed (env : Environment) (ax : Name) : Bool :=
  allowed.contains ax || isTrustedNativeDecide env ax

end Kimchi.CheckAxioms

run_cmd do
  let env ← getEnv
  let mut bad : Array (Name × Name) := #[]
  for root in Kimchi.CheckAxioms.roots do
    unless env.contains root do
      throwError "axiom-check root not in environment: {root}"
    for ax in (← liftCoreM <| Lean.collectAxioms root) do
      unless Kimchi.CheckAxioms.isAllowed env ax do
        bad := bad.push (root, ax)
  if bad.isEmpty then
    IO.println s!"✓ all {Kimchi.CheckAxioms.roots.length} roots reduce to the allowed axiom set \
      {Kimchi.CheckAxioms.allowed} (+ certified upstream native_decide)"
  else
    for (r, a) in bad do
      IO.eprintln s!"::error::{r} depends on disallowed axiom {a}"
    throwError "disallowed axioms found ({bad.size})"
