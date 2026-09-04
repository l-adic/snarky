import Pickles
import Lean.Elab.Command

/-! Gate the pickles package's axiom closure.

The roots are the results this package stands behind — the same list as the API manifest
`roots.txt`, whose grouped prose describes them: the two linearization circuit theorems,
one per side of the cycle, the two reflection endpoints they rest on, the two `ft_eval0`
circuit theorems built on them; the field-generic scalar-side gadget theorems (the IPA
gadgets, the fr-sponge schedule and challenge digests, the α-table, the domain scalars and
the mask-select); and the assembled `finalize_other_proof` theorems, generic and at the
deployed fields. Everything else the package proves — the machine's simulation laws, the
environment's compatibility, the transport lemmas, the decided α-bound — is in their
dependency closure, and `collectAxioms` walks the closure, so a stray axiom anywhere
beneath them is caught here without being named.

`Pickles/Reflect/Certificate.lean` is the only module in this tree permitted to decide by
`native_decide`: the two reflection certificates and the reachability facts about the
closed streams. Only the roots that rest on the deployed token streams — the linearization,
`ft_eval0` and deployed-field `finalize_other_proof` theorems — may carry that module's
certificates (`deployedRoots`); the field-generic gadget and assembly theorems, and the
rest of every closure, must reduce to the standard logical axioms alone.

The discriminator is the defining module rather than a name prefix, following the kimchi
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
    `Pickles.Reflect.evaluate_fqTokens,
    `Pickles.ftEval0Circuit_spec_fp,
    `Pickles.ftEval0Circuit_spec_fq,
    `Pickles.challengePolyEvals_spec,
    `Pickles.computeChallenges_spec,
    `Pickles.bCorrectCircuit_spec,
    `Pickles.combinedInnerProduct_spec_cip,
    `Pickles.permScalarCircuit_spec,
    `Pickles.challengeDigest_spec,
    `Pickles.squeezeXiR_spec,
    `Pickles.OptSponge.squeeze_spec,
    `Pickles.maskedChallengeDigest_spec,
    `Pickles.Linearization.precomputeAlphaPowers_spec,
    `Pickles.Pseudo.mask_spec,
    `Pickles.omegaPowers_spec,
    `Pickles.zkPolynomial_spec,
    `Pickles.zkPolynomial_eq_zkpmEval,
    `Pickles.knownDomainWhiches_spec,
    `Pickles.knownDomainVanishingPolynomial_spec,
    `Pickles.buildPow2PowsArray_spec,
    `Pickles.pow2PowSquare_spec,
    `Pickles.pow2PowMul_spec,
    `Pickles.finalizeOtherProofCore_spec,
    `Pickles.finalizeOtherProofStep_spec,
    `Pickles.finalizeOtherProofWrap_spec,
    `Pickles.finalizeOtherProofStep_spec_fp,
    `Pickles.finalizeOtherProofWrap_spec_fq,
    `Pickles.squeezePrechallenge_spec,
    `Pickles.fqSpongeTranscript_spec,
    `Pickles.assertPlonkChallenges_spec,
    `Pickles.FqTranscriptReads.wire ]

/-- The standard logical axioms, permitted everywhere. -/
def allowed : List Name := [ `propext, `Classical.choice, `Quot.sound ]

/-- The roots allowed to carry a `native_decide` certificate: those at the deployed token
streams, each resting on `Certificate.lean`'s decisions. -/
def deployedRoots : List Name :=
  [ `Pickles.Reflect.circuit_gateLinearization_fp,
    `Pickles.Reflect.circuit_gateLinearization_fq,
    `Pickles.Reflect.evaluate_fpTokens,
    `Pickles.Reflect.evaluate_fqTokens,
    `Pickles.ftEval0Circuit_spec_fp,
    `Pickles.ftEval0Circuit_spec_fq,
    `Pickles.finalizeOtherProofStep_spec_fp,
    `Pickles.finalizeOtherProofWrap_spec_fq ]

/-- A trusted `native_decide` certificate: one defined in an upstream CompElliptic module,
in `Pasta/Endo.lean`, or in `Pickles/Reflect/Certificate.lean`. -/
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
