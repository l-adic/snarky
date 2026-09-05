/-
Axiom-closure gate for the bulletproof PCS: the definitional surface — the abstract scheme
and the executable Pasta wire verifier — reduces to the standard logical axioms + the Pasta
trust base (native_decide certificates only, no axioms) and nothing else.

This package carries no soundness claim. The abstract opening soundness, the binding
results and the forking/knowledge-soundness layer over `Zcash/ironwood` were retired; what
remains is a SPECIFICATION — `Ipa.verify`/`Ipa.verifyFrom` is the transcription
proof-systems' `poly-commitment` is measured against, and the anchor a circuit
implementation of the opening check is proved faithful to.

The root list is a deletion guard as well as an axiom guard: a name absent from the environment
fails with `axiom-check root not in environment`, so removing a listed declaration — even
together with its `roots.txt` line — cannot pass silently.

Run from `formal/bulletproof-pcs/`:  lake env lean scripts/check_axioms.lean
(or from `formal/`:                  lake env lean bulletproof-pcs/scripts/check_axioms.lean)
-/
import Bulletproof
import Lean.Elab.Command

open Lean Lean.Elab.Command

namespace Bulletproof.CheckAxioms

/-- The PCS definitional surface: the executable wire verifier at both entry points (cold
    and the warm-sponge restart `kimchiVerify` finishes on), the wire parse, and the
    algebraic layer the verifier is stated over. Audited so no stray axiom — a
    `native_decide` outside the trusted certificates, say — hides in the executable path. -/
def roots : List Name :=
  [ -- the executable wire verifier and its warm-sponge entry point
    `Bulletproof.Ipa.verify,
    `Bulletproof.Ipa.verifyFrom,
    `Bulletproof.Ipa.verifyWith,
    `Bulletproof.Ipa.transcript,
    `Bulletproof.Ipa.transcriptFrom,
    `Bulletproof.Ipa.transcriptFrom_eq_ipaPrechallenges,
    `Bulletproof.Ipa.verifyWith_eq,
    `Bulletproof.Ipa.roundChallenges,
    -- the serde wire boundary and its parse
    `Bulletproof.Ipa.Wire.Proof.check,
    `Bulletproof.Ipa.Wire.Input.check,
    -- the batch layer the verifier reads its claims through
    `Bulletproof.Ipa.cipOf,
    `Bulletproof.Ipa.combineCommitments,
    `Bulletproof.Ipa.msm,
    -- the algebraic scheme the wire verifier is stated over
    `Bulletproof.commit,
    `Bulletproof.commitGen,
    `Bulletproof.openingRelation,
    `Bulletproof.openingRelationB,
    `Bulletproof.VerifierAcceptsAt,
    `Bulletproof.BatchAccepts,
    `Bulletproof.combinedCommitment,
    `Bulletproof.combinedInnerProduct,
    `Bulletproof.combinedEvalVector,
    `Bulletproof.bPoly,
    `Bulletproof.bPolyCoefficients,
    -- the chunk layer, and the two flattening identities that give it content
    `Bulletproof.chunkedCombinedCommitment,
    `Bulletproof.chunkedCombinedInnerProduct,
    `Bulletproof.chunkedCombinedCommitment_eq_flat,
    `Bulletproof.chunkedCombinedInnerProduct_eq_flat,
    `Bulletproof.innerProduct_combinedEvalVector,
    -- the polynomial chunking the commitment layer rests on
    `Bulletproof.chunkPoly_eval,
    `Bulletproof.eval_eq_sum_chunkPoly,
    `Bulletproof.chunkCoeffs_assemblePoly,
    `Bulletproof.assemblePoly_natDegree_lt ]

/-- The standard logical axioms, and nothing else — `native_decide` certificates are
    admitted separately, by defining module, in `isTrustedNativeDecide` below.
    (`Lean.ofReduceBool` is not produced by `native_decide` on this toolchain and is
    deliberately absent, as in kimchi's parallel gate.)

    Note what is *not* here: any Fiat–Shamir axiom. The former
    `poseidon_fiat_shamir_{vesta,pallas}` were deleted when the knowledge-soundness results
    took over as the API, and did not return when those were themselves retired;
    re-introducing an axiom of that kind fails this gate. -/
def allowed : List Name :=
  [ `propext, `Classical.choice, `Quot.sound ]

/-- A trusted `native_decide` certificate, discriminated by DEFINING MODULE rather than by
    name prefix (external-audit A-8; see kimchi's gate for the full note). -/
def isTrustedNativeDecide (env : Environment) (ax : Name) : Bool :=
  (ax.toString.splitOn "native_decide").length > 1 &&
    match env.getModuleFor? ax with
    | some m => (`CompElliptic).isPrefixOf m || m == `Pasta.Endo
    | none => false

def isAllowed (env : Environment) (ax : Name) : Bool :=
  allowed.contains ax || isTrustedNativeDecide env ax

end Bulletproof.CheckAxioms

run_cmd do
  let env ← getEnv
  let mut bad : Array (Name × Name) := #[]
  for root in Bulletproof.CheckAxioms.roots do
    unless env.contains root do
      throwError "axiom-check root not in environment: {root}"
    for ax in (← liftCoreM <| Lean.collectAxioms root) do
      unless Bulletproof.CheckAxioms.isAllowed env ax do
        bad := bad.push (root, ax)
  if bad.isEmpty then
    IO.println s!"✓ all {Bulletproof.CheckAxioms.roots.length} Bulletproof roots reduce to \
      the standard axioms + the Pasta trust base"
  else
    for (r, a) in bad do
      IO.eprintln s!"::error::{r} depends on disallowed axiom {a}"
    throwError "disallowed axioms found ({bad.size})"
