/-
Axiom-closure gate for the bulletproof PCS: the soundness surface reduces to the standard
logical axioms + the Pasta trust base (native_decide certificates only — no axioms) and
nothing else. There is NO Fiat-Shamir axiom: the random-oracle idealisation enters the
knowledge-soundness results only as the game's uniform challenge table. DL-binding is a
hypothesis throughout, never an axiom.

Run from `formal/bulletproof-pcs/`:  lake env lean scripts/check_axioms.lean
(or from `formal/`:                  lake env lean bulletproof-pcs/scripts/check_axioms.lean)
-/
import Bulletproof
import Bulletproof.Forking.KnowledgeSoundness
import Lean.Elab.Command

open Lean Lean.Elab.Command

namespace Bulletproof.CheckAxioms

/-- The PCS soundness surface. -/
def roots : List Name :=
  [ `Bulletproof.commitmentBinding_iff_no_relation,
    `Bulletproof.ipaRelation_unique,
    `Bulletproof.verify_reflects,
    `Bulletproof.chunked_batch_soundness,
    -- the headline, per curve
    `Bulletproof.Ipa.Forking.ipaVesta_knowledge_sound,
    `Bulletproof.Ipa.Forking.ipaPallas_knowledge_sound,
    -- the rung below it, which assumes no DL hardness
    `Bulletproof.Ipa.Forking.vesta_failure_measure_le,
    `Bulletproof.Ipa.Forking.pallas_failure_measure_le,
    -- what the headline does and does not claim
    `Bulletproof.Ipa.Forking.honestFamily_failure_set,
    `Bulletproof.Ipa.Forking.DeployedFamily.reductionEfficient_exists,
    `Bulletproof.Ipa.Forking.derivedUDL_iff_residual_measure,
    -- the checked defences of the deployed model (see roots.txt)
    `Bulletproof.Ipa.Forking.verifyOracle_spongeFS,
    `Bulletproof.Ipa.Forking.verifyOracleFrom_spongeFSFrom,
    `Bulletproof.Ipa.Forking.spongeFS_eq_from,
    `Bulletproof.Ipa.Forking.spongeOBase_eq_from,
    `Bulletproof.Ipa.Forking.spongeOScalar_eq_from,
    `Bulletproof.Ipa.Forking.toGroup_spongeOBase_preT,
    `Bulletproof.Ipa.Forking.uBaseOf_eq_transcript,
    `Bulletproof.Ipa.Forking.nodeTranscript_nodes,
    `Bulletproof.Ipa.Forking.sg_determined_of_verifyWith,
    `Bulletproof.Ipa.Forking.wireWins_pinTable,
    `Bulletproof.Ipa.Forking.pinTable_factors,
    `Bulletproof.Ipa.Forking.chainAt_sg,
    `Bulletproof.Ipa.Forking.wireWins_U_irrelevant,
    `Bulletproof.Ipa.Forking.deployedExtract_U_irrelevant,
    `Bulletproof.Ipa.Forking.uRepresentationOfBreak,
    `Bulletproof.Ipa.Forking.winsAtBase_uBaseOf,
    `Bulletproof.Ipa.Forking.honestNode_wins_everywhere,
    `Bulletproof.Ipa.Forking.verifyWith_of_deferred_delta ]

/-- Standard logical axioms plus `Lean.ofReduceBool` (CompElliptic's `native_decide`
    witnesses). NOTE what is NOT here: any Fiat-Shamir axiom. The former
    `poseidon_fiat_shamir_{vesta,pallas}` were deleted along with the old `ipa*_sound`
    chain when the knowledge-soundness results took over as the API; re-introducing an
    axiom of that kind fails this gate. -/
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
      the standard axioms + the Pasta trust base (no Fiat-Shamir axiom)"
  else
    for (r, a) in bad do
      IO.eprintln s!"::error::{r} depends on disallowed axiom {a}"
    throwError "disallowed axioms found ({bad.size})"
