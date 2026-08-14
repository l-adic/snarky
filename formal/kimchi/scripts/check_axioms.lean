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
    `Kimchi.Index.satisfies_iff_fullFamily_dvd,
    `Kimchi.Verifier.kimchiVerify,
    `Kimchi.Verifier.Wire.KimchiProof.check,
    `Kimchi.Verifier.Wire.KimchiVK.check,
    `Kimchi.Protocol.sound,
    -- The knowledge-soundness endpoints: the deployed verifier is knowledge-sound per curve,
    -- over the standard axioms and the Pasta certificates alone.
    `Kimchi.Verifier.KnowledgeSoundness.vesta_kimchi_knowledge_sound,
    `Kimchi.Verifier.KnowledgeSoundness.pallas_kimchi_knowledge_sound,
    -- The extractor's cost for this family (audit O-1a): the endpoints' call-bound hypothesis
    -- discharged at an explicit, proved R on the same tape that witnesses `Complete`, and the
    -- floor under that same hypothesis — no R below 1 satisfies it.
    `Kimchi.Verifier.KnowledgeSoundness.KimchiFamily.exists_complete_reductionEfficient,
    `Kimchi.Verifier.KnowledgeSoundness.KimchiFamily.one_le_of_reductionEfficient,
    -- The conditional-average counting layer (upstream's joint table-and-tape coin axis),
    -- standing beside the per-tape entries above and replacing neither. Existence as well as
    -- axioms: every public declaration of the block is pinned by name, terminals and plumbing
    -- alike, so neither a deletion sweep nor a `sorry` behind a reachable terminal is silent.
    `Kimchi.Verifier.KnowledgeSoundness.KimchiFamily.KimchiForkSpreadFamily,
    `Kimchi.Verifier.KnowledgeSoundness.KimchiFamily.attemptRuns_sum_le_of_forkSpreadFamily,
    `Kimchi.Verifier.KnowledgeSoundness.KimchiFamily.ReductionEfficientAvg,
    `Kimchi.Verifier.KnowledgeSoundness.KimchiFamily.reductionEfficientAvg_of_forkSpreadFamily,
    `Kimchi.Verifier.KnowledgeSoundness.KimchiFamily.reductionEfficientAvg_of_worstCase,
    `Kimchi.Verifier.KnowledgeSoundness.KimchiFamily.one_le_of_reductionEfficientAvg,
    -- The conditional-average PROBABILITY layer, and its two twin endpoints: knowledge
    -- soundness over (setup basis) x (challenge table x fork tape) jointly, with the tape
    -- sampled and no completeness hypothesis. Pinned on the same terms as the counting layer
    -- above — every public declaration of the block by name, terminals and plumbing alike.
    `Kimchi.Verifier.KnowledgeSoundness.KimchiFamily.relationFinderAvg,
    `Kimchi.Verifier.KnowledgeSoundness.KimchiFamily.DerivedUDLAdvantageLEAvg,
    `Kimchi.Verifier.KnowledgeSoundness.KimchiFamily.relation_summand_avg,
    `Kimchi.Verifier.KnowledgeSoundness.KimchiFamily.residual_summand_avg,
    `Kimchi.Verifier.KnowledgeSoundness.KimchiFamily.DiscreteLogRelationHardForAvg,
    `Kimchi.Verifier.KnowledgeSoundness.vesta_kimchi_knowledge_sound_avg,
    `Kimchi.Verifier.KnowledgeSoundness.pallas_kimchi_knowledge_sound_avg,
    `Kimchi.Verifier.Forking.honestKimchiFamily_wins,
    -- The Tier-2/3 surface (external-audit A-2): the faithfulness layer, the named
    -- anti-vacuity exhibits, and the REVISIT AGM lemmas are consumed by nothing, so no
    -- other root's closure reaches them — gate them by name or a `sorry` there passes
    -- the entire wired battery.
    `Kimchi.Verifier.KnowledgeSoundness.kimchiVerify_eq_verifyWith,
    `Kimchi.Verifier.Forking.Bridge.wins_iff_kimchiVerify,
    `Kimchi.Verifier.Forking.honestKimchiFamily_failure_set,
    `Kimchi.Verifier.KnowledgeSoundness.exists_ne_zero_kernel_scalarBasis,
    `Kimchi.Verifier.eval_pins_of_opening,
    `Kimchi.Verifier.combinedCommitment_eq_commit_of_rep,
    `Kimchi.Verifier.dlRelation_of_opening_ne,
    `Kimchi.Verifier.dlRelation_of_commit_eq,
    `Kimchi.Verifier.dlRelation_of_chunk_rep_ne,
    `Kimchi.Verifier.dlRelation_of_chunk_rep_masked_ne,
    `Kimchi.Verifier.ft_identity_of_chunks,
    -- the per-curve honest-family corollaries (external-audit B-4), and the same two guards
    -- against the conditional-average endpoints over the joint (table x tape) space
    `Kimchi.Verifier.Forking.vesta_honest_extraction_failure_measure_le,
    `Kimchi.Verifier.Forking.pallas_honest_extraction_failure_measure_le,
    `Kimchi.Verifier.Forking.vesta_honest_extraction_failure_measure_le_avg,
    `Kimchi.Verifier.Forking.pallas_honest_extraction_failure_measure_le_avg ]

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
