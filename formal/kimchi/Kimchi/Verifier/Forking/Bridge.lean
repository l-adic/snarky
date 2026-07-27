import Kimchi.Verifier.KnowledgeSoundness

/-!
# The deployed bridge — the game's win predicate versus the deployed verifier

`Kimchi.Verifier.KnowledgeSoundness` proves two things that never meet:

* `kimchiVerify_eq_verifyWith` — the **deployed** verifier is the challenge-generic verifier
  `kimchiVerifyWith` at nine named transcript reads, the last three of which come from the
  **warm** opening source `kimchiOpeningFS` (the fq sponge continued from the post-`ζ` state);
* `vesta_kimchi_knowledge_sound` / `pallas_kimchi_knowledge_sound` — the endpoints, which
  measure `KimchiFamily.Wins`, i.e. the *same* generic verifier at six **table** reads, `k + 1`
  more table reads, and a base `uBaseOf C (Ipa.cipOf (fam.claim basis O))` folded from
  `Poseidon.FqSponge.init` — **cold**.

This module writes down exactly what separates them and proves everything on either side of it.

## The two differences, and why only one of them is a theorem

The first is the **Fiat–Shamir idealisation**: the oracle table `O` supplies challenges where
the deployed run squeezes them. That is not a defect — it is the definition of the random-oracle
model, and it is what makes a forking argument possible at all. All one can ask is that it be
*faithful*: on a table agreeing with the sponge at the run's own nodes the two predicates must
coincide. That is `wins_iff_kimchiVerify` below, and it is proved.

The second is the **warm/cold residue**. `Bulletproof.Ipa.Forking.uBaseOf` folds the opening
sponge from `Poseidon.FqSponge.init`, whereas kimchi's deployed opening continues the fq sponge
from the warm post-`ζ` state. For the standalone IPA the two coincide, because there the opening
*is* the whole protocol and its sponge really does start cold (`uBaseOf_eq_warmBase_init` records
precisely that). Inside kimchi they do not, and no rewriting will make them: Poseidon's state
after absorbing the key digest, the public commitment chunks, the witness chunks, the
permutation and the quotient chunks is not the initial state.

**The residue is therefore a HYPOTHESIS here, not a target.** It is `FSFaithful.base`. Both
`Bulletproof.Ipa.Forking.uBaseOf` and `KimchiFamily.Wins` are frozen, so the honest options are
(a) re-derive the game's base from the warm state, changing a frozen definition, or (b) charge
the discrepancy as an extra term in the bound. Choosing between them is the mathematician's call;
what this module does is give the obstruction a name and prove that it is the *only* one.

## Contents

1. `uBaseOf_eq_warmBase_init` — the game's base is the start-state-general base oracle at
   `Poseidon.FqSponge.init`.
2. `FSFaithful` — the nine equations, bundled: eight Fiat–Shamir read equations and the base
   agreement.
3. `wins_iff_kimchiVerify` — **the bridge**: on a faithful table the win predicate *is* deployed
   acceptance.
4. `vesta_deployed_failure_measure_le` / `pallas_deployed_failure_measure_le` — the endpoints,
   restated over deployed acceptance on the faithful locus.

Everything here is Archon-original: these are statements about this development's own
constructions, so no external source is cited.
-/

namespace Kimchi.Verifier.Forking.Bridge

open Bulletproof Bulletproof.Ipa.Forking Kimchi.Verifier.KnowledgeSoundness
open scoped ENNReal

variable {C : Ipa.CommitmentCurve}

/-! ## 1. The cold base is the warm base of a cold start

`Bulletproof.Ipa.Forking.uBaseOf` is spelled with the *cold* base oracle `spongeOBase`. The warm
opening source `Ipa.Forking.spongeFSFrom C s₀` specialises to it at `s₀ = Poseidon.FqSponge.init`
(`Ipa.Forking.spongeFS_eq_from`), so the game's base is literally the warm base of a cold start.
This is the lemma that turns the base agreement of `FSFaithful` into the sharp statement "the
opening sponge may be restarted cold without changing its first squeeze". -/

/-- **The game's opening base is the warm base oracle started cold.** `uBaseOf` folds
`spongeOBase` along the `preT` prefix of the claim; `spongeOBase` is `spongeOBaseFrom` at
`Poseidon.FqSponge.init`, which is `(spongeFSFrom C Poseidon.FqSponge.init).squeezeBase`.

Project-local because both sides are this development's own constructions: `uBaseOf` lives in
`Bulletproof/Forking/Deployed.lean` (frozen) and the start-state-general oracles in
`Bulletproof/Forking/Transcript.lean`. -/
theorem uBaseOf_eq_warmBase_init {k m p : ℕ} (inp : Ipa.Input C k m p) :
    uBaseOf C (Ipa.cipOf inp)
      = C.toGroup ((spongeFSFrom C Poseidon.FqSponge.init).squeezeBase
          (IpaTranscriptElt.preT inp)) := rfl

/-! ## 2. Fiat–Shamir faithfulness of a table, as a hypothesis

`FSFaithful fam basis O` bundles the nine equations that stand between `KimchiFamily.Wins` and
the deployed verifier, stated at the family's *own* data (`fam.cvk basis`, `fam.proofOf basis O`,
`fam.pub basis`, `fam.digest basis`) so that the bundle is literally the hypothesis set of
`kimchiVerify_eq_verifyWith_of_reads`.

Eight of the nine are Fiat–Shamir read equations: they say the table `O` returns, at the run's
own transcript node, exactly what the deployed sponge squeezes there. The ninth,
`FSFaithful.base`, is the warm/cold residue discussed in the module preamble — it is *not* a
theorem and is not attempted here. -/

section Faithful

variable {nc k n : ℕ} [NeZero n] [Module C.ScalarField C.Point]

/-- **A table faithful to the run.** Fix a family, a basis and an oracle table `O`. This says the
table agrees with the deployed Fiat–Shamir schedule at all nine places the win predicate and the
deployed verifier could differ.

Fields `beta`–`evalscale` and `round`/`schnorr` are the eight *Fiat–Shamir* equations: on a
faithful table the random-oracle idealisation is exact at the run's own nodes. Field `base` is
the **warm/cold residue**: `KimchiFamily.Wins` feeds the generic verifier a base folded from
`Poseidon.FqSponge.init` (`uBaseOf`, see `uBaseOf_eq_warmBase_init`), while the deployed opening
continues the fq sponge from the post-`ζ` state. That conjunct is a modelling hypothesis, not a
provable equation; see the module preamble.

Project-local because it is a statement about this development's own game and verifier. -/
structure FSFaithful (fam : KimchiFamily C nc k n)
    (basis : Zcash.Snark.AugmentedIndex (2 ^ k) → C.Point) (O : Coins C nc k) : Prop where
  /-- The `β` read is the first fq squeeze of the deployed schedule. -/
  beta : reads (fam.digest basis) (fam.publicComm basis) (fam.proofOf basis O) O Squeeze.beta
    = Forking.poseidonO (KimchiTranscriptElt.preBeta (fam.cvk basis) (fam.proofOf basis O)
        (publicCommitment C (srsOfBasis k basis) (fam.cvk basis) (fam.pub basis)))
  /-- The `γ` read is the second fq squeeze (nothing is absorbed between it and `β`). -/
  gamma : reads (fam.digest basis) (fam.publicComm basis) (fam.proofOf basis O) O Squeeze.gamma
    = Forking.poseidonO (KimchiTranscriptElt.preGamma (fam.cvk basis) (fam.proofOf basis O)
        (publicCommitment C (srsOfBasis k basis) (fam.cvk basis) (fam.pub basis)))
  /-- The `α` read is the fq squeeze after the permutation commitment. -/
  alpha : reads (fam.digest basis) (fam.publicComm basis) (fam.proofOf basis O) O Squeeze.alpha
    = Forking.poseidonO (KimchiTranscriptElt.preAlpha (fam.cvk basis) (fam.proofOf basis O)
        (publicCommitment C (srsOfBasis k basis) (fam.cvk basis) (fam.pub basis)))
  /-- The `ζ` read is the fq squeeze after the quotient commitment. -/
  zeta : reads (fam.digest basis) (fam.publicComm basis) (fam.proofOf basis O) O Squeeze.zeta
    = Forking.poseidonO (KimchiTranscriptElt.preZeta (fam.cvk basis) (fam.proofOf basis O)
        (publicCommitment C (srsOfBasis k basis) (fam.cvk basis) (fam.pub basis)))
  /-- The polyscale `v` read is the fr sponge's first squeeze, taken at the warm fq digest and
  the public evaluation chunks the deployed `ζ` determines. -/
  polyscale : reads (fam.digest basis) (fam.publicComm basis) (fam.proofOf basis O) O
      Squeeze.polyscale
    = Forking.poseidonOFr (FrTranscriptElt.preV (fam.proofOf basis O)
        (warmDigest (fam.cvk basis) (fam.proofOf basis O)
          (publicCommitment C (srsOfBasis k basis) (fam.cvk basis) (fam.pub basis)))
        (kimchiPubEvals (srsOfBasis k basis) (fam.cvk basis) (fam.proofOf basis O)
          (fam.pub basis)))
  /-- The evalscale `u` read is the fr sponge's second squeeze. -/
  evalscale : reads (fam.digest basis) (fam.publicComm basis) (fam.proofOf basis O) O
      Squeeze.evalscale
    = Forking.poseidonOFr (FrTranscriptElt.preU (fam.proofOf basis O)
        (warmDigest (fam.cvk basis) (fam.proofOf basis O)
          (publicCommitment C (srsOfBasis k basis) (fam.cvk basis) (fam.pub basis)))
        (kimchiPubEvals (srsOfBasis k basis) (fam.cvk basis) (fam.proofOf basis O)
          (fam.pub basis)))
  /-- Each opening round read is the *warm* opening sponge's round squeeze, at the run's own
  claim. -/
  round : ∀ i : Fin k,
    reads (fam.digest basis) (fam.publicComm basis) (fam.proofOf basis O) O (Squeeze.ipaRound i)
      = (kimchiOpeningFS (fam.cvk basis) (fam.proofOf basis O)
          (publicCommitment C (srsOfBasis k basis) (fam.cvk basis) (fam.pub basis))).squeezeScalar
        (IpaTranscriptElt.preU (fam.claim basis O) i)
  /-- The Schnorr read is the warm opening sponge's final squeeze. -/
  schnorr : reads (fam.digest basis) (fam.publicComm basis) (fam.proofOf basis O) O
      Squeeze.schnorr
    = (kimchiOpeningFS (fam.cvk basis) (fam.proofOf basis O)
        (publicCommitment C (srsOfBasis k basis) (fam.cvk basis) (fam.pub basis))).squeezeScalar
      (IpaTranscriptElt.preC (fam.claim basis O))
  /-- **THE RESIDUE — base agreement.** The game's opening base, folded from
  `Poseidon.FqSponge.init`, equals the deployed one, folded from the warm post-`ζ` state. This is
  a modelling hypothesis: it is false in general (Poseidon's state after the kimchi absorbs is
  not the initial state), it is not proved anywhere, and it is deliberately visible here rather
  than hidden inside a weakened win predicate. -/
  base : uBaseOf C (Ipa.cipOf (fam.claim basis O))
    = C.toGroup ((kimchiOpeningFS (fam.cvk basis) (fam.proofOf basis O)
        (publicCommitment C (srsOfBasis k basis) (fam.cvk basis) (fam.pub basis))).squeezeBase
      (IpaTranscriptElt.preT (fam.claim basis O)))

/-! ## 3. The bridge

`KimchiFamily.Wins` and `kimchiVerify` are the same challenge-generic verifier at nine
arguments. `kimchiVerify_eq_verifyWith_of_reads` identifies the deployed nine; `FSFaithful`
identifies the game's nine with them. Rewriting along it turns one `Bool` into the other. -/

/-- The family's claim at a table IS `runInputWith` at the six pre-opening reads — `claim`
unfolded through `runClaim`. Definitional; named so that the bridge never has to check a large
`Ipa.Input` equation by `rfl` under metavariables. -/
private theorem claim_eq_runInputWith (fam : KimchiFamily C nc k n)
    (basis : Zcash.Snark.AugmentedIndex (2 ^ k) → C.Point) (O : Coins C nc k) :
    fam.claim basis O
      = runInputWith (srsOfBasis k basis) (fam.cvk basis) (fam.proofOf basis O) (fam.pub basis)
          (reads (fam.digest basis) (fam.publicComm basis) (fam.proofOf basis O) O Squeeze.beta)
          (reads (fam.digest basis) (fam.publicComm basis) (fam.proofOf basis O) O Squeeze.gamma)
          (reads (fam.digest basis) (fam.publicComm basis) (fam.proofOf basis O) O Squeeze.alpha)
          (reads (fam.digest basis) (fam.publicComm basis) (fam.proofOf basis O) O Squeeze.zeta)
          (reads (fam.digest basis) (fam.publicComm basis) (fam.proofOf basis O) O
            Squeeze.polyscale)
          (reads (fam.digest basis) (fam.publicComm basis) (fam.proofOf basis O) O
            Squeeze.evalscale) := rfl

/-- **The deployed verifier at the game's nine arguments.** `kimchiVerify_eq_verifyWith_of_reads`
fed the nine `FSFaithful` equations: the four fq reads, the two fr reads, the `k` round reads,
the Schnorr read and the base agreement. The remaining three hypotheses of that theorem — the
public commitment, the public evaluation chunks and the claim — are definitional pins.

Private: `wins_iff_kimchiVerify` is the public face, and this is the `Bool` equation underneath
it. -/
private theorem kimchiVerify_eq_gameArgs (fam : KimchiFamily C nc k n)
    (basis : Zcash.Snark.AugmentedIndex (2 ^ k) → C.Point) (O : Coins C nc k)
    (h : FSFaithful fam basis O) :
    kimchiVerify C (srsOfBasis k basis) (fam.cvk basis) (fam.proofOf basis O) (fam.pub basis)
      = kimchiVerifyWith (srsOfBasis k basis) (fam.cvk basis) (fam.proofOf basis O)
          (fam.pub basis)
          (reads (fam.digest basis) (fam.publicComm basis) (fam.proofOf basis O) O Squeeze.beta)
          (reads (fam.digest basis) (fam.publicComm basis) (fam.proofOf basis O) O Squeeze.gamma)
          (reads (fam.digest basis) (fam.publicComm basis) (fam.proofOf basis O) O Squeeze.alpha)
          (reads (fam.digest basis) (fam.publicComm basis) (fam.proofOf basis O) O Squeeze.zeta)
          (reads (fam.digest basis) (fam.publicComm basis) (fam.proofOf basis O) O
            Squeeze.polyscale)
          (reads (fam.digest basis) (fam.publicComm basis) (fam.proofOf basis O) O
            Squeeze.evalscale)
          (uBaseOf C (Ipa.cipOf (fam.claim basis O)))
          (Vector.ofFn fun i : Fin k =>
            reads (fam.digest basis) (fam.publicComm basis) (fam.proofOf basis O) O
              (Squeeze.ipaRound i))
          (reads (fam.digest basis) (fam.publicComm basis) (fam.proofOf basis O) O
            Squeeze.schnorr) := by
  refine kimchiVerify_eq_verifyWith_of_reads (srsOfBasis k basis) (fam.cvk basis)
    (fam.proofOf basis O) (fam.pub basis)
    (publicCommitment C (srsOfBasis k basis) (fam.cvk basis) (fam.pub basis)) _ _ _ _ _ _
    (kimchiPubEvals (srsOfBasis k basis) (fam.cvk basis) (fam.proofOf basis O) (fam.pub basis))
    (fam.claim basis O) _ _ _
    rfl h.beta h.gamma h.alpha h.zeta ?_ h.polyscale h.evalscale
    (claim_eq_runInputWith fam basis O) h.base ?_ h.schnorr
  · -- the public evaluation chunks: `kimchiPubEvals` is `publicEvalChunks` at the deployed `ζ`,
    -- and the read `ζ` is that squeeze by `FSFaithful.zeta`.
    rw [h.zeta]
    rfl
  · -- the `k` round challenges, one `FSFaithful.round` per index
    exact congrArg _ (funext h.round)

/-- **On a faithful table the game's claim is the deployed claim.** The six pre-opening read
equations already pin the whole batched IPA claim: `KimchiFamily.claim` is `runInputWith` at the
six reads (`claim_eq_runInputWith`) and `kimchiRunInput` is `runInputWith` at the six deployed
squeezes, so the six equations identify them argument by argument.

This is what makes the remaining three conjuncts of `FSFaithful` — the round reads, the Schnorr
read and the base agreement — statable interchangeably at the game's claim or at the deployed
one: the two are the same input. -/
theorem claim_eq_kimchiRunInput (fam : KimchiFamily C nc k n)
    (basis : Zcash.Snark.AugmentedIndex (2 ^ k) → C.Point) (O : Coins C nc k)
    (h : FSFaithful fam basis O) :
    fam.claim basis O
      = kimchiRunInput (srsOfBasis k basis) (fam.cvk basis) (fam.proofOf basis O)
          (fam.pub basis) := by
  rw [claim_eq_runInputWith, h.beta, h.gamma, h.alpha, h.zeta, h.polyscale, h.evalscale]
  rfl

/-- **THE BRIDGE — the win predicate is deployed acceptance, on a faithful table.** For a family,
a basis and an oracle table faithful to the run, `KimchiFamily.Wins` holds exactly when the
deployed kimchi verifier returns `true` on that run's SRS, verifying key, emitted proof and
public input.

This is the theorem the endpoints are missing: they bound the measure of `Wins ∧ ¬ Extracts`,
and this says `Wins` *is* "the deployed verifier accepted" wherever the model is accurate.

Project-local: it relates two of this development's own constructions, the forking game's win
predicate and the executable kimchi verifier. -/
theorem wins_iff_kimchiVerify (fam : KimchiFamily C nc k n)
    (basis : Zcash.Snark.AugmentedIndex (2 ^ k) → C.Point) (O : Coins C nc k)
    (h : FSFaithful fam basis O) :
    fam.Wins basis O ↔
      kimchiVerify C (srsOfBasis k basis) (fam.cvk basis) (fam.proofOf basis O)
        (fam.pub basis) = true := by
  rw [KimchiFamily.Wins, kimchiVerify_eq_gameArgs fam basis O h]

end Faithful

/-! ## 4. The endpoints, over deployed acceptance

`wins_iff_kimchiVerify` converts deployed acceptance into `KimchiFamily.Wins` **pointwise on the
faithful locus**, so the deployed failure event intersected with that locus is a subset of the
event the endpoints bound. Monotonicity of the outer measure does the rest.

Read the caveat on each statement before quoting it: intersecting with the faithful locus
*restricts* the measured event. These are modelling statements, not stronger bounds. -/

/-- **Vesta: the endpoint bounds deployed extraction failure on the faithful locus.** Over a
uniformly sampled setup basis and a uniform challenge table, the measure of the event

* the **deployed** kimchi verifier accepts the family's proof, and
* the extractor fails to hand back a satisfying witness table, and
* the table is faithful to the run (`FSFaithful`)

is at most `vesta_kimchi_knowledge_sound`'s four-summand bound, verbatim.

**Caveat — this is a modelling statement, not a stronger probability bound.** Intersecting with
the faithful locus RESTRICTS the measured event; in the random-oracle model the faithful tables
are a null set (a uniform table agrees with the sponge at nine prescribed nodes with negligible
probability), and one conjunct of `FSFaithful` — the base agreement — is the warm/cold residue,
which is not a theorem at all. What this says is that *where the model is accurate*, the event
the endpoint measures is the deployed event. It is emphatically **not** "the deployed verifier is
knowledge-sound"; conflating the two is the standard way to overclaim a random-oracle result.

Project-local because it composes this development's own bridge with its own endpoint. -/
theorem vesta_deployed_failure_measure_le {nc k n : ℕ} [NeZero n]
    (B : IpaVesta.Point) (fam : KimchiFamily IpaVesta.curve nc k n)
    (coins : Zcash.Snark.RecursiveForkCoins Prechallenge (k + 1))
    (hcoins : coins.Complete) {R : ℕ} {ε δ : ℝ≥0∞}
    (hHard : fam.DiscreteLogRelationHardFor B coins R ε δ)
    (hEff : fam.ReductionEfficient coins R) :
    (PMF.uniformOfFintype
        ((SetupIndex (2 ^ k) → IpaVesta.curve.ScalarField) × Coins _ nc k)).toOuterMeasure
        ({q | kimchiVerify IpaVesta.curve
              (srsOfBasis k (augOfSetup (Zcash.Snark.scalarBasis B q.1)))
              (fam.cvk (augOfSetup (Zcash.Snark.scalarBasis B q.1)))
              (fam.proofOf (augOfSetup (Zcash.Snark.scalarBasis B q.1)) q.2)
              (fam.pub (augOfSetup (Zcash.Snark.scalarBasis B q.1))) = true ∧
            ¬ fam.ExtractsWitness (augOfSetup (Zcash.Snark.scalarBasis B q.1)) q.2 coins}
          ∩ {q | FSFaithful fam (augOfSetup (Zcash.Snark.scalarBasis B q.1)) q.2})
      ≤ (fam.Q + k + 1) * (3 / (2 ^ 128 : ℕ))
        + ((2 ^ k + 1 : ℕ) : ℝ≥0∞) * ε + δ
        + ((fam.Q + 1 : ℕ) : ℝ≥0∞) * ((szBudget nc n fam.idx.zkRows : ℝ≥0∞) / (2 ^ 128 : ℕ)) := by
  refine le_trans (MeasureTheory.measure_mono ?_)
    (vesta_kimchi_knowledge_sound B fam coins hcoins hHard hEff)
  rintro q ⟨⟨haccept, hfail⟩, hfaithful⟩
  exact ⟨(wins_iff_kimchiVerify fam _ q.2 hfaithful).mpr haccept, hfail⟩

/-- **Pallas: the endpoint bounds deployed extraction failure on the faithful locus.** The
Pallas-side twin of `vesta_deployed_failure_measure_le`, over `Fq`/`IpaPallas`; same shape, same
four summands, and the same caveat — intersecting with the faithful locus restricts the measured
event, so this is a modelling statement about where the random-oracle idealisation is accurate,
not a stronger probability bound. -/
theorem pallas_deployed_failure_measure_le {nc k n : ℕ} [NeZero n]
    (B : IpaPallas.Point) (fam : KimchiFamily IpaPallas.curve nc k n)
    (coins : Zcash.Snark.RecursiveForkCoins Prechallenge (k + 1))
    (hcoins : coins.Complete) {R : ℕ} {ε δ : ℝ≥0∞}
    (hHard : fam.DiscreteLogRelationHardFor B coins R ε δ)
    (hEff : fam.ReductionEfficient coins R) :
    (PMF.uniformOfFintype
        ((SetupIndex (2 ^ k) → IpaPallas.curve.ScalarField) × Coins _ nc k)).toOuterMeasure
        ({q | kimchiVerify IpaPallas.curve
              (srsOfBasis k (augOfSetup (Zcash.Snark.scalarBasis B q.1)))
              (fam.cvk (augOfSetup (Zcash.Snark.scalarBasis B q.1)))
              (fam.proofOf (augOfSetup (Zcash.Snark.scalarBasis B q.1)) q.2)
              (fam.pub (augOfSetup (Zcash.Snark.scalarBasis B q.1))) = true ∧
            ¬ fam.ExtractsWitness (augOfSetup (Zcash.Snark.scalarBasis B q.1)) q.2 coins}
          ∩ {q | FSFaithful fam (augOfSetup (Zcash.Snark.scalarBasis B q.1)) q.2})
      ≤ (fam.Q + k + 1) * (3 / (2 ^ 128 : ℕ))
        + ((2 ^ k + 1 : ℕ) : ℝ≥0∞) * ε + δ
        + ((fam.Q + 1 : ℕ) : ℝ≥0∞) * ((szBudget nc n fam.idx.zkRows : ℝ≥0∞) / (2 ^ 128 : ℕ)) := by
  refine le_trans (MeasureTheory.measure_mono ?_)
    (pallas_kimchi_knowledge_sound B fam coins hcoins hHard hEff)
  rintro q ⟨⟨haccept, hfail⟩, hfaithful⟩
  exact ⟨(wins_iff_kimchiVerify fam _ q.2 hfaithful).mpr haccept, hfail⟩

end Kimchi.Verifier.Forking.Bridge
