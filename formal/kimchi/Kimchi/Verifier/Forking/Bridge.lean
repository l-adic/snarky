import Kimchi.Verifier.KnowledgeSoundness

/-!
# The deployed bridge — the game's win predicate versus the deployed verifier

`Kimchi.Verifier.KnowledgeSoundness` proves two things that never meet:

* `kimchiVerify_eq_verifyWith` — the **deployed** verifier is the challenge-generic verifier
  `kimchiVerifyWith` at nine named transcript reads, the last three of which come from the
  **warm** opening source `kimchiOpeningFS` (the fq sponge continued from the post-`ζ` state);
* `vesta_kimchi_knowledge_sound` / `pallas_kimchi_knowledge_sound` — the endpoints, which
  measure `KimchiFamily.Wins`, i.e. the *same* generic verifier at six **table** reads and
  `k + 1` more table reads.

This module writes down exactly what separates them and proves everything on either side of it.

## The one difference

It is the **Fiat–Shamir idealisation**, and nothing else: the oracle table `O` supplies
challenges where the deployed run squeezes them. That is not a defect — it is the definition of
the random-oracle model, and it is what makes a forking argument possible at all. All one can ask
is that it be *faithful*: on a table agreeing with the sponge at the run's own nodes the two
predicates must coincide. That is `wins_iff_kimchiVerify` below, and it is proved.

There is no second difference. The opening base the game feeds the generic verifier is
`KimchiFamily.warmBase` — `toGroup` of `kimchiOpeningFS`'s base squeeze at the `preT` prefix of
the run's own claim — which is the very term the deployed verifier hands over, so the base slots
of the two sides are the same term and agree by `rfl`. (An earlier form of this development ran
the game at the COLD `uBaseOf C (Ipa.cipOf (fam.claim basis O))`, folded from
`Poseidon.FqSponge.init`, and carried the gap as a ninth `FSFaithful` field. That field was a
modelling hypothesis, false in general — Poseidon's state after absorbing the key digest, the
public commitment chunks, the witness chunks, the permutation and the quotient chunks is not the
initial state — and it is gone: the game moved to the warm base instead.) The standalone IPA
keeps its cold base and is right to, because there the opening *is* the whole protocol and its
sponge really does start cold; `Bulletproof.Ipa.Forking.spongeFS_eq_from` records precisely
that.

## Contents

1. A prose note recording why the IPA side legitimately keeps its cold base while the kimchi
   game moves to `KimchiFamily.warmBase`.
2. `FSFaithful` — the eight Fiat–Shamir read equations, bundled.
3. `wins_iff_kimchiVerify` — **the bridge**: on a faithful table the win predicate *is* deployed
   acceptance.

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
(`Ipa.Forking.spongeFS_eq_from`), so the standalone opening's base is literally the warm base of
a cold start. Nothing in this module consumes it; it is recorded because it is the reason the IPA
side legitimately keeps `uBaseOf` while the kimchi game moves to `KimchiFamily.warmBase`. -/

/-! ## 2. Fiat–Shamir faithfulness of a table, as a hypothesis

`FSFaithful fam basis O` bundles the eight equations that stand between `KimchiFamily.Wins` and
the deployed verifier, stated at the family's *own* data (`fam.cvk basis`, `fam.proofOf basis O`,
`fam.pub basis`, `fam.digest basis`) so that the bundle is literally the hypothesis set of
`kimchiVerify_eq_verifyWith_of_reads`.

All eight are Fiat–Shamir read equations, and nothing else is in the bundle: each says the table
`O` returns, at the run's own transcript node, exactly what the deployed sponge squeezes there.
The base slot needs no equation, because the game and the deployed verifier are handed the same
term there (`KimchiFamily.warmBase`). -/

section Faithful

variable {nc k n : ℕ} [NeZero n] [Module C.ScalarField C.Point]

/-- **A table faithful to the run.** Fix a family, a basis and an oracle table `O`. This says the
table agrees with the deployed Fiat–Shamir schedule at all eight places the win predicate and the
deployed verifier could differ: the four fq squeezes `beta`–`zeta`, the two fr squeezes
`polyscale`/`evalscale`, the `k` opening round squeezes `round`, and the Schnorr squeeze
`schnorr`. On a faithful table the random-oracle idealisation is exact at the run's own nodes.

Every field is a *Fiat–Shamir* read equation — an instance of the same idealisation — so the
bundle is homogeneous, and no modelling hypothesis about the opening base hides inside it: the
game and the deployed verifier receive the same base term, `KimchiFamily.warmBase`, and the
corresponding argument of `kimchiVerify_eq_verifyWith_of_reads` is closed by `rfl`.

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

/-! ## 3. The bridge

`KimchiFamily.Wins` and `kimchiVerify` are the same challenge-generic verifier at nine
arguments. `kimchiVerify_eq_verifyWith_of_reads` identifies the deployed nine; `FSFaithful`
identifies eight of the game's nine with them, and the ninth — the opening base — is the same
term on both sides. Rewriting along it turns one `Bool` into the other. -/

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
fed the eight `FSFaithful` equations — the four fq reads, the two fr reads, the `k` round reads
and the Schnorr read — plus the base agreement, which needs no hypothesis: `KimchiFamily.warmBase`
unfolds to `toGroup` of `kimchiOpeningFS`'s base squeeze at `preT` of the run's claim, and
`fam.claim basis O` IS that run's claim, so the two sides are the same term and `rfl` closes it.
The remaining three hypotheses of that theorem — the public commitment, the public evaluation
chunks and the claim — are definitional pins.

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
          (fam.warmBase basis O)
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
    (claim_eq_runInputWith fam basis O) rfl ?_ h.schnorr
  · -- the public evaluation chunks: `kimchiPubEvals` is `publicEvalChunks` at the deployed `ζ`,
    -- and the read `ζ` is that squeeze by `FSFaithful.zeta`.
    rw [h.zeta]
    rfl
  · -- the `k` round challenges, one `FSFaithful.round` per index
    exact congrArg _ (funext h.round)

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

end Kimchi.Verifier.Forking.Bridge
