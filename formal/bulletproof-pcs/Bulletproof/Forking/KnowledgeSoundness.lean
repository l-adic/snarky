import Bulletproof.Forking.Deployed
import Zcash.Snark.Soundness.AGM.ProbabilityCoins

/-!
# Deployed IPA knowledge soundness under discrete log

`Forking/Deployed.lean` proves `deployedExtract_failure_measure_le`: the measure of oracle tables
on which the adversary convinces the deployed wire verifier while the extractor returns *no
instance* is at most `(Q + σ.k + 1) · 3 / 2 ^ 128`. That is the query-loss half, and it is the
analogue of ironwood's `ComputedAlgebraicFSFamily.acceptExtractionFailure_measure_le`
(`Forking/Adversary/Algebraic.lean:1176`), which measures `¬ (…).output.isSome` — *presence* of an
instance, not which branch it took.

It is not the end of the argument upstream, and it is not the end here. `deployedExtract` returns
`Option (OpeningOrBreak …)`, whose right branch is an `AlgebraicRelationWitness` — a discrete-log
relation among the augmented generators. A run that returns a break satisfies the presence bound
while yielding no opening, and at a prime-order group a nontrivial relation among `2 ^ k + 2`
generators always exists (`Soundness.lean:104-108`). So the presence bound alone does not say the
extractor produces openings.

Ironwood charges that branch to discrete log. Its terminal statements measure
`accept ∧ ¬ hasCleanOpening` (`Algebraic.lean:1164`), where `hasCleanOpening` inspects the branch
(`∃ o, x.run = PSum.inl o`), and pay for the difference with a third summand
`|basis| · ε` under a textbook-DL advantage bound. The composition is
`snarkFailure_prob_le_of_textbookDL` (`Algebraic.lean:1218`): the failure event is covered by the
presence-failure set together with the relation-finding set, `MeasureTheory.measure_union_le`
splits them, and `snarkRelation_prob_le_of_textbookDL` (`:892`) — a one-line wrapper over
`Zcash.Snark.relationWithCoins_prob_le_of_textbookDL` (`AGM/ProbabilityCoins.lean:182`) — bounds
the second.

This module states that composition at the deployed instantiation. The pieces it needs from
upstream are all generic and already present; nothing here re-derives a probability lemma.

## The sampled basis

The discrete-log reduction fixes a hidden slot in a *sampled* public basis
(`Zcash.Snark.scalarBasis`, `AGM/Probability.lean:56`), and `AlgebraicRelationWitness` is indexed
by that basis. A statement at one fixed `SRS` therefore cannot type the relation finder, which is
why ironwood carries `ComputedAlgebraicFSFamily` with its verifying key and adversary as functions
of the basis, and why `DeployedFamily` below does the same.

## The `U` slot

Kimchi derives the IPA base `U` from the transcript (`uBaseOf`, a map-to-curve of the
combined-inner-product challenge), where halo2 takes it from the public parameters. The identity
`hU` below is exactly that gap. Ironwood closes the same gap for its own hash-to-curve parameter
derivation with the generator random-oracle setup model — `orchardGeneratorROBasis`
(`AGM/ProbabilityVesta.lean:113`), documented there as modelling `gᵢ = H(0 ‖ i)`, `W = H(1)`,
`U = H(2)` — and lifts the bound through it in three lines
(`snarkFailure_prob_le_of_generatorRO_textbookDL`, `Algebraic.lean:1386`). Carrying `hU` as a
hypothesis here keeps that step separable and honest.
-/

namespace Bulletproof.Ipa.Forking

open Bulletproof Bulletproof.Forking Poseidon
open scoped ENNReal

variable {C : Ipa.CommitmentCurve} {k m p : ℕ}

section KnowledgeSoundness

variable [Module C.ScalarField C.Point]

/-! ## Reading a sampled basis as an SRS -/

/-- An augmented public basis read as one of our SRSs: ironwood's `ursOfAugmentedBasis`
(`AGM/Adapter.lean:336`) composed with `Forking.srsOf` (`Forking/Adapter.lean:36`). The slot
correspondence is `gen i ↦ g i`, `u ↦ U`, `w ↦ h`. -/
def srsOfBasis (k : ℕ) (basis : Zcash.Snark.AugmentedIndex (2 ^ k) → C.Point) : SRS C.Point :=
  Bulletproof.Forking.srsOf (Zcash.Snark.ursOfAugmentedBasis k basis)

omit [Module C.ScalarField C.Point] in
@[simp] theorem srsOfBasis_k (basis : Zcash.Snark.AugmentedIndex (2 ^ k) → C.Point) :
    (srsOfBasis k basis).k = k := rfl

omit [Module C.ScalarField C.Point] in
/-- Reassembling the augmented basis from the SRS slots loses no group element — ironwood's
round-trip `augmentedBasis_ursOfAugmentedBasis` (`AGM/Adapter.lean:344`) at our slot names. -/
@[simp] theorem augmentedBasis_srsOfBasis
    (basis : Zcash.Snark.AugmentedIndex (2 ^ k) → C.Point) :
    Zcash.Snark.augmentedBasis (srsOfBasis k basis).g (srsOfBasis k basis).U
      (srsOfBasis k basis).h = basis :=
  Zcash.Snark.augmentedBasis_ursOfAugmentedBasis k basis

/-! ## The basis-indexed adversary family -/

/-- **A basis-indexed deployed adversary family** — our analogue of
`Zcash.Snark.ComputedAlgebraicFSFamily` (`Forking/Adversary/Algebraic.lean:843`). One claim and
one bounded-query adversary per augmented public basis, together with the AGM representation of
the combined commitment at that basis. -/
structure DeployedFamily (C : Ipa.CommitmentCurve) [Module C.ScalarField C.Point]
    (k m p : ℕ) where
  /-- The claim presented at each basis. -/
  claim : (basis : Zcash.Snark.AugmentedIndex (2 ^ k) → C.Point) → Ipa.Input C k m p
  /-- The bounded-query algebraic adversary at each basis. -/
  adversary : (basis : Zcash.Snark.AugmentedIndex (2 ^ k) → C.Point) →
    Zcash.Snark.OracleComp (IpaNode C k) Prechallenge (Ipa.Proof C k)
  /-- The AGM generator coefficients of the combined commitment, at each basis. -/
  pg : (basis : Zcash.Snark.AugmentedIndex (2 ^ k) → C.Point) → Fin (2 ^ k) → C.ScalarField
  /-- The AGM blinding coefficient of the combined commitment, at each basis. -/
  pw : (basis : Zcash.Snark.AugmentedIndex (2 ^ k) → C.Point) → C.ScalarField
  /-- The AGM root representation itself — kimchi's Pedersen shape, since `U` is transcript-derived
  after the commitment is fixed. -/
  hP : ∀ basis,
    combinedCommitment (claim basis).polyscale (claim basis).commitmentFn
      = commitGen (srsOfBasis k basis).g (pg basis) + pw basis • (srsOfBasis k basis).h
  /-- The query bound shared by the whole family. -/
  Q : ℕ
  /-- Every basis's adversary respects it. -/
  queryBound : ∀ basis, (adversary basis).QueryBound Q

namespace DeployedFamily

variable (fam : DeployedFamily C k m p)

/-- The oracle table the adversary and the extractor share — ironwood's `Coins`
(`Algebraic.lean:857`) carries the recursive fork tape alongside; here that tape stays a
parameter, which makes the bound hold for every complete tape rather than on average. -/
abbrev Coins (_fam : DeployedFamily C k m p) : Type := IpaNode C k → Prechallenge

/-- One run of the deployed extractor, at a basis and an oracle table — ironwood's
`instanceAttempt` (`Algebraic.lean:862`). -/
def attempt (basis : Zcash.Snark.AugmentedIndex (2 ^ k) → C.Point) (O : fam.Coins)
    (coins : Zcash.Snark.RecursiveForkCoins Prechallenge (k + 1)) :
    Option (OpeningOrBreak
      { srsOfBasis k basis with U := uBaseOf C (Ipa.cipOf (fam.claim basis)) }
      (combinedCommitment (fam.claim basis).polyscale (fam.claim basis).commitmentFn)
      (combinedEvalVector (2 ^ k) (fam.claim basis).evalscale (fam.claim basis).pointFn)
      (Ipa.cipOf (fam.claim basis))) :=
  deployedExtract (srsOfBasis k basis) (Ipa.cipOf (fam.claim basis))
    (combinedEvalVector (2 ^ k) (fam.claim basis).evalscale (fam.claim basis).pointFn)
    (Ipa.cipOf (fam.claim basis))
    (combinedCommitment (fam.claim basis).polyscale (fam.claim basis).commitmentFn)
    (fam.pg basis) (fam.pw basis) (fam.hP basis) (fam.adversary basis) O coins

/-- **The extractor returned an opening** — ironwood's `hasCleanOpening` (`Algebraic.lean:1164`) at
our types. It inspects the `PSum` branch, which `deployedExtract … = none` does not: that is the
entire difference between the query-loss rung and the statement below. -/
def HasOpening (basis : Zcash.Snark.AugmentedIndex (2 ^ k) → C.Point) (O : fam.Coins)
    (coins : Zcash.Snark.RecursiveForkCoins Prechallenge (k + 1)) : Prop :=
  ∃ w, fam.attempt basis O coins = some (PSum.inl w)

/-- With the sampled basis's `u` slot identified with the transcript-derived `U`, the extractor's
break lives over the sampled basis itself. See the module docstring on the `U` slot. -/
theorem augmentedBasis_attempt (basis : Zcash.Snark.AugmentedIndex (2 ^ k) → C.Point)
    (hU : basis Zcash.Snark.AugmentedIndex.u = uBaseOf C (Ipa.cipOf (fam.claim basis))) :
    Zcash.Snark.augmentedBasis (srsOfBasis k basis).g
        (uBaseOf C (Ipa.cipOf (fam.claim basis))) (srsOfBasis k basis).h = basis := by
  rw [← hU]
  exact augmentedBasis_srsOfBasis basis

/-- **The break branch as a basis-indexed relation finder** — ironwood's `snarkRelationFinder`
(`Algebraic.lean:880`), which is the object the fixed-slot discrete-log reduction consumes. -/
def relationFinder
    (hU : ∀ basis, basis Zcash.Snark.AugmentedIndex.u
      = uBaseOf C (Ipa.cipOf (fam.claim basis)))
    (coins : Zcash.Snark.RecursiveForkCoins Prechallenge (k + 1)) :
    (basis : Zcash.Snark.AugmentedIndex (2 ^ k) → C.Point) → fam.Coins →
      Option (Zcash.Snark.AlgebraicRelationWitness (F := C.ScalarField) basis) :=
  fun basis O =>
    match fam.attempt basis O coins with
    | none => none
    | some (PSum.inl _) => none
    | some (PSum.inr rel) => some (fam.augmentedBasis_attempt basis (hU basis) ▸ rel)

end DeployedFamily

/-! ## The statement -/

/-- **Deployed IPA knowledge soundness under textbook discrete log.** Over a uniformly sampled
augmented public basis and a uniform oracle table, the probability that the executable wire
verifier accepts *and* the executable extractor fails to return an **opening** is at most the
recursive query loss plus the fixed-slot discrete-log loss.

The analogue of `Zcash.Snark.ComputedAlgebraicFSFamily.snarkFailure_prob_le_of_textbookDL`
(`Forking/Adversary/Algebraic.lean:1218`). Three deliberate differences, all inherited from the
first summand and each justified at `deployedExtract_failure_measure_le`: `fam.Q + k + 1` rather
than `Q + k`, for kimchi's Schnorr round, which halo2 has not; `3 / 2 ^ 128` rather than
`3 / Fintype.card F`, because the challenges are 128-bit prechallenges pushed through
`endoExpand`; and no `(Q + 1) / |F|` zero-challenge slice, which `hne` empties.

The intended route mirrors upstream `Algebraic.lean:1230-1257` step for step: cover the failure
event by the presence-failure set together with `Zcash.Snark.relSetWithCoins`, split with
`MeasureTheory.measure_union_le`, then `add_le_add` of `deployedExtract_failure_measure_le`
(through `Zcash.Snark.uniformOfFintype_prod_fiber_bound_right`) and
`Zcash.Snark.relationWithCoins_prob_le_of_textbookDL` (`AGM/ProbabilityCoins.lean:182`). -/
theorem deployedExtract_noOpening_measure_le_of_textbookDL
    (hsmul : ∀ (z : C.ScalarField) (Q : C.Point), z • Q = z.val • Q)
    (hinj : Function.Injective (expandPre C)) (hne : ∀ q, expandPre C q ≠ 0)
    (B : C.Point) (fam : DeployedFamily C k m p)
    (hU : ∀ basis, basis Zcash.Snark.AugmentedIndex.u
      = uBaseOf C (Ipa.cipOf (fam.claim basis)))
    (coins : Zcash.Snark.RecursiveForkCoins Prechallenge (k + 1))
    (hcoins : coins.Complete) {ε : ℝ≥0∞}
    (hDL : Zcash.Snark.TextbookDLWithCoinsAdvantageLE B (fam.relationFinder hU coins) ε) :
    (PMF.uniformOfFintype
        ((Zcash.Snark.AugmentedIndex (2 ^ k) → C.ScalarField) × fam.Coins)).toOuterMeasure
        {q | wireWins (srsOfBasis k (Zcash.Snark.scalarBasis B q.1))
                (fam.claim (Zcash.Snark.scalarBasis B q.1)) q.2
                ((fam.adversary (Zcash.Snark.scalarBasis B q.1)).run q.2) ∧
          ¬ fam.HasOpening (Zcash.Snark.scalarBasis B q.1) q.2 coins}
      ≤ (fam.Q + k + 1) * (3 / (2 ^ 128 : ℕ))
        + Fintype.card (Zcash.Snark.AugmentedIndex (2 ^ k)) * ε := by
  sorry

end KnowledgeSoundness

end Bulletproof.Ipa.Forking
