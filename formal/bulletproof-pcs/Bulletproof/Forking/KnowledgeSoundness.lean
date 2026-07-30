import Bulletproof.Forking.Deployed
import Zcash.Snark.Soundness.AGM.ProbabilityCoins
import Pasta.Basic
import Bulletproof.Forking.Honest

/-!
# Deployed IPA knowledge soundness under discrete log

`Forking/Deployed.lean` proves `deployedExtract_failure_measure_le`: the measure of oracle tables
on which the adversary convinces the deployed wire verifier while the extractor returns *no
instance* is at most `(Q + σ.k + 1) · 3 / 2 ^ 128`. That is the query-loss half — the analogue of
ironwood's `acceptExtractionFailure_measure_le` (`Forking/Adversary/Algebraic.lean:1176`), which
measures `¬ (…).output.isSome`: *presence* of an instance, not which branch it took.

That is not the end of the argument upstream, and it is not the end here. `deployedExtract`
returns `Option (OpeningOrBreak …)`, whose right branch is an `AlgebraicRelationWitness` — a
discrete-log relation among the augmented generators. A run returning a break satisfies the
presence bound while yielding no opening, and at prime order a nontrivial relation among the
`2 ^ k + 2` slots of the augmented basis always exists — the same counting argument
`Bulletproof.Soundness` makes for `2 ^ k + 1` generators. So the presence bound alone does not
say the extractor produces openings.

This module states the branch-inspecting bound. `HasOpening` demands `PSum.inl`, mirroring
ironwood's `hasCleanOpening` (`Algebraic.lean:1164`), and the break branch is paid for rather
than excused.

## The `U` slot, and why the sampled basis omits it

Of the `2 ^ k + 2` slots of `augmentedBasis σ.g σ.U σ.h`, only the `2 ^ k + 1` **setup** slots
(`σ.g`, `σ.h`) are hash-to-curve parameters fixed at SRS generation. `σ.U` is **transcript
derived** — `deployedExtract` overrides it with `uBaseOf C cip` — which the deployed Rust protocol
fixes and we do not choose. The fixed-slot discrete-log reduction plants its challenge in a
uniformly sampled slot, which is legitimate for a setup parameter and not for a derived one.

So the reduction samples the setup slots only (`SetupIndex`), injected into the augmented index
with a **dead** `u` slot (`augOfSetup`). That is sound because `σ.U` is dead in both the acceptance
event and the extractor — `Ipa.verifyWith` reads only `σ.g`/`σ.h` and takes `uBase` as a separate
argument, while `deployedExtract` overrides `σ.U` — recorded as `wireWins_U_irrelevant` and
`deployedExtract_U_irrelevant`, both `rfl`. `HasOpening` and `DeployedFamily` are therefore
unchanged, and the reduction pays one slot *fewer* than the full augmented basis.

The extractor's break is then split on its `U` coefficient:

* coefficient `0` — a relation among the *sampled* generators, charged to textbook discrete log
  exactly as upstream (`relationWithCoins_prob_le_of_textbookDL`, which is index-generic);
* coefficient `≠ 0` — a discrete-log representation of the transcript-derived base over the
  sampled generators (`uRepresentationOfBreak`, computed data). No challenge can be planted at a
  transcript-derived point, so this is **not** reducible to textbook discrete log; it is carried
  as an explicit third summand under `DerivedUDLAdvantageLE`.

Read `derivedUDL_iff_residual_measure` alongside that assumption: it is the residual event's own
measure, so unlike `ε` it is not a reduction to a standard problem. Ironwood never meets this
case — its `U` is the setup parameter `H(2)` (`AGM/ProbabilityVesta.lean:118-122`).

Compared with `Zcash.Snark.ComputedAlgebraicFSFamily.snarkFailure_prob_le_of_textbookDL`
(`Algebraic.lean:1218`), the first two summands are its two, with the three deployed deviations
documented at `deployedExtract_failure_measure_le`; the third is new.
-/

namespace Bulletproof.Ipa.Forking

open Bulletproof Bulletproof.Forking Poseidon
open scoped ENNReal

section KnowledgeSoundness

variable {C : Ipa.CommitmentCurve} {k m p : ℕ} [Module C.ScalarField C.Point]

/-! ## Reading a sampled basis as an SRS -/

/-- An augmented public basis read as one of our SRSs: ironwood's `ursOfAugmentedBasis`
(`AGM/Adapter.lean:336`) composed with `Forking.srsOf` (`Forking/Adapter.lean:36`). The slot
correspondence is `gen i ↦ g i`, `u ↦ U`, `w ↦ h`. -/
def srsOfBasis (k : ℕ) (basis : Zcash.Snark.AugmentedIndex (2 ^ k) → C.Point) : SRS C.Point :=
  Bulletproof.Forking.srsOf (Zcash.Snark.ursOfAugmentedBasis k basis)

omit [Module C.ScalarField C.Point] in
@[simp] theorem srsOfBasis_k (basis : Zcash.Snark.AugmentedIndex (2 ^ k) → C.Point) :
    (srsOfBasis k basis).k = k := rfl

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

/-- The oracle table the adversary and the extractor share — ironwood's `Coins`
(`Algebraic.lean:857`) carries the recursive fork tape alongside; here that tape stays a
parameter, which makes the bound hold for every complete tape rather than on average. -/
abbrev Coins (C : Ipa.CommitmentCurve) (k : ℕ) : Type := IpaNode C k → Prechallenge

namespace DeployedFamily

variable (fam : DeployedFamily C k m p)

/-- One run of the deployed extractor, at a basis and an oracle table — ironwood's
`instanceAttempt` (`Algebraic.lean:862`). -/
def attempt (basis : Zcash.Snark.AugmentedIndex (2 ^ k) → C.Point) (O : Coins C k)
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
def HasOpening (basis : Zcash.Snark.AugmentedIndex (2 ^ k) → C.Point) (O : Coins C k)
    (coins : Zcash.Snark.RecursiveForkCoins Prechallenge (k + 1)) : Prop :=
  ∃ w, fam.attempt basis O coins = some (PSum.inl w)

/-- **Accepting runs on which the extractor produced nothing at all** — ironwood's
`acceptExtractionFailure` (`Algebraic.lean:1169`) at our types. The *presence* failure the
query-loss rung already bounds: `deployedExtract_failure_measure_le` is stated at exactly this
set, since `fam.attempt` is `deployedExtract` by definition. -/
def acceptExtractionFailure (basis : Zcash.Snark.AugmentedIndex (2 ^ k) → C.Point)
    (coins : Zcash.Snark.RecursiveForkCoins Prechallenge (k + 1)) : Set (Coins C k) :=
  {O | wireWins (srsOfBasis k basis) (fam.claim basis) O ((fam.adversary basis).run O) ∧
    fam.attempt basis O coins = none}

end DeployedFamily

end KnowledgeSoundness

/-! ## 1. The setup-only basis -/

section Basis

variable {G : Type*} [AddCommGroup G]

/-- **The setup slots**: the `n` URS generators and the blinding generator. No `U` slot — `U` is
transcript derived, not a setup parameter. -/
abbrev SetupIndex (n : ℕ) := Fin n ⊕ Unit

namespace SetupIndex

/-- The slot of a URS generator. -/
def gen {n : ℕ} (i : Fin n) : SetupIndex n := Sum.inl i

/-- The slot of the blinding generator. -/
def blind {n : ℕ} : SetupIndex n := Sum.inr ()

end SetupIndex

/-- The setup-only public basis `(g, h)`. -/
private def setupBasis {n : ℕ} (g : Fin n → G) (H : G) : SetupIndex n → G
  | Sum.inl i => g i
  | Sum.inr _ => H

/-- Inject a setup basis into the augmented index, with a **dead** `u` slot. Nothing downstream
reads it: `wireWins` never touches `σ.U`, and `deployedExtract` overrides it. -/
def augOfSetup {n : ℕ} (bs : SetupIndex n → G) : Zcash.Snark.AugmentedIndex n → G
  | Sum.inl i => bs (Sum.inl i)
  | Sum.inr j => if j = 0 then 0 else bs (Sum.inr ())

/-- The slot count the DL reduction pays: one **better** than the incumbent `2 ^ k + 2`. -/
theorem card_setupIndex (n : ℕ) : Fintype.card (SetupIndex n) = n + 1 := by simp

end Basis

/-! ## 2. Reading an injected setup basis back off the SRS — `hU`'s replacement -/

section Roundtrip

variable {C : Ipa.CommitmentCurve} {k : ℕ} [Module C.ScalarField C.Point]

omit [Module C.ScalarField C.Point] in
/-- The same after the extractor's `U` override — the form the transport in `relationFinder`
needs, since the break's basis is read off `{ srsOfBasis k basis with U := uBaseOf C cip }`. -/
@[simp] theorem setupBasis_srsOfBasis_augOfSetup_override (bs : SetupIndex (2 ^ k) → C.Point)
    (X : C.Point) :
    setupBasis ({ srsOfBasis k (augOfSetup bs) with U := X }).g
        ({ srsOfBasis k (augOfSetup bs) with U := X }).h = bs := by
  funext i
  rcases i with i | u
  · rfl
  · cases u; rfl

/-- **The presented SRS's `U` slot is dead** — two SRSs differing only in `U` give the same
extractor run, by `rfl`. This is what licenses the dead slot in `augOfSetup`. -/
theorem deployedExtract_U_irrelevant (σ : SRS C.Point) (X : C.Point) (cip : C.ScalarField)
    (b : Fin (2 ^ σ.k) → C.ScalarField) (v : C.ScalarField) (P : C.Point)
    (pg : Fin (2 ^ σ.k) → C.ScalarField) (pw : C.ScalarField)
    (hP : P = commitGen σ.g pg + pw • σ.h)
    (A : Zcash.Snark.OracleComp (IpaNode C σ.k) Prechallenge (Ipa.Proof C σ.k))
    (O : IpaNode C σ.k → Prechallenge)
    (coins : Zcash.Snark.RecursiveForkCoins Prechallenge (σ.k + 1)) :
    deployedExtract σ cip b v P pg pw hP A O coins
      = deployedExtract { σ with U := X } cip b v P pg pw hP A O coins := rfl

omit [Module C.ScalarField C.Point] in
/-- Same for the win event: `Ipa.verifyWith` reads only `σ.g` and `σ.h`. -/
theorem wireWins_U_irrelevant {m p : ℕ} (σ : SRS C.Point) (X : C.Point)
    (claim : Ipa.Input C σ.k m p) (O : IpaNode C σ.k → Prechallenge)
    (π : Ipa.Proof C σ.k) :
    wireWins σ claim O π = wireWins { σ with U := X } claim O π := rfl

end Roundtrip

/-! ## 3. Splitting a break on its `U` coefficient -/

section Split

variable {F G : Type*} [Field F] [AddCommGroup G] [Module F G]

/-- Forget a coefficient vector's `U` entry. -/
private def dropU {n : ℕ} (c : Zcash.Snark.AugmentedIndex n → F) : SetupIndex n → F
  | Sum.inl i => c (Sum.inl i)
  | Sum.inr _ => c Zcash.Snark.AugmentedIndex.w

/-- **The general split of the augmented MSM**, with no hypothesis on the `U` coefficient. -/
private theorem representationEval_dropU_general {n : ℕ} (g : Fin n → G) (U H : G)
    (c : Zcash.Snark.AugmentedIndex n → F) :
    Zcash.Snark.representationEval (Zcash.Snark.augmentedBasis g U H) c
      = Zcash.Snark.representationEval (setupBasis g H) (dropU c)
        + c Zcash.Snark.AugmentedIndex.u • U := by
  simp only [Zcash.Snark.representationEval, Fintype.sum_sum_type, Fin.sum_univ_two,
    setupBasis, dropU, Zcash.Snark.augmentedBasis, Zcash.Snark.AugmentedIndex.w,
    Zcash.Snark.AugmentedIndex.u, Finset.univ_unique, Finset.sum_singleton]
  simp only [show ((1 : Fin 2) = 0) = False by simp, if_true, if_false]
  abel

/-- A break whose `U` coefficient vanishes **is** a break over the setup-only basis. Nontriviality
is free: `coeffs ≠ 0` together with `coeffs u = 0` forces a nonzero setup coefficient, so the
restriction never fails. -/
def restrictToSetup {n : ℕ} {g : Fin n → G} {U H : G}
    (r : Zcash.Snark.AlgebraicRelationWitness (F := F) (Zcash.Snark.augmentedBasis g U H))
    (hu : r.coeffs Zcash.Snark.AugmentedIndex.u = 0) :
    Zcash.Snark.AlgebraicRelationWitness (F := F) (setupBasis g H) where
  coeffs := dropU r.coeffs
  nontrivial := by
    intro hzero
    apply r.nontrivial
    funext i
    rcases i with i | j
    · exact congrFun hzero (Sum.inl i)
    · fin_cases j
      · exact hu
      · exact congrFun hzero (Sum.inr ())
  relation := by
    have h := representationEval_dropU_general (F := F) g U H r.coeffs
    rw [r.relation, hu, zero_smul, add_zero] at h
    exact h.symm

/-- **The residual, as computed data.** A break whose `U` coefficient is nonzero is an AGM
representation of the transcript-derived base `U` over the sampled setup generators — the
adversary opened `uBaseOf C cip` in `(g, h)`. Data-valued, not a `Prop`-level `∃`: this is what
keeps the third summand's assumption from being vacuous. -/
def uRepresentationOfBreak {n : ℕ} {g : Fin n → G} {U H : G}
    (r : Zcash.Snark.AlgebraicRelationWitness (F := F) (Zcash.Snark.augmentedBasis g U H))
    (hu : r.coeffs Zcash.Snark.AugmentedIndex.u ≠ 0) :
    Zcash.Snark.GroupRepresentation (F := F) (setupBasis g H) U where
  coeffs := fun i => -(r.coeffs Zcash.Snark.AugmentedIndex.u)⁻¹ * dropU r.coeffs i
  hEq := by
    have hsplit := representationEval_dropU_general g U H r.coeffs
    rw [r.relation] at hsplit
    have hbase : Zcash.Snark.representationEval (setupBasis g H) (dropU r.coeffs)
        = -(r.coeffs Zcash.Snark.AugmentedIndex.u) • U := by
      rw [neg_smul, eq_neg_iff_add_eq_zero, ← hsplit]
    have hscale : Zcash.Snark.representationEval (setupBasis g H)
        (fun i => -(r.coeffs Zcash.Snark.AugmentedIndex.u)⁻¹ * dropU r.coeffs i)
        = (-(r.coeffs Zcash.Snark.AugmentedIndex.u)⁻¹) •
            Zcash.Snark.representationEval (setupBasis g H) (dropU r.coeffs) := by
      simp only [Zcash.Snark.representationEval, Finset.smul_sum, mul_smul]
    rw [hscale, hbase, smul_smul,
      show -(r.coeffs Zcash.Snark.AugmentedIndex.u)⁻¹ * -(r.coeffs Zcash.Snark.AugmentedIndex.u)
        = 1 from by field_simp]
    exact one_smul _ _

end Split

/-! ## 4. The revised relation finder, and the residual -/

section Finder

variable {C : Ipa.CommitmentCurve} {k m p : ℕ} [Module C.ScalarField C.Point]
variable (fam : DeployedFamily C k m p)

/-- **The break branch as a relation finder over the SETUP-ONLY basis** — the object the
fixed-slot discrete-log reduction consumes, at `ι := SetupIndex (2 ^ k)`.

No `hU`: the transport is the unconditional round trip
`setupBasis_srsOfBasis_augOfSetup_override`. The `U`-touching breaks are filtered out here and
become the residual `TouchesU` below. -/
def relationFinder (coins : Zcash.Snark.RecursiveForkCoins Prechallenge (k + 1)) :
    (bs : SetupIndex (2 ^ k) → C.Point) → Coins C k →
      Option (Zcash.Snark.AlgebraicRelationWitness (F := C.ScalarField) bs) :=
  fun bs O =>
    match fam.attempt (augOfSetup bs) O coins with
    | none => none
    | some (PSum.inl _) => none
    | some (PSum.inr rel) =>
        if hu : rel.coeffs Zcash.Snark.AugmentedIndex.u = 0 then
          some (setupBasis_srsOfBasis_augOfSetup_override bs
            (uBaseOf C (Ipa.cipOf (fam.claim (augOfSetup bs)))) ▸ restrictToSetup rel hu)
        else none

/-- **The residual event**: the extractor returned a break that *touches the transcript-derived
base*. Such a break is not a relation among the sampled setup generators, so it is invisible to
the fixed-slot DL reduction. This event has no counterpart in the incumbent two-way cover — it is
where `hU` used to be doing (illegitimate) work. -/
def TouchesU (bs : SetupIndex (2 ^ k) → C.Point) (O : Coins C k)
    (coins : Zcash.Snark.RecursiveForkCoins Prechallenge (k + 1)) : Prop :=
  ∃ rel, fam.attempt (augOfSetup bs) O coins = some (PSum.inr rel) ∧
    rel.coeffs Zcash.Snark.AugmentedIndex.u ≠ 0

/-- **What the residual computes.** At a *sampled* setup basis every setup log over `B` is known
by construction (`scalarBasis B s i = s i • B`), so a `U`-touching break yields the discrete log
of the transcript-derived base `uBaseOf C (Ipa.cipOf (fam.claim …))` itself. Upstream's
`discreteLogOfBasis_of_relation` (`AGM/Adapter.lean:211`) at slot `u`. -/
def derivedULog (B : C.Point) (coins : Zcash.Snark.RecursiveForkCoins Prechallenge (k + 1))
    (s : SetupIndex (2 ^ k) → C.ScalarField) (O : Coins C k) :
    Option (Zcash.Snark.DiscreteLogRepresentation (F := C.ScalarField) B
      (uBaseOf C (Ipa.cipOf (fam.claim (augOfSetup (Zcash.Snark.scalarBasis B s)))))) :=
  match fam.attempt (augOfSetup (Zcash.Snark.scalarBasis B s)) O coins with
  | none => none
  | some (PSum.inl _) => none
  | some (PSum.inr rel) =>
      if hu : rel.coeffs Zcash.Snark.AugmentedIndex.u = 0 then none
      else
        some (Zcash.Snark.discreteLogOfBasis_of_relation B _
          (Zcash.Snark.augmentedCoeffs (fun i => s (SetupIndex.gen i)) 0 (s SetupIndex.blind))
          Zcash.Snark.AugmentedIndex.u rel
          (by
            rintro (i | j) hi
            · rfl
            · fin_cases j
              · exact absurd rfl hi
              · rfl)
          hu)

/-- **The derived-`U` discrete-log assumption** — the third summand's price, stated openly.

It says: over a uniformly sampled *setup* basis and a uniform oracle table, the extractor's break
computes a discrete log of the transcript-derived IPA base with probability at most `bound`.

This is **strictly beyond** ironwood's setup-generator random-oracle idealization
(`orchardGeneratorROBasis`, `AGM/ProbabilityVesta.lean:113`), which covers `gᵢ = H(0 ‖ i)`,
`W = H(1)`, `U = H(2)` — all *setup* parameters. Kimchi's `U` is a map-to-curve of a sponge output
consumed *after* the commitment is fixed, so no challenge can be planted there and the event
cannot be reduced to textbook DL. It is not hidden inside `hU`, and it is not claimed to follow
from anything upstream. -/
def DerivedUDLAdvantageLE (B : C.Point)
    (coins : Zcash.Snark.RecursiveForkCoins Prechallenge (k + 1)) (bound : ℝ≥0∞) : Prop :=
  (PMF.uniformOfFintype ((SetupIndex (2 ^ k) → C.ScalarField) × Coins C k)).toOuterMeasure
      {q | (derivedULog fam B coins q.1 q.2).isSome} ≤ bound

/-- The residual event is exactly the event `derivedULog` succeeds on: the assumption above bounds
the residual and nothing else. -/
theorem derivedULog_isSome_iff (B : C.Point)
    (coins : Zcash.Snark.RecursiveForkCoins Prechallenge (k + 1))
    (s : SetupIndex (2 ^ k) → C.ScalarField) (O : Coins C k) :
    (derivedULog fam B coins s O).isSome ↔
      TouchesU fam (Zcash.Snark.scalarBasis B s) O coins := by
  classical
  constructor
  · intro h
    by_cases hsome : (fam.attempt (augOfSetup (Zcash.Snark.scalarBasis B s)) O coins).isSome
    · obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hsome
      cases x with
      | inl o => simp [derivedULog, hx] at h
      | inr rel =>
        by_cases hu : rel.coeffs Zcash.Snark.AugmentedIndex.u = 0
        · simp [derivedULog, hx] at h
          exact absurd hu h
        · exact ⟨rel, hx, hu⟩
    · rw [Option.not_isSome_iff_eq_none] at hsome
      simp [derivedULog, hsome] at h
  · rintro ⟨rel, hx, hu⟩
    simp only [derivedULog, hx, dif_neg hu, Option.isSome_some]

/-- **`δ` is the residual event's own measure** — read this next to `DerivedUDLAdvantageLE`, and
do not mistake the two cryptographic hypotheses for the same kind of thing.

`ε` bounds the win set of the *discrete-log game*, over the probability space
`F × ι × (ι → F) × ρ`: a genuine reduction, connecting this protocol to a studied problem. `δ`
bounds a set on the *same* space as the conclusion, and this equivalence says it is the third
piece of `three_way_cover` restated. So assuming `δ` small is assuming that slice of the
conclusion, not deducing it — which is the honest reading, and the reason the `U`-touching runs
are described as unreduced rather than charged. -/
theorem derivedUDL_iff_residual_measure (B : C.Point)
    (coins : Zcash.Snark.RecursiveForkCoins Prechallenge (k + 1)) (δ : ℝ≥0∞) :
    DerivedUDLAdvantageLE fam B coins δ ↔
      (PMF.uniformOfFintype
          ((SetupIndex (2 ^ k) → C.ScalarField) × Coins C k)).toOuterMeasure
        {q | TouchesU fam (Zcash.Snark.scalarBasis B q.1) q.2 coins} ≤ δ := by
  have hset : {q : (SetupIndex (2 ^ k) → C.ScalarField) × Coins C k |
        TouchesU fam (Zcash.Snark.scalarBasis B q.1) q.2 coins}
      = {q | (derivedULog fam B coins q.1 q.2).isSome} := by
    ext q
    exact (derivedULog_isSome_iff fam B coins q.1 q.2).symm
  rw [hset]
  exact Iff.rfl

end Finder

/-! ## 5. The three-way cover -/

section Cover

variable {C : Ipa.CommitmentCurve} {k m p : ℕ} [Module C.ScalarField C.Point]

/-- A run that accepts and yields no opening either produced nothing at all (the presence rung,
already bounded by `deployedExtract_failure_measure_le`), or produced a setup-basis relation
(charged to textbook DL), or produced a `U`-touching break (the residual). -/
private theorem three_way_cover (B : C.Point) (fam : DeployedFamily C k m p)
    (coins : Zcash.Snark.RecursiveForkCoins Prechallenge (k + 1)) :
    {q : (SetupIndex (2 ^ k) → C.ScalarField) × Coins C k |
        wireWins (srsOfBasis k (augOfSetup (Zcash.Snark.scalarBasis B q.1)))
            (fam.claim (augOfSetup (Zcash.Snark.scalarBasis B q.1))) q.2
            ((fam.adversary (augOfSetup (Zcash.Snark.scalarBasis B q.1))).run q.2) ∧
          ¬ fam.HasOpening (augOfSetup (Zcash.Snark.scalarBasis B q.1)) q.2 coins}
      ⊆ {q | q.2 ∈ fam.acceptExtractionFailure
              (augOfSetup (Zcash.Snark.scalarBasis B q.1)) coins}
        ∪ (↑(Zcash.Snark.relSetWithCoins B (relationFinder fam coins)) :
            Set ((SetupIndex (2 ^ k) → C.ScalarField) × Coins C k))
        ∪ {q | TouchesU fam (Zcash.Snark.scalarBasis B q.1) q.2 coins} := by
  classical
  intro q hq
  obtain ⟨hacc, hnoopen⟩ := hq
  by_cases hsome : (fam.attempt (augOfSetup (Zcash.Snark.scalarBasis B q.1)) q.2 coins).isSome
  · obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hsome
    cases x with
    | inl o => exact absurd ⟨o, hx⟩ hnoopen
    | inr rel =>
      by_cases hu : rel.coeffs Zcash.Snark.AugmentedIndex.u = 0
      · refine Or.inl (Or.inr ?_)
        simp only [Finset.mem_coe, Zcash.Snark.relSetWithCoins, Finset.mem_filter,
          Finset.mem_univ, true_and]
        show (relationFinder fam coins (Zcash.Snark.scalarBasis B q.1) q.2).isSome = true
        simp only [relationFinder, hx, dif_pos hu, Option.isSome_some]
      · exact Or.inr ⟨rel, hx, hu⟩
  · exact Or.inl (Or.inl ⟨hacc, Option.not_isSome_iff_eq_none.mp hsome⟩)

end Cover

/-! ## 6. The three summands -/

section Summands

variable {C : Ipa.CommitmentCurve} {k m p : ℕ} [Module C.ScalarField C.Point]

/-- **First summand — reused verbatim.** `deployedExtract_failure_measure_le` (the LOCKED target)
lifted across the sampled setup basis by `uniformOfFintype_prod_fiber_bound_right`. Nothing about
the locked statement changes; only the type of the sampled coefficient vector does. -/
private theorem presence_summand
    (hsmul : ∀ (z : C.ScalarField) (Q : C.Point), z • Q = z.val • Q)
    (hinj : Function.Injective (expandPre C)) (hne : ∀ q, expandPre C q ≠ 0)
    (B : C.Point) (fam : DeployedFamily C k m p)
    (coins : Zcash.Snark.RecursiveForkCoins Prechallenge (k + 1)) (hcoins : coins.Complete) :
    (PMF.uniformOfFintype
        ((SetupIndex (2 ^ k) → C.ScalarField) × Coins C k)).toOuterMeasure
        {q | q.2 ∈ fam.acceptExtractionFailure
          (augOfSetup (Zcash.Snark.scalarBasis B q.1)) coins}
      ≤ (fam.Q + k + 1) * (3 / (2 ^ 128 : ℕ)) := by
  refine Zcash.Snark.uniformOfFintype_prod_fiber_bound_right
    (fun s => fam.acceptExtractionFailure (augOfSetup (Zcash.Snark.scalarBasis B s)) coins) ?_
  intro s
  exact deployedExtract_failure_measure_le hsmul hinj hne
    (srsOfBasis k (augOfSetup (Zcash.Snark.scalarBasis B s)))
    (fam.claim (augOfSetup (Zcash.Snark.scalarBasis B s)))
    (fam.pg (augOfSetup (Zcash.Snark.scalarBasis B s)))
    (fam.pw (augOfSetup (Zcash.Snark.scalarBasis B s)))
    (fam.hP (augOfSetup (Zcash.Snark.scalarBasis B s)))
    (fam.adversary (augOfSetup (Zcash.Snark.scalarBasis B s)))
    (fam.queryBound (augOfSetup (Zcash.Snark.scalarBasis B s))) coins hcoins

/-- **Second summand — one upstream call.** `relationWithCoins_prob_le_of_textbookDL`
(`AGM/ProbabilityCoins.lean:182`) is index-generic (`{ι} [Fintype ι] [DecidableEq ι]
[Nonempty ι]`), so it applies at `ι := SetupIndex (2 ^ k)` with no change. -/
theorem relation_summand (B : C.Point) (fam : DeployedFamily C k m p)
    (coins : Zcash.Snark.RecursiveForkCoins Prechallenge (k + 1)) {ε : ℝ≥0∞}
    (hDL : Zcash.Snark.TextbookDLWithCoinsAdvantageLE B (relationFinder fam coins) ε) :
    (PMF.uniformOfFintype
        ((SetupIndex (2 ^ k) → C.ScalarField) × Coins C k)).toOuterMeasure
        (Zcash.Snark.relSetWithCoins B (relationFinder fam coins))
      ≤ Fintype.card (SetupIndex (2 ^ k)) * ε :=
  Zcash.Snark.relationWithCoins_prob_le_of_textbookDL B _ hDL

/-- **Third summand — the residual, by its own assumption.** -/
theorem residual_summand (B : C.Point) (fam : DeployedFamily C k m p)
    (coins : Zcash.Snark.RecursiveForkCoins Prechallenge (k + 1)) {δ : ℝ≥0∞}
    (hU : DerivedUDLAdvantageLE fam B coins δ) :
    (PMF.uniformOfFintype
        ((SetupIndex (2 ^ k) → C.ScalarField) × Coins C k)).toOuterMeasure
        {q | TouchesU fam (Zcash.Snark.scalarBasis B q.1) q.2 coins}
      ≤ δ := by
  have hset : {q : (SetupIndex (2 ^ k) → C.ScalarField) × Coins C k |
        TouchesU fam (Zcash.Snark.scalarBasis B q.1) q.2 coins}
      = {q | (derivedULog fam B coins q.1 q.2).isSome} := by
    ext q
    exact (derivedULog_isSome_iff fam B coins q.1 q.2).symm
  rw [hset]
  exact hU

end Summands

/-! ## 7. The revised terminal statement -/

section Terminal

variable {C : Ipa.CommitmentCurve} {k m p : ℕ} [Module C.ScalarField C.Point]

/-- **Deployed IPA knowledge soundness under textbook discrete log — `hU`-free.**

Over a uniformly sampled *setup* basis (the `2 ^ k` URS generators and the blinding generator,
injected with a dead `u` slot) and a uniform oracle table, the probability that the executable
wire verifier accepts *and* the executable extractor fails to return an **opening** is at most

* the recursive query loss `(Q + k + 1) · 3 / 2 ^ 128` — `deployedExtract_failure_measure_le`,
  the LOCKED target, reused verbatim; plus
* the fixed-slot discrete-log loss `|SetupIndex (2 ^ k)| · ε = (2 ^ k + 1) · ε` — one slot
  *cheaper* than the incumbent `2 ^ k + 2`, because `U` is no longer sampled; plus
* the derived-`U` discrete-log loss `δ` — the honest price of kimchi's transcript-derived IPA
  base, which halo2 does not pay because its `U` is a setup parameter.

Compared with `Zcash.Snark.ComputedAlgebraicFSFamily.snarkFailure_prob_le_of_textbookDL`
(`Forking/Adversary/Algebraic.lean:1218`): the first two summands are its two, with the same three
deployed deviations documented at `deployedExtract_failure_measure_le` (`fam.Q + k + 1` for
kimchi's Schnorr round; `3 / 2 ^ 128` for 128-bit prechallenges; no `(Q + 1) / |F|` slice). The
third summand is new, and is the whole content of the `hU` correction. -/
theorem deployedExtract_noOpening_measure_le_of_textbookDL
    (hsmul : ∀ (z : C.ScalarField) (Q : C.Point), z • Q = z.val • Q)
    (hinj : Function.Injective (expandPre C)) (hne : ∀ q, expandPre C q ≠ 0)
    (B : C.Point) (fam : DeployedFamily C k m p)
    (coins : Zcash.Snark.RecursiveForkCoins Prechallenge (k + 1))
    (hcoins : coins.Complete) {ε δ : ℝ≥0∞}
    (hDL : Zcash.Snark.TextbookDLWithCoinsAdvantageLE B (relationFinder fam coins) ε)
    (hUDL : DerivedUDLAdvantageLE fam B coins δ) :
    (PMF.uniformOfFintype
        ((SetupIndex (2 ^ k) → C.ScalarField) × Coins C k)).toOuterMeasure
        {q | wireWins (srsOfBasis k (augOfSetup (Zcash.Snark.scalarBasis B q.1)))
                (fam.claim (augOfSetup (Zcash.Snark.scalarBasis B q.1))) q.2
                ((fam.adversary (augOfSetup (Zcash.Snark.scalarBasis B q.1))).run q.2) ∧
          ¬ fam.HasOpening (augOfSetup (Zcash.Snark.scalarBasis B q.1)) q.2 coins}
      ≤ (fam.Q + k + 1) * (3 / (2 ^ 128 : ℕ))
        + Fintype.card (SetupIndex (2 ^ k)) * ε + δ := by
  classical
  refine le_trans (MeasureTheory.measure_mono (three_way_cover B fam coins)) ?_
  refine le_trans (MeasureTheory.measure_union_le _ _) ?_
  refine add_le_add (le_trans (MeasureTheory.measure_union_le _ _) ?_)
    (residual_summand B fam coins hUDL)
  exact add_le_add (presence_summand hsmul hinj hne B fam coins hcoins)
    (relation_summand B fam coins hDL)

end Terminal

/-! ## 8. THE ACCEPTANCE TEST — the setup slot count -/

section PerCurve

/-- The setup slot count, evaluated: `2 ^ k + 1`. Curve-independent, and used by both
    per-curve endpoints. -/
private theorem vesta_card_setup (k : ℕ) : Fintype.card (SetupIndex (2 ^ k)) = 2 ^ k + 1 :=
  card_setupIndex _

end PerCurve

/-! ## 9. The capstone: hardness internalized, gated by the call bound

`deployedExtract_noOpening_measure_le_of_textbookDL` takes the two advantage bounds directly, so
it assumes them against an **unbounded** reduction. Ironwood's designated top-level statement —
`ComputedAlgebraicFSFamily.knowledgeSoundness_under_DL` (`Forking/Adversary/Algebraic.lean:1464`),
named as the verifier-soundness capstone in their proof map — assumes them only against reductions
making at most `R` black-box calls, which is the *weaker* and more plausible hypothesis. That is
what this section adds; the bound itself is unchanged.

**What the call bound does and does not say** (external-audit E-1 — an earlier revision here
OVERclaimed the limitation). `Complete` is a search-completeness condition — it is what makes
non-escape imply extraction — and it does not by itself bound the cost: `ReductionEfficient`
averages the run count over oracle tables, and a table on which the adversary loses costs
exactly ONE run (`recursiveAlgebraicForkFrom` descends without rewinding and returns at the
leaf), so the quantity gated here is the classical expected-forking cost, not the worst case.

What is *proved* is the worst case, and now for our own recursion rather than only upstream's:
`DeployedFamily.reductionEfficient_of_bounded` below discharges `ReductionEfficient` at
`R = (2n+1)^(k+1)` on any coin tape of node degree at most `n`, and
`DeployedFamily.exists_complete_reductionEfficient` exhibits a single tape that is `Complete`
*and* achieves it, at `n = 2 ^ 128`. That chain rests on `Bulletproof.Forking.kimchiExtractRuns_le`,
which is pointwise in the table, so it crosses the averaging axis for free.

The honest caveats, unchanged. The number is exponential in `k` and in the challenge domain —
the same regime as ironwood's `reductionEfficient_exponential` — so it is bookkeeping, not a
concrete-security claim. A *table-averaged* bound is still not proved here: upstream's
`ExpectedRuns.lean` proves `E[runs] ≤ (6/δ)^k` under a uniform good-challenge density floor on
the tape-averaged axis, and porting it to this axis remains open, as does any unconditional
polynomial bound. What has changed is only that `R` is now computed from the counter instead of
obtained from a `sup` that never inspects it (contrast `reductionEfficient_exists`, kept below
for exactly that contrast), and that it is bounded away from `0` by
`Bulletproof.Forking.one_le_kimchiExtractRuns`. -/

section Capstone

variable {C : Ipa.CommitmentCurve} {k m p : ℕ} [Module C.ScalarField C.Point]
variable (fam : DeployedFamily C k m p)

/-- **The extractor's call count at one basis and one table** — `deployedExtractRuns` at the
family's instantiation, i.e. a projection of the very recursion `attempt` runs. -/
def DeployedFamily.attemptRuns (basis : Zcash.Snark.AugmentedIndex (2 ^ k) → C.Point)
    (O : Coins C k) (coins : Zcash.Snark.RecursiveForkCoins Prechallenge (k + 1)) : ℕ :=
  deployedExtractRuns (srsOfBasis k basis) (Ipa.cipOf (fam.claim basis))
    (combinedEvalVector (2 ^ k) (fam.claim basis).evalscale (fam.claim basis).pointFn)
    (Ipa.cipOf (fam.claim basis))
    (combinedCommitment (fam.claim basis).polyscale (fam.claim basis).commitmentFn)
    (fam.adversary basis) O coins

/-- **The extractor makes at most `R` calls on average** — ironwood's `ReductionEfficient`
(`Algebraic.lean:1407`) at our types. The sum is over the oracle tables, with the fork tape a
parameter, matching how `Coins` is defined. -/
def DeployedFamily.ReductionEfficient
    (coins : Zcash.Snark.RecursiveForkCoins Prechallenge (k + 1)) (R : ℕ) : Prop :=
  ∀ basis : Zcash.Snark.AugmentedIndex (2 ^ k) → C.Point,
    ∑ O : Coins C k, fam.attemptRuns basis O coins ≤ R * Fintype.card (Coins C k)

/-- **Discrete log is hard for this family against `R`-call reductions** — ironwood's
`DiscreteLogRelationHardFor` (`Algebraic.lean`) at our types, carrying both advantage bounds
because our residual (`DerivedUDLAdvantageLE`) has no upstream counterpart: kimchi's `U` is
transcript derived, so the `U`-touching breaks cannot be charged to textbook discrete log.

Read `derivedUDL_iff_residual_measure` next to this: the `δ` component is the residual event's own
measure, not a reduction to a standard problem. Only the `ε` component is a genuine reduction. -/
def DeployedFamily.DiscreteLogRelationHardFor (B : C.Point)
    (coins : Zcash.Snark.RecursiveForkCoins Prechallenge (k + 1)) (R : ℕ) (ε δ : ℝ≥0∞) : Prop :=
  fam.ReductionEfficient coins R →
    Zcash.Snark.TextbookDLWithCoinsAdvantageLE B (relationFinder fam coins) ε ∧
      DerivedUDLAdvantageLE fam B coins δ

/-- **Deployed IPA knowledge soundness, under per-family discrete-log hardness gated by the
extractor call bound.** The analogue of
`Zcash.Snark.ComputedAlgebraicFSFamily.knowledgeSoundness_under_DL`
(`Forking/Adversary/Algebraic.lean:1464`) — ironwood's designated top-level verifier-soundness
capstone — and, like it, one application of the bound below it.

The measured event and the bound are exactly
`deployedExtract_noOpening_measure_le_of_textbookDL`'s. What changes is the hypothesis: hardness
is assumed only against reductions respecting the call bound `R`, rather than unconditionally.
See the section docstring on how large `R` honestly is. -/
private theorem deployedExtract_knowledgeSoundness_under_DL
    (hsmul : ∀ (z : C.ScalarField) (Q : C.Point), z • Q = z.val • Q)
    (hinj : Function.Injective (expandPre C)) (hne : ∀ q, expandPre C q ≠ 0)
    (B : C.Point)
    (coins : Zcash.Snark.RecursiveForkCoins Prechallenge (k + 1))
    (hcoins : coins.Complete) {R : ℕ} {ε δ : ℝ≥0∞}
    (hHard : fam.DiscreteLogRelationHardFor B coins R ε δ)
    (hEff : fam.ReductionEfficient coins R) :
    (PMF.uniformOfFintype
        ((SetupIndex (2 ^ k) → C.ScalarField) × Coins C k)).toOuterMeasure
        {q | wireWins (srsOfBasis k (augOfSetup (Zcash.Snark.scalarBasis B q.1)))
                (fam.claim (augOfSetup (Zcash.Snark.scalarBasis B q.1))) q.2
                ((fam.adversary (augOfSetup (Zcash.Snark.scalarBasis B q.1))).run q.2) ∧
          ¬ fam.HasOpening (augOfSetup (Zcash.Snark.scalarBasis B q.1)) q.2 coins}
      ≤ (fam.Q + k + 1) * (3 / (2 ^ 128 : ℕ))
        + Fintype.card (SetupIndex (2 ^ k)) * ε + δ :=
  deployedExtract_noOpening_measure_le_of_textbookDL hsmul hinj hne B fam coins hcoins
    (hHard hEff).1 (hHard hEff).2

/-- **Every fixed family has *some* call bound** — ironwood's `reductionEfficient_exists`
(`Algebraic.lean:1413`) at our types, and stated for the same reason: so nobody reads
`ReductionEfficient` as doing more than it does.

The proof never inspects the counter; it takes the maximum over the (finite) set of bases. So the
gate constrains *which* `R` the hardness assumption is indexed by — it does not by itself assert
that the extractor is efficient, and no asymptotic claim follows from it. -/
theorem DeployedFamily.reductionEfficient_exists [Fintype C.Point]
    (coins : Zcash.Snark.RecursiveForkCoins Prechallenge (k + 1)) :
    ∃ R, fam.ReductionEfficient coins R := by
  classical
  refine ⟨Finset.univ.sup fun basis => ∑ O : Coins C k, fam.attemptRuns basis O coins, ?_⟩
  intro basis
  refine le_trans (Finset.le_sup (f := fun basis => ∑ O : Coins C k,
    fam.attemptRuns basis O coins) (Finset.mem_univ basis)) ?_
  exact Nat.le_mul_of_pos_right _ Fintype.card_pos

/-- **A call bound computed from the counter**, on any coin tape of node degree at most `n`.
The pointwise bound `deployedExtractRuns_le` summed over the oracle tables — upstream's
`recursiveAlgebraicFork_sum_runs_le_unconditional` (`Recursive.lean:679`) is the same two-line
`calc`. Because the input is pointwise in the table, no averaging argument is involved and the
sum is trivial; that is precisely why this crosses the tape-vs-table axis that the conditional
`(6/δ)^k` bound does not.

Stands beside `reductionEfficient_exists`, which it does not supersede: that theorem's job is to
record what `ReductionEfficient` fails to say, and it still says it. -/
theorem DeployedFamily.reductionEfficient_of_bounded
    (coins : Zcash.Snark.RecursiveForkCoins Prechallenge (k + 1)) {n : ℕ}
    (hB : coins.Bounded n) :
    fam.ReductionEfficient coins ((2 * n + 1) ^ (k + 1)) := by
  intro basis
  calc ∑ O : Coins C k, fam.attemptRuns basis O coins
      ≤ ∑ _O : Coins C k, (2 * n + 1) ^ (k + 1) :=
        Finset.sum_le_sum fun O _ =>
          deployedExtractRuns_le (srsOfBasis k basis) (Ipa.cipOf (fam.claim basis))
            (combinedEvalVector (2 ^ k) (fam.claim basis).evalscale (fam.claim basis).pointFn)
            (Ipa.cipOf (fam.claim basis))
            (combinedCommitment (fam.claim basis).polyscale (fam.claim basis).commitmentFn)
            (fam.adversary basis) O coins hB
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, Nat.mul_comm]

/-- **The two coin-side hypotheses of every endpoint are jointly dischargeable, with an explicit
proved `R`.** One tape is at once `Complete` — what the knowledge-soundness statements assume, so
that non-escape forces extraction — and efficient at `R = (2 · 2 ^ 128 + 1) ^ (k + 1)`, a number
this tree computes from the extractor's own counter rather than obtains from a `sup` over bases.

That sentence is the whole content: before it, the efficiency gate could only be satisfied by an
`R` nothing had inspected. It remains a *worst-case*, exponential number, and no polynomial or
table-averaged claim follows from it. -/
theorem DeployedFamily.exists_complete_reductionEfficient :
    ∃ coins : Zcash.Snark.RecursiveForkCoins Prechallenge (k + 1),
      coins.Complete ∧ fam.ReductionEfficient coins ((2 * 2 ^ 128 + 1) ^ (k + 1)) := by
  obtain ⟨coins, hc, hb⟩ := exists_complete_bounded_coins (k + 1)
  exact ⟨coins, hc, fam.reductionEfficient_of_bounded coins hb⟩

/-- **No `R` below `1` satisfies the efficiency gate.** The extractor runs the adversary at least
once on every oracle table (`one_le_deployedExtractRuns`), so the sum over tables is at least
`Fintype.card (Coins C k)`, which `R * Fintype.card (Coins C k)` does not bound at `R = 0`.

It does not make `hEff` non-trivial to *satisfy* — `exists_complete_reductionEfficient` does
that — only rules out an `R` advertising a zero-call reduction, against which discrete-log
hardness would be assumed for free. -/
theorem DeployedFamily.one_le_of_reductionEfficient
    (coins : Zcash.Snark.RecursiveForkCoins Prechallenge (k + 1)) {R : ℕ}
    (h : fam.ReductionEfficient coins R) : 1 ≤ R := by
  -- `ReductionEfficient` quantifies over every basis, so the basis is immaterial: take zero.
  have hlow : 1 * Fintype.card (Coins C k)
      ≤ ∑ O : Coins C k, fam.attemptRuns (fun _ => 0) O coins := by
    calc 1 * Fintype.card (Coins C k) = ∑ _O : Coins C k, 1 := by
          rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, Nat.mul_comm]
      _ ≤ _ := Finset.sum_le_sum fun O _ =>
          one_le_deployedExtractRuns (srsOfBasis k (fun _ => 0))
            (Ipa.cipOf (fam.claim (fun _ => 0)))
            (combinedEvalVector (2 ^ k) (fam.claim (fun _ => 0)).evalscale
              (fam.claim (fun _ => 0)).pointFn)
            (Ipa.cipOf (fam.claim (fun _ => 0)))
            (combinedCommitment (fam.claim (fun _ => 0)).polyscale
              (fam.claim (fun _ => 0)).commitmentFn)
            (fam.adversary (fun _ => 0)) O coins
  exact Nat.le_of_mul_le_mul_right (hlow.trans (h fun _ => 0)) Fintype.card_pos

/-! ### The capstone, per curve -/

/-- **Vesta, capstone form.** The call-bound-gated statement at the deployed curve, with every
curve hypothesis discharged. -/
private theorem vesta_knowledgeSoundness_under_DL {k m p : ℕ}
    (B : IpaVesta.Point) (fam : DeployedFamily IpaVesta.curve k m p)
    (coins : Zcash.Snark.RecursiveForkCoins Prechallenge (k + 1))
    (hcoins : coins.Complete) {R : ℕ} {ε δ : ℝ≥0∞}
    (hHard : fam.DiscreteLogRelationHardFor B coins R ε δ)
    (hEff : fam.ReductionEfficient coins R) :
    (PMF.uniformOfFintype
        ((SetupIndex (2 ^ k) → IpaVesta.curve.ScalarField) × Coins IpaVesta.curve k)).toOuterMeasure
        {q | wireWins (srsOfBasis k (augOfSetup (Zcash.Snark.scalarBasis B q.1)))
                (fam.claim (augOfSetup (Zcash.Snark.scalarBasis B q.1))) q.2
                ((fam.adversary (augOfSetup (Zcash.Snark.scalarBasis B q.1))).run q.2) ∧
          ¬ fam.HasOpening (augOfSetup (Zcash.Snark.scalarBasis B q.1)) q.2 coins}
      ≤ (fam.Q + k + 1) * (3 / (2 ^ 128 : ℕ))
        + Fintype.card (SetupIndex (2 ^ k)) * ε + δ :=
  deployedExtract_knowledgeSoundness_under_DL fam Pasta.vesta_smul_val
    expandPre_vesta_injective expandPre_vesta_ne_zero B coins hcoins hHard hEff

/-- **Pallas, capstone form.** -/
private theorem pallas_knowledgeSoundness_under_DL {k m p : ℕ}
    (B : IpaPallas.Point) (fam : DeployedFamily IpaPallas.curve k m p)
    (coins : Zcash.Snark.RecursiveForkCoins Prechallenge (k + 1))
    (hcoins : coins.Complete) {R : ℕ} {ε δ : ℝ≥0∞}
    (hHard : fam.DiscreteLogRelationHardFor B coins R ε δ)
    (hEff : fam.ReductionEfficient coins R) :
    (PMF.uniformOfFintype
        ((SetupIndex (2 ^ k) → IpaPallas.curve.ScalarField)
          × Coins IpaPallas.curve k)).toOuterMeasure
        {q | wireWins (srsOfBasis k (augOfSetup (Zcash.Snark.scalarBasis B q.1)))
                (fam.claim (augOfSetup (Zcash.Snark.scalarBasis B q.1))) q.2
                ((fam.adversary (augOfSetup (Zcash.Snark.scalarBasis B q.1))).run q.2) ∧
          ¬ fam.HasOpening (augOfSetup (Zcash.Snark.scalarBasis B q.1)) q.2 coins}
      ≤ (fam.Q + k + 1) * (3 / (2 ^ 128 : ℕ))
        + Fintype.card (SetupIndex (2 ^ k)) * ε + δ :=
  deployedExtract_knowledgeSoundness_under_DL fam Pasta.pallas_smul_val
    expandPre_pallas_injective expandPre_pallas_ne_zero B coins hcoins hHard hEff

/-! ### The query-loss rung, per curve

`deployedExtract_failure_measure_le` (`Forking/Deployed.lean`) is generic in the curve, with
`hsmul`, `hinj` and `hne` as hypotheses. Every one is a theorem at each deployed bundle, so the
rung instantiates outright — recorded here because a generic statement whose hypotheses are never
discharged is the shape that hid the `hU` defect. -/

/-- **Vesta, query-loss rung.** `hsmul` by `Pasta.vesta_smul_val`, `hinj`/`hne` by
`expandPre_vesta_injective` / `expandPre_vesta_ne_zero`. -/
theorem vesta_failure_measure_le {m p : ℕ} (σ : SRS IpaVesta.Point)
    (claim : Ipa.Input IpaVesta.curve σ.k m p)
    (pg : Fin (2 ^ σ.k) → IpaVesta.curve.ScalarField) (pw : IpaVesta.curve.ScalarField)
    (hP : combinedCommitment claim.polyscale claim.commitmentFn
      = commitGen σ.g pg + pw • σ.h)
    (A : Zcash.Snark.OracleComp (IpaNode IpaVesta.curve σ.k) Prechallenge
      (Ipa.Proof IpaVesta.curve σ.k))
    {Q : ℕ} (hQ : A.QueryBound Q)
    (coins : Zcash.Snark.RecursiveForkCoins Prechallenge (σ.k + 1)) (hcoins : coins.Complete) :
    (PMF.uniformOfFintype (IpaNode IpaVesta.curve σ.k → Prechallenge)).toOuterMeasure
        {O | wireWins σ claim O (A.run O) ∧
          deployedExtract σ (Ipa.cipOf claim)
              (combinedEvalVector (2 ^ σ.k) claim.evalscale claim.pointFn)
              (Ipa.cipOf claim) (combinedCommitment claim.polyscale claim.commitmentFn)
              pg pw hP A O coins = none}
      ≤ (Q + σ.k + 1) * (3 / (2 ^ 128 : ℕ)) :=
  deployedExtract_failure_measure_le Pasta.vesta_smul_val expandPre_vesta_injective
    expandPre_vesta_ne_zero σ claim pg pw hP A hQ coins hcoins

/-- **Pallas, query-loss rung.** Same discharge. -/
theorem pallas_failure_measure_le {m p : ℕ} (σ : SRS IpaPallas.Point)
    (claim : Ipa.Input IpaPallas.curve σ.k m p)
    (pg : Fin (2 ^ σ.k) → IpaPallas.curve.ScalarField) (pw : IpaPallas.curve.ScalarField)
    (hP : combinedCommitment claim.polyscale claim.commitmentFn
      = commitGen σ.g pg + pw • σ.h)
    (A : Zcash.Snark.OracleComp (IpaNode IpaPallas.curve σ.k) Prechallenge
      (Ipa.Proof IpaPallas.curve σ.k))
    {Q : ℕ} (hQ : A.QueryBound Q)
    (coins : Zcash.Snark.RecursiveForkCoins Prechallenge (σ.k + 1)) (hcoins : coins.Complete) :
    (PMF.uniformOfFintype (IpaNode IpaPallas.curve σ.k → Prechallenge)).toOuterMeasure
        {O | wireWins σ claim O (A.run O) ∧
          deployedExtract σ (Ipa.cipOf claim)
              (combinedEvalVector (2 ^ σ.k) claim.evalscale claim.pointFn)
              (Ipa.cipOf claim) (combinedCommitment claim.polyscale claim.commitmentFn)
              pg pw hP A O coins = none}
      ≤ (Q + σ.k + 1) * (3 / (2 ^ 128 : ℕ)) :=
  deployedExtract_failure_measure_le Pasta.pallas_smul_val expandPre_pallas_injective
    expandPre_pallas_ne_zero σ claim pg pw hP A hQ coins hcoins

/-! ### The headline: the deployed IPA verifier is knowledge-sound, per curve

One statement per curve, every curve-specific hypothesis discharged and every constant evaluated.
Read the caveats in the docstring as part of the claim — each is a real limit, and each is stated
because a reader who skips them would overclaim. -/

/-- **The deployed Vesta IPA verifier is knowledge-sound, in the random-oracle model.**

For a family of `Q`-query algebraic adversaries against the deployed Vesta IPA opening verifier,
over a uniformly sampled setup basis and uniform challenge oracle: the probability that an
adversary makes the **executable wire verifier** accept while the **executable extractor** fails
to return an opening is at most

`(Q + k + 1) · 3 / 2¹²⁸  +  (2ᵏ + 1) · ε  +  δ`.

The extractor is `deployedExtract`, a plain computable `def` whose `#eval` on a fixture is checked
by `scripts/check_extractor_computes.sh` — the guard that separates a reduction which *computes*
the witness from one that merely asserts it exists. Acceptance is `Ipa.verifyWith`'s own `Bool`,
not a re-modelled predicate.

**What is assumed.** `hHard`: discrete log is `(ε, δ)`-hard for this family against reductions
making at most `R` black-box calls. `hEff`: the extractor respects that call bound. `hcoins`: the
fork tape is complete.

**Four limits, all real.**
1. *Random-oracle model.* The challenges are a uniform table, where the deployed protocol squeezes
   them from the Poseidon sponge. `verifyOracle_spongeFS` (`Forking/Transcript.lean`) proves the
   abstract verifier at the sponge source *is* `Ipa.verify`; replacing the sponge by a uniform
   table is the idealization, and it is carried by no Lean axiom.
2. *`δ` is not a reduction.* `derivedUDL_iff_residual_measure` proves it is the residual event's
   own measure. Only `ε` reduces to a standard problem. This is the price of kimchi's
   transcript-derived `U`, which halo2 does not pay — ironwood has no analogue.
3. *The extractor's cost is bounded only in the worst case.*
   `DeployedFamily.reductionEfficient_of_bounded` discharges `hEff` at `R = (2n + 1)^(k+1)`
   on any tape of node degree at most `n`, and
   `DeployedFamily.exists_complete_reductionEfficient` exhibits one tape that is `Complete`
   and efficient at once, at `n = 2 ^ 128` — exponential in `k` and in the challenge domain.
   No sub-worst-case bound is proved here: `ReductionEfficient` averages over the oracle
   tables and a losing table costs one run, so what it gates is the classical
   expected-forking cost, and upstream's tape-averaged `(6/δ)^k` does not cross that axis
   (see the `ReductionEfficient` section docstring; external-audit O-1b, open). `ε` is still
   assumed for this finder rather than derived from a time bound: at
   `R = (2·2¹²⁸ + 1)^(k+1)` a reduction is permitted enough oracle calls to solve discrete log
   outright, so `hHard` there is satisfiable only at `ε ≈ 1`.
4. *One claim.* The statement is single-claim; recovering individual polynomials from a batch is
   the separate un-batching layer (`chunked_batch_soundness`).

The query-loss term is unconditional — it holds against an unbounded adversary — and at realistic
`Q` it dominates the other two by tens of bits. -/
theorem ipaVesta_knowledge_sound {k m p : ℕ}
    (B : IpaVesta.Point) (fam : DeployedFamily IpaVesta.curve k m p)
    (coins : Zcash.Snark.RecursiveForkCoins Prechallenge (k + 1))
    (hcoins : coins.Complete) {R : ℕ} {ε δ : ℝ≥0∞}
    (hHard : fam.DiscreteLogRelationHardFor B coins R ε δ)
    (hEff : fam.ReductionEfficient coins R) :
    (PMF.uniformOfFintype
        ((SetupIndex (2 ^ k) → IpaVesta.curve.ScalarField) × Coins IpaVesta.curve k)).toOuterMeasure
        {q | wireWins (srsOfBasis k (augOfSetup (Zcash.Snark.scalarBasis B q.1)))
                (fam.claim (augOfSetup (Zcash.Snark.scalarBasis B q.1))) q.2
                ((fam.adversary (augOfSetup (Zcash.Snark.scalarBasis B q.1))).run q.2) ∧
          ¬ fam.HasOpening (augOfSetup (Zcash.Snark.scalarBasis B q.1)) q.2 coins}
      ≤ (fam.Q + k + 1) * (3 / (2 ^ 128 : ℕ)) + ((2 ^ k + 1 : ℕ) : ℝ≥0∞) * ε + δ := by
  have h := vesta_knowledgeSoundness_under_DL B fam coins hcoins hHard hEff
  rwa [vesta_card_setup k] at h

/-- **The deployed Pallas IPA verifier is knowledge-sound, in the random-oracle model.** The
Pallas twin of `ipaVesta_knowledge_sound`; same statement, same assumptions, same four limits. -/
theorem ipaPallas_knowledge_sound {k m p : ℕ}
    (B : IpaPallas.Point) (fam : DeployedFamily IpaPallas.curve k m p)
    (coins : Zcash.Snark.RecursiveForkCoins Prechallenge (k + 1))
    (hcoins : coins.Complete) {R : ℕ} {ε δ : ℝ≥0∞}
    (hHard : fam.DiscreteLogRelationHardFor B coins R ε δ)
    (hEff : fam.ReductionEfficient coins R) :
    (PMF.uniformOfFintype
        ((SetupIndex (2 ^ k) → IpaPallas.curve.ScalarField)
          × Coins IpaPallas.curve k)).toOuterMeasure
        {q | wireWins (srsOfBasis k (augOfSetup (Zcash.Snark.scalarBasis B q.1)))
                (fam.claim (augOfSetup (Zcash.Snark.scalarBasis B q.1))) q.2
                ((fam.adversary (augOfSetup (Zcash.Snark.scalarBasis B q.1))).run q.2) ∧
          ¬ fam.HasOpening (augOfSetup (Zcash.Snark.scalarBasis B q.1)) q.2 coins}
      ≤ (fam.Q + k + 1) * (3 / (2 ^ 128 : ℕ)) + ((2 ^ k + 1 : ℕ) : ℝ≥0∞) * ε + δ := by
  have h := pallas_knowledgeSoundness_under_DL B fam coins hcoins hHard hEff
  rwa [vesta_card_setup k] at h

end Capstone

/-! ## 10. The honest acceptance witness

The terminal's failure set is `wireWins ∧ ¬HasOpening`. A bound on it would be uninteresting if
the `wireWins` conjunct were what made the set small — "nobody accepts, so nothing fails". This
section rules that out by exhibiting a family that accepts on **every** oracle table at **every**
basis, built from the anti-vacuity companion `honestNode_wireWins_everywhere` (`Honest.lean`).
For that family the failure set is exactly `¬HasOpening`, so the bound is a statement about the
extractor and nothing else.

This is the instantiation the `hU` version could not have had at any curve. -/

section Honest

variable {C : Ipa.CommitmentCurve} {k m p : ℕ} [Module C.ScalarField C.Point]

/-- The degenerate claim: every commitment, point, evaluation and scalar zero. -/
private def trivialInput (C : Ipa.CommitmentCurve) (k m p : ℕ) : Ipa.Input C k m p where
  commitments := Vector.replicate m 0
  xs := Vector.replicate p 0
  evals := Vector.replicate m (Vector.replicate p 0)
  polyscale := 0
  evalscale := 0
  proof := { lr := Vector.replicate k (0, 0), delta := 0, z1 := 0, z2 := 0, sg := 0 }

/-- `(0, 0)` opens the degenerate claim. -/
private theorem trivial_hopen (basis : Zcash.Snark.AugmentedIndex (2 ^ k) → C.Point) :
    openingRelationB
      { srsOfBasis k basis with U := uBaseOf C (Ipa.cipOf (trivialInput C k m p)) }
      (combinedCommitment (trivialInput C k m p).polyscale (trivialInput C k m p).commitmentFn)
      (combinedEvalVector (2 ^ k) (trivialInput C k m p).evalscale
        (trivialInput C k m p).pointFn)
      (Ipa.cipOf (trivialInput C k m p)) 0 0 := by
  constructor
  · simp [Bulletproof.commit, commitGen, trivialInput, combinedCommitment,
      Ipa.Input.commitmentFn]
  · simp [trivialInput, Ipa.cipOf, combinedInnerProduct, innerProduct, Ipa.Input.evalFn]

/-- **The honest family.** Its adversary is the honest prover of
`honestNode_wireWins_everywhere`, which wins on every oracle table. `noncomputable` only because
the adversary is extracted with `.choose`; the extractor it is fed to is untouched. -/
private noncomputable def honestFamily
    (hsmul : ∀ (z : C.ScalarField) (Q : C.Point), z • Q = z.val • Q)
    (hne : ∀ q, expandPre C q ≠ 0) (k m p : ℕ) : DeployedFamily C k m p where
  claim := fun _ => trivialInput C k m p
  adversary := fun basis =>
    (honestNode_wireWins_everywhere hsmul hne (srsOfBasis k basis)
      (trivialInput C k m p) 0 0 (trivial_hopen basis)).choose
  pg := fun _ => 0
  pw := fun _ => 0
  hP := by
    intro basis
    simp [trivialInput, combinedCommitment, commitGen, Ipa.Input.commitmentFn]
  Q := k + 1
  queryBound := fun basis =>
    (honestNode_wireWins_everywhere hsmul hne (srsOfBasis k basis)
      (trivialInput C k m p) 0 0 (trivial_hopen basis)).choose_spec.1

/-- **The honest family accepts everywhere** — at every basis, on every oracle table. -/
private theorem honestFamily_accepts_everywhere
    (hsmul : ∀ (z : C.ScalarField) (Q : C.Point), z • Q = z.val • Q)
    (hne : ∀ q, expandPre C q ≠ 0)
    (basis : Zcash.Snark.AugmentedIndex (2 ^ k) → C.Point)
    (O : Coins C k) :
    wireWins (srsOfBasis k basis) ((honestFamily hsmul hne k m p).claim basis) O
      (((honestFamily hsmul hne k m p).adversary basis).run O) :=
  (honestNode_wireWins_everywhere hsmul hne (srsOfBasis k basis)
    (trivialInput C k m p) 0 0 (trivial_hopen basis)).choose_spec.2 O

/-- **So for the honest family the terminal measures exactly "the extractor returned no
opening".** The acceptance conjunct is satisfied everywhere, hence carries none of the bound. -/
theorem honestFamily_failure_set
    (hsmul : ∀ (z : C.ScalarField) (Q : C.Point), z • Q = z.val • Q)
    (hne : ∀ q, expandPre C q ≠ 0) (B : C.Point)
    (coins : Zcash.Snark.RecursiveForkCoins Prechallenge (k + 1)) :
    {q : (SetupIndex (2 ^ k) → C.ScalarField) × Coins C k |
        wireWins (srsOfBasis k (augOfSetup (Zcash.Snark.scalarBasis B q.1)))
            ((honestFamily hsmul hne k m p).claim
              (augOfSetup (Zcash.Snark.scalarBasis B q.1))) q.2
            (((honestFamily hsmul hne k m p).adversary
              (augOfSetup (Zcash.Snark.scalarBasis B q.1))).run q.2) ∧
          ¬ (honestFamily hsmul hne k m p).HasOpening
            (augOfSetup (Zcash.Snark.scalarBasis B q.1)) q.2 coins}
      = {q | ¬ (honestFamily hsmul hne k m p).HasOpening
            (augOfSetup (Zcash.Snark.scalarBasis B q.1)) q.2 coins} := by
  ext q
  simp only [Set.mem_setOf_eq, and_iff_right_iff_imp]
  intro _
  exact honestFamily_accepts_everywhere hsmul hne _ q.2

end Honest

end Bulletproof.Ipa.Forking
