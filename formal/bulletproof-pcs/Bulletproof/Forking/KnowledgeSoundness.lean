import Bulletproof.Forking.Deployed
import Zcash.Snark.Soundness.AGM.ProbabilityCoins
import Pasta.Basic

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
presence bound while yielding no opening, and at prime order a nontrivial relation among
`2 ^ k + 2` generators always exists (`Soundness.lean:104-108`). So the presence bound alone does
not say the extractor produces openings.

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

/-- **Accepting runs on which the extractor produced nothing at all** — ironwood's
`acceptExtractionFailure` (`Algebraic.lean:1169`) at our types. The *presence* failure the
query-loss rung already bounds: `deployedExtract_failure_measure_le` is stated at exactly this
set, since `fam.attempt` is `deployedExtract` by definition. -/
def acceptExtractionFailure (basis : Zcash.Snark.AugmentedIndex (2 ^ k) → C.Point)
    (coins : Zcash.Snark.RecursiveForkCoins Prechallenge (k + 1)) : Set fam.Coins :=
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
def setupBasis {n : ℕ} (g : Fin n → G) (H : G) : SetupIndex n → G
  | Sum.inl i => g i
  | Sum.inr _ => H

/-- Inject a setup basis into the augmented index, with a **dead** `u` slot. Nothing downstream
reads it: `wireWins` never touches `σ.U`, and `deployedExtract` overrides it. -/
def augOfSetup {n : ℕ} (bs : SetupIndex n → G) : Zcash.Snark.AugmentedIndex n → G
  | Sum.inl i => bs (Sum.inl i)
  | Sum.inr j => if j = 0 then 0 else bs (Sum.inr ())

@[simp] theorem augOfSetup_gen {n : ℕ} (bs : SetupIndex n → G) (i : Fin n) :
    augOfSetup bs (Zcash.Snark.AugmentedIndex.gen i) = bs (SetupIndex.gen i) := rfl

@[simp] theorem augOfSetup_u {n : ℕ} (bs : SetupIndex n → G) :
    augOfSetup bs (Zcash.Snark.AugmentedIndex.u) = 0 := rfl

@[simp] theorem augOfSetup_w {n : ℕ} (bs : SetupIndex n → G) :
    augOfSetup bs (Zcash.Snark.AugmentedIndex.w) = bs SetupIndex.blind := rfl

/-- The slot count the DL reduction pays: one **better** than the incumbent `2 ^ k + 2`. -/
theorem card_setupIndex (n : ℕ) : Fintype.card (SetupIndex n) = n + 1 := by simp

end Basis

/-! ## 2. Reading an injected setup basis back off the SRS — `hU`'s replacement -/

section Roundtrip

variable {C : Ipa.CommitmentCurve} {k : ℕ} [Module C.ScalarField C.Point]

omit [Module C.ScalarField C.Point] in
/-- **The round trip, unconditionally.** This is what replaces `hU`: not a hypothesis, a theorem.
Compare `augmentedBasis_srsOfBasis` (`KnowledgeSoundness.lean:80`), which is upstream's
`augmentedBasis_ursOfAugmentedBasis` round trip. -/
@[simp] theorem setupBasis_srsOfBasis_augOfSetup (bs : SetupIndex (2 ^ k) → C.Point) :
    setupBasis (srsOfBasis k (augOfSetup bs)).g (srsOfBasis k (augOfSetup bs)).h = bs := by
  funext i
  rcases i with i | u
  · rfl
  · cases u; rfl

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
def dropU {n : ℕ} (c : Zcash.Snark.AugmentedIndex n → F) : SetupIndex n → F
  | Sum.inl i => c (Sum.inl i)
  | Sum.inr _ => c Zcash.Snark.AugmentedIndex.w

/-- **The general split of the augmented MSM**, with no hypothesis on the `U` coefficient. -/
theorem representationEval_dropU_general {n : ℕ} (g : Fin n → G) (U H : G)
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
    (bs : SetupIndex (2 ^ k) → C.Point) → fam.Coins →
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
def TouchesU (bs : SetupIndex (2 ^ k) → C.Point) (O : fam.Coins)
    (coins : Zcash.Snark.RecursiveForkCoins Prechallenge (k + 1)) : Prop :=
  ∃ rel, fam.attempt (augOfSetup bs) O coins = some (PSum.inr rel) ∧
    rel.coeffs Zcash.Snark.AugmentedIndex.u ≠ 0

/-- **What the residual computes.** At a *sampled* setup basis every setup log over `B` is known
by construction (`scalarBasis B s i = s i • B`), so a `U`-touching break yields the discrete log
of the transcript-derived base `uBaseOf C (Ipa.cipOf (fam.claim …))` itself. Upstream's
`discreteLogOfBasis_of_relation` (`AGM/Adapter.lean:211`) at slot `u`. -/
def derivedULog (B : C.Point) (coins : Zcash.Snark.RecursiveForkCoins Prechallenge (k + 1))
    (s : SetupIndex (2 ^ k) → C.ScalarField) (O : fam.Coins) :
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
  (PMF.uniformOfFintype ((SetupIndex (2 ^ k) → C.ScalarField) × fam.Coins)).toOuterMeasure
      {q | (derivedULog fam B coins q.1 q.2).isSome} ≤ bound

/-- The residual event is exactly the event `derivedULog` succeeds on: the assumption above bounds
the residual and nothing else. -/
theorem derivedULog_isSome_iff (B : C.Point)
    (coins : Zcash.Snark.RecursiveForkCoins Prechallenge (k + 1))
    (s : SetupIndex (2 ^ k) → C.ScalarField) (O : fam.Coins) :
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
          ((SetupIndex (2 ^ k) → C.ScalarField) × fam.Coins)).toOuterMeasure
        {q | TouchesU fam (Zcash.Snark.scalarBasis B q.1) q.2 coins} ≤ δ := by
  have hset : {q : (SetupIndex (2 ^ k) → C.ScalarField) × fam.Coins |
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
theorem three_way_cover (B : C.Point) (fam : DeployedFamily C k m p)
    (coins : Zcash.Snark.RecursiveForkCoins Prechallenge (k + 1)) :
    {q : (SetupIndex (2 ^ k) → C.ScalarField) × fam.Coins |
        wireWins (srsOfBasis k (augOfSetup (Zcash.Snark.scalarBasis B q.1)))
            (fam.claim (augOfSetup (Zcash.Snark.scalarBasis B q.1))) q.2
            ((fam.adversary (augOfSetup (Zcash.Snark.scalarBasis B q.1))).run q.2) ∧
          ¬ fam.HasOpening (augOfSetup (Zcash.Snark.scalarBasis B q.1)) q.2 coins}
      ⊆ {q | q.2 ∈ fam.acceptExtractionFailure
              (augOfSetup (Zcash.Snark.scalarBasis B q.1)) coins}
        ∪ (↑(Zcash.Snark.relSetWithCoins B (relationFinder fam coins)) :
            Set ((SetupIndex (2 ^ k) → C.ScalarField) × fam.Coins))
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
theorem presence_summand
    (hsmul : ∀ (z : C.ScalarField) (Q : C.Point), z • Q = z.val • Q)
    (hinj : Function.Injective (expandPre C)) (hne : ∀ q, expandPre C q ≠ 0)
    (B : C.Point) (fam : DeployedFamily C k m p)
    (coins : Zcash.Snark.RecursiveForkCoins Prechallenge (k + 1)) (hcoins : coins.Complete) :
    (PMF.uniformOfFintype
        ((SetupIndex (2 ^ k) → C.ScalarField) × fam.Coins)).toOuterMeasure
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
        ((SetupIndex (2 ^ k) → C.ScalarField) × fam.Coins)).toOuterMeasure
        (Zcash.Snark.relSetWithCoins B (relationFinder fam coins))
      ≤ Fintype.card (SetupIndex (2 ^ k)) * ε :=
  Zcash.Snark.relationWithCoins_prob_le_of_textbookDL B _ hDL

/-- **Third summand — the residual, by its own assumption.** -/
theorem residual_summand (B : C.Point) (fam : DeployedFamily C k m p)
    (coins : Zcash.Snark.RecursiveForkCoins Prechallenge (k + 1)) {δ : ℝ≥0∞}
    (hU : DerivedUDLAdvantageLE fam B coins δ) :
    (PMF.uniformOfFintype
        ((SetupIndex (2 ^ k) → C.ScalarField) × fam.Coins)).toOuterMeasure
        {q | TouchesU fam (Zcash.Snark.scalarBasis B q.1) q.2 coins}
      ≤ δ := by
  have hset : {q : (SetupIndex (2 ^ k) → C.ScalarField) × fam.Coins |
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
        ((SetupIndex (2 ^ k) → C.ScalarField) × fam.Coins)).toOuterMeasure
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

/-! ## 8. THE ACCEPTANCE TEST — the per-curve corollaries -/

section PerCurve

/-- **Vesta.** Every curve-specific hypothesis discharged: `hsmul` by `Pasta.vesta_smul_val`,
`hinj` by `expandPre_vesta_injective`, `hne` by `expandPre_vesta_ne_zero`. What remains are the
two cryptographic assumptions (`hDL`, `hUDL`), the fork tape, and the family itself — nothing
that constrains the curve.

This is the statement the incumbent could not have: `hU` at `IpaVesta.curve` would have forced
`Function.Surjective IpaVesta.curve.toGroup`, and `GroupMapVesta.toGroup` picks one canonical
`y` per `x`. -/
theorem vesta_noOpening_measure_le_of_textbookDL {k m p : ℕ}
    (B : IpaVesta.Point) (fam : DeployedFamily IpaVesta.curve k m p)
    (coins : Zcash.Snark.RecursiveForkCoins Prechallenge (k + 1))
    (hcoins : coins.Complete) {ε δ : ℝ≥0∞}
    (hDL : Zcash.Snark.TextbookDLWithCoinsAdvantageLE B (relationFinder fam coins) ε)
    (hUDL : DerivedUDLAdvantageLE fam B coins δ) :
    (PMF.uniformOfFintype
        ((SetupIndex (2 ^ k) → IpaVesta.curve.ScalarField) × fam.Coins)).toOuterMeasure
        {q | wireWins (srsOfBasis k (augOfSetup (Zcash.Snark.scalarBasis B q.1)))
                (fam.claim (augOfSetup (Zcash.Snark.scalarBasis B q.1))) q.2
                ((fam.adversary (augOfSetup (Zcash.Snark.scalarBasis B q.1))).run q.2) ∧
          ¬ fam.HasOpening (augOfSetup (Zcash.Snark.scalarBasis B q.1)) q.2 coins}
      ≤ (fam.Q + k + 1) * (3 / (2 ^ 128 : ℕ))
        + Fintype.card (SetupIndex (2 ^ k)) * ε + δ :=
  deployedExtract_noOpening_measure_le_of_textbookDL Pasta.vesta_smul_val
    expandPre_vesta_injective expandPre_vesta_ne_zero B fam coins hcoins hDL hUDL

/-- **Pallas**, same discharge. -/
theorem pallas_noOpening_measure_le_of_textbookDL {k m p : ℕ}
    (B : IpaPallas.Point) (fam : DeployedFamily IpaPallas.curve k m p)
    (coins : Zcash.Snark.RecursiveForkCoins Prechallenge (k + 1))
    (hcoins : coins.Complete) {ε δ : ℝ≥0∞}
    (hDL : Zcash.Snark.TextbookDLWithCoinsAdvantageLE B (relationFinder fam coins) ε)
    (hUDL : DerivedUDLAdvantageLE fam B coins δ) :
    (PMF.uniformOfFintype
        ((SetupIndex (2 ^ k) → IpaPallas.curve.ScalarField) × fam.Coins)).toOuterMeasure
        {q | wireWins (srsOfBasis k (augOfSetup (Zcash.Snark.scalarBasis B q.1)))
                (fam.claim (augOfSetup (Zcash.Snark.scalarBasis B q.1))) q.2
                ((fam.adversary (augOfSetup (Zcash.Snark.scalarBasis B q.1))).run q.2) ∧
          ¬ fam.HasOpening (augOfSetup (Zcash.Snark.scalarBasis B q.1)) q.2 coins}
      ≤ (fam.Q + k + 1) * (3 / (2 ^ 128 : ℕ))
        + Fintype.card (SetupIndex (2 ^ k)) * ε + δ :=
  deployedExtract_noOpening_measure_le_of_textbookDL Pasta.pallas_smul_val
    expandPre_pallas_injective expandPre_pallas_ne_zero B fam coins hcoins hDL hUDL

/-- The Vesta bound, with the slot count evaluated: `2 ^ k + 1`. -/
theorem vesta_card_setup (k : ℕ) : Fintype.card (SetupIndex (2 ^ k)) = 2 ^ k + 1 :=
  card_setupIndex _

end PerCurve

end Bulletproof.Ipa.Forking
