import Kimchi.Verifier.Reflect

/-!
# Deferred accumulator checks

The commitment equation deferred by recursive verification, its executable checks, and the
handover of that obligation into another proof's old accumulators. These definitions use only
Kimchi proofs, verifier keys and the SRS. Circuit-cell readings remain in Pickles.
-/

namespace Kimchi.Verifier

open Bulletproof Bulletproof.Ipa Poseidon.FqSponge

variable {C : KimchiCurve}

/-- The wire's round challenges of `cp`: the IPA transcript's prechallenges, endo-expanded, from
the run's warm sponge on its own input. -/
def wireChallenges {nc : ℕ} (σ : SRS C.Point) (cvk : KimchiVK C nc) (cp : KimchiProof C nc σ.k)
    (pub : Array C.ScalarField) : Vector C.ScalarField σ.k :=
  (transcriptFrom C (runOracles C σ cvk cp pub).warm (runInput C σ cvk cp pub)).2.1

/-- The deferred `sg`-correctness equation of the proof's opening at the wire's round
challenges (`verifyWith`'s second conjunct), which pickles checks one proof later. -/
def SgOk {nc : ℕ} (σ : SRS C.Point) (cvk : KimchiVK C nc) (cp : KimchiProof C nc σ.k)
    (pub : Array C.ScalarField) : Prop :=
  (runInput C σ cvk cp pub).proof.sg
    = msm C σ.g (bPolyCoefficients fun i => (wireChallenges σ cvk cp pub)[i])

/-- `sgOk` at the Lagrange points `L`: the deferred check on the verifier's run (`runAt`) at the
public commitment to `L`, computed once. -/
def sgOkWith {nc : ℕ} (σ : SRS C.Point) (cvk : KimchiVK C nc) (L : Array (Vector C.Point nc))
    (cp : KimchiProof C nc σ.k) (pub : Array C.ScalarField) : Bool :=
  let r := runAt C σ cvk cp pub (publicCommitment C σ L pub)
  let tr := transcriptFrom C r.1 r.2
  decide (r.2.proof.sg = msm C σ.g (bPolyCoefficients fun i => tr.2.1[i]))

/-- The decidable mirror of `SgOk`: the deferred check as run out of circuit on a wire
proof, at the key's Lagrange points, one per public-input cell. -/
def sgOk {nc : ℕ} (σ : SRS C.Point) (cvk : KimchiVK C nc) (cp : KimchiProof C nc σ.k)
    (pub : Array C.ScalarField) : Bool :=
  sgOkWith σ cvk (cvk.lagrangePoints σ pub.size).toArray cp pub

/-! ## The deferred obligation, carried

Pickles never checks `SgOk` on the proof itself. The proof's `(sg, round challenges)` becomes
an old accumulator of the next proof on the same curve, whose batch opens it; the circuit in
between, on the other curve, computes the challenges and passes them through its statement.
`carry` decides that handover on two proofs, and `accOk` the deferred equation on the
accumulator alone. -/

/-- Whether an old accumulator's commitment is the challenge polynomial of its round challenges
over the SRS: `SgOk` with the proof's opening and transcript replaced by what the next proof
carries. -/
def accOk (σ : SRS C.Point) (a : Accumulator C σ.k) : Bool :=
  decide (a.sg = msm C σ.g (bPolyCoefficients fun i => a.u[i]))

/-- `carry` at the Lagrange points `L`: the handover on the verifier's run (`runAt`) at the
public commitment to `L`, computed once. -/
def carryWith {nc : ℕ} (σ : SRS C.Point) (cvk : KimchiVK C nc) (L : Array (Vector C.Point nc))
    (cp : KimchiProof C nc σ.k) (pub : Array C.ScalarField)
    {nc' : ℕ} (cp' : KimchiProof C nc' σ.k) (i : Fin cp'.olds.size) : Bool :=
  let r := runAt C σ cvk cp pub (publicCommitment C σ L pub)
  let tr := transcriptFrom C r.1 r.2
  decide (cp'.olds[i].sg = r.2.proof.sg ∧ cp'.olds[i].u = tr.2.1)

/-- Whether `cp'` carries `cp`'s deferred obligation as its old accumulator `i`: the
accumulator's commitment is `cp`'s opening's `sg`, its challenges the wire's round challenges
of `cp`, at the key's Lagrange points, one per public-input cell. -/
def carry {nc : ℕ} (σ : SRS C.Point) (cvk : KimchiVK C nc) (cp : KimchiProof C nc σ.k)
    (pub : Array C.ScalarField)
    {nc' : ℕ} (cp' : KimchiProof C nc' σ.k) (i : Fin cp'.olds.size) : Bool :=
  carryWith σ cvk (cvk.lagrangePoints σ pub.size).toArray cp pub cp' i

/-! ### At more Lagrange points

A driver computes a key's Lagrange points once, as many as the key's public-input count, and
decides `sgOk` and `carry` at them: the public commitment reads only as many as the input has
cells (`publicCommitment_lagrangePoints_of_le`), so these are the same verdicts. -/

/-- `sgOkWith` at the key's Lagrange points, at least one per public-input cell, is `sgOk`. -/
theorem sgOkWith_lagrangePoints {nc : ℕ} (σ : SRS C.Point) (cvk : KimchiVK C nc)
    (cp : KimchiProof C nc σ.k) (pub : Array C.ScalarField) {m : ℕ} (h : pub.size ≤ m) :
    sgOkWith σ cvk (cvk.lagrangePoints σ m).toArray cp pub = sgOk σ cvk cp pub := by
  simp only [sgOkWith, sgOk, publicCommitment_lagrangePoints_of_le C σ cvk pub h]

/-- `carryWith` at the key's Lagrange points, at least one per public-input cell, is
`carry`. -/
theorem carryWith_lagrangePoints {nc : ℕ} (σ : SRS C.Point) (cvk : KimchiVK C nc)
    (cp : KimchiProof C nc σ.k) (pub : Array C.ScalarField) {m : ℕ} (h : pub.size ≤ m)
    {nc' : ℕ} (cp' : KimchiProof C nc' σ.k) (i : Fin cp'.olds.size) :
    carryWith σ cvk (cvk.lagrangePoints σ m).toArray cp pub cp' i = carry σ cvk cp pub cp' i := by
  simp only [carryWith, carry, publicCommitment_lagrangePoints_of_le C σ cvk pub h]

/-- `kimchiVerifyWith` accepting gives `sgOkWith` at the same Lagrange points: the opening check
ends with the deferred `sg` equation. -/
theorem sgOkWith_of_kimchiVerifyWith {nc : ℕ} (σ : SRS C.Point) (cvk : KimchiVK C nc)
    (L : Array (Vector C.Point nc)) (cp : KimchiProof C nc σ.k) (pub : Array C.ScalarField)
    (h : kimchiVerifyWith C σ cvk L cp pub = true) : sgOkWith σ cvk L cp pub = true := by
  unfold kimchiVerifyWith at h
  split at h
  · exact absurd h Bool.false_ne_true
  · simp only [sgOkWith, Ipa.verifyFrom, Ipa.verifyWith, Bool.and_eq_true] at h ⊢
    exact h.2

/-- An accumulator `cp` carries into `cp'` passes `accOk` when `cp` passes `sgOkWith` at the
carry's Lagrange points: the carry makes it `cp`'s `sg` and round challenges. -/
theorem accOk_of_carryWith {nc : ℕ} (σ : SRS C.Point) (cvk : KimchiVK C nc)
    (L : Array (Vector C.Point nc)) (cp : KimchiProof C nc σ.k) (pub : Array C.ScalarField)
    {nc' : ℕ} (cp' : KimchiProof C nc' σ.k) (i : Fin cp'.olds.size)
    (hc : carryWith σ cvk L cp pub cp' i = true) (hs : sgOkWith σ cvk L cp pub = true) :
    accOk σ cp'.olds[i] = true := by
  simp only [carryWith, sgOkWith, accOk, decide_eq_true_eq] at hc hs ⊢
  rw [hc.1, hc.2]
  exact hs

/-- An accepted proof carries an old accumulator whose deferred equation is false. -/
def AccumulatorFailure {C : KimchiCurve} {nc : Nat}
    (σ : SRS C.Point) (vk : KimchiVK C nc)
    (q : KimchiProof C nc σ.k) (pub : Array C.ScalarField) : Prop :=
  kimchiVerify C σ vk q pub = true ∧
    ∃ a ∈ q.olds.toList, accOk σ a = false

/-- Once handover gives membership, acceptance closes the earlier proof or witnesses failure. -/
theorem accepts_or_accumulatorFailure {C : KimchiCurve} {nc nc' : Nat}
    (σ : SRS C.Point) (vk : KimchiVK C nc) (p : KimchiProof C nc σ.k)
    (pub : Array C.ScalarField)
    (nextVk : KimchiVK C nc') (q : KimchiProof C nc' σ.k) (nextPub : Array C.ScalarField)
    (hmem : (⟨p.opening.sg, wireChallenges σ vk p pub⟩ : Accumulator C σ.k) ∈ q.olds.toList)
    (hAccept : kimchiVerify C σ nextVk q nextPub = true)
    (hCapstone : SgOk σ vk p pub → kimchiVerify C σ vk p pub = true) :
    kimchiVerify C σ vk p pub = true ∨ AccumulatorFailure σ nextVk q nextPub := by
  by_cases hAcc : accOk σ ⟨p.opening.sg, wireChallenges σ vk p pub⟩ = true
  · have hSg : SgOk σ vk p pub := by
      simp only [accOk, decide_eq_true_eq] at hAcc
      exact hAcc
    exact Or.inl (hCapstone hSg)
  · exact Or.inr ⟨hAccept, _, hmem, Bool.eq_false_iff.mpr hAcc⟩

end Kimchi.Verifier
