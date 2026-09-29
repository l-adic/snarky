import Mathlib
import Kimchi.Verifier.Kimchi

/-!
# The run functions and the body reflection

Every intermediate of `kimchiVerify`'s body as a named total function of the checked
records: the oracles, the combination powers, the combined claims, the ft commitment, the
flat segment stream and the batched IPA input. `runInput`'s commitment and claim columns are
`runStreamP` projections by definition, so no separate content equalities are needed.

The run functions are for proofs, not for running: each recomputes the public commitment, and
with it the SRS's Lagrange points. The body itself (`kimchiVerifyWith`) computes its run once
(`runAt`), at the Lagrange points it is given.

`kimchiVerify_reflects` reads an acceptance as `Guards` plus the warm-sponge IPA finish on
`runInput`. Proof-carried public evaluations are adversarial batch data, believed only
through binding; without them, at `nc = 1`, the verifier computes the barycentric fallback
(`publicEvalChunks`).
-/

open Bulletproof

namespace Kimchi.Verifier

open CompElliptic.CurveForms.ShortWeierstrass
open Poseidon Poseidon.FqSponge Bulletproof
open Kimchi.Protocol.Linearization Polynomial
open Kimchi.Verifier

variable (C : Ipa.KimchiCurve)

/-! ## The run-derived data -/

variable {nc : ℕ}

/-- The run's public commitment: `publicCommitment` at the key's first `pub.size` Lagrange
points. -/
def runPublicComm (σ : SRS C.Point) (cvk : KimchiVK C nc) (pub : Array C.ScalarField) :
    Vector C.Point nc :=
  publicCommitment C σ (cvk.lagrangePoints σ pub.size).toArray pub

/-- The run's fq-sponge oracles, `fqOracles` at the run's own public commitment. -/
def runOracles (σ : SRS C.Point) (cvk : KimchiVK C nc)
    (cp : KimchiProof C nc σ.k) (pub : Array C.ScalarField) : FqOracles C :=
  fqOracles C cvk cp (runPublicComm C σ cvk pub)

/-- The second batch point `ζω`. -/
def runZetaOmega (σ : SRS C.Point) (cvk : KimchiVK C nc)
    (cp : KimchiProof C nc σ.k) (pub : Array C.ScalarField) : C.ScalarField :=
  (runOracles C σ cvk cp pub).zeta * cvk.omega

/-- The domain-size power `ζⁿ`, by the squaring ladder. The wrap circuit's deferred `ζⁿ`
claim is tied to it. -/
def runZetaN (σ : SRS C.Point) (cvk : KimchiVK C nc)
    (cp : KimchiProof C nc σ.k) (pub : Array C.ScalarField) : C.ScalarField :=
  powPow2 (runOracles C σ cvk cp pub).zeta cvk.domainLog2

/-- The power `(ζω)ⁿ`, by the squaring ladder. -/
def runZetaOmegaN (σ : SRS C.Point) (cvk : KimchiVK C nc)
    (cp : KimchiProof C nc σ.k) (pub : Array C.ScalarField) : C.ScalarField :=
  powPow2 (runZetaOmega C σ cvk cp pub) cvk.domainLog2

/-- The chunk-combination power `ζ^{2^σ.k}`. The wrap circuit's deferred `ζ^{2^σ.k}` claim
is tied to it. -/
def runZetaM (σ : SRS C.Point) (cvk : KimchiVK C nc)
    (cp : KimchiProof C nc σ.k) (pub : Array C.ScalarField) : C.ScalarField :=
  powPow2 (runOracles C σ cvk cp pub).zeta σ.k

/-- The chunk-combination power `(ζω)^{2^σ.k}`. -/
def runZetaOmegaM (σ : SRS C.Point) (cvk : KimchiVK C nc)
    (cp : KimchiProof C nc σ.k) (pub : Array C.ScalarField) : C.ScalarField :=
  powPow2 (runZetaOmega C σ cvk cp pub) σ.k

/-- The run's public evaluation chunk vectors: proof-carried when present, else the
one-chunk barycentric fallback. -/
def runPubEvals (σ : SRS C.Point) (cvk : KimchiVK C nc)
    (cp : KimchiProof C nc σ.k) (pub : Array C.ScalarField) :
    Kimchi.Verifier.PointEvaluations (Vector C.ScalarField nc) :=
  publicEvalChunks cp cvk.n cvk.omega (runOracles C σ cvk cp pub).zeta
    (runZetaOmega C σ cvk cp pub) (runZetaN C σ cvk cp pub)
    (runZetaOmegaN C σ cvk cp pub) pub


/-- The run's evaluations, chunk-combined into the linearization's `Evals` record. -/
def runLinEvals (σ : SRS C.Point) (cvk : KimchiVK C nc)
    (cp : KimchiProof C nc σ.k) (pub : Array C.ScalarField) :
    Evals C.ScalarField :=
  cp.linEvals (runZetaM C σ cvk cp pub) (runZetaOmegaM C σ cvk cp pub)

/-- The run's fr-sponge oracles: the polyscale `ξ` and the evalscale `r` of the batch. -/
def runFrOracles (σ : SRS C.Point) (cvk : KimchiVK C nc)
    (cp : KimchiProof C nc σ.k) (pub : Array C.ScalarField) : FrOracles C :=
  frOracles C cp (runOracles C σ cvk cp pub).digest (runPubEvals C σ cvk cp pub)

/-- The run's computed `ft(ζ)` claim at a given combined public evaluation. -/
def runFtEval0P (σ : SRS C.Point) (cvk : KimchiVK C nc)
    (cp : KimchiProof C nc σ.k) (pub : Array C.ScalarField)
    (pubEval0 : C.ScalarField) : C.ScalarField :=
  ftEval0 cvk.n cvk.zkRows cvk.omega (fun i => cvk.shifts[i]) cvk.endo
    (mdsOfParams C.frSponge.params)
    (runOracles C σ cvk cp pub).alpha (runOracles C σ cvk cp pub).beta
    (runOracles C σ cvk cp pub).gamma (runOracles C σ cvk cp pub).zeta pubEval0
    (runLinEvals C σ cvk cp pub)


/-- The run's permutation scalar, the coefficient of `runFComm`. -/
def runPScalar (σ : SRS C.Point) (cvk : KimchiVK C nc)
    (cp : KimchiProof C nc σ.k) (pub : Array C.ScalarField) : C.ScalarField :=
  permScalar (runOracles C σ cvk cp pub).beta (runOracles C σ cvk cp pub).gamma
    (runOracles C σ cvk cp pub).alpha
    (zkpmEval cvk.n cvk.zkRows cvk.omega (runOracles C σ cvk cp pub).zeta)
    (runLinEvals C σ cvk cp pub)

/-- The run's linearized permutation commitment: the last σ commitment's chunks, each
scaled by `runPScalar`. -/
def runFComm (σ : SRS C.Point) (cvk : KimchiVK C nc)
    (cp : KimchiProof C nc σ.k) (pub : Array C.ScalarField) :
    Vector C.Point nc :=
  cvk.sigmaComm[6].map (fun P => (runPScalar C σ cvk cp pub).val • P)

/-- The run's constructed ft commitment: `runFComm` minus `ζⁿ − 1` times the quotient
commitment, each chunk-combined at `ζ^{2^σ.k}`. -/
def runFtComm (σ : SRS C.Point) (cvk : KimchiVK C nc)
    (cp : KimchiProof C nc σ.k) (pub : Array C.ScalarField) : C.Point :=
  Ipa.combineCommitments C (runZetaM C σ cvk cp pub)
      (runFComm C σ cvk cp pub).toArray
    - (runZetaN C σ cvk cp pub - 1).val
        • Ipa.combineCommitments C (runZetaM C σ cvk cp pub) cp.tComm

/-- The run's flat segment stream at public evaluations `pe`, in batch order: the old
accumulators' rows, the public row's chunks, the one-segment ft row, then the chunks of the
`tailRowsOf` rows. Each segment is a `(commitment, ζ-claim, ζω-claim)` triple. -/
def runStreamP (σ : SRS C.Point) (cvk : KimchiVK C nc)
    (cp : KimchiProof C nc σ.k) (pub : Array C.ScalarField)
    (pe : Kimchi.Verifier.PointEvaluations (Vector C.ScalarField nc)) :
    Vector (C.Point × C.ScalarField × C.ScalarField)
      (cp.olds.size + (nc + 1 + tailRowCount * nc)) :=
  (⟨cp.olds.map (fun a => (a.sg, bPoly a.u.get (runOracles C σ cvk cp pub).zeta,
      bPoly a.u.get (runZetaOmega C σ cvk cp pub))), by simp⟩
    : Vector (C.Point × C.ScalarField × C.ScalarField) cp.olds.size)
    ++ ((Vector.ofFn fun c : Fin nc =>
          ((runPublicComm C σ cvk pub)[c], pe.zeta[c], pe.zetaOmega[c]))
        ++ (⟨#[(runFtComm C σ cvk cp pub,
               runFtEval0P C σ cvk cp pub
                 (combineAt (runZetaM C σ cvk cp pub) pe.zeta.toArray),
               cp.ftEval1)], rfl⟩
            : Vector (C.Point × C.ScalarField × C.ScalarField) 1)
        ++ (tailRowsOf C cvk cp).flatten)

/-- The batched IPA input at given public evaluations and combination scalars. -/
def runInputP (σ : SRS C.Point) (cvk : KimchiVK C nc)
    (cp : KimchiProof C nc σ.k) (pub : Array C.ScalarField)
    (pe : Kimchi.Verifier.PointEvaluations (Vector C.ScalarField nc))
    (v u : C.ScalarField) :
    Ipa.Input C σ.k (cp.olds.size + (nc + 1 + tailRowCount * nc)) evalPts where
  commitments := (runStreamP C σ cvk cp pub pe).map (·.1)
  xs := ⟨#[(runOracles C σ cvk cp pub).zeta, runZetaOmega C σ cvk cp pub], rfl⟩
  evals := (runStreamP C σ cvk cp pub pe).map
    (fun r => (⟨#[r.2.1, r.2.2], rfl⟩ : Vector C.ScalarField evalPts))
  polyscale := v
  evalscale := u
  proof := cp.opening

/-- `runInputP` at the run's own public evaluations and fr-sponge scalars: the input
`kimchiVerify` hands to `Ipa.verifyFrom`. -/
def runInput (σ : SRS C.Point) (cvk : KimchiVK C nc)
    (cp : KimchiProof C nc σ.k) (pub : Array C.ScalarField) :
    Ipa.Input C σ.k (cp.olds.size + (nc + 1 + tailRowCount * nc)) evalPts :=
  runInputP C σ cvk cp pub (runPubEvals C σ cvk cp pub)
    (runFrOracles C σ cvk cp pub).xi (runFrOracles C σ cvk cp pub).r

/-! ## Zero public-input cells

Zero cells past the end of the public input change no run function: the input enters only
through the public commitment and the barycentric evaluations, and a zero cell adds nothing to
either. -/

section AppendZero

variable (σ : SRS C.Point) (cvk : KimchiVK C nc) (cp : KimchiProof C nc σ.k)
  (pub zs : Array C.ScalarField) (hz : ∀ z ∈ zs, z = 0)
include hz

theorem runPublicComm_append_zero :
    runPublicComm C σ cvk (pub ++ zs) = runPublicComm C σ cvk pub := by
  unfold runPublicComm
  rw [publicCommitment_append_zero C σ _ pub zs hz (by simp),
    publicCommitment_lagrangePoints_of_le C σ cvk pub (by simp)]

theorem runOracles_append_zero :
    runOracles C σ cvk cp (pub ++ zs) = runOracles C σ cvk cp pub := by
  simp only [runOracles, runPublicComm_append_zero C σ cvk pub zs hz]

theorem runZetaN_append_zero : runZetaN C σ cvk cp (pub ++ zs) = runZetaN C σ cvk cp pub := by
  simp only [runZetaN, runOracles_append_zero C σ cvk cp pub zs hz]

theorem runZetaM_append_zero : runZetaM C σ cvk cp (pub ++ zs) = runZetaM C σ cvk cp pub := by
  simp only [runZetaM, runOracles_append_zero C σ cvk cp pub zs hz]

theorem runPubEvals_append_zero :
    runPubEvals C σ cvk cp (pub ++ zs) = runPubEvals C σ cvk cp pub := by
  simp only [runPubEvals, runZetaOmega, runZetaN, runZetaOmegaN,
    runOracles_append_zero C σ cvk cp pub zs hz, publicEvalChunks_append_zero _ _ _ _ _ _ _ _ _ hz]

theorem runPScalar_append_zero :
    runPScalar C σ cvk cp (pub ++ zs) = runPScalar C σ cvk cp pub := by
  simp only [runPScalar, runLinEvals, runZetaM, runZetaOmegaM, runZetaOmega,
    runOracles_append_zero C σ cvk cp pub zs hz]

theorem runInput_append_zero :
    runInput C σ cvk cp (pub ++ zs) = runInput C σ cvk cp pub := by
  simp only [runInput, runInputP, runStreamP, runFrOracles, runFtComm, runFComm, runFtEval0P,
    runPScalar, runLinEvals, runZetaOmega, runZetaN, runZetaM, runZetaOmegaM,
    runOracles_append_zero C σ cvk cp pub zs hz, runPubEvals_append_zero C σ cvk cp pub zs hz,
    runPublicComm_append_zero C σ cvk pub zs hz]

end AppendZero

/-! ## The body reflection -/

/-- The argument-dependent guards of `kimchiVerify`: the accumulator count and the public
input's length are the key's. -/
def Guards {k : ℕ} (cvk : KimchiVK C nc) (cp : KimchiProof C nc k) (pub : Array C.ScalarField) :
    Prop :=
  cp.olds.size = cvk.prevChallenges ∧ pub.size = cvk.publicCount

/-- `kimchiVerify` accepts iff the guards hold and the warm-sponge IPA finish (`verifyFrom`)
accepts on the run's own input. -/
theorem kimchiVerify_reflects (σ : SRS C.Point) (cvk : KimchiVK C nc) (cp : KimchiProof C nc σ.k)
    (pub : Array C.ScalarField) :
    kimchiVerify C σ cvk cp pub = true
      ↔ Guards C cvk cp pub ∧
        Ipa.verifyFrom C σ (runOracles C σ cvk cp pub).warm (runInput C σ cvk cp pub) = true := by
  have hkv : kimchiVerify C σ cvk cp pub
      = (if cp.olds.size ≠ cvk.prevChallenges || pub.size ≠ cvk.publicCount then false
          else Ipa.verifyFrom C σ (runOracles C σ cvk cp pub).warm (runInput C σ cvk cp pub)) := by
    unfold kimchiVerify kimchiVerifyWith
    by_cases h : pub.size = cvk.publicCount
    · rw [← h]
      rfl
    · have hg : (decide (cp.olds.size ≠ cvk.prevChallenges) || decide (pub.size ≠ cvk.publicCount))
          = true := by simp [h]
      simp only [hg, if_true]
  have hcond : (cp.olds.size ≠ cvk.prevChallenges || pub.size ≠ cvk.publicCount) = true
      ↔ ¬ Guards C cvk cp pub := by
    simp only [Guards, Bool.or_eq_true, decide_eq_true_eq, ne_eq, not_and_or]
  rw [hkv]
  by_cases hg : Guards C cvk cp pub
  · rw [if_neg (hcond.not.mpr (not_not.mpr hg))]
    simp [hg]
  · rw [if_pos (hcond.mpr hg)]
    simp [hg]

end Kimchi.Verifier
