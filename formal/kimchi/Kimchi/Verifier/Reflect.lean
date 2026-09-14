import Mathlib
import Kimchi.Verifier.Kimchi

/-!
# The run functions and the body reflection

Every intermediate of `kimchiVerify`'s body as a named total function of the checked
records — the oracles, the combination powers, the combined claims, the constructed
ft commitment, the flat segment stream, and the batched IPA input. `runInput`'s
commitment and claim columns are `runStreamP` projections BY DEFINITION, so no
separate content equalities are needed.
`kimchiVerify_reflects` reads an acceptance into these closed forms — the two
argument-dependent guards plus the warm-sponge IPA finish on the run's own stream.
At `nc = 1` with no carried public evaluations, the
verifier computes the barycentric fallback inline (`publicEvals`); at `nc > 1` the
carried chunk vectors are adversarial batch data, believed only through binding.
-/

open Bulletproof

namespace Kimchi.Verifier

open CompElliptic.CurveForms.ShortWeierstrass
open Poseidon Poseidon.FqSponge Bulletproof Kimchi.Index
open Kimchi.Protocol.Linearization Polynomial
open Kimchi.Verifier

variable (C : Ipa.CommitmentCurve)

/-! ## The run-derived data -/

variable {nc : ℕ}

/-- The run's fq-sponge oracles: the deployed chunk-fold schedule at the run's own
per-chunk public commitment. -/
def runOracles (σ : SRS C.Point) (cvk : KimchiVK C nc)
    (cp : KimchiProof C nc σ.k) (pub : Array C.ScalarField) : FqOracles C :=
  fqOracles C cvk cp (publicCommitment C σ cvk pub)

/-- The second batch point `ζω`. -/
def runZetaOmega (σ : SRS C.Point) (cvk : KimchiVK C nc)
    (cp : KimchiProof C nc σ.k) (pub : Array C.ScalarField) : C.ScalarField :=
  (runOracles C σ cvk cp pub).zeta * cvk.omega

/-- The domain-size power `ζⁿ`, by the squaring ladder. Public: the wrap circuit consumes it
as the deferred `zeta_to_domain_size` claim, which the group-half read ties to this. -/
def runZetaN (σ : SRS C.Point) (cvk : KimchiVK C nc)
    (cp : KimchiProof C nc σ.k) (pub : Array C.ScalarField) : C.ScalarField :=
  powPow2 (runOracles C σ cvk cp pub).zeta cvk.domainLog2

/-- The power `(ζω)ⁿ`, by the squaring ladder. -/
def runZetaOmegaN (σ : SRS C.Point) (cvk : KimchiVK C nc)
    (cp : KimchiProof C nc σ.k) (pub : Array C.ScalarField) : C.ScalarField :=
  powPow2 (runZetaOmega C σ cvk cp pub) cvk.domainLog2

/-- The chunk-combination power `ζ^{2^σ.k}` (`ζ^max_poly_size`). Public: the wrap circuit
consumes it as the deferred `zeta_to_srs_length` claim, which the group-half read ties to
this. -/
def runZetaM (σ : SRS C.Point) (cvk : KimchiVK C nc)
    (cp : KimchiProof C nc σ.k) (pub : Array C.ScalarField) : C.ScalarField :=
  powPow2 (runOracles C σ cvk cp pub).zeta σ.k

/-- The chunk-combination power `(ζω)^{2^σ.k}`. -/
def runZetaOmegaM (σ : SRS C.Point) (cvk : KimchiVK C nc)
    (cp : KimchiProof C nc σ.k) (pub : Array C.ScalarField) : C.ScalarField :=
  powPow2 (runZetaOmega C σ cvk cp pub) σ.k

/-- The run's public evaluation chunk vectors: proof-carried when present, the
one-chunk barycentric fallback otherwise (verifier.rs:332–379). -/
def runPubEvals (σ : SRS C.Point) (cvk : KimchiVK C nc)
    (cp : KimchiProof C nc σ.k) (pub : Array C.ScalarField) :
    Kimchi.Verifier.PointEvaluations (Vector C.ScalarField nc) :=
  publicEvalChunks cp cvk.n cvk.omega (runOracles C σ cvk cp pub).zeta
    (runZetaOmega C σ cvk cp pub) (runZetaN C σ cvk cp pub)
    (runZetaOmegaN C σ cvk cp pub) pub


/-- The run's chunk-combined evaluation record — the verifier's `evals.combine`. -/
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
    (mdsOfParams C.frParams)
    (runOracles C σ cvk cp pub).alpha (runOracles C σ cvk cp pub).beta
    (runOracles C σ cvk cp pub).gamma (runOracles C σ cvk cp pub).zeta pubEval0
    (runLinEvals C σ cvk cp pub)


/-- The run's permutation scalar (the `f_comm` coefficient). -/
def runPScalar (σ : SRS C.Point) (cvk : KimchiVK C nc)
    (cp : KimchiProof C nc σ.k) (pub : Array C.ScalarField) : C.ScalarField :=
  permScalar (runOracles C σ cvk cp pub).beta (runOracles C σ cvk cp pub).gamma
    (runOracles C σ cvk cp pub).alpha
    (zkpmEval cvk.n cvk.zkRows cvk.omega (runOracles C σ cvk cp pub).zeta)
    (runLinEvals C σ cvk cp pub)

/-- The run's `f_comm` chunks — the `pScalar`-scaled `σ₆` chunk vector. -/
def runFComm (σ : SRS C.Point) (cvk : KimchiVK C nc)
    (cp : KimchiProof C nc σ.k) (pub : Array C.ScalarField) :
    Vector C.Point nc :=
  cvk.sigmaComm[6].map (fun P => (runPScalar C σ cvk cp pub).val • P)

/-- The run's constructed ft commitment (verifier.rs:960–965): the DOUBLE collapse at
`ζ^{2^σ.k}` — `combine(ζ^max, f_comm) − (ζⁿ − 1)·combine(ζ^max, t_comm)`. -/
def runFtComm (σ : SRS C.Point) (cvk : KimchiVK C nc)
    (cp : KimchiProof C nc σ.k) (pub : Array C.ScalarField) : C.Point :=
  Ipa.combineCommitments C (runZetaM C σ cvk cp pub)
      (runFComm C σ cvk cp pub).toArray
    - (runZetaN C σ cvk cp pub - 1).val
        • Ipa.combineCommitments C (runZetaM C σ cvk cp pub) cp.tComm

/-- The run's flat segment stream in `to_batch` order: the proof's old accumulators' rows,
the public row's chunks, the single-chunk ft row, then the 43 tail rows' chunks
(`(tailRowsOf …).flatten`) — every segment a `(commitment, ζ-claim, ζω-claim)` triple,
every read total. -/
def runStreamP (σ : SRS C.Point) (cvk : KimchiVK C nc)
    (cp : KimchiProof C nc σ.k) (pub : Array C.ScalarField)
    (pe : Kimchi.Verifier.PointEvaluations (Vector C.ScalarField nc)) :
    Vector (C.Point × C.ScalarField × C.ScalarField)
      (cp.olds.size + (nc + 1 + tailRowCount * nc)) :=
  (⟨cp.olds.map (fun a => (a.sg, bPoly a.u.get (runOracles C σ cvk cp pub).zeta,
      bPoly a.u.get (runZetaOmega C σ cvk cp pub))), by simp⟩
    : Vector (C.Point × C.ScalarField × C.ScalarField) cp.olds.size)
    ++ ((Vector.ofFn fun c : Fin nc =>
          ((publicCommitment C σ cvk pub)[c], pe.zeta[c], pe.zetaOmega[c]))
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

/-- The batched IPA input the run hands to the warm-sponge opening finish (closed
form). -/
def runInput (σ : SRS C.Point) (cvk : KimchiVK C nc)
    (cp : KimchiProof C nc σ.k) (pub : Array C.ScalarField) :
    Ipa.Input C σ.k (cp.olds.size + (nc + 1 + tailRowCount * nc)) evalPts :=
  runInputP C σ cvk cp pub (runPubEvals C σ cvk cp pub)
    (runFrOracles C σ cvk cp pub).xi (runFrOracles C σ cvk cp pub).r


/-! ## The body reflection -/


/-! ## The body reflection -/

/-- The argument-dependent guards of `kimchiVerify` (verifier.rs:810–820, and the public
input against the Lagrange table and the domain): the public input fits the Lagrange table
and the domain, and the accumulator count is the key's. -/
def Guards {k : ℕ} (cvk : KimchiVK C nc) (cp : KimchiProof C nc k) (pub : Array C.ScalarField) :
    Prop :=
  ¬ (cvk.lagrangeBasis.size < pub.size ∨ cvk.n < pub.size ∨ cp.olds.size ≠ cvk.prevChallenges)

/-- `kimchiVerify` accepts iff the guards hold and the warm-sponge IPA finish (`verifyFrom`)
accepts on the run's own input. -/
theorem kimchiVerify_reflects (σ : SRS C.Point) (cvk : KimchiVK C nc) (cp : KimchiProof C nc σ.k)
    (pub : Array C.ScalarField) :
    kimchiVerify C σ cvk cp pub = true
      ↔ Guards C cvk cp pub ∧
        Ipa.verifyFrom C σ (runOracles C σ cvk cp pub).warm (runInput C σ cvk cp pub) = true := by
  have hkv : kimchiVerify C σ cvk cp pub
      = (if cvk.lagrangeBasis.size < pub.size || cvk.n < pub.size
            || cp.olds.size ≠ cvk.prevChallenges then false
          else Ipa.verifyFrom C σ (runOracles C σ cvk cp pub).warm (runInput C σ cvk cp pub)) := rfl
  have hcond : (cvk.lagrangeBasis.size < pub.size || cvk.n < pub.size
      || cp.olds.size ≠ cvk.prevChallenges) = true ↔ ¬ Guards C cvk cp pub := by
    simp only [Guards, Bool.or_eq_true, decide_eq_true_eq, ne_eq, not_not, or_assoc]
  rw [hkv]
  by_cases hg : Guards C cvk cp pub
  · rw [if_neg (hcond.not.mpr (not_not.mpr hg))]
    simp [hg]
  · rw [if_pos (hcond.mpr hg)]
    simp [hg]

end Kimchi.Verifier
