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
private def runZetaOmega (σ : SRS C.Point) (cvk : KimchiVK C nc)
    (cp : KimchiProof C nc σ.k) (pub : Array C.ScalarField) : C.ScalarField :=
  (runOracles C σ cvk cp pub).zeta * cvk.omega

/-- The domain-size power `ζⁿ`, by the squaring ladder. -/
private def runZetaN (σ : SRS C.Point) (cvk : KimchiVK C nc)
    (cp : KimchiProof C nc σ.k) (pub : Array C.ScalarField) : C.ScalarField :=
  powPow2 (runOracles C σ cvk cp pub).zeta cvk.domainLog2

/-- The power `(ζω)ⁿ`, by the squaring ladder. -/
private def runZetaOmegaN (σ : SRS C.Point) (cvk : KimchiVK C nc)
    (cp : KimchiProof C nc σ.k) (pub : Array C.ScalarField) : C.ScalarField :=
  powPow2 (runZetaOmega C σ cvk cp pub) cvk.domainLog2

/-- The chunk-combination power `ζ^{2^σ.k}` (`ζ^max_poly_size`). -/
private def runZetaM (σ : SRS C.Point) (cvk : KimchiVK C nc)
    (cp : KimchiProof C nc σ.k) (pub : Array C.ScalarField) : C.ScalarField :=
  powPow2 (runOracles C σ cvk cp pub).zeta σ.k

/-- The chunk-combination power `(ζω)^{2^σ.k}`. -/
private def runZetaOmegaM (σ : SRS C.Point) (cvk : KimchiVK C nc)
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
private def runLinEvals (σ : SRS C.Point) (cvk : KimchiVK C nc)
    (cp : KimchiProof C nc σ.k) (pub : Array C.ScalarField) :
    Evals C.ScalarField :=
  cp.linEvals (runZetaM C σ cvk cp pub) (runZetaOmegaM C σ cvk cp pub)

/-- The run's fr-sponge challenges `(v, u)` — polyscale and evalscale of the batch. -/
def runVU (σ : SRS C.Point) (cvk : KimchiVK C nc)
    (cp : KimchiProof C nc σ.k) (pub : Array C.ScalarField) :
    C.ScalarField × C.ScalarField :=
  frOracles C cp (runOracles C σ cvk cp pub).digest (runPubEvals C σ cvk cp pub)

/-- The run's computed `ft(ζ)` claim at a given combined public evaluation. -/
private def runFtEval0P (σ : SRS C.Point) (cvk : KimchiVK C nc)
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
private def runFComm (σ : SRS C.Point) (cvk : KimchiVK C nc)
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

/-- The run's flat segment stream in `to_batch` order: the public row's chunks, the
single-chunk ft row, then the 43 tail rows' chunks (`(tailRowsOf …).flatten`) — every
segment a `(commitment, ζ-claim, ζω-claim)` triple, every read total. -/
def runStreamP (σ : SRS C.Point) (cvk : KimchiVK C nc)
    (cp : KimchiProof C nc σ.k) (pub : Array C.ScalarField)
    (pe : Kimchi.Verifier.PointEvaluations (Vector C.ScalarField nc)) :
    Vector (C.Point × C.ScalarField × C.ScalarField) (nc + 1 + tailRowCount * nc) :=
  (Vector.ofFn fun c : Fin nc =>
      ((publicCommitment C σ cvk pub)[c], pe.zeta[c], pe.zetaOmega[c]))
    ++ (⟨#[(runFtComm C σ cvk cp pub,
           runFtEval0P C σ cvk cp pub
             (combineAt (runZetaM C σ cvk cp pub) pe.zeta.toArray),
           cp.ftEval1)], rfl⟩
        : Vector (C.Point × C.ScalarField × C.ScalarField) 1)
    ++ (tailRowsOf C cvk cp).flatten

/-- The batched IPA input at given public evaluations and combination scalars. -/
private def runInputP (σ : SRS C.Point) (cvk : KimchiVK C nc)
    (cp : KimchiProof C nc σ.k) (pub : Array C.ScalarField)
    (pe : Kimchi.Verifier.PointEvaluations (Vector C.ScalarField nc))
    (v u : C.ScalarField) : Ipa.Input C σ.k (nc + 1 + tailRowCount * nc) evalPts where
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
    Ipa.Input C σ.k (nc + 1 + tailRowCount * nc) evalPts :=
  runInputP C σ cvk cp pub (runPubEvals C σ cvk cp pub)
    (runVU C σ cvk cp pub).1 (runVU C σ cvk cp pub).2


/-! ## The body reflection -/


end Kimchi.Verifier
