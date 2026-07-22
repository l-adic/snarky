import Mathlib
import Kimchi.Verifier.Kimchi

/-!
# The run functions and the body reflection

Every intermediate of `kimchiVerify`'s body as a named total function of the checked
records — the oracles, the combination powers, the combined claims, the constructed
ft commitment, the 45 logical rows and their flat segment stream, and the batched IPA
input. `runInput`'s commitment and claim columns are `flatRows (runLogicalP …)`
projections BY DEFINITION, so no separate content equalities are needed.
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
    (cp : KimchiProof C nc) (pub : Array C.ScalarField) : FqOracles C :=
  fqOracles C cvk cp (publicCommitment C σ cvk pub)

/-- The second batch point `ζω`. -/
def runZetaOmega (σ : SRS C.Point) (cvk : KimchiVK C nc)
    (cp : KimchiProof C nc) (pub : Array C.ScalarField) : C.ScalarField :=
  (runOracles C σ cvk cp pub).zeta * cvk.omega

/-- The domain-size power `ζⁿ`, by the squaring ladder. -/
def runZetaN (σ : SRS C.Point) (cvk : KimchiVK C nc)
    (cp : KimchiProof C nc) (pub : Array C.ScalarField) : C.ScalarField :=
  powPow2 (runOracles C σ cvk cp pub).zeta cvk.domainLog2

/-- The power `(ζω)ⁿ`, by the squaring ladder. -/
private def runZetaOmegaN (σ : SRS C.Point) (cvk : KimchiVK C nc)
    (cp : KimchiProof C nc) (pub : Array C.ScalarField) : C.ScalarField :=
  powPow2 (runZetaOmega C σ cvk cp pub) cvk.domainLog2

/-- The chunk-combination power `ζ^{2^σ.k}` (`ζ^max_poly_size`). -/
def runZetaM (σ : SRS C.Point) (cvk : KimchiVK C nc)
    (cp : KimchiProof C nc) (pub : Array C.ScalarField) : C.ScalarField :=
  powPow2 (runOracles C σ cvk cp pub).zeta σ.k

/-- The chunk-combination power `(ζω)^{2^σ.k}`. -/
def runZetaOmegaM (σ : SRS C.Point) (cvk : KimchiVK C nc)
    (cp : KimchiProof C nc) (pub : Array C.ScalarField) : C.ScalarField :=
  powPow2 (runZetaOmega C σ cvk cp pub) σ.k

/-- The run's public evaluation chunk vectors: proof-carried when present, the
one-chunk barycentric fallback otherwise (verifier.rs:332–379). -/
def runPubEvals (σ : SRS C.Point) (cvk : KimchiVK C nc)
    (cp : KimchiProof C nc) (pub : Array C.ScalarField) :
    Kimchi.Verifier.PointEvaluations (Vector C.ScalarField nc) :=
  publicEvalChunks cp cvk.n cvk.omega (runOracles C σ cvk cp pub).zeta
    (runZetaOmega C σ cvk cp pub) (runZetaN C σ cvk cp pub)
    (runZetaOmegaN C σ cvk cp pub) pub

/-- The run's chunk-combined public evaluation at `ζ` — `ft_eval0`'s public slot. -/
def runPubEval0 (σ : SRS C.Point) (cvk : KimchiVK C nc)
    (cp : KimchiProof C nc) (pub : Array C.ScalarField) : C.ScalarField :=
  combineAt (runZetaM C σ cvk cp pub) (runPubEvals C σ cvk cp pub).zeta.toArray

/-- The run's chunk-combined evaluation record — the verifier's `evals.combine`. -/
def runLinEvals (σ : SRS C.Point) (cvk : KimchiVK C nc)
    (cp : KimchiProof C nc) (pub : Array C.ScalarField) :
    Evals C.ScalarField :=
  cp.linEvals (runZetaM C σ cvk cp pub) (runZetaOmegaM C σ cvk cp pub)

/-- The run's fr-sponge challenges `(v, u)` — polyscale and evalscale of the batch. -/
def runVU (σ : SRS C.Point) (cvk : KimchiVK C nc)
    (cp : KimchiProof C nc) (pub : Array C.ScalarField) :
    C.ScalarField × C.ScalarField :=
  frOracles C cvk cp (runOracles C σ cvk cp pub).digest (runPubEvals C σ cvk cp pub)

/-- The run's computed `ft(ζ)` claim at a given combined public evaluation. -/
def runFtEval0P (σ : SRS C.Point) (cvk : KimchiVK C nc)
    (cp : KimchiProof C nc) (pub : Array C.ScalarField)
    (pubEval0 : C.ScalarField) : C.ScalarField :=
  ftEval0 cvk.n cvk.zkRows cvk.omega (fun i => cvk.shifts[i]) cvk.endo
    (mdsOfParams cvk.frParams)
    (runOracles C σ cvk cp pub).alpha (runOracles C σ cvk cp pub).beta
    (runOracles C σ cvk cp pub).gamma (runOracles C σ cvk cp pub).zeta pubEval0
    (runLinEvals C σ cvk cp pub)

/-- The run's computed `ft(ζ)` claim (closed form). -/
def runFtEval0 (σ : SRS C.Point) (cvk : KimchiVK C nc)
    (cp : KimchiProof C nc) (pub : Array C.ScalarField) : C.ScalarField :=
  runFtEval0P C σ cvk cp pub (runPubEval0 C σ cvk cp pub)

/-- The run's permutation scalar (the `f_comm` coefficient). -/
def runPScalar (σ : SRS C.Point) (cvk : KimchiVK C nc)
    (cp : KimchiProof C nc) (pub : Array C.ScalarField) : C.ScalarField :=
  permScalar (runOracles C σ cvk cp pub).beta (runOracles C σ cvk cp pub).gamma
    (runOracles C σ cvk cp pub).alpha
    (zkpmEval cvk.n cvk.zkRows cvk.omega (runOracles C σ cvk cp pub).zeta)
    (runLinEvals C σ cvk cp pub)

/-- The run's `f_comm` chunks — the `pScalar`-scaled `σ₆` chunk vector. -/
def runFComm (σ : SRS C.Point) (cvk : KimchiVK C nc)
    (cp : KimchiProof C nc) (pub : Array C.ScalarField) :
    Vector C.Point nc :=
  cvk.sigmaComm[6].map (fun P => (runPScalar C σ cvk cp pub).val • P)

/-- The run's constructed ft commitment (verifier.rs:960–965): the DOUBLE collapse at
`ζ^{2^σ.k}` — `combine(ζ^max, f_comm) − (ζⁿ − 1)·combine(ζ^max, t_comm)`. -/
def runFtComm (σ : SRS C.Point) (cvk : KimchiVK C nc)
    (cp : KimchiProof C nc) (pub : Array C.ScalarField) : C.Point :=
  Ipa.combineCommitments C (runZetaM C σ cvk cp pub)
      (runFComm C σ cvk cp pub).toArray
    - (runZetaN C σ cvk cp pub - 1).val
        • Ipa.combineCommitments C (runZetaM C σ cvk cp pub) cp.tComm

/-- The run's 45 LOGICAL rows in `to_batch` order, at given public evaluation chunk
vectors: each row its chunk-vector commitment with the per-chunk claims at `(ζ, ζω)`
(the ft row single-chunk). -/
def runLogicalP (σ : SRS C.Point) (cvk : KimchiVK C nc)
    (cp : KimchiProof C nc) (pub : Array C.ScalarField)
    (pe : Kimchi.Verifier.PointEvaluations (Vector C.ScalarField nc)) :
    Array (Array C.Point × Array C.ScalarField × Array C.ScalarField) :=
  #[((publicCommitment C σ cvk pub).toArray, pe.zeta.toArray, pe.zetaOmega.toArray),
    (#[runFtComm C σ cvk cp pub],
      #[runFtEval0P C σ cvk cp pub
          (combineAt (runZetaM C σ cvk cp pub) pe.zeta.toArray)],
      #[cp.ftEval1]),
    (cp.zComm.toArray, cp.evals.z.zeta.toArray, cp.evals.z.zetaOmega.toArray),
    (cvk.genericComm.toArray, cp.evals.genericSelector.zeta.toArray,
      cp.evals.genericSelector.zetaOmega.toArray),
    (cvk.poseidonComm.toArray, cp.evals.poseidonSelector.zeta.toArray,
      cp.evals.poseidonSelector.zetaOmega.toArray),
    (cvk.completeAddComm.toArray, cp.evals.completeAddSelector.zeta.toArray,
      cp.evals.completeAddSelector.zetaOmega.toArray),
    (cvk.mulComm.toArray, cp.evals.mulSelector.zeta.toArray,
      cp.evals.mulSelector.zetaOmega.toArray),
    (cvk.emulComm.toArray, cp.evals.emulSelector.zeta.toArray,
      cp.evals.emulSelector.zetaOmega.toArray),
    (cvk.endomulScalarComm.toArray, cp.evals.endomulScalarSelector.zeta.toArray,
      cp.evals.endomulScalarSelector.zetaOmega.toArray)]
  ++ (cp.wComm.zip cp.evals.w).toArray.map
      (fun x => (x.1.toArray, x.2.zeta.toArray, x.2.zetaOmega.toArray))
  ++ (cvk.coefficientsComm.zip cp.evals.coefficients).toArray.map
      (fun x => (x.1.toArray, x.2.zeta.toArray, x.2.zetaOmega.toArray))
  ++ ((cvk.sigmaComm.take 6).zip cp.evals.s).toArray.map
      (fun x => (x.1.toArray, x.2.zeta.toArray, x.2.zetaOmega.toArray))

/-- The flat segment rows of a logical-row array — the `to_batch` stream: each logical
row's chunks zipped with its per-chunk claims, consecutively. -/
def flatRows (logical : Array (Array C.Point × Array C.ScalarField × Array C.ScalarField)) :
    Array (C.Point × C.ScalarField × C.ScalarField) :=
  logical.flatMap (fun r => (r.1.zip (r.2.1.zip r.2.2)).map (fun ce => (ce.1, ce.2.1, ce.2.2)))

/-- The batched IPA input at given public evaluations and combination scalars. -/
def runInputP (σ : SRS C.Point) (cvk : KimchiVK C nc)
    (cp : KimchiProof C nc) (pub : Array C.ScalarField)
    (pe : Kimchi.Verifier.PointEvaluations (Vector C.ScalarField nc))
    (v u : C.ScalarField) : Ipa.Input C where
  commitments := (flatRows C (runLogicalP C σ cvk cp pub pe)).map (·.1)
  xs := #[(runOracles C σ cvk cp pub).zeta, runZetaOmega C σ cvk cp pub]
  evals := (flatRows C (runLogicalP C σ cvk cp pub pe)).map (fun r => #[r.2.1, r.2.2])
  polyscale := v
  evalscale := u
  proof := cp.opening

/-- The acceptance decision at given public evaluations and combination scalars. -/
private def runBody (σ : SRS C.Point) (cvk : KimchiVK C nc)
    (cp : KimchiProof C nc) (pub : Array C.ScalarField)
    (pe : Kimchi.Verifier.PointEvaluations (Vector C.ScalarField nc))
    (v u : C.ScalarField) : Bool :=
  Ipa.verifyFrom C σ (runOracles C σ cvk cp pub).warm
    (runInputP C σ cvk cp pub pe v u)

/-- The batched IPA input the run hands to the warm-sponge opening finish (closed
form). -/
def runInput (σ : SRS C.Point) (cvk : KimchiVK C nc)
    (cp : KimchiProof C nc) (pub : Array C.ScalarField) : Ipa.Input C :=
  runInputP C σ cvk cp pub (runPubEvals C σ cvk cp pub)
    (runVU C σ cvk cp pub).1 (runVU C σ cvk cp pub).2

/-- The warm post-`ζ` sponge state the opening verification continues from. -/
def runWarm (σ : SRS C.Point) (cvk : KimchiVK C nc)
    (cp : KimchiProof C nc) (pub : Array C.ScalarField) :
    FqSponge.S C.base :=
  (runOracles C σ cvk cp pub).warm

/-! ## The body reflection -/

/-- **The body reflection**: a `kimchiVerify` acceptance is the two
argument-dependent guards plus the warm-sponge IPA finish accepting the run's own
flat segment stream — no trust, pure code-path reading. The `replace` re-expresses
`kimchiVerify`'s body through the named run functions (definitional: they mirror the
body's `let`s; the one pair destructuring, `(v, u) := frOracles …`, stays a match),
so no sponge computation is ever reduced. -/
theorem kimchiVerify_reflects (σ : SRS C.Point) (cvk : KimchiVK C nc)
    (cp : KimchiProof C nc) (pub : Array C.ScalarField)
    (hv : kimchiVerify C σ cvk cp pub = true) :
    pub.size ≤ cvk.lagrangeBasis.size ∧ pub.size ≤ cvk.n
      ∧ Ipa.verifyFrom C σ (runWarm C σ cvk cp pub)
          (runInput C σ cvk cp pub) = true := by
  replace hv : (if cvk.lagrangeBasis.size < pub.size || cvk.n < pub.size then
      false
    else
      match runVU C σ cvk cp pub with
      | (v, u) => runBody C σ cvk cp pub (runPubEvals C σ cvk cp pub) v u) = true := hv
  split at hv
  case isTrue => exact absurd hv (by simp)
  case isFalse hguard =>
  have hg : ¬ cvk.lagrangeBasis.size < pub.size ∧ ¬ cvk.n < pub.size := by
    simpa [not_or] using hguard
  rcases hvu : runVU C σ cvk cp pub with ⟨vv, uu⟩
  rw [hvu] at hv
  replace hv : runBody C σ cvk cp pub (runPubEvals C σ cvk cp pub) vv uu = true := hv
  have hv0 : vv = (runVU C σ cvk cp pub).1 := by rw [hvu]
  have hv1 : uu = (runVU C σ cvk cp pub).2 := by rw [hvu]
  subst hv0
  subst hv1
  exact ⟨Nat.le_of_not_lt hg.1, Nat.le_of_not_lt hg.2, hv⟩

end Kimchi.Verifier
