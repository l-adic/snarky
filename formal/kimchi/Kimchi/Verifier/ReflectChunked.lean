import Mathlib
import Kimchi.Verifier.Chunked

/-!
# Chunked kimchi verifier reflection: `Chunked.kimchiVerify = true` ⟹ a `ReflectedRun`

The trust-free reflection layer of the CHUNKED deployed verifier
(`Kimchi/Verifier/Chunked.lean`): every intermediate of `Chunked.kimchiVerify`'s body as
a named function of the wire data, and `kimchiVerify_reflects` reading `verify = true`
into the structured transcript — the guard shapes, the single warm-sponge IPA
acceptance of the run's own flat segment stream, and the stream's content as the
flat-map of the 45 LOGICAL rows (public, ft, `z`, six selectors, `w`, coefficients,
`σ[0..6)`), each row its chunk vector zipped with its per-chunk claims. Pure code-path
reading, no assumption. At `nc = 1` with no carried public evaluations, the verifier
computes the barycentric fallback inline (`publicEvals`); at `nc > 1` the carried
chunk vectors are adversarial batch data, believed only through binding.
-/

open Bulletproof

namespace Kimchi.Verifier.Chunked

open CompElliptic.CurveForms.ShortWeierstrass
open Poseidon Poseidon.FqSponge Bulletproof Kimchi.Index
open Kimchi.Protocol.Linearization Polynomial
open Kimchi.Verifier

variable (C : Ipa.CommitmentCurve)

/-! ## The run-derived data -/

/-- The run's chunk count, from the domain and SRS widths (production `chunk_size`). -/
def runNc (σ : SRS C.Point) (vk : KimchiVK C) : ℕ :=
  2 ^ (vk.domainLog2 - σ.k)

/-- The run's fq-sponge oracles: the deployed chunk-fold schedule at the run's own
per-chunk public commitment. -/
def runOracles (σ : SRS C.Point) (vk : KimchiVK C) (p : KimchiProof C)
    (pub : Array C.ScalarField) : FqOracles C :=
  fqOracles C vk p (publicCommitment C σ vk (runNc C σ vk) pub)

/-- The second batch point `ζω`. -/
def runZetaOmega (σ : SRS C.Point) (vk : KimchiVK C) (p : KimchiProof C)
    (pub : Array C.ScalarField) : C.ScalarField :=
  (runOracles C σ vk p pub).zeta * vk.omega

/-- The domain-size power `ζⁿ`, by the squaring ladder. -/
def runZetaN (σ : SRS C.Point) (vk : KimchiVK C) (p : KimchiProof C)
    (pub : Array C.ScalarField) : C.ScalarField :=
  powPow2 (runOracles C σ vk p pub).zeta vk.domainLog2

/-- The power `(ζω)ⁿ`, by the squaring ladder. -/
def runZetaOmegaN (σ : SRS C.Point) (vk : KimchiVK C) (p : KimchiProof C)
    (pub : Array C.ScalarField) : C.ScalarField :=
  powPow2 (runZetaOmega C σ vk p pub) vk.domainLog2

/-- The chunk-combination power `ζ^{2^σ.k}` (`ζ^max_poly_size`). -/
def runZetaM (σ : SRS C.Point) (vk : KimchiVK C) (p : KimchiProof C)
    (pub : Array C.ScalarField) : C.ScalarField :=
  powPow2 (runOracles C σ vk p pub).zeta σ.k

/-- The chunk-combination power `(ζω)^{2^σ.k}`. -/
def runZetaOmegaM (σ : SRS C.Point) (vk : KimchiVK C) (p : KimchiProof C)
    (pub : Array C.ScalarField) : C.ScalarField :=
  powPow2 (runZetaOmega C σ vk p pub) σ.k

/-- The run's public evaluation chunk vectors: proof-carried when present, the
one-chunk barycentric fallback otherwise (verifier.rs:332–379). -/
def runPubEvals (σ : SRS C.Point) (vk : KimchiVK C) (p : KimchiProof C)
    (pub : Array C.ScalarField) : Kimchi.Verifier.PointEvaluations (Array C.ScalarField) :=
  publicEvalChunks p vk.n vk.omega (runOracles C σ vk p pub).zeta
    (runZetaOmega C σ vk p pub) (runZetaN C σ vk p pub) (runZetaOmegaN C σ vk p pub) pub

/-- The run's chunk-combined public evaluation at `ζ` — `ft_eval0`'s public slot. -/
def runPubEval0 (σ : SRS C.Point) (vk : KimchiVK C) (p : KimchiProof C)
    (pub : Array C.ScalarField) : C.ScalarField :=
  combineAt (runZetaM C σ vk p pub) (runPubEvals C σ vk p pub).zeta

/-- The run's chunk-combined evaluation record — the verifier's `evals.combine`. -/
def runLinEvals (σ : SRS C.Point) (vk : KimchiVK C) (p : KimchiProof C)
    (pub : Array C.ScalarField) : Evals C.ScalarField :=
  p.linEvals (runZetaM C σ vk p pub) (runZetaOmegaM C σ vk p pub)

/-- The run's fr-sponge challenges `(v, u)` — polyscale and evalscale of the batch. -/
def runVU (σ : SRS C.Point) (vk : KimchiVK C) (p : KimchiProof C)
    (pub : Array C.ScalarField) : C.ScalarField × C.ScalarField :=
  frOracles C vk p (runOracles C σ vk p pub).digest (runPubEvals C σ vk p pub)

/-- The run's computed `ft(ζ)` claim at a given combined public evaluation. -/
def runFtEval0P (σ : SRS C.Point) (vk : KimchiVK C) (p : KimchiProof C)
    (pub : Array C.ScalarField) (pubEval0 : C.ScalarField) : C.ScalarField :=
  ftEval0 vk.n vk.zkRows vk.omega (fun i => vk.shifts[i.val]!) vk.endo
    (mdsOfParams vk.frParams)
    (runOracles C σ vk p pub).alpha (runOracles C σ vk p pub).beta
    (runOracles C σ vk p pub).gamma (runOracles C σ vk p pub).zeta pubEval0
    (runLinEvals C σ vk p pub)

/-- The run's computed `ft(ζ)` claim (closed form). -/
def runFtEval0 (σ : SRS C.Point) (vk : KimchiVK C) (p : KimchiProof C)
    (pub : Array C.ScalarField) : C.ScalarField :=
  runFtEval0P C σ vk p pub (runPubEval0 C σ vk p pub)

/-- The run's permutation scalar (the `f_comm` coefficient). -/
def runPScalar (σ : SRS C.Point) (vk : KimchiVK C) (p : KimchiProof C)
    (pub : Array C.ScalarField) : C.ScalarField :=
  permScalar (runOracles C σ vk p pub).beta (runOracles C σ vk p pub).gamma
    (runOracles C σ vk p pub).alpha
    (zkpmEval vk.n vk.zkRows vk.omega (runOracles C σ vk p pub).zeta)
    (runLinEvals C σ vk p pub)

/-- The run's `f_comm` chunks — the `pScalar`-scaled `σ₆` chunk vector. -/
def runFComm (σ : SRS C.Point) (vk : KimchiVK C) (p : KimchiProof C)
    (pub : Array C.ScalarField) : Array C.Point :=
  (vk.sigmaComm.getD 6 #[]).map (fun P => (runPScalar C σ vk p pub).val • P)

/-- The run's constructed ft commitment (verifier.rs:960–965): the DOUBLE collapse at
`ζ^{2^σ.k}` — `combine(ζ^max, f_comm) − (ζⁿ − 1)·combine(ζ^max, t_comm)`. -/
def runFtComm (σ : SRS C.Point) (vk : KimchiVK C) (p : KimchiProof C)
    (pub : Array C.ScalarField) : C.Point :=
  Ipa.combineCommitments C (runZetaM C σ vk p pub) (runFComm C σ vk p pub)
    - (runZetaN C σ vk p pub - 1).val
        • Ipa.combineCommitments C (runZetaM C σ vk p pub) p.tComm

/-- The run's 45 LOGICAL rows in `to_batch` order, at given public evaluation chunk
vectors: each row its chunk-vector commitment with the per-chunk claims at `(ζ, ζω)`
(the ft row single-chunk). -/
def runLogicalP (σ : SRS C.Point) (vk : KimchiVK C) (p : KimchiProof C)
    (pub : Array C.ScalarField) (pe : Kimchi.Verifier.PointEvaluations (Array C.ScalarField)) :
    Array (Array C.Point × Array C.ScalarField × Array C.ScalarField) :=
  #[(publicCommitment C σ vk (runNc C σ vk) pub, pe.zeta, pe.zetaOmega),
    (#[runFtComm C σ vk p pub],
      #[runFtEval0P C σ vk p pub (combineAt (runZetaM C σ vk p pub) pe.zeta)],
      #[p.ftEval1]),
    (p.zComm, p.evals.z.zeta, p.evals.z.zetaOmega),
    (vk.genericComm, p.evals.genericSelector.zeta, p.evals.genericSelector.zetaOmega),
    (vk.poseidonComm, p.evals.poseidonSelector.zeta, p.evals.poseidonSelector.zetaOmega),
    (vk.completeAddComm, p.evals.completeAddSelector.zeta,
      p.evals.completeAddSelector.zetaOmega),
    (vk.mulComm, p.evals.mulSelector.zeta, p.evals.mulSelector.zetaOmega),
    (vk.emulComm, p.evals.emulSelector.zeta, p.evals.emulSelector.zetaOmega),
    (vk.endomulScalarComm, p.evals.endomulScalarSelector.zeta,
      p.evals.endomulScalarSelector.zetaOmega)]
  ++ (p.wComm.zip p.evals.w).map (fun x => (x.1, x.2.zeta, x.2.zetaOmega))
  ++ (vk.coefficientsComm.zip p.evals.coefficients).map
      (fun x => (x.1, x.2.zeta, x.2.zetaOmega))
  ++ ((vk.sigmaComm.extract 0 6).zip p.evals.s).map
      (fun x => (x.1, x.2.zeta, x.2.zetaOmega))

/-- The 45 logical rows at the run's own public evaluations (closed form). -/
def runLogical (σ : SRS C.Point) (vk : KimchiVK C) (p : KimchiProof C)
    (pub : Array C.ScalarField) :
    Array (Array C.Point × Array C.ScalarField × Array C.ScalarField) :=
  runLogicalP C σ vk p pub (runPubEvals C σ vk p pub)

/-- The flat segment rows of a logical-row array — the `to_batch` stream: each logical
row's chunks zipped with its per-chunk claims, consecutively. -/
def flatRows (logical : Array (Array C.Point × Array C.ScalarField × Array C.ScalarField)) :
    Array (C.Point × C.ScalarField × C.ScalarField) :=
  logical.flatMap (fun r => (r.1.zip (r.2.1.zip r.2.2)).map (fun ce => (ce.1, ce.2.1, ce.2.2)))

/-- The batched IPA input at given public evaluations and combination scalars. -/
def runInputP (σ : SRS C.Point) (vk : KimchiVK C) (p : KimchiProof C)
    (pub : Array C.ScalarField) (pe : Kimchi.Verifier.PointEvaluations (Array C.ScalarField))
    (v u : C.ScalarField) : Ipa.Input C where
  commitments := (flatRows C (runLogicalP C σ vk p pub pe)).map (·.1)
  xs := #[(runOracles C σ vk p pub).zeta, runZetaOmega C σ vk p pub]
  evals := (flatRows C (runLogicalP C σ vk p pub pe)).map (fun r => #[r.2.1, r.2.2])
  polyscale := v
  evalscale := u
  proof := p.opening

/-- The acceptance decision at given public evaluations and combination scalars. -/
def runBody (σ : SRS C.Point) (vk : KimchiVK C) (p : KimchiProof C)
    (pub : Array C.ScalarField) (pe : Kimchi.Verifier.PointEvaluations (Array C.ScalarField))
    (v u : C.ScalarField) : Bool :=
  Ipa.verifyFrom C σ (runOracles C σ vk p pub).warm (runInputP C σ vk p pub pe v u)

/-- The batched IPA input the run hands to the warm-sponge opening finish (closed
form). -/
def runInput (σ : SRS C.Point) (vk : KimchiVK C) (p : KimchiProof C)
    (pub : Array C.ScalarField) : Ipa.Input C :=
  runInputP C σ vk p pub (runPubEvals C σ vk p pub)
    (runVU C σ vk p pub).1 (runVU C σ vk p pub).2

/-- The warm post-`ζ` sponge state the opening verification continues from. -/
def runWarm (σ : SRS C.Point) (vk : KimchiVK C) (p : KimchiProof C)
    (pub : Array C.ScalarField) : FqSponge.S C.base :=
  (runOracles C σ vk p pub).warm

/-! ## Reflection: the accepted run's own batch, read off the code path -/

/-- **The chunked reflected run** — what a `Chunked.kimchiVerify`-accepted run *is*,
read off the code path: the shape guard passes (`shapeBad = false` — ONE boolean fact;
individual shapes and chunk counts are read off it on demand by small extraction
lemmas), and the warm-sponge IPA finish accepts the run's own flat segment stream —
`runInput`'s commitment and claim columns are `flatRows (runLogical …)` projections BY
DEFINITION, so no separate content equalities are needed. This reflected run is the
premise the chunked `kimchi_fiat_shamir_*` axioms are stated over. -/
structure ReflectedRun (σ : SRS C.Point) (vk : KimchiVK C) (p : KimchiProof C)
    (pub : Array C.ScalarField) : Prop where
  /-- Every shape and chunk-count guard passes. -/
  shape : shapeBad C σ vk p pub = false
  /-- The warm-sponge opening finish accepts the run's own flat segment stream. -/
  accepts : Ipa.verifyFrom C σ (runWarm C σ vk p pub) (runInput C σ vk p pub) = true

/-- **Reflection**: an accepted chunked run yields its `ReflectedRun` — no trust, pure
code-path reading. The `replace` re-expresses `Chunked.kimchiVerify`'s body through the
named run functions (definitional: they mirror the body's `let`s; the one pair
destructuring, `(v, u) := frOracles …`, stays a match), so no sponge computation is
ever reduced. -/
theorem kimchiVerify_reflects (σ : SRS C.Point) (vk : KimchiVK C) (p : KimchiProof C)
    (pub : Array C.ScalarField) (hv : kimchiVerify C σ vk p pub = true) :
    ReflectedRun C σ vk p pub := by
  replace hv : (if shapeBad C σ vk p pub then
      false
    else
      match runVU C σ vk p pub with
      | (v, u) => runBody C σ vk p pub (runPubEvals C σ vk p pub) v u) = true := hv
  split at hv
  · exact absurd hv (by simp)
  · rename_i hguard
    rcases hvu : runVU C σ vk p pub with ⟨vv, uu⟩
    rw [hvu] at hv
    replace hv : runBody C σ vk p pub (runPubEvals C σ vk p pub) vv uu = true := hv
    have hv0 : vv = (runVU C σ vk p pub).1 := by rw [hvu]
    have hv1 : uu = (runVU C σ vk p pub).2 := by rw [hvu]
    subst hv0
    subst hv1
    exact ⟨Bool.of_not_eq_true hguard, hv⟩

end Kimchi.Verifier.Chunked
