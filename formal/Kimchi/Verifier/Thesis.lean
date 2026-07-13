import Kimchi.Verifier.Kimchi
import Kimchi.Verifier.Reflection
import Kimchi.Verifier.FtExtract

/-!
# The thesis (milestone 5): soundness of the deployed kimchi verifier

The project's final composition, per Pasta curve: a run accepted by the deployed executable
verifier (`kimchiVerify`, over wire data, all challenges derived by the Poseidon sponge),
under DL-binding and the verifier-key correspondence, forces a satisfying witness table for
the modeled circuit — `kimchiVesta_sound` / `kimchiPallas_sound`:

    KimchiVesta.verify σ vk p pub = true  +  DL-binding  +  VKCorresponds
      ⟹  ∃ wTab, Satisfies idx (pubView idx pub) wTab

**The trust story** (everything the roots assume, in one place):

* **DL-binding** stays a *hypothesis* (`hbind`, the no-DL-relation form): it is
  information-theoretically false at real parameters and meaningful only computationally
  (see `Commitment/IPA/Soundness/Batch.lean`). Nothing discharges it; the theorem is
  conditional on it, exactly as `ipaVesta_sound` is.
* **`VKCorresponds`** is a hypothesis discharged constructively for honest keys
  (`vkCorresponds_indexerOf`) and by the fixture MSM check for the production key
  (`Correspond.lean`); the wire key enters through the view `KimchiVK.comms`. Its
  scalar-side extension — the wire key's `omega`/`shifts`/`zkRows`/`endo` agree with the
  Index's — is carried as explicit hypotheses (`homega`/`hshifts`/`hzk`/`hendo`), the
  facts the Rust pipeline enforces by construction and never states.
* **Two independent Fiat-Shamir axioms per curve.** The kimchi-level axiom
  (`kimchi_fiat_shamir_vesta` / `kimchi_fiat_shamir_pallas`) hands back the *accumulated*
  transcript tree (`KimchiTreeAcc`): the challenge grids of the rewinding/forking
  extraction together with, per node, wire batch data and the deployed IPA acceptance
  (`Ipa.verify … = true`) — and **no `FiatShamirTreeB` content**. It packages the
  scalar-challenge rewinding, the random-oracle behaviour of the Poseidon sponge at the
  kimchi schedule, and the prefix-ordering of that schedule (each datum is committed
  before the challenges that follow it are squeezed). Each node's `FiatShamirTreeB`
  family — the batched-IPA extraction data — is then *derived* from the per-node IPA
  axiom (`poseidon_fiat_shamir_*`, `Reflection.lean`) by the bridges
  `kimchiTreeAcc_tree_{vesta,pallas}`, so the two assumptions are independent and both
  are genuinely invoked by the roots.
* **Everything else is proved.** The reflection section (`kimchiVerify_reflects`,
  `ReflectedRun`) is trust-free: it reads the accepted run's own batch off the code path —
  the 45-row layout, the sponge-derived challenges, the constructed ft commitment and the
  computed `ftEval0` claim. It is the **premise the Fiat-Shamir axiom is stated over**:
  `kimchiVerify_reflects` turns `verify = true` into a `ReflectedRun`, and each
  `kimchi_fiat_shamir_*` takes that reflected run as its hypothesis — so the axiom is
  anchored to the observed transcript, not a bare boolean, and the reflection is
  load-bearing rather than a side witness. `kimchiTree_sound` then closes by one
  application of `kimchiProof_sound_ft`, whose own closure is axiom-free.

The axiom closure of the roots is therefore: the three standard logical axioms, the
kimchi Fiat-Shamir axiom and the per-node IPA Fiat-Shamir axiom (one pair per curve),
and — through the Pasta point-group module instances
(`vestaPointModule`/`pallasPointModule`) — the Hasse-bound axioms and CompElliptic's
`native_decide` order witnesses. Verified by `scripts/check_axioms.lean`.

## Contents

* `KimchiVK.comms`, `pubView` — the wire-key → `IndexComms` and public-array views.
* `runOracles` … `runInput`, `runWarm` — the run-derived data: the deployed verifier's
  intermediate values as named functions of the wire data (definitional mirrors of
  `kimchiVerify`'s `let`s; the `…P` forms are parameterized by the pair-destructured
  values so the reflection never has to reduce a sponge computation). These are kept
  **flat** — each accessor calls `runOracles` rather than projecting a single shared
  `runData` bundle — on purpose: they are non-executed specification functions, and
  bundling the sponge output into one structure forces `kimchiVerify_reflects` to
  reduce that bundle, which overruns the recursion limit. The flat form keeps the
  reflection's definitional unfolding shallow (default `maxRecDepth`); the apparent
  non-sharing has no runtime cost because nothing evaluates them.
* `ReflectedRun`, `kimchiVerify_reflects` — the trust-free reflection (Move 1); the
  reflected run is the premise each `kimchi_fiat_shamir_*` axiom is stated over.
* `KimchiTree` — the transcript-tree bundle: exactly the hypothesis list of
  `kimchiProof_sound_ft` beyond binding and the key correspondence.
* `lagBasis_eval`, `barycentricPubEval`, `barycentricPubEval_eq` — the barycentric
  public evaluation (the deployed verifier's formula, in Index vocabulary) and its
  proved identity with the interpolant's value off the domain, so the accumulated
  bundle's `hftE` speaks the verifier's own value; `publicEvals_ofFn_eq` ties the
  `Finset.sum` form to the executable `publicEvals` fold.
* `KimchiTreeAcc`, `KimchiTreeAcc.nodeInput` — the accumulated bundle: `KimchiTree` with
  the per-node `FiatShamirTreeB` families replaced by wire batch data and deployed IPA
  acceptance, and the per-node wire input the IPA axiom is applied to.
* `kimchi_fiat_shamir_vesta` / `_pallas` — the declared assumption (Move 2), concluding
  `KimchiTreeAcc`.
* `kimchiTreeAcc_tree_vesta` / `_pallas` — the bridges: every node's transcript tree
  derived from `poseidon_fiat_shamir_*`.
* `kimchiTree_sound`, `kimchiVesta_sound`, `kimchiPallas_sound` — the composition and the
  two thesis roots (Move 3).
-/

namespace Kimchi.Verifier

open CompElliptic.CurveForms.ShortWeierstrass
open Kimchi.Sponge Kimchi.Sponge.FqSponge Kimchi.Commitment.IPA Kimchi.Index
open Kimchi.Verifier.Linearization Polynomial
open CompElliptic.Fields.Pasta

/-! ## The wire views -/

/-- The committed-column view of a wire verifier key: the `IndexComms` record the abstract
soundness layer speaks about, read off the key's arrays (`getD` at the checked sizes — the
shape guards of `kimchiVerify` pin `sigmaComm` to 7 and `coefficientsComm` to 15 entries).
This is the view function through which `VKCorresponds` is stated for a wire key. -/
def KimchiVK.comms {C : Ipa.CommitmentCurve} (vk : KimchiVK C) : IndexComms C.Point where
  sigma i := vk.sigmaComm.getD (i : ℕ) 0
  coefficients c := vk.coefficientsComm.getD (c : ℕ) 0
  generic := vk.genericComm
  poseidon := vk.poseidonComm
  completeAdd := vk.completeAddComm
  varBaseMul := vk.mulComm
  endoMul := vk.emulComm
  endoScalar := vk.endomulScalarComm

/-- The public-input array as the `Fin idx.publicCount`-indexed function the circuit model
consumes (`getD`, total; the thesis hypotheses pin `pub.size = idx.publicCount`). -/
def pubView {F : Type*} [Field F] {n : ℕ} (idx : Index F n) (pub : Array F) :
    Fin idx.publicCount → F :=
  fun i => pub.getD (i : ℕ) 0

/-! ## The run-derived data

The deployed verifier's intermediate values as named functions of the wire data — each a
definitional mirror of the corresponding `let` in `kimchiVerify`'s body, so the reflection
below is pure code-path reading. The values that the body binds by *destructuring* the
`publicEvals` and `frOracles` pairs enter the `…P` forms as parameters — the closed forms
apply them at the pairs' components — so no proof step ever needs to reduce a sponge
computation. -/

variable (C : Ipa.CommitmentCurve)

/-- The run's fq-sponge oracles: the deployed schedule at the run's own public commitment
(`fqOracles` at `publicCommitment` — verifier.rs:156–283). -/
def runOracles (σ : SRS C.Point) (vk : KimchiVK C) (p : KimchiProof C)
    (pub : Array C.ScalarField) : FqOracles C :=
  fqOracles C vk p (publicCommitment C σ vk pub)

/-- The second batch point `ζω`. -/
def runZetaOmega (σ : SRS C.Point) (vk : KimchiVK C) (p : KimchiProof C)
    (pub : Array C.ScalarField) : C.ScalarField :=
  (runOracles C σ vk p pub).zeta * vk.omega

/-- The domain-size power `ζⁿ`, by the verifier's squaring ladder (`powPow2`). -/
def runZetaN (σ : SRS C.Point) (vk : KimchiVK C) (p : KimchiProof C)
    (pub : Array C.ScalarField) : C.ScalarField :=
  powPow2 (runOracles C σ vk p pub).zeta vk.domainLog2

/-- The power `(ζω)ⁿ`, by the squaring ladder. -/
def runZetaOmegaN (σ : SRS C.Point) (vk : KimchiVK C) (p : KimchiProof C)
    (pub : Array C.ScalarField) : C.ScalarField :=
  powPow2 (runZetaOmega C σ vk p pub) vk.domainLog2

/-- The run's negated public evaluations at `(ζ, ζω)` (verifier.rs:332–379). -/
def runPubEvals (σ : SRS C.Point) (vk : KimchiVK C) (p : KimchiProof C)
    (pub : Array C.ScalarField) : C.ScalarField × C.ScalarField :=
  publicEvals vk.n vk.omega (runOracles C σ vk p pub).zeta (runZetaOmega C σ vk p pub)
    (runZetaN C σ vk p pub) (runZetaOmegaN C σ vk p pub) pub

/-- The run's fr-sponge challenges `(v, u)` — polyscale and evalscale of the batch. -/
def runVU (σ : SRS C.Point) (vk : KimchiVK C) (p : KimchiProof C)
    (pub : Array C.ScalarField) : C.ScalarField × C.ScalarField :=
  frOracles C vk p (runOracles C σ vk p pub).digest (runPubEvals C σ vk p pub).1
    (runPubEvals C σ vk p pub).2

/-- The run's computed `ft(ζ)` claim at a given public evaluation —
`Linearization.ftEval0` at the run's own challenges, shifts, and evaluation record
(verifier.rs:414–478). -/
def runFtEval0P (σ : SRS C.Point) (vk : KimchiVK C) (p : KimchiProof C)
    (pub : Array C.ScalarField) (pubEval0 : C.ScalarField) : C.ScalarField :=
  Linearization.ftEval0 vk.n vk.zkRows vk.omega (fun i => vk.shifts[i.val]!) vk.endo
    (runOracles C σ vk p pub).alpha (runOracles C σ vk p pub).beta
    (runOracles C σ vk p pub).gamma (runOracles C σ vk p pub).zeta pubEval0 p.evals

/-- The run's computed `ft(ζ)` claim (closed form). -/
def runFtEval0 (σ : SRS C.Point) (vk : KimchiVK C) (p : KimchiProof C)
    (pub : Array C.ScalarField) : C.ScalarField :=
  runFtEval0P C σ vk p pub (runPubEvals C σ vk p pub).1

/-- The run's permutation scalar (the `f_comm` coefficient, verifier.rs:897–956). -/
def runPScalar (σ : SRS C.Point) (vk : KimchiVK C) (p : KimchiProof C)
    (pub : Array C.ScalarField) : C.ScalarField :=
  Linearization.permScalar (runOracles C σ vk p pub).beta (runOracles C σ vk p pub).gamma
    (runOracles C σ vk p pub).alpha
    (Linearization.zkpmEval vk.n vk.zkRows vk.omega (runOracles C σ vk p pub).zeta)
    p.evals

/-- The run's `f_comm` — the single σ-commitment term at this gate set. -/
def runFComm (σ : SRS C.Point) (vk : KimchiVK C) (p : KimchiProof C)
    (pub : Array C.ScalarField) : C.Point :=
  (runPScalar C σ vk p pub).val • vk.sigmaComm.getD 6 0

/-- The run's constructed ft commitment (verifier.rs:960–965):
`f_comm − (ζⁿ − 1) · combine(ζⁿ, t_comm)`, in executable vocabulary — the same Maller
combination the tree bundle's `hftC` assumes at the grid, here read off the code path. -/
def runFtComm (σ : SRS C.Point) (vk : KimchiVK C) (p : KimchiProof C)
    (pub : Array C.ScalarField) : C.Point :=
  runFComm C σ vk p pub
    - (runZetaN C σ vk p pub - 1).val
        • Ipa.combineCommitments C (runZetaN C σ vk p pub) p.tComm

/-- The run's 45 evaluation rows in the `to_batch` order (verifier.rs:967–1071): public,
ft, `z`, the six selectors, `w[0..15]`, `coefficients[0..15]`, `sigma[0..6]` — at given
public evaluations. -/
def runRowsP (σ : SRS C.Point) (vk : KimchiVK C) (p : KimchiProof C)
    (pub : Array C.ScalarField) (pubEval0 pubEval1 : C.ScalarField) :
    Array (C.Point × C.ScalarField × C.ScalarField) :=
  #[(publicCommitment C σ vk pub, pubEval0, pubEval1),
    (runFtComm C σ vk p pub, runFtEval0P C σ vk p pub pubEval0, p.ftEval1),
    (p.zComm, p.z.zeta, p.z.zetaOmega),
    (vk.genericComm, p.genericSelector.zeta, p.genericSelector.zetaOmega),
    (vk.poseidonComm, p.poseidonSelector.zeta, p.poseidonSelector.zetaOmega),
    (vk.completeAddComm, p.completeAddSelector.zeta, p.completeAddSelector.zetaOmega),
    (vk.mulComm, p.mulSelector.zeta, p.mulSelector.zetaOmega),
    (vk.emulComm, p.emulSelector.zeta, p.emulSelector.zetaOmega),
    (vk.endomulScalarComm, p.endomulScalarSelector.zeta,
      p.endomulScalarSelector.zetaOmega)]
  ++ (p.wComm.zip p.w).map (fun x => (x.1, x.2.zeta, x.2.zetaOmega))
  ++ (vk.coefficientsComm.zip p.coefficients).map (fun x => (x.1, x.2.zeta, x.2.zetaOmega))
  ++ ((vk.sigmaComm.extract 0 6).zip p.s).map (fun x => (x.1, x.2.zeta, x.2.zetaOmega))

/-- The batched IPA input at given public evaluations and combination scalars. -/
def runInputP (σ : SRS C.Point) (vk : KimchiVK C) (p : KimchiProof C)
    (pub : Array C.ScalarField) (pubEval0 pubEval1 v u : C.ScalarField) :
    Ipa.Input C where
  commitments := (runRowsP C σ vk p pub pubEval0 pubEval1).map (fun x => x.1)
  xs := #[(runOracles C σ vk p pub).zeta, runZetaOmega C σ vk p pub]
  evals := (runRowsP C σ vk p pub pubEval0 pubEval1).map (fun r => #[r.2.1, r.2.2])
  polyscale := v
  evalscale := u
  proof := p.opening

/-- The acceptance decision at given public evaluations and combination scalars — the
warm-sponge IPA finish on the parameterized input. -/
def runBody (σ : SRS C.Point) (vk : KimchiVK C) (p : KimchiProof C)
    (pub : Array C.ScalarField) (pubEval0 pubEval1 v u : C.ScalarField) : Bool :=
  Ipa.verifyFrom C σ (runOracles C σ vk p pub).warm
    (runInputP C σ vk p pub pubEval0 pubEval1 v u)

/-- The batched IPA input the run hands to the warm-sponge opening finish (closed form):
the 45-row commitments and claims, the batch points `(ζ, ζω)`, and the fr-sponge scalars
`(v, u)`. -/
def runInput (σ : SRS C.Point) (vk : KimchiVK C) (p : KimchiProof C)
    (pub : Array C.ScalarField) : Ipa.Input C :=
  runInputP C σ vk p pub (runPubEvals C σ vk p pub).1 (runPubEvals C σ vk p pub).2
    (runVU C σ vk p pub).1 (runVU C σ vk p pub).2

/-- The warm post-`ζ` sponge state the opening verification continues from. -/
def runWarm (σ : SRS C.Point) (vk : KimchiVK C) (p : KimchiProof C)
    (pub : Array C.ScalarField) : FqSponge.S C.base :=
  (runOracles C σ vk p pub).warm

/-! ## Reflection (Move 1): the accepted run's own batch, read off the code path -/

/-- Fold a zip-row map to its commitment column: first projections give back the
commitment array. -/
private theorem zipRows_map_fst (A : Array C.Point) (B : Array (PointEval C.ScalarField))
    (h : A.size ≤ B.size) :
    ((A.zip B).map (fun x => (x.1, x.2.zeta, x.2.zetaOmega))).map (fun r => r.1) = A := by
  apply Array.ext'
  simp only [Array.toList_map, Array.toList_zip, List.map_map]
  exact List.map_fst_zip (by simpa using h)

/-- Fold a zip-row map to its claims column: the paired evaluations give back the
per-column `(at ζ, at ζω)` pairs. -/
private theorem zipRows_map_snd (A : Array C.Point) (B : Array (PointEval C.ScalarField))
    (h : B.size ≤ A.size) :
    ((A.zip B).map (fun x => (x.1, x.2.zeta, x.2.zetaOmega))).map
        (fun r => #[r.2.1, r.2.2])
      = B.map (fun e => #[e.zeta, e.zetaOmega]) := by
  apply Array.ext'
  simp only [Array.toList_map, Array.toList_zip, List.map_map]
  have hcomp : ((fun r : C.Point × C.ScalarField × C.ScalarField => #[r.2.1, r.2.2])
        ∘ fun x : C.Point × PointEval C.ScalarField => (x.1, x.2.zeta, x.2.zetaOmega))
      = (fun e : PointEval C.ScalarField => #[e.zeta, e.zetaOmega]) ∘ Prod.snd := rfl
  rw [hcomp, ← List.map_map, List.map_snd_zip (by simpa using h)]

/-- **The reflected run** (Move 1, trust-free): what a `kimchiVerify`-accepted run *is*,
read off the code path — the shape facts the guards enforce; acceptance of the run's own
45-row batch by the warm-sponge IPA finish; and the batch's content: the commitment
column is the public commitment, the constructed ft commitment (`runFtComm`, the
`f_comm − (ζⁿ−1)·combine(ζⁿ, t_comm)` combination), `z_comm`, the six selector
commitments, then exactly the proof's witness commitments, the key's coefficient
commitments, and the key's first six σ commitments; the claims column is the pair
`(computed ftEval0, p.ftEval1)` on the ft row and the proof's own wire evaluation pairs
on every column row (read by the abstract layer through `Input.evalFn`). The challenges
`(β, γ, α, ζ, v, u)` are the sponge-derived ones, named by `runOracles`/`runVU`. This
reflected run is the premise each `kimchi_fiat_shamir_*` axiom is stated over — the
axiom is anchored to the observed transcript, not a bare acceptance boolean. -/
structure ReflectedRun (σ : SRS C.Point) (vk : KimchiVK C) (p : KimchiProof C)
    (pub : Array C.ScalarField) : Prop where
  shape_wComm : p.wComm.size = 15
  shape_tComm : p.tComm.size = 7
  shape_w : p.w.size = 15
  shape_s : p.s.size = 6
  shape_coeffs : p.coefficients.size = 15
  shape_sigmaComm : vk.sigmaComm.size = 7
  shape_coeffsComm : vk.coefficientsComm.size = 15
  shape_shifts : vk.shifts.size = 7
  shape_lagrange : pub.size ≤ vk.lagrangeBasis.size
  shape_pub : pub.size ≤ vk.n
  shape_srs : 2 ^ σ.k = vk.n
  /-- The warm-sponge opening finish accepts the run's own batch. -/
  accepts : Ipa.verifyFrom C σ (runWarm C σ vk p pub) (runInput C σ vk p pub) = true
  /-- The commitment column: public, constructed ft, `z`, selectors, then the wire
  arrays themselves. -/
  comm_eq : (runInput C σ vk p pub).commitments
    = #[publicCommitment C σ vk pub, runFtComm C σ vk p pub, p.zComm, vk.genericComm,
        vk.poseidonComm, vk.completeAddComm, vk.mulComm, vk.emulComm,
        vk.endomulScalarComm]
      ++ p.wComm ++ vk.coefficientsComm ++ vk.sigmaComm.extract 0 6
  /-- The claims column: the computed public and ft claims, then the proof's own wire
  evaluation pairs. -/
  evals_eq : (runInput C σ vk p pub).evals
    = #[#[(runPubEvals C σ vk p pub).1, (runPubEvals C σ vk p pub).2],
        #[runFtEval0 C σ vk p pub, p.ftEval1],
        #[p.z.zeta, p.z.zetaOmega],
        #[p.genericSelector.zeta, p.genericSelector.zetaOmega],
        #[p.poseidonSelector.zeta, p.poseidonSelector.zetaOmega],
        #[p.completeAddSelector.zeta, p.completeAddSelector.zetaOmega],
        #[p.mulSelector.zeta, p.mulSelector.zetaOmega],
        #[p.emulSelector.zeta, p.emulSelector.zetaOmega],
        #[p.endomulScalarSelector.zeta, p.endomulScalarSelector.zetaOmega]]
      ++ p.w.map (fun e => #[e.zeta, e.zetaOmega])
      ++ p.coefficients.map (fun e => #[e.zeta, e.zetaOmega])
      ++ p.s.map (fun e => #[e.zeta, e.zetaOmega])

/-- **Reflection** (Move 1): an accepted run yields its `ReflectedRun` — no trust, pure
code-path reading. The one `replace` re-expresses `kimchiVerify`'s body through the named
run functions (definitional: the run functions mirror the body's `let`s, and the pair
destructurings stay as matches, so no sponge computation is ever reduced); the guards
give the shapes; the batch content follows from the zip-row folds at the checked
sizes. -/
theorem kimchiVerify_reflects (σ : SRS C.Point) (vk : KimchiVK C) (p : KimchiProof C)
    (pub : Array C.ScalarField) (hv : kimchiVerify C σ vk p pub = true) :
    ReflectedRun C σ vk p pub := by
  replace hv : (if p.wComm.size != 15 || p.tComm.size != 7 || p.w.size != 15
        || p.s.size != 6 || p.coefficients.size != 15 || vk.sigmaComm.size != 7
        || vk.coefficientsComm.size != 15 || vk.shifts.size != 7
        || decide (vk.lagrangeBasis.size < pub.size) || decide (vk.n < pub.size)
        || 2 ^ σ.k != vk.n then
      false
    else
      match runPubEvals C σ vk p pub with
      | (pubEval0, pubEval1) =>
        match frOracles C vk p (runOracles C σ vk p pub).digest pubEval0 pubEval1 with
        | (v, u) => runBody C σ vk p pub pubEval0 pubEval1 v u) = true := hv
  split at hv
  · exact absurd hv (by simp)
  · rename_i hguard
    simp only [Bool.not_eq_true, Bool.or_eq_false_iff, bne_eq_false_iff_eq,
      decide_eq_false_iff_not, Nat.not_lt] at hguard
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩ := hguard
    -- name the destructured pairs, then land on the closed forms
    rcases hpe : runPubEvals C σ vk p pub with ⟨pe0, pe1⟩
    rw [hpe] at hv
    replace hv : (match frOracles C vk p (runOracles C σ vk p pub).digest pe0 pe1 with
      | (v, u) => runBody C σ vk p pub pe0 pe1 v u) = true := hv
    rcases hvu : frOracles C vk p (runOracles C σ vk p pub).digest pe0 pe1 with ⟨vv, uu⟩
    rw [hvu] at hv
    replace hv : runBody C σ vk p pub pe0 pe1 vv uu = true := hv
    have hpe0 : pe0 = (runPubEvals C σ vk p pub).1 := by rw [hpe]
    have hpe1 : pe1 = (runPubEvals C σ vk p pub).2 := by rw [hpe]
    subst hpe0
    subst hpe1
    have hVU : runVU C σ vk p pub = (vv, uu) := hvu
    have hv0 : vv = (runVU C σ vk p pub).1 := by rw [hVU]
    have hv1 : uu = (runVU C σ vk p pub).2 := by rw [hVU]
    subst hv0
    subst hv1
    refine ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, hv, ?_, ?_⟩
    · show ((runRowsP C σ vk p pub (runPubEvals C σ vk p pub).1
          (runPubEvals C σ vk p pub).2).map (fun x => x.1)) = _
      unfold runRowsP
      simp only [Array.map_append]
      rw [zipRows_map_fst C _ _ (by omega), zipRows_map_fst C _ _ (by omega),
        zipRows_map_fst C _ _ (by rw [Array.size_extract]; omega)]
      simp only [List.map_toArray, List.map_cons, List.map_nil]
    · show ((runRowsP C σ vk p pub (runPubEvals C σ vk p pub).1
          (runPubEvals C σ vk p pub).2).map (fun r => #[r.2.1, r.2.2])) = _
      unfold runRowsP
      simp only [Array.map_append]
      rw [zipRows_map_snd C _ _ (by omega), zipRows_map_snd C _ _ (by omega),
        zipRows_map_snd C _ _ (by rw [Array.size_extract]; omega)]
      simp only [List.map_toArray, List.map_cons, List.map_nil]
      rfl

/-! ## The transcript-tree bundle (Move 2) -/

/-- **The kimchi transcript tree**: the full hypothesis bundle of `kimchiProof_sound_ft`
beyond DL-binding and the key correspondence — exactly what rewinding an accepted run
under a random-oracle sponge produces, packaged so the thesis is one unpacking plus one
application. Stated at the Index's own scalar data (`idx.omega`, `idx.zkRows`,
`idx.shifts`, `idx.endoBase`, `idx.pubPoly pub`); the Fiat-Shamir axioms below carry the
wire-key ↔ Index scalar compatibility as antecedents, so the bundle's content is honest.

Field groups, in `kimchiProof_sound_ft`'s order:

* `b`/`g`/`α`/`ζ` with their injectivity and size facts — the challenge grids over
  `(β, γ, α, ζ)`, the rewinding surrogate: `M`/`NN` exceed `7·(n − zkRows)`, `NNN`
  exceeds the aggregate degree bound, and every `ζ`-point avoids `1`, `ω^{n−zkRows}`,
  and the `n`-th roots of unity (`hζ₁`/`hζb`/`hζn`).
* `zC`/`E`/`ξ`/`r`/`A`/`hFS`/`hacc` — per grid node, the batch data of the 43-row
  assembly `batchC wC (zC a c) comms` with the **prefix-sharing shape**: the witness
  commitments `wC` are tree-wide (a parameter, pinned by the axiom to the run's own),
  the accumulator commitment `zC` varies only with `(β, γ)`, the claims `E` are the
  node's own; `hFS`/`hacc` are the per-node `FiatShamirTreeB` families and their
  acceptances — the batched-IPA extraction data `batch_soundnessA` consumes (at the
  Pasta instantiations these are derived from `poseidon_fiat_shamir_*` by the bridges
  below, not assumed).
* `TC`/`aft`/`ρft`/`hftC`/`hftE` — the ft-row data of the t extraction: the seven
  quotient-chunk commitments `TC`, `ζ`-free per `(β, γ, α)`-prefix (committed before
  `ζ` is sampled), and per node a bound ft witness committing to the verifier's
  `ftComm` combination (`hftC` — the Maller `permScalar·σ₆ − (ζⁿ−1)·∑ζⁿⁱ·TC` shape)
  whose value is the verifier's computed `ftEval0` (`hftE`, at the claimed record and
  the Index-side public polynomial).
* `q`/`hq` — per prefix, seven designated `ζ`-grid points with injective `ζⁿ`-values
  (the Vandermonde recovery points of `t_extraction`; their `ζⁿ ≠ 1` side comes from
  `hζn`). -/
structure KimchiTree {F G : Type*} [Field F] [AddCommGroup G] [Module F G]
    {n : ℕ} [NeZero n] (σ : SRS G) (idx : Index F n) (pub : Fin idx.publicCount → F)
    (comms : IndexComms G) (wC : Fin 15 → G) where
  M : ℕ
  NN : ℕ
  NNN : ℕ
  b : Fin M → F
  g : Fin NN → F
  hb : Function.Injective b
  hg : Function.Injective g
  hM : 7 * (n - idx.zkRows) < M
  hN : 7 * (n - idx.zkRows) < NN
  ζ : Fin M → Fin NN → Fin NNN → F
  hζ : ∀ a c, Function.Injective (ζ a c)
  hζ₁ : ∀ a c p, ζ a c p ≠ 1
  hζb : ∀ a c p, ζ a c p ≠ idx.omega ^ (n - idx.zkRows)
  hζn : ∀ a c p, (ζ a c p) ^ n ≠ 1
  α : Fin M → Fin NN → Fin (Index.gateAlphaCount + Index.permAlphaCount) → F
  hα : ∀ a c, Function.Injective (α a c)
  hD : Index.degreeBound n < NNN
  zC : Fin M → Fin NN → G
  E : Fin M → Fin NN → Fin (Index.gateAlphaCount + Index.permAlphaCount) → Fin NNN
    → Fin 43 → Fin 2 → F
  ξ : Fin M → Fin NN → Fin (Index.gateAlphaCount + Index.permAlphaCount) → Fin NNN
    → Fin 43 → F
  hξ : ∀ a c s p, Function.Injective (ξ a c s p)
  r : Fin M → Fin NN → Fin (Index.gateAlphaCount + Index.permAlphaCount) → Fin NNN
    → Fin 2 → F
  hr : ∀ a c s p, Function.Injective (r a c s p)
  A : Fin M → Fin NN → Fin (Index.gateAlphaCount + Index.permAlphaCount) → Fin NNN
    → Fin 43 → Fin 2 → Prop
  hFS : ∀ a c s p (i : Fin 43) (j : Fin 2),
    FiatShamirTreeB σ (combinedCommitment (ξ a c s p i) (batchC wC (zC a c) comms))
      (combinedEvalVector (2 ^ σ.k) (r a c s p j) ![ζ a c p, idx.omega * ζ a c p])
      (combinedInnerProduct (ξ a c s p i) (r a c s p j) (E a c s p))
      (A a c s p i j)
  hacc : ∀ a c s p i j, A a c s p i j
  TC : Fin M → Fin NN → Fin (Index.gateAlphaCount + Index.permAlphaCount) → Fin 7 → G
  aft : Fin M → Fin NN → Fin (Index.gateAlphaCount + Index.permAlphaCount) → Fin NNN
    → Fin (2 ^ σ.k) → F
  ρft : Fin M → Fin NN → Fin (Index.gateAlphaCount + Index.permAlphaCount) → Fin NNN
    → F
  hftC : ∀ a c s p, commit σ (aft a c s p) (ρft a c s p)
    = permScalar (b a) (g c) (α a c s) (zkpmEval n idx.zkRows idx.omega (ζ a c p))
          (claimedEvals (E a c s p))
        • comms.sigma 6
      - ((ζ a c p) ^ n - 1) • ∑ i : Fin 7, ((ζ a c p) ^ n) ^ (i : ℕ) • TC a c s i
  hftE : ∀ a c s p, innerProduct (aft a c s p) (evalVector (2 ^ σ.k) (ζ a c p))
    = ftEval0 n idx.zkRows idx.omega idx.shifts idx.endoBase (α a c s) (b a) (g c)
        (ζ a c p) (-((idx.pubPoly pub).eval (ζ a c p))) (claimedEvals (E a c s p))
  q : Fin M → Fin NN → Fin (Index.gateAlphaCount + Index.permAlphaCount) → Fin 7
    → Fin NNN
  hq : ∀ a c s, Function.Injective fun j => (ζ a c (q a c s j)) ^ n

/-! ## The generic composition -/

/-- **The tree closes the circuit**: a `KimchiTree`, DL-binding, and the key
correspondence force a satisfying witness table — one unpacking of the bundle plus one
application of `kimchiProof_sound_ft`. Generic over the module; the thesis roots
instantiate it at the Pasta point groups. -/
theorem kimchiTree_sound {F G : Type*} [Field F] [AddCommGroup G] [Module F G]
    {n : ℕ} [NeZero n] [DecidableEq F] (σ : SRS G)
    (idx : Index F n) (hk : 2 ^ σ.k = n)
    (hbind : ∀ (w : Fin (2 ^ σ.k) → F) (w_h : F), DLRelation σ w w_h → w = 0 ∧ w_h = 0)
    (comms : IndexComms G) (hvk : VKCorresponds σ comms idx)
    (pub : Fin idx.publicCount → F) (wC : Fin 15 → G)
    (T : KimchiTree σ idx pub comms wC) :
    ∃ wTab : Fin n → Fin 15 → F, Satisfies idx pub wTab :=
  kimchiProof_sound_ft σ idx hk hbind comms hvk pub T.b T.g T.hb T.hg T.hM T.hN
    T.ζ T.hζ T.hζ₁ T.hζb T.hζn T.α T.hα T.hD wC T.zC T.E T.ξ T.hξ T.r T.hr T.A T.hFS
    T.hacc T.TC T.aft T.ρft T.hftC T.hftE T.q T.hq

/-! ## The barycentric public evaluation

The deployed verifier computes the public evaluation at `ζ` by the barycentric formula
(`publicEvals`, verifier.rs:332–379), not by evaluating the public interpolant. The
accumulated bundle below states its `hftE` at that verifier-computed value
(`barycentricPubEval`), and the identity with the interpolant's value off the domain —
`barycentricPubEval idx ζ pub = −(idx.pubPoly pub).eval ζ` at `ζⁿ ≠ 1` — is **proved**
(`barycentricPubEval_eq`) and applied by the bridges, so the Fiat-Shamir axioms package
no algebraic content about the public column. -/

section Barycentric

open Kimchi.Quotient

/-- **The Lagrange basis off the domain**: for `ζ` with `ζⁿ ≠ 1`,
`Lⱼ(ζ) = ωʲ·(ζⁿ − 1) / (n·(ζ − ωʲ))` — the barycentric summand. Project-local: evaluates
the numerator identity `lagNumer_mul_sub` (`Quotient/Permutation.lean`) at `ζ` and clears
denominators (`ζ ≠ ωʲ` because `ζⁿ ≠ 1`; `(n : F) ≠ 0` from the primitive root). -/
theorem lagBasis_eval {F : Type*} [Field F] {n : ℕ} {ω ζ : F}
    (hω : IsPrimitiveRoot ω n) (hn : 0 < n) (hζn : ζ ^ n ≠ 1) (j : Fin n) :
    (columnPoly ω (Permutation.rowIndicator j)).eval ζ
      = ω ^ (j : ℕ) * (ζ ^ n - 1) / ((n : F) * (ζ - ω ^ (j : ℕ))) := by
  haveI : NeZero n := ⟨hn.ne'⟩
  have hnF : ((n : ℕ) : F) ≠ 0 := hω.neZero'.out
  have hωj : (ω : F) ^ (j : ℕ) ≠ 0 := pow_ne_zero _ (hω.ne_zero hn.ne')
  have hζω : ζ - ω ^ (j : ℕ) ≠ 0 := by
    rw [sub_ne_zero]
    intro hEq
    apply hζn
    rw [hEq, ← pow_mul, mul_comm, pow_mul, hω.pow_eq_one, one_pow]
  have h := congrArg (Polynomial.eval ζ) (Permutation.lagNumer_mul_sub hω hn j)
  simp only [Permutation.lagNumer, zH, eval_mul, eval_sub, eval_C, eval_X, eval_pow,
    eval_one] at h
  rw [eq_div_iff (mul_ne_zero hnF hζω)]
  field_simp at h
  linear_combination h

/-- **The barycentric public evaluation**: the `Finset.sum` form of the deployed
verifier's first `publicEvals` component (verifier.rs:332–379; the summand convention is
`pubDot`'s, `−(ζ − ωʲ)⁻¹ · pubⱼ · ωʲ`), in the Index vocabulary the tree bundle speaks
(`pub : Fin idx.publicCount → F`, no wire array). This is the value `KimchiTreeAcc.hftE`
is stated at. -/
noncomputable def barycentricPubEval {F : Type*} [Field F] {n : ℕ}
    (idx : Index F n) (ζ : F) (pub : Fin idx.publicCount → F) : F :=
  (∑ j : Fin idx.publicCount,
      -(ζ - idx.omega ^ (j : ℕ))⁻¹ * pub j * idx.omega ^ (j : ℕ))
    * (ζ ^ n - 1) * (n : F)⁻¹

/-- **Barycentric = interpolant off the domain** — the identity the Fiat-Shamir axioms
used to assume silently, now proved: at any `ζ` with `ζⁿ ≠ 1`,
`barycentricPubEval idx ζ pub = −(idx.pubPoly pub).eval ζ`. The interpolant expands over
the Lagrange basis (`columnPoly_eq_sum_indicator`); the `Fin n` sum collapses to the
public rows (`pubAt` vanishes beyond `publicCount ≤ n`, from `idx.public_le`); and
`lagBasis_eval` gives each term. The bridges apply this per node (at the grid's `hζn`)
to hand `KimchiTree` its interpolant-form `hftE`. -/
theorem barycentricPubEval_eq {F : Type*} [Field F] {n : ℕ} [NeZero n]
    (idx : Index F n) (pub : Fin idx.publicCount → F) {ζ : F} (hζn : ζ ^ n ≠ 1) :
    barycentricPubEval idx ζ pub = -((idx.pubPoly pub).eval ζ) := by
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hω := idx.omega_prim
  have hnF : ((n : ℕ) : F) ≠ 0 := hω.neZero'.out
  have hpc : idx.publicCount ≤ n := idx.public_le.trans (Nat.sub_le _ _)
  have hR : (idx.pubPoly pub).eval ζ
      = ∑ i ∈ Finset.range idx.publicCount,
          (if h : i < idx.publicCount then pub ⟨i, h⟩ else 0)
            * (idx.omega ^ i * (ζ ^ n - 1) / ((n : F) * (ζ - idx.omega ^ i))) := by
    rw [show idx.pubPoly pub = columnPoly idx.omega (pubAt idx pub) from rfl,
      columnPoly_eq_sum_indicator hω hn, eval_finsetSum]
    have hterm : ∀ j : Fin n,
        (pubAt idx pub j • columnPoly idx.omega (Permutation.rowIndicator j)).eval ζ
          = (if h : (j : ℕ) < idx.publicCount then pub ⟨(j : ℕ), h⟩ else 0)
              * (idx.omega ^ (j : ℕ) * (ζ ^ n - 1)
                  / ((n : F) * (ζ - idx.omega ^ (j : ℕ)))) := by
      intro j
      rw [eval_smul, smul_eq_mul, lagBasis_eval hω hn hζn j, pubAt]
    rw [Finset.sum_congr rfl fun j _ => hterm j,
      Fin.sum_univ_eq_sum_range (fun i => (if h : i < idx.publicCount then pub ⟨i, h⟩ else 0)
        * (idx.omega ^ i * (ζ ^ n - 1) / ((n : F) * (ζ - idx.omega ^ i)))) n]
    exact (Finset.sum_subset (Finset.range_subset_range.mpr hpc) (fun i _ hi => by
      rw [dif_neg (by simpa using hi), zero_mul])).symm
  rw [hR, ← Fin.sum_univ_eq_sum_range (fun i =>
      (if h : i < idx.publicCount then pub ⟨i, h⟩ else 0)
        * (idx.omega ^ i * (ζ ^ n - 1) / ((n : F) * (ζ - idx.omega ^ i))))
      idx.publicCount]
  unfold barycentricPubEval
  rw [Finset.sum_mul, Finset.sum_mul, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [dif_pos j.isLt]
  simp only [Fin.eta]
  have hζω : ζ - idx.omega ^ (j : ℕ) ≠ 0 := by
    rw [sub_ne_zero]
    intro hEq
    apply hζn
    rw [hEq, ← pow_mul, mul_comm, pow_mul, hω.pow_eq_one, one_pow]
  field_simp

/-- The `pubDot` fold, generalized: from state `(a, w)`, the running-`ω`-power fold
returns `a` plus the indexed barycentric dot at powers `w·ωⁱ`, next power `w·ω^len`
(the fold→indexed-sum pattern, list carrier with arbitrary start). -/
private theorem pubDot_foldl {F : Type*} [Field F] (ω pt : F) (l : List F) (a w : F) :
    l.foldl (fun (acc : F × F) pi =>
        (acc.1 + -(pt - acc.2)⁻¹ * pi * acc.2, acc.2 * ω)) (a, w)
      = (a + ∑ i : Fin l.length,
            -(pt - w * ω ^ (i : ℕ))⁻¹ * l.get i * (w * ω ^ (i : ℕ)),
          w * ω ^ l.length) := by
  induction l generalizing a w with
  | nil => simp
  | cons x xs ih =>
    rw [List.foldl_cons, ih]
    refine Prod.ext ?_ ?_
    · simp only [List.length_cons, Fin.sum_univ_succ, Fin.val_zero, pow_zero, mul_one,
        List.get_eq_getElem, Fin.val_succ, List.getElem_cons_zero, List.getElem_cons_succ]
      rw [_root_.add_assoc]
      congr 1
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [pow_succ]
      ring
    · simp only [List.length_cons, pow_succ]
      ring

/-- **The executable tie**: the deployed verifier's first `publicEvals` component *is*
`barycentricPubEval` at the Index view of the public array (`Array.ofFn`), with no
side condition — the empty-input `(0, 0)` branch matches the empty sum. Project-local:
grounds the accumulated bundle's `hftE` value in the code the verifier actually runs
(`pubDot`'s fold via `pubDot_foldl`). -/
theorem publicEvals_ofFn_eq {F : Type*} [Field F] {n : ℕ} (idx : Index F n) (ζ : F)
    (pub : Fin idx.publicCount → F) :
    (publicEvals n idx.omega ζ (idx.omega * ζ) (ζ ^ n) ((idx.omega * ζ) ^ n)
        (Array.ofFn pub)).1
      = barycentricPubEval idx ζ pub := by
  by_cases hpc : idx.publicCount = 0
  · haveI : IsEmpty (Fin idx.publicCount) := by rw [hpc]; exact Fin.isEmpty'
    rw [publicEvals, if_pos (by simp [hpc])]
    rw [barycentricPubEval, Finset.univ_eq_empty, Finset.sum_empty, zero_mul, zero_mul]
  replace hpc : 0 < idx.publicCount := Nat.pos_of_ne_zero hpc
  have hdot : pubDot idx.omega ζ (Array.ofFn pub)
      = ∑ j : Fin idx.publicCount,
          -(ζ - idx.omega ^ (j : ℕ))⁻¹ * pub j * idx.omega ^ (j : ℕ) := by
    unfold pubDot
    rw [← Array.foldl_toList, Array.toList_ofFn, pubDot_foldl]
    simp only [one_mul, _root_.zero_add]
    refine Fintype.sum_equiv (finCongr (List.length_ofFn)) _ _ fun i => ?_
    simp only [List.get_eq_getElem, List.getElem_ofFn, finCongr_apply, Fin.val_cast]
    rfl
  rw [publicEvals, if_neg (by simp [hpc.ne'])]
  rw [hdot, barycentricPubEval]

end Barycentric

/-! ## The accumulated tree: the axioms' slimmed content (Move 2) -/

/-- **The accumulated kimchi transcript tree** — the slimmed conclusion of the kimchi
Fiat-Shamir axioms: everything `KimchiTree` carries EXCEPT the per-node
`FiatShamirTreeB` families and their acceptance propositions `(A, hFS, hacc)`, which are
replaced by per-node *wire* data: an opaque commitment array per `(β, γ)` node related
row-by-row to the abstract 43-row assembly (`cs`/`hcsSize`/`hcs` — an opaque array plus
a relation hypothesis, never an `Array.ofFn` build), a wire evaluation matrix whose
entries are the abstract claims (`es`/`hes`), and per `(ξ, r)`-grid point an opening
proof with the deployed acceptance of the node's batched input at the eval points
`(ζ, ωζ)` (`prf`/`hacc` — `Ipa.verify … = true`, the executable verifier itself). The
Pasta bridges below derive each node's `FiatShamirTreeB` family from the per-node IPA
axiom (`poseidon_fiat_shamir_*`), so this bundle carries no Fiat-Shamir-tree content of
its own. Generic over the curve bundle `C` (`Ipa.verify C` is curve-generic); only the
bridges are Pasta-specific. All other fields are verbatim `KimchiTree`'s — see its
docstring for the field-group story — except `hftE`, stated here at the verifier's
*barycentric* public evaluation (`barycentricPubEval`, the value the deployed code
computes) rather than the interpolant's; the bridges convert by the proved identity
`barycentricPubEval_eq`. -/
structure KimchiTreeAcc [Module C.ScalarField C.Point] {n : ℕ} [NeZero n]
    (σ : SRS C.Point) (idx : Index C.ScalarField n)
    (pub : Fin idx.publicCount → C.ScalarField) (comms : IndexComms C.Point)
    (wC : Fin 15 → C.Point) where
  M : ℕ
  NN : ℕ
  NNN : ℕ
  b : Fin M → C.ScalarField
  g : Fin NN → C.ScalarField
  hb : Function.Injective b
  hg : Function.Injective g
  hM : 7 * (n - idx.zkRows) < M
  hN : 7 * (n - idx.zkRows) < NN
  ζ : Fin M → Fin NN → Fin NNN → C.ScalarField
  hζ : ∀ a c, Function.Injective (ζ a c)
  hζ₁ : ∀ a c p, ζ a c p ≠ 1
  hζb : ∀ a c p, ζ a c p ≠ idx.omega ^ (n - idx.zkRows)
  hζn : ∀ a c p, (ζ a c p) ^ n ≠ 1
  α : Fin M → Fin NN → Fin (Index.gateAlphaCount + Index.permAlphaCount) → C.ScalarField
  hα : ∀ a c, Function.Injective (α a c)
  hD : Index.degreeBound n < NNN
  zC : Fin M → Fin NN → C.Point
  E : Fin M → Fin NN → Fin (Index.gateAlphaCount + Index.permAlphaCount) → Fin NNN
    → Fin 43 → Fin 2 → C.ScalarField
  ξ : Fin M → Fin NN → Fin (Index.gateAlphaCount + Index.permAlphaCount) → Fin NNN
    → Fin 43 → C.ScalarField
  hξ : ∀ a c s p, Function.Injective (ξ a c s p)
  r : Fin M → Fin NN → Fin (Index.gateAlphaCount + Index.permAlphaCount) → Fin NNN
    → Fin 2 → C.ScalarField
  hr : ∀ a c s p, Function.Injective (r a c s p)
  /-- Per `(β, γ)` node, the wire commitment array of the rewound batch — opaque. -/
  cs : Fin M → Fin NN → Array C.Point
  /-- The wire commitment array has the 43 batch rows. -/
  hcsSize : ∀ a c, (cs a c).size = 43
  /-- Row-by-row, the wire array is the abstract assembly `batchC wC (zC a c) comms`. -/
  hcs : ∀ a c (i : Fin 43), (cs a c).getD (i : ℕ) 0 = batchC wC (zC a c) comms i
  /-- Per node, the wire evaluation matrix of the rewound batch — opaque. -/
  es : Fin M → Fin NN → Fin (Index.gateAlphaCount + Index.permAlphaCount) → Fin NNN
    → Array (Array C.ScalarField)
  /-- Entry-by-entry, the wire matrix carries the abstract claims `E`. -/
  hes : ∀ a c s p (i : Fin 43) (j : Fin 2),
    ((es a c s p)[(i : ℕ)]!)[(j : ℕ)]! = E a c s p i j
  /-- Per `(ξ, r)`-grid point, the node's IPA opening proof. -/
  prf : Fin M → Fin NN → Fin (Index.gateAlphaCount + Index.permAlphaCount) → Fin NNN
    → Fin 43 → Fin 2 → Ipa.Proof C
  /-- The deployed verifier accepts every node's batched input — the acceptance the
  bridges hand to the per-node IPA axiom. -/
  hacc : ∀ a c s p (i : Fin 43) (j : Fin 2),
    Ipa.verify C σ (Ipa.mkInput C (cs a c) #[ζ a c p, idx.omega * ζ a c p] (es a c s p)
      (ξ a c s p i) (r a c s p j) (prf a c s p i j)) = true
  TC : Fin M → Fin NN → Fin (Index.gateAlphaCount + Index.permAlphaCount) → Fin 7
    → C.Point
  aft : Fin M → Fin NN → Fin (Index.gateAlphaCount + Index.permAlphaCount) → Fin NNN
    → Fin (2 ^ σ.k) → C.ScalarField
  ρft : Fin M → Fin NN → Fin (Index.gateAlphaCount + Index.permAlphaCount) → Fin NNN
    → C.ScalarField
  hftC : ∀ a c s p, commit σ (aft a c s p) (ρft a c s p)
    = permScalar (b a) (g c) (α a c s) (zkpmEval n idx.zkRows idx.omega (ζ a c p))
          (claimedEvals (E a c s p))
        • comms.sigma 6
      - ((ζ a c p) ^ n - 1) • ∑ i : Fin 7, ((ζ a c p) ^ n) ^ (i : ℕ) • TC a c s i
  /-- The bound ft witness's value is the verifier's computed `ftEval0` — at the
  verifier's own *barycentric* public evaluation (`barycentricPubEval`); the bridges
  rewrite it to `KimchiTree`'s interpolant form by `barycentricPubEval_eq` at the
  node's `hζn`. -/
  hftE : ∀ a c s p, innerProduct (aft a c s p) (evalVector (2 ^ σ.k) (ζ a c p))
    = ftEval0 n idx.zkRows idx.omega idx.shifts idx.endoBase (α a c s) (b a) (g c)
        (ζ a c p) (barycentricPubEval idx (ζ a c p) pub) (claimedEvals (E a c s p))
  q : Fin M → Fin NN → Fin (Index.gateAlphaCount + Index.permAlphaCount) → Fin 7
    → Fin NNN
  hq : ∀ a c s, Function.Injective fun j => (ζ a c (q a c s j)) ^ n

/-! ## The per-node Fiat-Shamir derivation -/

/-- `combinedCommitment` congruence across an index-count equality: reindexing the
commitment family along `Fin.cast` preserves the polyscale combination. -/
private theorem combinedCommitment_reindex {F G : Type*} [Field F] [AddCommGroup G]
    [Module F G] (ξ : F) {n m : ℕ} (h : n = m) (Cn : Fin n → G) (Cm : Fin m → G)
    (hC : ∀ i : Fin n, Cn i = Cm (Fin.cast h i)) :
    combinedCommitment ξ Cn = combinedCommitment ξ Cm := by
  unfold combinedCommitment
  refine Fintype.sum_equiv (finCongr h) _ _ fun i => ?_
  simp only [finCongr_apply, Fin.val_cast]
  rw [hC i]

/-- `combinedInnerProduct` congruence across a first-index-count equality. -/
private theorem combinedInnerProduct_reindex {F : Type*} [Field F] (ξ r : F)
    {n n' m : ℕ} (h : n = n') (e : Fin n → Fin m → F) (e' : Fin n' → Fin m → F)
    (he : ∀ (i : Fin n) (j : Fin m), e i j = e' (Fin.cast h i) j) :
    combinedInnerProduct ξ r e = combinedInnerProduct ξ r e' := by
  unfold combinedInnerProduct
  refine Fintype.sum_equiv (finCongr h) _ _ fun i => ?_
  simp only [finCongr_apply, Fin.val_cast]
  refine congrArg (ξ ^ (i : ℕ) * ·) ?_
  exact Finset.sum_congr rfl fun j _ => by rw [he i j]

section TreeOfAcc

variable {C} [Module C.ScalarField C.Point] {n : ℕ} [NeZero n] {σ : SRS C.Point}
  {idx : Index C.ScalarField n} {pub : Fin idx.publicCount → C.ScalarField}
  {comms : IndexComms C.Point} {wC : Fin 15 → C.Point}

/-- The wire input of one accumulated-tree node: the node's opaque commitment array and
evaluation matrix, batched at the `(ξ, r)`-grid scalars over the node's two eval points
`(ζ, ωζ)`, with the node's opening proof. The accumulated `hacc` states the deployed
verifier accepts exactly this input; the bridges apply the per-node IPA axiom to it. -/
def KimchiTreeAcc.nodeInput (T : KimchiTreeAcc C σ idx pub comms wC)
    (a : Fin T.M) (c : Fin T.NN)
    (s : Fin (Index.gateAlphaCount + Index.permAlphaCount)) (p : Fin T.NNN)
    (i : Fin 43) (j : Fin 2) : Ipa.Input C :=
  Ipa.mkInput C (T.cs a c) #[T.ζ a c p, idx.omega * T.ζ a c p] (T.es a c s p)
    (T.ξ a c s p i) (T.r a c s p j) (T.prf a c s p i j)

/-- **Per-node Fiat-Shamir transport**: the IPA-axiom-shaped transcript-tree family at a
node's wire input (`hax`, defeq to `poseidon_fiat_shamir_*` at `nodeInput` — the `hcip`
move of `ipaVesta_sound`), re-expressed over the abstract batch data: the opaque
commitment array collapses to the 43-row assembly (`hcs`), the two wire eval points to
`![ζ, ωζ]`, and the wire combined inner product to the one over the abstract claims
(`hes`). Sub-terms stay opaque throughout — the acceptance proposition
`Ipa.verify … = true` is never reduced. -/
private theorem KimchiTreeAcc.nodeFS (T : KimchiTreeAcc C σ idx pub comms wC)
    (a : Fin T.M) (c : Fin T.NN)
    (s : Fin (Index.gateAlphaCount + Index.permAlphaCount)) (p : Fin T.NNN)
    (i : Fin 43) (j : Fin 2)
    (hax : FiatShamirTreeB σ
      (combinedCommitment (T.ξ a c s p i)
        (fun t : Fin (T.cs a c).size => (T.cs a c)[t]))
      (combinedEvalVector (2 ^ σ.k) (T.r a c s p j) (T.nodeInput a c s p i j).pointFn)
      (Ipa.cipOf (T.nodeInput a c s p i j))
      (Ipa.verify C σ (T.nodeInput a c s p i j) = true)) :
    FiatShamirTreeB σ
      (combinedCommitment (T.ξ a c s p i) (batchC wC (T.zC a c) comms))
      (combinedEvalVector (2 ^ σ.k) (T.r a c s p j)
        ![T.ζ a c p, idx.omega * T.ζ a c p])
      (combinedInnerProduct (T.ξ a c s p i) (T.r a c s p j) (T.E a c s p))
      (Ipa.verify C σ (T.nodeInput a c s p i j) = true) := by
  have hgetD : ∀ (m : ℕ) (hm : m < (T.cs a c).size),
      (T.cs a c).getD m 0 = (T.cs a c)[m] := by
    intro m hm
    simp [Array.getD, hm]
  -- the commitment column: the opaque wire array is the 43-row assembly
  have hP : combinedCommitment (T.ξ a c s p i)
        (fun t : Fin (T.cs a c).size => (T.cs a c)[t])
      = combinedCommitment (T.ξ a c s p i) (batchC wC (T.zC a c) comms) := by
    refine combinedCommitment_reindex _ (T.hcsSize a c) _ _ fun t => ?_
    have h1 := T.hcs a c (Fin.cast (T.hcsSize a c) t)
    simp only [Fin.val_cast] at h1
    rw [hgetD (t : ℕ) t.isLt] at h1
    exact h1
  -- the eval points: the wire two-point array is `![ζ, ωζ]`
  have hx : ∀ t : Fin 2, (T.nodeInput a c s p i j).pointFn t
      = ![T.ζ a c p, idx.omega * T.ζ a c p] t := by
    intro t
    fin_cases t <;> rfl
  have hb : combinedEvalVector (2 ^ σ.k) (T.r a c s p j)
        (T.nodeInput a c s p i j).pointFn
      = combinedEvalVector (2 ^ σ.k) (T.r a c s p j)
          ![T.ζ a c p, idx.omega * T.ζ a c p] :=
    congrArg (fun x : Fin 2 → C.ScalarField =>
      combinedEvalVector (2 ^ σ.k) (T.r a c s p j) x) (funext hx)
  -- the combined inner product: the wire matrix carries the abstract claims
  have hv : Ipa.cipOf (T.nodeInput a c s p i j)
      = combinedInnerProduct (T.ξ a c s p i) (T.r a c s p j) (T.E a c s p) := by
    show combinedInnerProduct (T.ξ a c s p i) (T.r a c s p j)
        (fun (t : Fin (T.cs a c).size) (u : Fin 2) =>
          ((T.es a c s p)[(t : ℕ)]!)[(u : ℕ)]!)
      = combinedInnerProduct (T.ξ a c s p i) (T.r a c s p j) (T.E a c s p)
    exact combinedInnerProduct_reindex _ _ (T.hcsSize a c) _ _
      fun t u => T.hes a c s p (Fin.cast (T.hcsSize a c) t) u
  rw [hP, hb, hv] at hax
  exact hax

end TreeOfAcc

/-- **The Vesta bridge (the Fiat-Shamir derivation)**: an accumulated tree yields the
full transcript tree. Every node's `FiatShamirTreeB` family is *derived* — not assumed —
from the per-node IPA axiom `poseidon_fiat_shamir_vesta` at the node's own wire input
(`nodeInput`), transported to the abstract batch data by `nodeFS`; the acceptance
propositions `A` are instantiated as the deployed per-node acceptances
`Ipa.verify … = true`, discharged by the accumulated `hacc`. This is where the thesis
genuinely invokes the IPA-level assumption. The ft value hypothesis is converted from
the accumulated barycentric form to `KimchiTree`'s interpolant form by
`barycentricPubEval_eq` at each node's `hζn`. -/
def kimchiTreeAcc_tree_vesta {n : ℕ} [NeZero n] {σ : SRS IpaVesta.Point}
    {idx : Index Fp n} {pub : Fin idx.publicCount → Fp}
    {comms : IndexComms IpaVesta.Point} {wC : Fin 15 → IpaVesta.Point}
    (T : KimchiTreeAcc IpaVesta.curve σ idx pub comms wC) :
    KimchiTree σ idx pub comms wC where
  M := T.M
  NN := T.NN
  NNN := T.NNN
  b := T.b
  g := T.g
  hb := T.hb
  hg := T.hg
  hM := T.hM
  hN := T.hN
  ζ := T.ζ
  hζ := T.hζ
  hζ₁ := T.hζ₁
  hζb := T.hζb
  hζn := T.hζn
  α := T.α
  hα := T.hα
  hD := T.hD
  zC := T.zC
  E := T.E
  ξ := T.ξ
  hξ := T.hξ
  r := T.r
  hr := T.hr
  A := fun a c s p i j => Ipa.verify IpaVesta.curve σ (T.nodeInput a c s p i j) = true
  hFS := fun a c s p i j =>
    T.nodeFS a c s p i j (poseidon_fiat_shamir_vesta σ (T.nodeInput a c s p i j))
  hacc := fun a c s p i j => T.hacc a c s p i j
  TC := T.TC
  aft := T.aft
  ρft := T.ρft
  hftC := T.hftC
  hftE := fun a c s p => by
    have h := T.hftE a c s p
    rwa [barycentricPubEval_eq idx pub (T.hζn a c p)] at h
  q := T.q
  hq := T.hq

/-- **The Pallas bridge.** The Pallas-side twin of `kimchiTreeAcc_tree_vesta`, deriving
every node's `FiatShamirTreeB` family from `poseidon_fiat_shamir_pallas`. -/
def kimchiTreeAcc_tree_pallas {n : ℕ} [NeZero n] {σ : SRS IpaPallas.Point}
    {idx : Index Fq n} {pub : Fin idx.publicCount → Fq}
    {comms : IndexComms IpaPallas.Point} {wC : Fin 15 → IpaPallas.Point}
    (T : KimchiTreeAcc IpaPallas.curve σ idx pub comms wC) :
    KimchiTree σ idx pub comms wC where
  M := T.M
  NN := T.NN
  NNN := T.NNN
  b := T.b
  g := T.g
  hb := T.hb
  hg := T.hg
  hM := T.hM
  hN := T.hN
  ζ := T.ζ
  hζ := T.hζ
  hζ₁ := T.hζ₁
  hζb := T.hζb
  hζn := T.hζn
  α := T.α
  hα := T.hα
  hD := T.hD
  zC := T.zC
  E := T.E
  ξ := T.ξ
  hξ := T.hξ
  r := T.r
  hr := T.hr
  A := fun a c s p i j => Ipa.verify IpaPallas.curve σ (T.nodeInput a c s p i j) = true
  hFS := fun a c s p i j =>
    T.nodeFS a c s p i j (poseidon_fiat_shamir_pallas σ (T.nodeInput a c s p i j))
  hacc := fun a c s p i j => T.hacc a c s p i j
  TC := T.TC
  aft := T.aft
  ρft := T.ρft
  hftC := T.hftC
  hftE := fun a c s p => by
    have h := T.hftE a c s p
    rwa [barycentricPubEval_eq idx pub (T.hζn a c p)] at h
  q := T.q
  hq := T.hq

/-! ## The Fiat-Shamir axioms (Move 2, Pasta) -/

/-- **AXIOM (Fiat-Shamir, kimchi, Vesta).** A run accepted by the deployed Vesta kimchi
verifier admits the *accumulated* transcript tree: `KimchiTreeAcc` at the run's own
data — the wire key's committed columns (`vk.comms`) and witness commitments
(prefix-sharing: the tree's `wC` is the run's own `w_comm`), against an Index whose
scalar data matches the wire key's (the `homega`/`hzk`/`hshifts`/`hendo`/`hpub`
antecedents; the domain-size pin `2^σ.k = n` is the run's own guard). It packages the
rewinding/forking extraction of the scalar challenges, the random-oracle behaviour of
the Poseidon sponge at the kimchi schedule, **and the prefix-ordering of that
schedule** — witness commitments are absorbed before `β/γ`, the accumulator before `α`,
the quotient chunks before `ζ` (so `TC` is `ζ`-free per prefix), and the opening
argument runs from the warm post-`ζ` state. It carries **no `FiatShamirTreeB`
content**: each rewound node comes with wire batch data and its deployed IPA acceptance
(`Ipa.verify … = true`) only; the node's transcript tree is derived from the
*independent* per-node IPA axiom (`poseidon_fiat_shamir_vesta`) by
`kimchiTreeAcc_tree_vesta`, so both assumptions appear in the thesis roots' closures.

Premise (not a bare boolean): the axiom is stated over `ReflectedRun` — the trust-free
reflection of the accepted run, produced by `kimchiVerify_reflects` from `verify = true`
and fed in by the thesis root. So the axiom is anchored to the observed transcript in the
verifier's own vocabulary (the 45-row batch, the constructed ft commitment, the computed
`ftEval0` claim): the reflection is load-bearing, and the rewinding the axiom posits
extends a run it is forced to be consistent with. The bundle's `hftE` is
stated at the verifier-computed *barycentric* public evaluation (`barycentricPubEval`);
its identity with the interpolant's value off the domain is a **proved lemma**
(`barycentricPubEval_eq`, at `ζⁿ ≠ 1`), applied by the bridge — no algebraic content
about the public column is packaged with the axiom. -/
axiom kimchi_fiat_shamir_vesta (σ : SRS IpaVesta.Point) (vk : KimchiVesta.VK)
    (p : KimchiVesta.Proof) (pub : Array Fp) {n : ℕ} [NeZero n] (idx : Index Fp n)
    (hk : 2 ^ σ.k = n)
    (homega : vk.omega = idx.omega)
    (hzk : vk.zkRows = idx.zkRows)
    (hshifts : ∀ i : Fin 7, vk.shifts.getD (i : ℕ) 0 = idx.shifts i)
    (hendo : vk.endo = idx.endoBase)
    (hpub : pub.size = idx.publicCount)
    (hrefl : ReflectedRun IpaVesta.curve σ vk p pub) :
    KimchiTreeAcc IpaVesta.curve σ idx (pubView idx pub) vk.comms
      (fun i => p.wComm.getD (i : ℕ) 0)

/-- **AXIOM (Fiat-Shamir, kimchi, Pallas).** The Pallas-side twin of
`kimchi_fiat_shamir_vesta` — see its docstring for the packaged content and the
boundary-choice notes; its nodes' transcript trees are likewise derived from the
independent `poseidon_fiat_shamir_pallas` by `kimchiTreeAcc_tree_pallas`. -/
axiom kimchi_fiat_shamir_pallas (σ : SRS IpaPallas.Point) (vk : KimchiPallas.VK)
    (p : KimchiPallas.Proof) (pub : Array Fq) {n : ℕ} [NeZero n] (idx : Index Fq n)
    (hk : 2 ^ σ.k = n)
    (homega : vk.omega = idx.omega)
    (hzk : vk.zkRows = idx.zkRows)
    (hshifts : ∀ i : Fin 7, vk.shifts.getD (i : ℕ) 0 = idx.shifts i)
    (hendo : vk.endo = idx.endoBase)
    (hpub : pub.size = idx.publicCount)
    (hrefl : ReflectedRun IpaPallas.curve σ vk p pub) :
    KimchiTreeAcc IpaPallas.curve σ idx (pubView idx pub) vk.comms
      (fun i => p.wComm.getD (i : ℕ) 0)

/-! ## The thesis (Move 3) -/

/-- **THE THESIS (Vesta): soundness of the deployed kimchi verifier.** A run accepted by
the deployed Vesta verifier — one proof, wire data, all challenges Poseidon-derived —
under the no-DL-relation binding hypothesis and the verifier-key correspondence (the
committed columns via `VKCorresponds` at the `vk.comms` view; the scalar data via the
explicit `homega`/`hzk`/`hshifts`/`hendo`/`hpub` hypotheses), forces a satisfying witness
table for the modeled circuit. Composes `kimchi_fiat_shamir_vesta` with the bridge
`kimchiTreeAcc_tree_vesta` — which derives every node's transcript tree from
`poseidon_fiat_shamir_vesta` — and `kimchiTree_sound`; see the module docstring for the
full trust story. -/
theorem kimchiVesta_sound (σ : SRS IpaVesta.Point) (vk : KimchiVesta.VK)
    (p : KimchiVesta.Proof) (pub : Array Fp) {n : ℕ} [NeZero n] (idx : Index Fp n)
    (hk : 2 ^ σ.k = n)
    (hvk : VKCorresponds σ vk.comms idx)
    (homega : vk.omega = idx.omega)
    (hzk : vk.zkRows = idx.zkRows)
    (hshifts : ∀ i : Fin 7, vk.shifts.getD (i : ℕ) 0 = idx.shifts i)
    (hendo : vk.endo = idx.endoBase)
    (hpub : pub.size = idx.publicCount)
    (hbind : ∀ (w : Fin (2 ^ σ.k) → Fp) (wh : Fp), DLRelation σ w wh → w = 0 ∧ wh = 0)
    (hacc : KimchiVesta.verify σ vk p pub = true) :
    ∃ wTab : Fin n → Fin 15 → Fp, Satisfies idx (pubView idx pub) wTab :=
  kimchiTree_sound σ idx hk hbind vk.comms hvk (pubView idx pub)
    (fun i => p.wComm.getD (i : ℕ) 0)
    (kimchiTreeAcc_tree_vesta
      (kimchi_fiat_shamir_vesta σ vk p pub idx hk homega hzk hshifts hendo hpub
        (kimchiVerify_reflects IpaVesta.curve σ vk p pub hacc)))

/-- **THE THESIS (Pallas).** The Pallas-side twin of `kimchiVesta_sound`. -/
theorem kimchiPallas_sound (σ : SRS IpaPallas.Point) (vk : KimchiPallas.VK)
    (p : KimchiPallas.Proof) (pub : Array Fq) {n : ℕ} [NeZero n] (idx : Index Fq n)
    (hk : 2 ^ σ.k = n)
    (hvk : VKCorresponds σ vk.comms idx)
    (homega : vk.omega = idx.omega)
    (hzk : vk.zkRows = idx.zkRows)
    (hshifts : ∀ i : Fin 7, vk.shifts.getD (i : ℕ) 0 = idx.shifts i)
    (hendo : vk.endo = idx.endoBase)
    (hpub : pub.size = idx.publicCount)
    (hbind : ∀ (w : Fin (2 ^ σ.k) → Fq) (wh : Fq), DLRelation σ w wh → w = 0 ∧ wh = 0)
    (hacc : KimchiPallas.verify σ vk p pub = true) :
    ∃ wTab : Fin n → Fin 15 → Fq, Satisfies idx (pubView idx pub) wTab :=
  kimchiTree_sound σ idx hk hbind vk.comms hvk (pubView idx pub)
    (fun i => p.wComm.getD (i : ℕ) 0)
    (kimchiTreeAcc_tree_pallas
      (kimchi_fiat_shamir_pallas σ vk p pub idx hk homega hzk hshifts hendo hpub
        (kimchiVerify_reflects IpaPallas.curve σ vk p pub hacc)))

end Kimchi.Verifier
