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
* **The ONE Fiat-Shamir axiom per curve** (`kimchi_fiat_shamir_vesta` /
  `kimchi_fiat_shamir_pallas`): an accepted run admits the full transcript tree
  (`KimchiTree`) that `kimchiProof_sound_ft` consumes. It packages the rewinding/forking
  extraction, the random-oracle behaviour of the Poseidon sponge, and the prefix-ordering
  of the sponge schedule (each datum is committed before the challenges that follow it are
  squeezed). It **subsumes the per-node IPA axiom**: the tree's `FiatShamirTreeB` families
  are part of the bundle, so the thesis does NOT additionally invoke
  `poseidon_fiat_shamir_*`.
* **Everything else is proved.** The reflection section (`kimchiVerify_reflects`,
  `ReflectedRun`) is trust-free: it reads the accepted run's own batch off the code path —
  the 45-row layout, the sponge-derived challenges, the constructed ft commitment and the
  computed `ftEval0` claim — and is the base-node consistency witness for the axiom's
  bundle (the tree's root is the run itself, with exactly this reflected data).
  `kimchiTree_sound` then closes by one application of `kimchiProof_sound_ft`, whose own
  closure is axiom-free.

The axiom closure of the roots is therefore: the three standard logical axioms, the one
kimchi Fiat-Shamir axiom, and — through the Pasta point-group module instances
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
* `ReflectedRun`, `kimchiVerify_reflects` — the trust-free reflection (Move 1).
* `powPow2_eq`, `runZetaN_eq`, `runFtComm_abstract` — the executable-to-abstract bridges
  (the squaring ladder is `ζ ^ n`; the ft combination in module vocabulary).
* `KimchiTree` — the transcript-tree bundle: exactly the hypothesis list of
  `kimchiProof_sound_ft` beyond binding and the key correspondence.
* `kimchi_fiat_shamir_vesta` / `_pallas` — the declared assumption (Move 2).
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
`f_comm − (ζⁿ − 1) · combine(ζⁿ, t_comm)`, executable vocabulary.
`runFtComm_abstract` restates it in the module vocabulary of the soundness layer. -/
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

/-! ## The squaring-ladder bridge -/

/-- The verifier's squaring ladder computes the `2^k`-th power. Project-local: `powPow2`
is this library's own executable power (`Kimchi/Verifier/Kimchi.lean`). -/
theorem powPow2_eq {F : Type*} [Field F] (x : F) (k : ℕ) : powPow2 x k = x ^ 2 ^ k := by
  induction k with
  | zero => simp [powPow2]
  | succ k ih =>
    unfold powPow2 at ih ⊢
    rw [List.range_succ, List.foldl_append, ih]
    simp only [List.foldl_cons, List.foldl_nil]
    rw [← pow_add]
    congr 1
    rw [pow_succ]
    omega

/-- The run's ladder value is the genuine domain-size power `ζ ^ n`. -/
theorem runZetaN_eq (σ : SRS C.Point) (vk : KimchiVK C) (p : KimchiProof C)
    (pub : Array C.ScalarField) :
    runZetaN C σ vk p pub = (runOracles C σ vk p pub).zeta ^ vk.n :=
  powPow2_eq _ _

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
`(β, γ, α, ζ, v, u)` are the sponge-derived ones, named by `runOracles`/`runVU`; the
scalar-action bridge to the module vocabulary is `runFtComm_abstract` below. This is the
base-node consistency witness for the Fiat-Shamir axiom's transcript tree. -/
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

section AbstractConstruction

variable {C}
variable [Module C.ScalarField C.Point]
  (hsmul : ∀ (z : C.ScalarField) (P : C.Point), z • P = z.val • P)

include hsmul in
/-- **The ft construction fact, module vocabulary** (Move 1's scalar-action bridge, the
`hsmul` pattern of `Reflection.lean`): the run's constructed ft commitment is
`pS • σ₆-commitment − (ζⁿ-ladder − 1) • ∑ᵢ (ζⁿ-ladder)ⁱ • t_commᵢ` — the exact shape of
the tree bundle's `hftC` at the wire key's `comms` view (`runZetaN_eq` supplies
`ladder = ζ ^ n`). -/
theorem runFtComm_abstract (σ : SRS C.Point) (vk : KimchiVK C) (p : KimchiProof C)
    (pub : Array C.ScalarField) (ht : p.tComm.size = 7) :
    runFtComm C σ vk p pub
      = runPScalar C σ vk p pub • vk.comms.sigma 6
        - (runZetaN C σ vk p pub - 1)
            • ∑ i : Fin 7, (runZetaN C σ vk p pub) ^ (i : ℕ) • p.tComm.getD (i : ℕ) 0 := by
  have hgetD : ∀ (j : ℕ) (h : j < p.tComm.size), p.tComm.getD j 0 = p.tComm[j] := by
    intro j h
    simp [Array.getD, h]
  have hsum : combinedCommitment (runZetaN C σ vk p pub)
        (fun i : Fin p.tComm.size => p.tComm[i])
      = ∑ i : Fin 7, (runZetaN C σ vk p pub) ^ (i : ℕ) • p.tComm.getD (i : ℕ) 0 := by
    refine Fintype.sum_equiv (finCongr ht) _ _ fun i => ?_
    simp only [finCongr_apply, Fin.val_cast, Fin.getElem_fin]
    rw [hgetD (i : ℕ) i.isLt]
  unfold runFtComm runFComm
  rw [combineCommitments_eq hsmul, hsum,
    ← hsmul (runPScalar C σ vk p pub) (vk.sigmaComm.getD 6 0),
    ← hsmul (runZetaN C σ vk p pub - 1)
      (∑ i : Fin 7, (runZetaN C σ vk p pub) ^ (i : ℕ) • p.tComm.getD (i : ℕ) 0)]
  rfl

end AbstractConstruction

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
  acceptances — the batched-IPA extraction data `batch_soundnessA` consumes (this is
  what subsumes the per-node IPA Fiat-Shamir axiom).
* `TC`/`aft`/`ρft`/`hftC`/`hftE` — the ft-row data of the t extraction: the seven
  quotient-chunk commitments `TC`, `ζ`-free per `(β, γ, α)`-prefix (committed before
  `ζ` is sampled), and per node a bound ft witness committing to the verifier's
  `ftComm` combination (`hftC` — the reflected `runFtComm_abstract` shape) whose value
  is the verifier's computed `ftEval0` (`hftE`, at the claimed record and the Index-side
  public polynomial).
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

/-! ## The Fiat-Shamir axioms (Move 2, Pasta) -/

/-- **AXIOM (Fiat-Shamir, kimchi, Vesta).** A run accepted by the deployed Vesta kimchi
verifier admits the full transcript tree: `KimchiTree` at the run's own data — the wire
key's committed columns (`vk.comms`) and witness commitments (prefix-sharing: the tree's
`wC` is the run's own `w_comm`), against an Index whose scalar data matches the wire
key's (the `homega`/`hzk`/`hshifts`/`hendo`/`hpub` antecedents; the domain-size pin
`2^σ.k = n` is the run's own guard). This is the project's sole non-standard assumption
at the kimchi level: it packages the rewinding/forking extraction, the random-oracle
behaviour of the Poseidon sponge, **and the prefix-ordering of the sponge schedule** —
witness commitments are absorbed before `β/γ`, the accumulator before `α`, the quotient
chunks before `ζ` (so `TC` is `ζ`-free per prefix), and the opening argument runs from
the warm post-`ζ` state. The tree's `FiatShamirTreeB` families are part of the bundle,
so this axiom **subsumes the per-node IPA axiom** (`poseidon_fiat_shamir_vesta`): the
thesis does not additionally invoke it.

Boundary choice (documented judgment call): the axiom is stated over *reflected abstract
data* — the `kimchiProof_sound_ft` hypothesis bundle — rather than over per-node wire
runs; the trust-free `kimchiVerify_reflects` (`ReflectedRun`, with `runFtComm_abstract`
and `runZetaN_eq`) exhibits the accepted run itself in exactly the bundle's vocabulary
(the 45-row batch, the constructed ft commitment, the computed `ftEval0` claim), which
is the base-node consistency of the tree. The bundle's `hftE` is stated at the
Index-side public polynomial `idx.pubPoly` — the identity between the verifier's
barycentric public evaluation and the interpolant's value off the domain is part of the
packaged content (an honest-transcript algebraic fact at `ζⁿ ≠ 1`). -/
axiom kimchi_fiat_shamir_vesta (σ : SRS IpaVesta.Point) (vk : KimchiVesta.VK)
    (p : KimchiVesta.Proof) (pub : Array Fp) {n : ℕ} [NeZero n] (idx : Index Fp n)
    (hk : 2 ^ σ.k = n)
    (homega : vk.omega = idx.omega)
    (hzk : vk.zkRows = idx.zkRows)
    (hshifts : ∀ i : Fin 7, vk.shifts.getD (i : ℕ) 0 = idx.shifts i)
    (hendo : vk.endo = idx.endoBase)
    (hpub : pub.size = idx.publicCount)
    (hacc : KimchiVesta.verify σ vk p pub = true) :
    KimchiTree σ idx (pubView idx pub) vk.comms (fun i => p.wComm.getD (i : ℕ) 0)

/-- **AXIOM (Fiat-Shamir, kimchi, Pallas).** The Pallas-side twin of
`kimchi_fiat_shamir_vesta` — see its docstring for the packaged content and the
boundary-choice notes; it likewise subsumes `poseidon_fiat_shamir_pallas`. -/
axiom kimchi_fiat_shamir_pallas (σ : SRS IpaPallas.Point) (vk : KimchiPallas.VK)
    (p : KimchiPallas.Proof) (pub : Array Fq) {n : ℕ} [NeZero n] (idx : Index Fq n)
    (hk : 2 ^ σ.k = n)
    (homega : vk.omega = idx.omega)
    (hzk : vk.zkRows = idx.zkRows)
    (hshifts : ∀ i : Fin 7, vk.shifts.getD (i : ℕ) 0 = idx.shifts i)
    (hendo : vk.endo = idx.endoBase)
    (hpub : pub.size = idx.publicCount)
    (hacc : KimchiPallas.verify σ vk p pub = true) :
    KimchiTree σ idx (pubView idx pub) vk.comms (fun i => p.wComm.getD (i : ℕ) 0)

/-! ## The thesis (Move 3) -/

/-- **THE THESIS (Vesta): soundness of the deployed kimchi verifier.** A run accepted by
the deployed Vesta verifier — one proof, wire data, all challenges Poseidon-derived —
under the no-DL-relation binding hypothesis and the verifier-key correspondence (the
committed columns via `VKCorresponds` at the `vk.comms` view; the scalar data via the
explicit `homega`/`hzk`/`hshifts`/`hendo`/`hpub` hypotheses), forces a satisfying witness
table for the modeled circuit. Composes `kimchi_fiat_shamir_vesta` (the sole
non-standard assumption) with `kimchiTree_sound`; see the module docstring for the full
trust story. -/
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
    (kimchi_fiat_shamir_vesta σ vk p pub idx hk homega hzk hshifts hendo hpub hacc)

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
    (kimchi_fiat_shamir_pallas σ vk p pub idx hk homega hzk hshifts hendo hpub hacc)

end Kimchi.Verifier
