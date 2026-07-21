import Mathlib
import Kimchi.Verifier.Kimchi
import Bulletproof.Reflection
import Kimchi.Verifier.Reduction.Correspond
import Kimchi.Protocol.Equation
import Kimchi.Permutation.Permutation

/-!
# Kimchi verifier reflection: `kimchiVerify = true` ⟹ a well-formed `ReflectedRun`

The trust-free reflection layer of the deployed kimchi verifier: reading the executable
verifier's code path (, over wire data) into the structured transcript the
abstract soundness layer speaks about. `kimchiVerify_reflects` turns `verify = true` into a
`ReflectedRun` (the batch commitment/eval correspondence and the single IPA acceptance) with
no assumption — pure code-path reading. `barycentricPubEval_eq` proves the barycentric
public-evaluation identity the verifier's  computes equals the interpolant
form.

These are grid-independent: they describe one accepted run. The challenge-grid extraction
and the composition to `Satisfies` live above this file (the Fiat-Shamir bridge + capstone).
-/

open Bulletproof

namespace Kimchi.Verifier

open CompElliptic.CurveForms.ShortWeierstrass
open Poseidon Poseidon.FqSponge Bulletproof Kimchi.Index
open Kimchi.Protocol.Linearization Polynomial
open CompElliptic.Fields.Pasta

open CompElliptic.Fields.Pasta

/-! ## The wire views -/

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
private def runZetaOmega (σ : SRS C.Point) (vk : KimchiVK C) (p : KimchiProof C)
    (pub : Array C.ScalarField) : C.ScalarField :=
  (runOracles C σ vk p pub).zeta * vk.omega

/-- The domain-size power `ζⁿ`, by the verifier's squaring ladder (`powPow2`). -/
def runZetaN (σ : SRS C.Point) (vk : KimchiVK C) (p : KimchiProof C)
    (pub : Array C.ScalarField) : C.ScalarField :=
  powPow2 (runOracles C σ vk p pub).zeta vk.domainLog2

/-- The power `(ζω)ⁿ`, by the squaring ladder. -/
private def runZetaOmegaN (σ : SRS C.Point) (vk : KimchiVK C) (p : KimchiProof C)
    (pub : Array C.ScalarField) : C.ScalarField :=
  powPow2 (runZetaOmega C σ vk p pub) vk.domainLog2

/-- The run's negated public evaluations at `(ζ, ζω)` (verifier.rs:332–379). -/
def runPubEvals (σ : SRS C.Point) (vk : KimchiVK C) (p : KimchiProof C)
    (pub : Array C.ScalarField) : C.ScalarField × C.ScalarField :=
  publicEvals vk.n vk.omega (runOracles C σ vk p pub).zeta (runZetaOmega C σ vk p pub)
    (runZetaN C σ vk p pub) (runZetaOmegaN C σ vk p pub) pub

/-- The run's fr-sponge challenges `(v, u)` — polyscale and evalscale of the batch. -/
private def runVU (σ : SRS C.Point) (vk : KimchiVK C) (p : KimchiProof C)
    (pub : Array C.ScalarField) : C.ScalarField × C.ScalarField :=
  frOracles C vk p (runOracles C σ vk p pub).digest (runPubEvals C σ vk p pub).1
    (runPubEvals C σ vk p pub).2

/-- The run's computed `ft(ζ)` claim at a given public evaluation —
`Linearization.ftEval0` at the run's own challenges, shifts, and evaluation record
(verifier.rs:414–478). -/
def runFtEval0P (σ : SRS C.Point) (vk : KimchiVK C) (p : KimchiProof C)
    (pub : Array C.ScalarField) (pubEval0 : C.ScalarField) : C.ScalarField :=
  ftEval0 vk.n vk.zkRows vk.omega (fun i => vk.shifts[i.val]!) vk.endo
    (runOracles C σ vk p pub).alpha (runOracles C σ vk p pub).beta
    (runOracles C σ vk p pub).gamma (runOracles C σ vk p pub).zeta pubEval0 p.linEvals

/-- The run's computed `ft(ζ)` claim (closed form). -/
def runFtEval0 (σ : SRS C.Point) (vk : KimchiVK C) (p : KimchiProof C)
    (pub : Array C.ScalarField) : C.ScalarField :=
  runFtEval0P C σ vk p pub (runPubEvals C σ vk p pub).1

/-- The run's permutation scalar (the `f_comm` coefficient, verifier.rs:897–956). -/
def runPScalar (σ : SRS C.Point) (vk : KimchiVK C) (p : KimchiProof C)
    (pub : Array C.ScalarField) : C.ScalarField :=
  permScalar (runOracles C σ vk p pub).beta (runOracles C σ vk p pub).gamma
    (runOracles C σ vk p pub).alpha
    (zkpmEval vk.n vk.zkRows vk.omega (runOracles C σ vk p pub).zeta)
    p.linEvals

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
private def runRowsP (σ : SRS C.Point) (vk : KimchiVK C) (p : KimchiProof C)
    (pub : Array C.ScalarField) (pubEval0 pubEval1 : C.ScalarField) :
    Array (C.Point × C.ScalarField × C.ScalarField) :=
  #[(publicCommitment C σ vk pub, pubEval0, pubEval1),
    (runFtComm C σ vk p pub, runFtEval0P C σ vk p pub pubEval0, p.ftEval1),
    (p.zComm, p.evals.z.zeta, p.evals.z.zetaOmega),
    (vk.genericComm, p.evals.genericSelector.zeta, p.evals.genericSelector.zetaOmega),
    (vk.poseidonComm, p.evals.poseidonSelector.zeta, p.evals.poseidonSelector.zetaOmega),
    (vk.completeAddComm, p.evals.completeAddSelector.zeta, p.evals.completeAddSelector.zetaOmega),
    (vk.mulComm, p.evals.mulSelector.zeta, p.evals.mulSelector.zetaOmega),
    (vk.emulComm, p.evals.emulSelector.zeta, p.evals.emulSelector.zetaOmega),
    (vk.endomulScalarComm, p.evals.endomulScalarSelector.zeta,
      p.evals.endomulScalarSelector.zetaOmega)]
  ++ (p.wComm.zip p.evals.w).map (fun x => (x.1, x.2.zeta, x.2.zetaOmega))
  ++ (vk.coefficientsComm.zip p.evals.coefficients).map (fun x => (x.1, x.2.zeta, x.2.zetaOmega))
  ++ ((vk.sigmaComm.extract 0 6).zip p.evals.s).map (fun x => (x.1, x.2.zeta, x.2.zetaOmega))

/-- The batched IPA input at given public evaluations and combination scalars. -/
private def runInputP (σ : SRS C.Point) (vk : KimchiVK C) (p : KimchiProof C)
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
private def runBody (σ : SRS C.Point) (vk : KimchiVK C) (p : KimchiProof C)
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
private theorem zipRows_map_fst (A : Array C.Point) (B : Array (PointEvaluations C.ScalarField))
    (h : A.size ≤ B.size) :
    ((A.zip B).map (fun x => (x.1, x.2.zeta, x.2.zetaOmega))).map (fun r => r.1) = A := by
  apply Array.ext'
  simp only [Array.toList_map, Array.toList_zip, List.map_map]
  exact List.map_fst_zip (by simpa using h)

/-- Fold a zip-row map to its claims column: the paired evaluations give back the
per-column `(at ζ, at ζω)` pairs. -/
private theorem zipRows_map_snd (A : Array C.Point) (B : Array (PointEvaluations C.ScalarField))
    (h : B.size ≤ A.size) :
    ((A.zip B).map (fun x => (x.1, x.2.zeta, x.2.zetaOmega))).map
        (fun r => #[r.2.1, r.2.2])
      = B.map (fun e => #[e.zeta, e.zetaOmega]) := by
  apply Array.ext'
  simp only [Array.toList_map, Array.toList_zip, List.map_map]
  have hcomp : ((fun r : C.Point × C.ScalarField × C.ScalarField => #[r.2.1, r.2.2])
        ∘ fun x : C.Point × PointEvaluations C.ScalarField => (x.1, x.2.zeta, x.2.zetaOmega))
      = (fun e : PointEvaluations C.ScalarField => #[e.zeta, e.zetaOmega]) ∘ Prod.snd := rfl
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
  shape_w : p.evals.w.size = 15
  shape_s : p.evals.s.size = 6
  shape_coeffs : p.evals.coefficients.size = 15
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
        #[p.evals.z.zeta, p.evals.z.zetaOmega],
        #[p.evals.genericSelector.zeta, p.evals.genericSelector.zetaOmega],
        #[p.evals.poseidonSelector.zeta, p.evals.poseidonSelector.zetaOmega],
        #[p.evals.completeAddSelector.zeta, p.evals.completeAddSelector.zetaOmega],
        #[p.evals.mulSelector.zeta, p.evals.mulSelector.zetaOmega],
        #[p.evals.emulSelector.zeta, p.evals.emulSelector.zetaOmega],
        #[p.evals.endomulScalarSelector.zeta, p.evals.endomulScalarSelector.zetaOmega]]
      ++ p.evals.w.map (fun e => #[e.zeta, e.zetaOmega])
      ++ p.evals.coefficients.map (fun e => #[e.zeta, e.zetaOmega])
      ++ p.evals.s.map (fun e => #[e.zeta, e.zetaOmega])

/-- **Reflection** (Move 1): an accepted run yields its `ReflectedRun` — no trust, pure
code-path reading. The one `replace` re-expresses `kimchiVerify`'s body through the named
run functions (definitional: the run functions mirror the body's `let`s, and the pair
destructurings stay as matches, so no sponge computation is ever reduced); the guards
give the shapes; the batch content follows from the zip-row folds at the checked
sizes. -/
theorem kimchiVerify_reflects (σ : SRS C.Point) (vk : KimchiVK C) (p : KimchiProof C)
    (pub : Array C.ScalarField) (hv : kimchiVerify C σ vk p pub = true) :
    ReflectedRun C σ vk p pub := by
  replace hv : (if p.wComm.size != 15 || p.tComm.size != 7 || p.evals.w.size != 15
        || p.evals.s.size != 6 || p.evals.coefficients.size != 15 || vk.sigmaComm.size != 7
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


section Barycentric

open Kimchi.Lift

/-- **The Lagrange basis off the domain**: for `ζ` with `ζⁿ ≠ 1`,
`Lⱼ(ζ) = ωʲ·(ζⁿ − 1) / (n·(ζ − ωʲ))` — the barycentric summand. Evaluates
the numerator identity `lagNumer_mul_sub` (`Quotient/Permutation.lean`) at `ζ` and clears
denominators (`ζ ≠ ωʲ` because `ζⁿ ≠ 1`; `(n : F) ≠ 0` from the primitive root). -/
private theorem lagBasis_eval {F : Type*} [Field F] {n : ℕ} {ω ζ : F}
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

/-- Interpolation is linear in the column: `columnPoly v = ∑ⱼ vⱼ • Lⱼ` with
`Lⱼ = columnPoly (rowIndicator j)` the Lagrange basis. Degree-`< n` agreement on the
domain: at node `i` the left side reads `vᵢ` and the right collapses to the `j = i`
term. -/
private theorem columnPoly_eq_sum_indicator {F : Type*} [Field F] {n : ℕ} {ω : F}
    (hω : IsPrimitiveRoot ω n) (hn : 0 < n) (v : Fin n → F) :
    columnPoly ω v
      = ∑ j : Fin n, v j • columnPoly ω (Permutation.rowIndicator j) := by
  have hd2 : (∑ j : Fin n, v j • columnPoly ω (Permutation.rowIndicator j)).degree
      < n := by
    apply lt_of_le_of_lt (degree_sum_le _ _)
    rw [Finset.sup_lt_iff (by exact_mod_cast WithBot.bot_lt_coe (n : ℕ))]
    exact fun j _ => lt_of_le_of_lt (degree_smul_le _ _) (degree_columnPoly_lt hω _)
  refine eq_of_eval_eq_on_domain hω hn (degree_columnPoly_lt hω _) hd2 ?_
  intro i hi
  rw [show ((ω : F) ^ i) = ω ^ ((⟨i, hi⟩ : Fin n) : ℕ) from rfl, eval_columnPoly hω,
    eval_finsetSum]
  rw [Finset.sum_eq_single (⟨i, hi⟩ : Fin n)]
  · rw [eval_smul, eval_columnPoly hω, Permutation.rowIndicator, if_pos rfl,
      smul_eq_mul, mul_one]
  · intro j _ hj
    rw [eval_smul, eval_columnPoly hω, Permutation.rowIndicator,
      if_neg (fun hEq => hj hEq.symm), smul_eq_mul, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

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

end Barycentric

end Kimchi.Verifier
