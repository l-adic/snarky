import Bulletproof.Wire
import Kimchi.Protocol.Linearization
import Kimchi.Verifier.Reduction.Correspond
import Poseidon.FqSponge

/-!
# The kimchi verifier body over the checked records

The kimchi verifier transcribed from proof-systems `kimchi/src/verifier.rs`: the
Fiat-Shamir argument (`oracles`, :126–634) and the partial verification (`to_batch`,
:781–1194), finished by the batched IPA opening check at production chunking
(`chunk_size = d1 / max_poly_size`, any power-of-two `nc`; `nc = 1` is the one-chunk
case). The scalar-side closed forms are `Kimchi.Protocol.Linearization`
(`ftEval0`/`permScalar`/`zkpmEval`); the sponge layer is `Poseidon.FqSponge`, reused
at both fields; the opening finish is the `Bulletproof.Ipa` acceptance, restarted from
the **warm** fq-sponge state (`BatchEvaluationProof { sponge: fq_sponge, .. }`,
verifier.rs:1184–1193).

This module is the CHECKED side of the wire boundary (`Kimchi/Verifier/Wire.lean`):
the records here (`KimchiProof C nc`, `KimchiVK C nc`) carry the chunk count in their
types — they are exactly what `Wire.KimchiProof.check`/`Wire.KimchiVK.check` produce,
so uniformity is definitional, every read is total, and nothing above this module can
depend on unchecked data. The raw serde-typed wire records and the `check` parse live
in the `Wire` module, which deliberately holds no verifier: clients parse at the
run's chunk count and call `kimchiVerify` (this module) on the parsed records —
check-then-verify is the client's one-line composition. The protocol and soundness
layers never import `Wire`.

Scope (every deferral is declared here):

* no lookups (the wire records carry none) and no recursion (`prev_challenges`
  absent) — but the *constant* fr-sponge absorb of the empty recursion list's digest
  is transcribed (verifier.rs:290–299);
* the VK digest is an *input* (`KimchiVK.digest`); transcribing
  `VerifierIndex::digest()` (verifier_index.rs:399) is a declared deferral;
* `linearization.index_terms` is empty at the basic gate set, so `f_comm` is the
  single σ-commitment term (verifier.rs:897–956);
* `σ.k > domainLog2` — production's sub-SRS `chunk_size = 1` regime — is out of
  scope (the verifier rejects it);
* production's key carries the public-input count (`pub public: usize`,
  verifier_index.rs:71 — a serialized field) and `to_batch` rejects a mismatched
  argument outright (`public_input.len() != verifier_index.public`,
  verifier.rs:816–820, re-checked :835–838). The wire key here carries no count, so
  `kimchiVerify` substitutes the two bounds the body needs — the public input against
  the Lagrange table and against the domain — so the Lagrange MSM and the barycentric
  sums read only genuine entries. The exact-length pin is recovered at the soundness
  layer: the capstones fix `pub.size = idx.publicCount` through `pubView`.
-/

namespace Kimchi.Verifier

open CompElliptic.CurveForms.ShortWeierstrass
open Poseidon Poseidon.FqSponge Bulletproof

variable (C : Ipa.CommitmentCurve)

/-! ## The evaluation containers -/

/-- An evaluation pair at the two batch points — production's `PointEvaluations`
(`proof.rs`): the column at `ζ` and at `ζω`. -/
structure PointEvaluations (F : Type*) where
  zeta : F
  zetaOmega : F
deriving Inhabited

/-- The proof's claimed evaluations, one `PointEvaluations` per column family
(`ProofEvaluations`, proof.rs), generic in the per-point payload `E`: `Array F` on the
wire (chunk vectors of unchecked length), `Vector F nc` after `check`. The fixed
column counts (15 witness, 6 evaluated σ, 15 coefficient) are `[Evals; N]` in
production — serde-enforced, so type-level here. Optional gates and lookup data are
declared deferrals. -/
structure ProofEvaluations (E : Type*) where
  /-- The 15 witness-column evaluation pairs, `w[i] = (wᵢ(ζ), wᵢ(ζω))`. -/
  w : Vector (PointEvaluations E) wCols
  /-- The permutation-aggregation evaluation pair. -/
  z : PointEvaluations E
  /-- The first 6 σ-polynomial evaluation pairs (the 7th is commitment-only). -/
  s : Vector (PointEvaluations E) sigmaRows
  /-- The 15 coefficient-column evaluation pairs. -/
  coefficients : Vector (PointEvaluations E) coeffCols
  genericSelector : PointEvaluations E
  poseidonSelector : PointEvaluations E
  completeAddSelector : PointEvaluations E
  mulSelector : PointEvaluations E
  emulSelector : PointEvaluations E
  endomulScalarSelector : PointEvaluations E

/-! ## The checked records -/

/-- The public-evaluation source, resolving production's control flow
(verifier.rs:332–379): carried evaluations are accepted at any `nc` and REQUIRED at
`nc > 1`; the barycentric fallback exists only at `nc = 1` (it needs `ζ`, so it is
computed in the verifier body). -/
inductive PubEvalSrc (C : Ipa.CommitmentCurve) (nc : ℕ) where
  | carried (pe : PointEvaluations (Vector C.ScalarField nc))
  | barycentric (h : nc = 1)

/-- A chunk-validated proof at round count `k` (the SRS's `σ.k`): what
`KimchiProof.check nc k` returns, and the only thing the verifier body and the
soundness layer ever read. -/
structure KimchiProof (C : Ipa.CommitmentCurve) (nc k : ℕ) where
  wComm : Vector (Vector C.Point nc) wCols
  zComm : Vector C.Point nc
  /-- The quotient chunks: genuinely variable-length, so the bound is carried. -/
  tComm : Array C.Point
  tComm_le : tComm.size ≤ 7 * nc
  evals : ProofEvaluations (Vector C.ScalarField nc)
  pubEvals : PubEvalSrc C nc
  ftEval1 : C.ScalarField
  opening : Ipa.Proof C k

/-- A chunk-validated verifier key. -/
structure KimchiVK (C : Ipa.CommitmentCurve) (nc : ℕ) where
  domainLog2 : ℕ
  omega : C.ScalarField
  sigmaComm : Vector (Vector C.Point nc) permCols
  coefficientsComm : Vector (Vector C.Point nc) coeffCols
  genericComm : Vector C.Point nc
  poseidonComm : Vector C.Point nc
  completeAddComm : Vector C.Point nc
  mulComm : Vector C.Point nc
  emulComm : Vector C.Point nc
  endomulScalarComm : Vector C.Point nc
  shifts : Vector C.ScalarField permCols
  zkRows : ℕ
  endo : C.ScalarField
  digest : C.BaseField
  lagrangeBasis : Array (Vector C.Point nc)
  frParams : Params C.ScalarField

/-- The domain size of a checked key. -/
def KimchiVK.n {C : Ipa.CommitmentCurve} {nc : ℕ}
    (cvk : KimchiVK C nc) : ℕ := 2 ^ cvk.domainLog2

/-- The fr-sponge spec of a checked key. -/
private def KimchiVK.frSpec {C : Ipa.CommitmentCurve} {nc : ℕ}
    (cvk : KimchiVK C nc) : FqSponge.Spec C.scalar C.scalar :=
  ⟨cvk.frParams, 0⟩

/-- A Poseidon parameter table's MDS matrix as the gate's `Mds` record — the wire form
of production's `Constants { mds: G::sponge_params().mds, .. }` (the scalar-side table,
per curve). Consumed by the verifiers' `ftEval0` and pinned to `idx.mds` by the wire
correspondence. -/
def mdsOfParams {F : Type*} (p : Poseidon.Params F) : Gate.Poseidon.Mds F :=
  ⟨p.mds.1.1, p.mds.1.2.1, p.mds.1.2.2,
   p.mds.2.1.1, p.mds.2.1.2.1, p.mds.2.1.2.2,
   p.mds.2.2.1, p.mds.2.2.2.1, p.mds.2.2.2.2⟩

/-! ## The fr-sponge and the sponge digests -/

/-- The fr-sponge digest (`DefaultFrSponge::digest`, kimchi/src/plonk_sponge.rs): the
plain first squeeze — same field, no cast. -/
private def frDigest (sp : FqSponge.Spec C.scalar C.scalar) (s : FqSponge.S C.scalar) :
    C.ScalarField :=
  (challengeFq sp s).1

/-- The fq-sponge digest (`DefaultFqSponge::digest`, sponge.rs:388–397): squeeze one base
element and cast it to the scalar field by `from_bigint`, which returns **zero when the
value does not fit** — not a modular reduction. The state is consumed (production takes
`mut self`); the caller keeps its pre-digest copy. -/
private def fqDigest (s : FqSponge.S C.base) : C.ScalarField :=
  let (x, _) := challengeFq C.sponge s
  if x.val < C.scalar then ((x.val : ℕ) : C.ScalarField) else 0

/-! ## The oracle outputs and the public evaluations -/

/-- The fq-sponge outputs of `oracles` (verifier.rs:156–283): the challenges, the digest
handed to the fr-sponge, and the **warm** post-`ζ` sponge state that the opening
verification continues (verifier.rs:1184). -/
structure FqOracles (C : Ipa.CommitmentCurve) where
  beta : C.ScalarField
  gamma : C.ScalarField
  alpha : C.ScalarField
  zeta : C.ScalarField
  /-- `fq_sponge.clone().digest()` (verifier.rs:283). -/
  digest : C.ScalarField
  /-- The pre-digest sponge state, continued by the IPA finish. -/
  warm : FqSponge.S C.base

/-- `x ^ (2 ^ k)` by `k` squarings. The domain-size exponents `ζⁿ` (`n = 2 ^ domainLog2`)
would otherwise run through the linear `npowRec`, making `#eval` of the verifier
impractical at production domain sizes. -/
def powPow2 {F : Type*} [Field F] (x : F) (k : ℕ) : F :=
  (List.range k).foldl (fun a _ => a * a) x

/-- The shared summand of the two public evaluations (verifier.rs:338–375): over the
public inputs, `∑ᵢ −(pt − ωⁱ)⁻¹ · pubᵢ · ωⁱ`, by a running-`ω`-power fold.
`batch_inversion` (:346) is an optimization — per-element inversion is the same value. -/
private def pubDot {F : Type*} [Field F] (omega pt : F) (pub : Array F) : F :=
  (pub.foldl (fun (acc : F × F) pi =>
    (acc.1 + -(pt - acc.2)⁻¹ * pi * acc.2, acc.2 * omega)) (0, 1)).1

/-- The negated public evaluations at `ζ` and `ζω` (verifier.rs:332–379): `(0, 0)` for
empty input, else `(∑ᵢ −(ζ − ωⁱ)⁻¹ pubᵢ ωⁱ) · (ζⁿ − 1) · n⁻¹` and the `ζω` analogue.
These are the values production uses downstream (the public polynomial is committed
negated) — no re-negation. -/
def publicEvals {F : Type*} [Field F] (n : ℕ)
    (omega zeta zetaOmega zetaN zetaOmegaN : F) (pub : Array F) : F × F :=
  if pub.size = 0 then (0, 0)
  else
    (pubDot omega zeta pub * (zetaN - 1) * (n : F)⁻¹,
     pubDot omega zetaOmega pub * (n : F)⁻¹ * (zetaOmegaN - 1))

/-! ## The warm-sponge opening finish -/

/-- The IPA acceptance from a **warm** sponge state: production hands the post-`ζ`
fq-sponge to the opening verifier (`BatchEvaluationProof { sponge: fq_sponge, .. }`,
verifier.rs:1184–1193). The standalone `Bulletproof.Ipa.verify` (validated against the
opening fixtures) hard-codes the fresh `FqSponge.init` start, so this is a copy: the
verbatim body of `Ipa.transcript` + `Ipa.verify` with `FqSponge.init` replaced by
`s₀`. That verbatim correspondence is the invariant that keeps the copy in sync with
`Bulletproof.Ipa`, and the copy, like the rest of this module, is adjudicated against
production by the fixture drivers. The claim's shape is carried by its type, so there
are no runtime guards. -/
def Ipa.verifyFrom {m p : ℕ} (σ : SRS C.Point) (s₀ : FqSponge.S C.base)
    (inp : Ipa.Input C σ.k m p) : Bool :=
  let s := absorbFr C.sponge s₀ (Ipa.shiftScalar C (Ipa.cipOf inp))
  let (t, s) := challengeFq C.sponge s
  let uBase := C.toGroup t
  let (chals, s) := Ipa.roundChallenges C s inp.proof.lr
  let s := absorbG C.sponge s inp.proof.delta
  let (c, _) := squeezeChallenge C.sponge s
  let chal : Fin σ.k → C.ScalarField := fun i => chals[i]
  let b0 := combinedB chal inp.evalscale inp.pointFn
  let v := Ipa.cipOf inp
  let P := Ipa.combineCommitments C inp.polyscale inp.commitments.toArray
  let Q := (inp.proof.lr.toArray.zip chals.toArray).foldl
    (fun acc (LRu : (C.Point × C.Point) × C.ScalarField) =>
      acc + (LRu.2⁻¹.val • LRu.1.1 + LRu.2.val • LRu.1.2))
    (P + v.val • uBase)
  let schnorr := decide (c.val • Q + inp.proof.delta
    = inp.proof.z1.val • inp.proof.sg + (inp.proof.z1 * b0).val • uBase
        + inp.proof.z2.val • σ.h)
  let sgOk := decide (inp.proof.sg = Ipa.msm C σ.g (bPolyCoefficients chal))
  schnorr && sgOk

/-! ## The Fiat-Shamir schedules -/

/-- The fq-sponge schedule of `oracles` (verifier.rs:156–283): `absorb_commitment` is
chunk-wise `absorbG`, so the public-commitment and per-column absorbs are chunk
folds; the squeeze schedule is chunk-count-independent. -/
def fqOracles {nc k : ℕ} (cvk : KimchiVK C nc) (cp : KimchiProof C nc k)
    (publicComm : Vector C.Point nc) : FqOracles C :=
  let s := absorbFq C.sponge FqSponge.init [cvk.digest]
  let s := publicComm.foldl (absorbG C.sponge) s
  let s := cp.wComm.foldl (fun s col => col.foldl (absorbG C.sponge) s) s
  let (beta, s) := challenge C.sponge s
  let (gamma, s) := challenge C.sponge s
  let s := cp.zComm.foldl (absorbG C.sponge) s
  let (alpha, s) := squeezeChallenge C.sponge s
  let s := cp.tComm.foldl (absorbG C.sponge) s
  let (zeta, s) := squeezeChallenge C.sponge s
  ⟨beta, gamma, alpha, zeta, fqDigest C s, s⟩

/-- The fr-sponge schedule (verifier.rs:284–405): every absorb widened to the column's
chunk vector — the two public chunk vectors via `absorb_multiple` (:391–392), then per
column the `ζ`-chunk vector and the `ζω`-chunk vector (`absorb_evaluations`,
plonk_sponge.rs: one `sponge.absorb` per point vector), in the `absorb_evaluations`
order. -/
def frOracles {nc k : ℕ} (cvk : KimchiVK C nc) (cp : KimchiProof C nc k)
    (fqDig : C.ScalarField) (pubEvals : PointEvaluations (Vector C.ScalarField nc)) :
    C.ScalarField × C.ScalarField :=
  let sp := cvk.frSpec
  let ab := fun (s : FqSponge.S C.scalar)
      (e : PointEvaluations (Vector C.ScalarField nc)) =>
    absorbFq sp (absorbFq sp s e.zeta.toList) e.zetaOmega.toList
  let s := absorbFq sp FqSponge.init [fqDig]
  let s := absorbFq sp s [frDigest C sp FqSponge.init]
  let s := absorbFq sp s [cp.ftEval1]
  let s := absorbFq sp s pubEvals.zeta.toList
  let s := absorbFq sp s pubEvals.zetaOmega.toList
  let s := ab s cp.evals.z
  let s := ab s cp.evals.genericSelector
  let s := ab s cp.evals.poseidonSelector
  let s := ab s cp.evals.completeAddSelector
  let s := ab s cp.evals.mulSelector
  let s := ab s cp.evals.emulSelector
  let s := ab s cp.evals.endomulScalarSelector
  let s := cp.evals.w.foldl ab s
  let s := cp.evals.coefficients.foldl ab s
  let s := cp.evals.s.foldl ab s
  let (v', s) := challengeNat sp s
  let (u', _) := challengeNat sp s
  (endoExpand C.sponge.lam v', endoExpand C.sponge.lam u')

/-! ## The scalar side -/

/-- The chunk combination `∑ c, chunks[c] · xM ^ c` at `xM = pt^max_poly_size` — the
per-column body of `evals.combine` (`eval_polynomial(chunks, pt^max)`, proof.rs:537–542),
by a running-power fold. Identity on one-chunk vectors. -/
def combineAt {F : Type*} [Field F] (xM : F) (chunks : Array F) : F :=
  (chunks.foldl (fun (acc : F × F) c => (acc.1 + acc.2 * c, acc.2 * xM)) (0, 1)).1

/-- The public evaluation chunk vectors (verifier.rs:332–379): the proof-carried
`evals.public` when present (production prefers it at ANY `nc`); else the one-chunk
barycentric computation — the `nc = 1`-only branch, its `nc = 1` proof carried by the
`PubEvalSrc.barycentric` constructor. -/
def publicEvalChunks {C : Ipa.CommitmentCurve} {nc k : ℕ} (cp : KimchiProof C nc k)
    (n : ℕ) (omega zeta zetaOmega zetaN zetaOmegaN : C.ScalarField)
    (pub : Array C.ScalarField) : PointEvaluations (Vector C.ScalarField nc) :=
  match cp.pubEvals with
  | .carried pe => pe
  | .barycentric h =>
    let (e0, e1) := publicEvals n omega zeta zetaOmega zetaN zetaOmegaN pub
    ⟨⟨#[e0], by simp [h]⟩, ⟨#[e1], by simp [h]⟩⟩

/-- The proof's evaluations, chunk-combined, as the linearization's `Evals` record —
the verifier's `evals.combine(&powers_of_eval_points_for_chunks)` (verifier.rs:409):
every column combined at `ζ^max_poly_size` (`ζω`-side values at `(ζω)^max_poly_size`).
Every read is total off the checked record. -/
def KimchiProof.linEvals {C : Ipa.CommitmentCurve} {nc k : ℕ}
    (cp : KimchiProof C nc k) (zetaM zetaOmegaM : C.ScalarField) :
    Kimchi.Protocol.Linearization.Evals C.ScalarField where
  w i := combineAt zetaM (cp.evals.w[i]).zeta.toArray
  wOmega i := combineAt zetaOmegaM (cp.evals.w[i]).zetaOmega.toArray
  z := combineAt zetaM cp.evals.z.zeta.toArray
  zOmega := combineAt zetaOmegaM cp.evals.z.zetaOmega.toArray
  s i := combineAt zetaM (cp.evals.s[i]).zeta.toArray
  coeffs i := combineAt zetaM (cp.evals.coefficients[i]).zeta.toArray
  genericSelector := combineAt zetaM cp.evals.genericSelector.zeta.toArray
  poseidonSelector := combineAt zetaM cp.evals.poseidonSelector.zeta.toArray
  completeAddSelector := combineAt zetaM cp.evals.completeAddSelector.zeta.toArray
  mulSelector := combineAt zetaM cp.evals.mulSelector.zeta.toArray
  emulSelector := combineAt zetaM cp.evals.emulSelector.zeta.toArray
  endoScalarSelector := combineAt zetaM cp.evals.endomulScalarSelector.zeta.toArray

/-! ## The group side -/

/-- The public-input commitment, per chunk (verifier.rs:833–858): empty input gives
`nc` copies of the blinding commitment `srs.h` (:845); else chunk `c` is the MSM of the
`c`-chunks of the Lagrange-basis commitments against the negated public input
(`PolyComm::multi_scalar_mul` is chunk-wise, commitment.rs:348–378), plus `srs.h` from
the all-ones `mask_custom` blinder applied per chunk (:849–856; ipa.rs:497–514). Every
Lagrange chunk read is total off the checked key. -/
def publicCommitment {nc : ℕ} (σ : SRS C.Point) (cvk : KimchiVK C nc)
    (pub : Array C.ScalarField) : Vector C.Point nc :=
  if pub.size = 0 then Vector.replicate nc σ.h
  else
    Vector.ofFn (fun (c : Fin nc) =>
      ((cvk.lagrangeBasis.extract 0 pub.size).zip pub).foldl
        (fun acc Pp => acc + (-Pp.2).val • Pp.1[c]) 0
      + σ.h)

/-! ## The stream combinators -/

/-- Reading a flattened uniform block vector: block `q`, offset `r` sits at
`q·n + r`. The general read behind every tail-region access of the batch stream. -/
theorem flatten_read {α : Type*} {m n : ℕ} (v : Vector (Vector α n) m) (q r : ℕ)
    (hq : q < m) (hr : r < n) :
    v.flatten[q * n + r]'(by
      calc q * n + r < (q + 1) * n := by rw [Nat.succ_mul]; omega
        _ ≤ m * n := Nat.mul_le_mul_right n hq)
      = (v[q]'hq)[r]'hr := by
  have hdiv : (q * n + r) / n = q := by
    rw [Nat.mul_comm q n, Nat.mul_add_div (by omega : 0 < n), Nat.div_eq_of_lt hr]
    omega
  have hmod : (q * n + r) % n = r := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hr]
  rw [Vector.getElem_flatten]
  simp only [hdiv, hmod]

/-- One logical batch row's per-chunk segment triples: the chunk commitments zipped
with the per-chunk claims at `(ζ, ζω)`. -/
def zipSeg {nc : ℕ} (comm : Vector C.Point nc)
    (ev : PointEvaluations (Vector C.ScalarField nc)) :
    Vector (C.Point × C.ScalarField × C.ScalarField) nc :=
  Vector.ofFn fun c => (comm[c], ev.zeta[c], ev.zetaOmega[c])

/-- The 43 tail rows of the batch stream in `to_batch` order (`z`, the six selectors,
witness `0–14`, coefficients `0–14`, σ `0–5`), each row its per-chunk segments. -/
def tailRowsOf {nc k : ℕ} (cvk : KimchiVK C nc) (cp : KimchiProof C nc k) :
    Vector (Vector (C.Point × C.ScalarField × C.ScalarField) nc) tailRowCount :=
  (⟨#[zipSeg C cp.zComm cp.evals.z,
      zipSeg C cvk.genericComm cp.evals.genericSelector,
      zipSeg C cvk.poseidonComm cp.evals.poseidonSelector,
      zipSeg C cvk.completeAddComm cp.evals.completeAddSelector,
      zipSeg C cvk.mulComm cp.evals.mulSelector,
      zipSeg C cvk.emulComm cp.evals.emulSelector,
      zipSeg C cvk.endomulScalarComm cp.evals.endomulScalarSelector], rfl⟩
    : Vector _ litRowCount)
  ++ (cp.wComm.zip cp.evals.w).map (fun x => zipSeg C x.1 x.2)
  ++ (cvk.coefficientsComm.zip cp.evals.coefficients).map (fun x => zipSeg C x.1 x.2)
  ++ ((cvk.sigmaComm.take sigmaRows).zip cp.evals.s).map (fun x => zipSeg C x.1 x.2)

/-! ## The verifier -/

/-- **The verifier body over checked records** (`to_batch` + the opening check,
verifier.rs:781–1194, one proof, basic gate set): the two remaining argument-dependent
guards (the public input against the domain and the Lagrange table); the per-chunk
public commitment; the Fiat-Shamir schedules at chunk absorbs; the scalar side on
chunk-COMBINED evaluations; the `ft_comm` double collapse at `ζ^max_poly_size`
(:960–965); the 45 logical rows in `to_batch` order flattened to the SEGMENT stream
(one flat row per chunk, ft single — the per-chunk polyscale walk of
`combined_inner_product`/`combine_commitments`); the warm-sponge IPA finish. -/
def kimchiVerify {nc : ℕ} (σ : SRS C.Point) (cvk : KimchiVK C nc)
    (cp : KimchiProof C nc σ.k) (pub : Array C.ScalarField) : Bool :=
  let n := cvk.n
  -- Production's guard here is the exact count `public_input.len() != verifier_index.public`
  -- (verifier.rs:816–820); the wire key carries no count, so these two bounds
  -- substitute — a declared deviation (module preamble), closed at the soundness layer.
  if cvk.lagrangeBasis.size < pub.size || n < pub.size then
    false
  else
    let publicComm := publicCommitment C σ cvk pub
    let o := fqOracles C cvk cp publicComm
    let zetaOmega := o.zeta * cvk.omega
    let zetaN := powPow2 o.zeta cvk.domainLog2
    let zetaOmegaN := powPow2 zetaOmega cvk.domainLog2
    let zetaM := powPow2 o.zeta σ.k
    let zetaOmegaM := powPow2 zetaOmega σ.k
    let pubEvals := publicEvalChunks cp n cvk.omega o.zeta zetaOmega zetaN zetaOmegaN pub
    let pubEval0 := combineAt zetaM pubEvals.zeta.toArray
    let e := cp.linEvals zetaM zetaOmegaM
    let shifts : Fin permCols → C.ScalarField := fun i => cvk.shifts[i]
    let ftEval0 := Kimchi.Protocol.Linearization.ftEval0 n cvk.zkRows cvk.omega shifts
      cvk.endo (mdsOfParams cvk.frParams) o.alpha o.beta o.gamma o.zeta pubEval0 e
    let (v, u) := frOracles C cvk cp o.digest pubEvals
    let zkpmZ := Kimchi.Protocol.Linearization.zkpmEval n cvk.zkRows cvk.omega o.zeta
    let pScalar := Kimchi.Protocol.Linearization.permScalar o.beta o.gamma o.alpha zkpmZ e
    let fComm := cvk.sigmaComm[6].map (fun P => pScalar.val • P)
    let ftComm := Ipa.combineCommitments C zetaM fComm.toArray
      - (zetaN - 1).val • Ipa.combineCommitments C zetaM cp.tComm
    let stream : Vector (C.Point × C.ScalarField × C.ScalarField) (nc + 1 + tailRowCount * nc) :=
      (Vector.ofFn fun c : Fin nc =>
          (publicComm[c], pubEvals.zeta[c], pubEvals.zetaOmega[c]))
        ++ (⟨#[(ftComm, ftEval0, cp.ftEval1)], rfl⟩
            : Vector (C.Point × C.ScalarField × C.ScalarField) 1)
        ++ (tailRowsOf C cvk cp).flatten
    let inp : Ipa.Input C σ.k (nc + 1 + tailRowCount * nc) evalPts :=
      { commitments := stream.map (·.1)
        xs := ⟨#[o.zeta, zetaOmega], rfl⟩
        evals := stream.map (fun r => (⟨#[r.2.1, r.2.2], rfl⟩ : Vector _ evalPts))
        polyscale := v
        evalscale := u
        proof := cp.opening }
    Ipa.verifyFrom C σ o.warm inp

/-! ## The committed-column view -/

/-- The committed-column view of a checked verifier key: the `IndexComms` over
per-chunk carriers (`Fin nc → C.Point`) the reduction speaks about — every read
total. The glue between the checked wire and the abstract capstones. -/
def KimchiVK.comms {C : Ipa.CommitmentCurve} {nc : ℕ}
    (cvk : KimchiVK C nc) : Kimchi.Verifier.IndexComms (Fin nc → C.Point) where
  sigma i c := (cvk.sigmaComm[i])[c]
  coefficients cc c := (cvk.coefficientsComm[cc])[c]
  generic c := cvk.genericComm[c]
  poseidon c := cvk.poseidonComm[c]
  completeAdd c := cvk.completeAddComm[c]
  varBaseMul c := cvk.mulComm[c]
  endoMul c := cvk.emulComm[c]
  endoScalar c := cvk.endomulScalarComm[c]

/-- The public-input array as the `Fin idx.publicCount`-indexed function the circuit
model consumes (`getD`, total; the capstones pin `pub.size = idx.publicCount`, so the
view reads only genuine entries). The wire-to-abstract public view. -/
def pubView {F : Type*} [Field F] {n : ℕ} (idx : Index F n) (pub : Array F) :
    Fin idx.publicCount → F :=
  fun i => pub.getD (i : ℕ) 0

end Kimchi.Verifier
