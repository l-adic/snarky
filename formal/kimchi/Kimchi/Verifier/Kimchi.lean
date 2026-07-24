import Bulletproof.Wire
import Kimchi.Protocol.Linearization
import Kimchi.Columns
import Poseidon.FqSponge
import Kimchi.Index.Basic

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
  /-- The evaluation at `ζ`. -/
  zeta : F
  /-- The evaluation at `ζω`. -/
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
  /-- The generic selector's evaluation pair. -/
  genericSelector : PointEvaluations E
  /-- The poseidon selector's evaluation pair. -/
  poseidonSelector : PointEvaluations E
  /-- The completeAdd selector's evaluation pair. -/
  completeAddSelector : PointEvaluations E
  /-- The varBaseMul selector's evaluation pair. -/
  mulSelector : PointEvaluations E
  /-- The endoMul selector's evaluation pair. -/
  emulSelector : PointEvaluations E
  /-- The endoScalar selector's evaluation pair. -/
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
  /-- The witness-column commitments (`w_comm`), one `nc`-chunk vector per column. -/
  wComm : Vector (Vector C.Point nc) wCols
  /-- The permutation-aggregation commitment (`z_comm`). -/
  zComm : Vector C.Point nc
  /-- The quotient chunks: genuinely variable-length, so the bound is carried. -/
  tComm : Array C.Point
  tComm_le : tComm.size ≤ 7 * nc
  /-- The claimed evaluations, per column family and per chunk. -/
  evals : ProofEvaluations (Vector C.ScalarField nc)
  /-- The public-evaluation source: carried pairs, or the barycentric fallback at `nc = 1`. -/
  pubEvals : PubEvalSrc C nc
  /-- `ft(ζω)` (Maller's optimization) — the ft row is single-chunk. -/
  ftEval1 : C.ScalarField
  /-- The batched IPA opening proof, at the SRS's round count `k`. -/
  opening : Ipa.Proof C k

/-- A chunk-validated verifier key. -/
structure KimchiVK (C : Ipa.CommitmentCurve) (nc : ℕ) where
  /-- The domain size exponent: `n = 2 ^ domainLog2`. -/
  domainLog2 : ℕ
  /-- The domain generator `ω` (`domain.group_gen`). -/
  omega : C.ScalarField
  /-- The permutation commitments (`sigma_comm`), one `nc`-chunk vector per σ column. -/
  sigmaComm : Vector (Vector C.Point nc) permCols
  /-- The coefficient-column commitments (`coefficients_comm`). -/
  coefficientsComm : Vector (Vector C.Point nc) coeffCols
  /-- The generic selector's commitment. -/
  genericComm : Vector C.Point nc
  /-- The poseidon selector's commitment. -/
  poseidonComm : Vector C.Point nc
  /-- The completeAdd selector's commitment. -/
  completeAddComm : Vector C.Point nc
  /-- The varBaseMul selector's commitment. -/
  mulComm : Vector C.Point nc
  /-- The endoMul selector's commitment. -/
  emulComm : Vector C.Point nc
  /-- The endoScalar selector's commitment. -/
  endomulScalarComm : Vector C.Point nc
  /-- The permutation coset shifts (`shift`). -/
  shifts : Vector C.ScalarField permCols
  /-- The number of zero-knowledge rows (`zk_rows`). -/
  zkRows : ℕ
  /-- `verifier_index.endo`, the `ft_eval0` endo coefficient. -/
  endo : C.ScalarField
  /-- The precomputed `VerifierIndex::digest()` — an input here. -/
  digest : C.BaseField
  /-- The Lagrange-basis commitments, chunk-validated in full — SRS-derived data
  (`get_lagrange_basis` computes them from the SRS), a model input like `digest`. -/
  lagrangeBasis : Array (Vector C.Point nc)

/-- The domain size of a checked key. -/
def KimchiVK.n {C : Ipa.CommitmentCurve} {nc : ℕ}
    (cvk : KimchiVK C nc) : ℕ := 2 ^ cvk.domainLog2

/-- The fr-sponge spec of a commitment curve: the curve's scalar-side Poseidon
parameters (`C.frParams`, production's `G::sponge_params()`) with `lam := 0` —
deliberately dead: the fr-sponge path never endo-expands through its own spec.
`frOracles` expands its two squeezed prechallenges at `C.sponge.lam` (the eigenvalue
lives on the fq-side spec), and `frDigest`'s `challengeFq`/`challengeNat` never read
`lam`, so the slot is unused and zeroed. -/
def frSpec (C : Ipa.CommitmentCurve) : FqSponge.Spec C.scalar C.scalar :=
  ⟨C.frParams, 0⟩

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
def frDigest (sp : FqSponge.Spec C.scalar C.scalar) (s : FqSponge.S C.scalar) :
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
  /-- The permutation argument's challenge `β`. -/
  beta : C.ScalarField
  /-- The permutation argument's challenge `γ`. -/
  gamma : C.ScalarField
  /-- The constraint-combination challenge `α`. -/
  alpha : C.ScalarField
  /-- The evaluation-point challenge `ζ`. -/
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
def frOracles {nc k : ℕ} (cp : KimchiProof C nc k)
    (fqDig : C.ScalarField) (pubEvals : PointEvaluations (Vector C.ScalarField nc)) :
    C.ScalarField × C.ScalarField :=
  let sp := frSpec C
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

/-- The literal single-column head block of the batch tail, in `to_batch` order: the
accumulator `z` and the six selectors — the `litRowCount` rows whose commitments are
single named record fields. The ONE place this vector literal is written; every read
of the head region goes through `tailRows_read_lit` below. -/
def litRowsOf {nc k : ℕ} (cvk : KimchiVK C nc) (cp : KimchiProof C nc k) :
    Vector (Vector (C.Point × C.ScalarField × C.ScalarField) nc) litRowCount :=
  ⟨#[zipSeg C cp.zComm cp.evals.z,
     zipSeg C cvk.genericComm cp.evals.genericSelector,
     zipSeg C cvk.poseidonComm cp.evals.poseidonSelector,
     zipSeg C cvk.completeAddComm cp.evals.completeAddSelector,
     zipSeg C cvk.mulComm cp.evals.mulSelector,
     zipSeg C cvk.emulComm cp.evals.emulSelector,
     zipSeg C cvk.endomulScalarComm cp.evals.endomulScalarSelector], rfl⟩

/-- The 43 tail rows of the batch stream in `to_batch` order (`z`, the six selectors,
witness `0–14`, coefficients `0–14`, σ `0–5`), each row its per-chunk segments. -/
def tailRowsOf {nc k : ℕ} (cvk : KimchiVK C nc) (cp : KimchiProof C nc k) :
    Vector (Vector (C.Point × C.ScalarField × C.ScalarField) nc) tailRowCount :=
  litRowsOf C cvk cp
  ++ (cp.wComm.zip cp.evals.w).map (fun x => zipSeg C x.1 x.2)
  ++ (cvk.coefficientsComm.zip cp.evals.coefficients).map (fun x => zipSeg C x.1 x.2)
  ++ ((cvk.sigmaComm.take sigmaRows).zip cp.evals.s).map (fun x => zipSeg C x.1 x.2)

/-! ### The tail-region reads

The four append regions of `tailRowsOf`, read off by `Vector.getElem_append` dispatch —
stated here, next to the definition, so its region layout is written exactly once. The
reflection layer (`Capstone/Reflection.lean`) consumes these for every stream read. -/

section TailReads

variable {nc k : ℕ} {cvk : KimchiVK C nc} {cp : KimchiProof C nc k}

/-- Tail row `j < 7` is the `j`-th literal row (`z` + the six selectors). -/
theorem tailRows_read_lit (j : ℕ) (hj : j < litRowCount) :
    (tailRowsOf C cvk cp)[j]'(by omega) = (litRowsOf C cvk cp)[j]'hj := by
  show (litRowsOf C cvk cp
      ++ (cp.wComm.zip cp.evals.w).map (fun x => zipSeg C x.1 x.2)
      ++ (cvk.coefficientsComm.zip cp.evals.coefficients).map (fun x => zipSeg C x.1 x.2)
      ++ ((cvk.sigmaComm.take sigmaRows).zip cp.evals.s).map
        (fun x => zipSeg C x.1 x.2))[j]'(by omega) = _
  rw [Vector.getElem_append, dif_pos (by omega), Vector.getElem_append,
    dif_pos (by omega), Vector.getElem_append, dif_pos hj]

/-- Tail row `7 + q` is witness column `q`'s row. -/
theorem tailRows_read_w (q : ℕ) (hq : q < wCols) :
    (tailRowsOf C cvk cp)[7 + q]'(by omega)
      = zipSeg C (cp.wComm[q]'hq) (cp.evals.w[q]'hq) := by
  show (litRowsOf C cvk cp
      ++ (cp.wComm.zip cp.evals.w).map (fun x => zipSeg C x.1 x.2)
      ++ (cvk.coefficientsComm.zip cp.evals.coefficients).map (fun x => zipSeg C x.1 x.2)
      ++ ((cvk.sigmaComm.take sigmaRows).zip cp.evals.s).map
        (fun x => zipSeg C x.1 x.2))[7 + q]'(by omega) = _
  rw [Vector.getElem_append, dif_pos (by omega), Vector.getElem_append,
    dif_pos (by omega), Vector.getElem_append, dif_neg (by omega)]
  simp only [show 7 + q - 7 = q from by omega, Vector.getElem_map, Vector.getElem_zip]

/-- Tail row `22 + q` is coefficient column `q`'s row. -/
theorem tailRows_read_c (q : ℕ) (hq : q < coeffCols) :
    (tailRowsOf C cvk cp)[22 + q]'(by omega)
      = zipSeg C (cvk.coefficientsComm[q]'hq) (cp.evals.coefficients[q]'hq) := by
  show (litRowsOf C cvk cp
      ++ (cp.wComm.zip cp.evals.w).map (fun x => zipSeg C x.1 x.2)
      ++ (cvk.coefficientsComm.zip cp.evals.coefficients).map (fun x => zipSeg C x.1 x.2)
      ++ ((cvk.sigmaComm.take sigmaRows).zip cp.evals.s).map
        (fun x => zipSeg C x.1 x.2))[22 + q]'(by omega) = _
  rw [Vector.getElem_append, dif_pos (by omega), Vector.getElem_append,
    dif_neg (by omega)]
  simp only [show 22 + q - (7 + 15) = q from by omega, Vector.getElem_map,
    Vector.getElem_zip]

/-- Tail row `37 + q` is the `q`-th σ row. -/
theorem tailRows_read_s (q : ℕ) (hq : q < sigmaRows) :
    (tailRowsOf C cvk cp)[37 + q]'(by omega)
      = zipSeg C (cvk.sigmaComm[q]'(by omega)) (cp.evals.s[q]'hq) := by
  show (litRowsOf C cvk cp
      ++ (cp.wComm.zip cp.evals.w).map (fun x => zipSeg C x.1 x.2)
      ++ (cvk.coefficientsComm.zip cp.evals.coefficients).map (fun x => zipSeg C x.1 x.2)
      ++ ((cvk.sigmaComm.take sigmaRows).zip cp.evals.s).map
        (fun x => zipSeg C x.1 x.2))[37 + q]'(by omega) = _
  rw [Vector.getElem_append, dif_neg (by omega)]
  simp only [show 37 + q - (7 + 15 + 15) = q from by omega, Vector.getElem_map,
    Vector.getElem_zip, Vector.getElem_take]
  rfl

end TailReads

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
      cvk.endo (mdsOfParams C.frParams) o.alpha o.beta o.gamma o.zeta pubEval0 e
    let (v, u) := frOracles C cp o.digest pubEvals
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

/-! ## The public-input view -/

/-- The public-input array as the `Fin idx.publicCount`-indexed function the circuit
model consumes (`getD`, total; the capstones pin `pub.size = idx.publicCount`, so the
view reads only genuine entries). The wire-to-abstract public view. -/
def pubView {F : Type*} [Field F] {n : ℕ} (idx : Index F n) (pub : Array F) :
    Fin idx.publicCount → F :=
  fun i => pub.getD (i : ℕ) 0

end Kimchi.Verifier
