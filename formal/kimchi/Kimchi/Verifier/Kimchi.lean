import Bulletproof.Wire
import Kimchi.Protocol.Linearization
import Kimchi.Columns
import Poseidon.FqSponge

/-!
# The kimchi verifier body over the checked records

The kimchi verifier transcribed from proof-systems' `kimchi/src/verifier.rs`: the Fiat–Shamir
argument (lines 126–634) and the partial verification (lines 781–1194), finished by the
batched IPA opening check at any power-of-two chunk count `nc` (`nc = 1` is the one-chunk
case). The scalar-side closed forms are `Kimchi.Protocol.Linearization` (`ftEval0`,
`permScalar`, `zkpmEval`); the sponge layer is `Poseidon.FqSponge`, used at both fields; the
opening is `Ipa.verifyFrom`, restarted from the warm fq-sponge state the challenge schedule
leaves (lines 1184–1193).

## The checked side of the wire boundary

The records here (`KimchiProof`, `KimchiVK`) carry the chunk count in their types. They are
what `KimchiProof.check` and `KimchiVK.check` in `Kimchi.Verifier.Wire` produce, so every
read is total and nothing in this module reads unchecked data. `Kimchi.Verifier.Wire` holds
the serde-typed records and their parse but no verifier: a client parses at the run's chunk
count and calls `kimchiVerify` on the parsed records.

## Scope

The modeled fragment, and every deviation from the upstream file:

* no lookups and no optional gates: the records carry neither. The basic gate set adds no
  index terms to the linearization, so the linearized commitment is the one σ-commitment
  term (lines 897–956);
* the old accumulators are on the wire: a proof carries them (`KimchiProof.olds`, each a
  commitment and its `k` expanded round challenges) and the key their count
  (`KimchiVK.prevChallenges`, checked by `kimchiVerify` as upstream checks it, lines
  810–815). Both schedules and the batch read them where upstream does (lines 165–168,
  290–299, 311–329, 972–975). Validated on a deployed pickles wrap proof with two
  accumulators (`fixtures/kimchi_proof_pallas_pickles.json`);
* the opening's `U` base is the map-to-curve point with its ordinate in the lower half
  (`KimchiCurve.uBase`), as the pinned proof-systems derives it at both of its IPA sites.
  Upstream proof-systems takes the field's square root as returned, a sign a circuit cannot
  check without that pin;
* the verifier-index digest is an input (`KimchiVK.digest`), not computed from the key;
* upstream's sub-SRS regime, a domain smaller than the SRS with one chunk per column (lines
  145–152), is in scope: `Wire.runNc` is upstream's chunk-count formula, and every deployed
  pickles proof but the two-proof wrap lives there (wrap domains `2^13`, `2^14` against the
  `2^15` Tock SRS; small step domains against the `2^16` Tick SRS). The body reads the SRS
  exponent where upstream reads its maximum polynomial size (`ζ^M`, the opening's round
  count), so nothing else distinguishes the regime; the pickles fixture above is its
  evidence;
* at the two excluded evaluation points `ζ ∈ {1, ω^(n−zkRows)}` upstream panics (lines
  459–460), while this executable takes `ZMod`'s junk division (`x/0 = 0`) and proceeds: a
  real difference between the two algorithms;
* the final check is the two bracket equations as a conjunction, `A = 0 ∧ B = 0`, where
  upstream settles one MSM, `∑ᵢ (rⁱ·Aᵢ + sⁱ·Bᵢ) = 0` at fresh random weights `r`, `s`. On one
  proof both weights are `1` and upstream's test is `A + B = 0`, so acceptance here implies
  upstream acceptance, not conversely (`Bulletproof/Wire.lean`, *What `verify` checks*).
  Batching several proofs is out of scope;
* upstream's key carries the public-input count as a serialized field, and upstream rejects
  a public input of any other length (lines 816–820, re-checked at 835–838). The wire key
  here carries no count, so `kimchiVerify` checks the two bounds the body needs instead: the
  public input against the Lagrange table and against the domain, so the Lagrange MSM and
  the barycentric sums read only genuine entries.
-/

namespace Kimchi.Verifier

open CompElliptic.CurveForms.ShortWeierstrass
open Poseidon Poseidon.FqSponge Bulletproof

variable (C : Ipa.KimchiCurve)

/-! ## The evaluation containers -/

/-- An evaluation pair at the two batch points: a column's value at `ζ` and at `ζω`. -/
structure PointEvaluations (F : Type*) where
  /-- The evaluation at `ζ`. -/
  zeta : F
  /-- The evaluation at `ζω`. -/
  zetaOmega : F

/-- The pair as a row of the batch's evaluation matrix: `ζ` then `ζω`. -/
def PointEvaluations.toVector {F : Type*} (e : PointEvaluations F) : Vector F evalPts :=
  #v[e.zeta, e.zetaOmega]

/-- The proof's claimed evaluations, one `PointEvaluations` per column family, generic in
the per-point payload `E`: `Array F` on the wire (chunk vectors of unchecked length),
`Vector F nc` after the parse. The fixed column counts (`wCols` witness, `sigmaRows` evaluated σ,
`coeffCols` coefficient) are type-level. -/
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

/-- Push a map through an evaluation pair. -/
def PointEvaluations.map {α β : Type*} (f : α → β) (e : PointEvaluations α) :
    PointEvaluations β :=
  ⟨f e.zeta, f e.zetaOmega⟩

/-- Push a map through the evaluation record, pair by pair. -/
def ProofEvaluations.map {α β : Type*} (f : α → β) (e : ProofEvaluations α) :
    ProofEvaluations β where
  w := e.w.map (PointEvaluations.map f)
  z := e.z.map f
  s := e.s.map (PointEvaluations.map f)
  coefficients := e.coefficients.map (PointEvaluations.map f)
  genericSelector := e.genericSelector.map f
  poseidonSelector := e.poseidonSelector.map f
  completeAddSelector := e.completeAddSelector.map f
  mulSelector := e.mulSelector.map f
  emulSelector := e.emulSelector.map f
  endomulScalarSelector := e.endomulScalarSelector.map f

/-- The fr-sponge transcript as the list absorbed, every entry widened to its column's chunk
vector: the fq-sponge digest, the recursion digest, `ft(ζω)`, the two public chunk vectors,
then each column's `ζ`-chunk and `ζω`-chunk vectors (`z`, the six selectors, the witness
columns, the coefficient columns, the σ columns). -/
def frTranscript {F : Type*} {nc : ℕ} (fqDig recDigest ftEval1 : F)
    (pubEvals : PointEvaluations (Vector F nc)) (evals : ProofEvaluations (Vector F nc)) :
    List F :=
  let pt := fun (e : PointEvaluations (Vector F nc)) => e.zeta.toList ++ e.zetaOmega.toList
  [fqDig, recDigest, ftEval1] ++ pubEvals.zeta.toList ++ pubEvals.zetaOmega.toList
    ++ pt evals.z ++ pt evals.genericSelector ++ pt evals.poseidonSelector
    ++ pt evals.completeAddSelector ++ pt evals.mulSelector ++ pt evals.emulSelector
    ++ pt evals.endomulScalarSelector
    ++ (evals.w.toList.map pt).flatten ++ (evals.coefficients.toList.map pt).flatten
    ++ (evals.s.toList.map pt).flatten

/-- The fr-sponge's two raw squeezes over a transcript, before the limb packing: a fresh
sponge absorbs the transcript and is squeezed once for the polyscale, again for the
evalscale. `frOracles` packs each to its low 128 bits and endo-expands
(`frOracles_eq_frPrechallenges`); the circuit's fr-sponge is stated over the same pair
(`Pickles.squeezeXiR_spec`). -/
def frSqueezes {F : Type*} [Field F] (p : Poseidon.Params F) (transcript : List F) : F × F :=
  let sq := Poseidon.squeeze p (Poseidon.absorb p Poseidon.init transcript)
  (sq.1, (Poseidon.squeeze p sq.2).1)

/-! ## The checked records -/

/-- The public-evaluation source: carried evaluations, accepted at any `nc` and required at
`nc > 1`, or the barycentric fallback, which exists only at `nc = 1` and is computed in the
verifier body because it needs `ζ`. -/
inductive PubEvalSrc (C : Ipa.KimchiCurve) (nc : ℕ) where
  | carried (pe : PointEvaluations (Vector C.ScalarField nc))
  | barycentric (h : nc = 1)

/-- An old accumulator: a commitment the batch opens at the challenge polynomial of a
previous opening — its final folded generator and the `k` endo-expanded round challenges.
A proof carries them one chunk each (`KimchiProof.olds`). -/
structure Accumulator (C : Ipa.KimchiCurve) (k : ℕ) where
  /-- The previous opening's final folded generator, a single point. -/
  sg : C.Point
  /-- Its round challenges, endo-expanded into the scalar field. -/
  u : Vector C.ScalarField k

/-- A chunk-validated proof at the SRS's round count `k`: what `Wire.KimchiProof.check`
returns, and what `kimchiVerify` reads. -/
structure KimchiProof (C : Ipa.KimchiCurve) (nc k : ℕ) where
  /-- The witness-column commitments, one `nc`-chunk vector per column. -/
  wComm : Vector (Vector C.Point nc) wCols
  /-- The permutation-aggregation commitment. -/
  zComm : Vector C.Point nc
  /-- The quotient chunks: genuinely variable-length, so the bound is carried. -/
  tComm : Array C.Point
  tComm_le : tComm.size ≤ quotChunks * nc
  /-- The claimed evaluations, per column family and per chunk. -/
  evals : ProofEvaluations (Vector C.ScalarField nc)
  /-- The public-evaluation source: carried pairs, or the barycentric fallback at `nc = 1`. -/
  pubEvals : PubEvalSrc C nc
  /-- `ft(ζω)` (Maller's optimization) — the ft row is single-chunk. -/
  ftEval1 : C.ScalarField
  /-- The batched IPA opening proof, at the SRS's round count `k`. -/
  opening : Ipa.Proof C k
  /-- The old accumulators, each at the SRS's round count `k`. -/
  olds : Array (Accumulator C k)

/-- A chunk-validated verifier key: what `Wire.KimchiVK.check` returns. -/
structure KimchiVK (C : Ipa.KimchiCurve) (nc : ℕ) where
  /-- The domain size exponent: `n = 2 ^ domainLog2`. -/
  domainLog2 : ℕ
  /-- The domain generator `ω`. -/
  omega : C.ScalarField
  /-- The permutation commitments, one `nc`-chunk vector per σ column. -/
  sigmaComm : Vector (Vector C.Point nc) permCols
  /-- The coefficient-column commitments, one `nc`-chunk vector per column. -/
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
  /-- The permutation coset shifts. -/
  shifts : Vector C.ScalarField permCols
  /-- The number of zero-knowledge rows. -/
  zkRows : ℕ
  /-- The accumulator count the key was built with: `kimchiVerify` rejects a proof whose
  `olds` has any other length. -/
  prevChallenges : ℕ
  /-- The endomorphism coefficient `ftEval0` reads. -/
  endo : C.ScalarField
  /-- The verifier-index digest, an input rather than computed from the key. -/
  digest : C.BaseField
  /-- The Lagrange-basis commitments, chunk-validated in full: SRS-derived data, an input
  like `digest`. -/
  lagrangeBasis : Array (Vector C.Point nc)

/-- The domain size of a checked key. -/
def KimchiVK.n {C : Ipa.KimchiCurve} {nc : ℕ}
    (cvk : KimchiVK C nc) : ℕ := 2 ^ cvk.domainLog2

/-- A Poseidon parameter table's MDS matrix as the gate's `Mds` record, the form
`kimchiVerify` hands `ftEval0`. `Gate.Poseidon.mdsOfParams` is the same repackaging behind
the gate's wholesale `import Mathlib`, which the executable path avoids. -/
def mdsOfParams {F : Type*} (p : Poseidon.Params F) : Gate.Poseidon.Mds F :=
  ⟨p.mds.1.1, p.mds.1.2.1, p.mds.1.2.2,
   p.mds.2.1.1, p.mds.2.1.2.1, p.mds.2.1.2.2,
   p.mds.2.2.1, p.mds.2.2.2.1, p.mds.2.2.2.2⟩

/-! ## The fr-sponge and the sponge digests -/

/-- The fr-sponge digest: the plain first squeeze, in the same field, with no cast. -/
def frDigest (sp : FqSponge.Spec C.scalar C.scalar) (s : FqSponge.S C.scalar) :
    C.ScalarField :=
  (challengeFq sp s).1

/-- The recursion digest: the digest of a second fresh fr-sponge that absorbed every old
accumulator's challenges in order. At no accumulators it is the constant
`frDigest C C.frSponge FqSponge.init`. -/
def recDigest {k : ℕ} (us : Array (Vector C.ScalarField k)) : C.ScalarField :=
  frDigest C C.frSponge
    (absorbFq C.frSponge FqSponge.init (us.toList.map Vector.toList).flatten)

/-- The cast of the fq-sponge digest into the scalar field: the representative when it
fits, else zero — not a modular reduction. The sponge produces only the base-field element
(`FqRun.digestElem`); this cast is the consumer's step. -/
def castDigest (x : C.BaseField) : C.ScalarField :=
  if x.val < C.scalar then ((x.val : ℕ) : C.ScalarField) else 0

/-! ## The oracle outputs and the public evaluations -/

/-- The fq-sponge outputs: the challenges, the digest handed to the fr-sponge, and the warm
post-`ζ` sponge state the opening check continues. -/
structure FqOracles (C : Ipa.KimchiCurve) where
  /-- The permutation argument's challenge `β`. -/
  beta : C.ScalarField
  /-- The permutation argument's challenge `γ`. -/
  gamma : C.ScalarField
  /-- The constraint-combination challenge `α`. -/
  alpha : C.ScalarField
  /-- The evaluation-point challenge `ζ`. -/
  zeta : C.ScalarField
  /-- The fq-sponge digest, cast into the scalar field (`castDigest`). -/
  digest : C.ScalarField
  /-- The pre-digest sponge state, continued by the IPA finish. -/
  warm : FqSponge.S C.base

/-- The fr-sponge outputs: the batch's polyscale and evalscale, endo-expanded. -/
structure FrOracles (C : Ipa.KimchiCurve) where
  /-- The polyscale `ξ`. -/
  xi : C.ScalarField
  /-- The evalscale `r`. -/
  r : C.ScalarField

/-- `x ^ (2 ^ k)` by `k` squarings. The domain-size exponents `ζⁿ` (`n = 2 ^ domainLog2`)
would otherwise run through the linear `npowRec`, making `#eval` of the verifier
impractical at production domain sizes. -/
def powPow2 {F : Type*} [Field F] (x : F) (k : ℕ) : F :=
  (List.range k).foldl (fun a _ => a * a) x

/-- `powPow2` is the power it computes. -/
theorem powPow2_eq {F : Type*} [Field F] (x : F) (k : ℕ) : powPow2 x k = x ^ 2 ^ k := by
  induction k with
  | zero => simp [powPow2]
  | succ k ih =>
      rw [powPow2, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      show powPow2 x k * powPow2 x k = _
      rw [ih, ← pow_add, ← two_mul, ← pow_succ']

/-- The shared sum of the two public evaluations, `∑ᵢ −(pt − ωⁱ)⁻¹ · pubᵢ · ωⁱ`, by a
running-`ω`-power fold. Each term is inverted on its own, the same value a batched
inversion gives. -/
private def pubDot {F : Type*} [Field F] (omega pt : F) (pub : Array F) : F :=
  (pub.foldl (fun (acc : F × F) pi =>
    (acc.1 + -(pt - acc.2)⁻¹ * pi * acc.2, acc.2 * omega)) (0, 1)).1

/-- The negated public evaluations at `ζ` and `ζω`: `(0, 0)` for empty input, else
`pubDot` at each point scaled by `(ptⁿ − 1) · n⁻¹`. The public polynomial is committed
negated (`publicCommitment`), so the batch uses these values with no re-negation. -/
private def publicEvals {F : Type*} [Field F] (n : ℕ)
    (omega zeta zetaOmega zetaN zetaOmegaN : F) (pub : Array F) : F × F :=
  if pub.size = 0 then (0, 0)
  else
    (pubDot omega zeta pub * (zetaN - 1) * (n : F)⁻¹,
     pubDot omega zetaOmega pub * (n : F)⁻¹ * (zetaOmegaN - 1))

/-! ## The Fiat–Shamir schedules -/

/-- The fq-sponge run before any cast or expansion: the four 128-bit prechallenges, the
digest element in the base field, and the warm post-`ζ` state. A circuit's group half
(`Pickles.fqSpongeTranscript`) emits these; `FqRun.expand` is the consumer's step. -/
structure FqRun (C : Ipa.KimchiCurve) where
  /-- The `β` prechallenge. -/
  beta : Prechallenge
  /-- The `γ` prechallenge. -/
  gamma : Prechallenge
  /-- The `α` prechallenge. -/
  alpha : Prechallenge
  /-- The `ζ` prechallenge. -/
  zeta : Prechallenge
  /-- The digest squeeze, a base-field element, before `castDigest`. -/
  digestElem : C.BaseField
  /-- The pre-digest sponge state, continued by the IPA finish. -/
  warm : FqSponge.S C.base

/-- The fq-sponge schedule, opening with the index digest and the old accumulators'
commitments. Each commitment is absorbed chunk by chunk (`absorbG`), so the absorbs are
chunk folds while the squeeze schedule does not depend on the chunk count. Every squeeze is
`challengeNat`. -/
def fqRun {nc k : ℕ} (cvk : KimchiVK C nc) (cp : KimchiProof C nc k)
    (publicComm : Vector C.Point nc) : FqRun C :=
  let s := absorbFq C.sponge FqSponge.init [cvk.digest]
  let s := (cp.olds.map (·.sg)).foldl (absorbG C.sponge) s
  let s := publicComm.foldl (absorbG C.sponge) s
  let s := cp.wComm.foldl (fun s col => col.foldl (absorbG C.sponge) s) s
  let (beta, s) := challengeNat C.sponge s
  let (gamma, s) := challengeNat C.sponge s
  let s := cp.zComm.foldl (absorbG C.sponge) s
  let (alpha, s) := challengeNat C.sponge s
  let s := cp.tComm.foldl (absorbG C.sponge) s
  let (zeta, s) := challengeNat C.sponge s
  ⟨beta, gamma, alpha, zeta, (challengeFq C.sponge s).1, s⟩

/-- The consumer's view of an fq-sponge run: `β, γ` cast into the scalar field, `α, ζ`
endo-expanded at the sponge's eigenvalue, the digest cast. -/
def FqRun.expand (r : FqRun C) : FqOracles C :=
  ⟨(r.beta.val : C.ScalarField), (r.gamma.val : C.ScalarField),
    endoExpand C.lam r.alpha.val, endoExpand C.lam r.zeta.val,
    castDigest C r.digestElem, r.warm⟩

/-- The fq-sponge oracles: the run, expanded. -/
def fqOracles {nc k : ℕ} (cvk : KimchiVK C nc) (cp : KimchiProof C nc k)
    (publicComm : Vector C.Point nc) : FqOracles C :=
  (fqRun C cvk cp publicComm).expand

/-- The fq-sponge run over the Poseidon automaton, commitments as coordinate pairs and the
old accumulators' commitments absorbed after the index digest: the four raw squeezed
elements behind `β, γ, α, ζ`, the digest element, and the pre-digest state. The circuit's
fq-sponge is stated over this. -/
def fqSqueezes {F : Type*} [Field F] (p : Poseidon.Params F) (indexDigest : F)
    (recursion pubComm : List (F × F)) (wComm : List (List (F × F)))
    (zComm tComm : List (F × F)) : (F × F × F × F) × F × Poseidon.State F :=
  let pts := fun (s : Poseidon.State F) (l : List (F × F)) =>
    l.foldl (fun s q => Poseidon.absorb p s [q.1, q.2]) s
  let s := pts (pts (Poseidon.absorb p Poseidon.init [indexDigest]) recursion) pubComm
  let s := wComm.foldl pts s
  let sqβ := Poseidon.squeeze p s
  let sqγ := Poseidon.squeeze p sqβ.2
  let sqα := Poseidon.squeeze p (pts sqγ.2 zComm)
  let sqζ := Poseidon.squeeze p (pts sqα.2 tComm)
  ((sqβ.1, sqγ.1, sqα.1, sqζ.1), (Poseidon.squeeze p sqζ.2).1, sqζ.2)

/-- A commitment's chunk coordinates, in chunk order. -/
def coords {n : ℕ} (v : Vector C.Point n) : List (C.BaseField × C.BaseField) :=
  v.toList.map fun P => (P.x, P.y)

/-- A point fold from an empty limb buffer is the coordinate fold on the automaton. -/
private theorem foldl_absorbG (l : List C.Point) (st : Poseidon.State C.BaseField) :
    l.foldl (absorbG C.sponge) ⟨st, []⟩
      = ⟨(l.map fun P => (P.x, P.y)).foldl
          (fun s q => Poseidon.absorb C.sponge.params s [q.1, q.2]) st, []⟩ := by
  induction l generalizing st with
  | nil => rfl
  | cons P l ih => simp only [List.foldl_cons, List.map_cons, absorbG, absorbFq, ih]

/-- The column fold likewise, column by column. -/
private theorem foldl_cols {nc : ℕ} (cols : List (Vector C.Point nc))
    (st : Poseidon.State C.BaseField) :
    cols.foldl (fun s col => col.toList.foldl (absorbG C.sponge) s) ⟨st, []⟩
      = ⟨(cols.map fun col => col.toList.map fun P => (P.x, P.y)).foldl
          (fun s l => l.foldl (fun s q => Poseidon.absorb C.sponge.params s [q.1, q.2]) s)
          st, []⟩ := by
  induction cols generalizing st with
  | nil => rfl
  | cons col cols ih => simp only [List.foldl_cons, List.map_cons, foldl_absorbG, ih]

/-- The raw run `fqRun` through `fqSqueezes` on the automaton, field by field: each
prechallenge is the packing of its squeeze, the digest element the digest squeeze, the warm
state the pre-digest state with an empty limb buffer. The circuit's fq-sponge is read against
`fqSqueezes`; this is how that read reaches the wire's run. -/
theorem fqRun_eq_fqSqueezes {nc k : ℕ} (cvk : KimchiVK C nc) (cp : KimchiProof C nc k)
    (publicComm : Vector C.Point nc) :
    let r := fqSqueezes C.sponge.params cvk.digest
      ((cp.olds.map (·.sg)).toList.map fun P => (P.x, P.y)) (coords C publicComm)
      (cp.wComm.toList.map (coords C)) (coords C cp.zComm)
      (cp.tComm.toList.map fun P => (P.x, P.y))
    (fqRun C cvk cp publicComm).beta.val = r.1.1.val % 2 ^ 128 ∧
    (fqRun C cvk cp publicComm).gamma.val = r.1.2.1.val % 2 ^ 128 ∧
    (fqRun C cvk cp publicComm).alpha.val = r.1.2.2.1.val % 2 ^ 128 ∧
    (fqRun C cvk cp publicComm).zeta.val = r.1.2.2.2.val % 2 ^ 128 ∧
    (fqRun C cvk cp publicComm).digestElem = r.2.1 ∧
    (fqRun C cvk cp publicComm).warm = ⟨r.2.2, []⟩ := by
  dsimp only
  simp only [fqRun, fqSqueezes, coords, absorbFq, FqSponge.init, ← Vector.foldl_toList,
    ← Array.foldl_toList, foldl_absorbG, foldl_cols, challengeNat_fresh, challengeFq,
    List.foldl_map, and_self]

/-- The fr-sponge run before any expansion: the two 128-bit prechallenges. A circuit's
scalar half (`Pickles.squeezeXiR`) recomputes them; `FrRun.expand` is the consumer's
step. -/
structure FrRun where
  /-- The `ξ` prechallenge. -/
  xi : Prechallenge
  /-- The `r` prechallenge. -/
  r : Prechallenge

/-- The fr-sponge schedule: absorb `frTranscript`, with the recursion digest `recDigest` of
the proof's old accumulators' challenges, then squeeze the two 128-bit prechallenges. Every
squeeze is `challengeNat`. -/
def frRun {nc k : ℕ} (cp : KimchiProof C nc k)
    (fqDig : C.ScalarField) (pubEvals : PointEvaluations (Vector C.ScalarField nc)) : FrRun :=
  let sp := C.frSponge
  let s := absorbFq sp FqSponge.init
    (frTranscript fqDig (recDigest C (cp.olds.map (·.u))) cp.ftEval1 pubEvals cp.evals)
  let (xi, s) := challengeNat sp s
  let (r, _) := challengeNat sp s
  ⟨xi, r⟩

/-- The consumer's view of an fr-sponge run: both prechallenges endo-expanded at the
sponge's eigenvalue — the polyscale and the evalscale. -/
def FrRun.expand (x : FrRun) : FrOracles C :=
  ⟨endoExpand C.lam x.xi.val, endoExpand C.lam x.r.val⟩

/-- The fr-sponge oracles: the run, expanded. -/
def frOracles {nc k : ℕ} (cp : KimchiProof C nc k)
    (fqDig : C.ScalarField) (pubEvals : PointEvaluations (Vector C.ScalarField nc)) :
    FrOracles C :=
  FrRun.expand C (frRun C cp fqDig pubEvals)

/-- The fr-sponge's two 128-bit prechallenges over a transcript, as naturals: the values
`challengeNat` packs from the two raw squeezes (`frSqueezes`), before the endomorphism
expansion. `frOracles` is their expansion (`frOracles_eq_frPrechallenges`). -/
def frPrechallenges {p : ℕ} [Field (ZMod p)] (params : Poseidon.Params (ZMod p))
    (transcript : List (ZMod p)) : ℕ × ℕ :=
  let sq := frSqueezes params transcript
  (sq.1.val % 2 ^ 128, sq.2.val % 2 ^ 128)

/-- `frOracles` is the endo-expansion of `frPrechallenges` over `frTranscript` at the old
accumulators' `recDigest`: `challengeNat` from an empty limb buffer is one raw squeeze's
value mod `2^128`. -/
theorem frOracles_eq_frPrechallenges {nc k : ℕ} (cp : KimchiProof C nc k)
    (fqDig : C.ScalarField) (pubEvals : PointEvaluations (Vector C.ScalarField nc)) :
    frOracles C cp fqDig pubEvals =
      let pre := frPrechallenges C.frSponge.params
        (frTranscript fqDig (recDigest C (cp.olds.map (·.u))) cp.ftEval1 pubEvals cp.evals)
      ⟨endoExpand C.lam pre.1, endoExpand C.lam pre.2⟩ := by
  simp only [frOracles, FrRun.expand, frRun, frPrechallenges, frSqueezes, absorbFq,
    challengeNat_fresh]
  rfl

/-! ## The scalar side -/

/-- The chunk combination `∑ c, chunks[c] · xM ^ c`, by a running-power fold;
`kimchiVerify` passes `xM = pt^M` for the SRS size `M`. A one-chunk vector combines to its
chunk. -/
def combineAt {F : Type*} [Field F] (xM : F) (chunks : Array F) : F :=
  (chunks.foldl (fun (acc : F × F) c => (acc.1 + acc.2 * c, acc.2 * xM)) (0, 1)).1

/-- The public evaluation chunk vectors: the proof-carried pairs when present, at any `nc`;
else the one-chunk barycentric computation, whose `nc = 1` proof the
`PubEvalSrc.barycentric` constructor carries. -/
def publicEvalChunks {C : Ipa.KimchiCurve} {nc k : ℕ} (cp : KimchiProof C nc k)
    (n : ℕ) (omega zeta zetaOmega zetaN zetaOmegaN : C.ScalarField)
    (pub : Array C.ScalarField) : PointEvaluations (Vector C.ScalarField nc) :=
  match cp.pubEvals with
  | .carried pe => pe
  | .barycentric h =>
    let (e0, e1) := publicEvals n omega zeta zetaOmega zetaN zetaOmegaN pub
    ⟨⟨#[e0], by simp [h]⟩, ⟨#[e1], by simp [h]⟩⟩

/-- The proof's evaluations, chunk-combined, as the linearization's `Evals` record: every
`ζ`-side value combined at `zetaM`, every `ζω`-side value at `zetaOmegaM`. -/
def KimchiProof.linEvals {C : Ipa.KimchiCurve} {nc k : ℕ}
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

/-- The public-input commitment, per chunk: on empty input, `nc` copies of the blinding
base `σ.h`; else chunk `c` is the MSM of the Lagrange-basis commitments' `c`-chunks against
the negated public input, plus `σ.h`, the all-ones blinder applied per chunk. -/
def publicCommitment {nc : ℕ} (σ : SRS C.Point) (cvk : KimchiVK C nc)
    (pub : Array C.ScalarField) : Vector C.Point nc :=
  if pub.size = 0 then Vector.replicate nc σ.h
  else
    Vector.ofFn (fun (c : Fin nc) =>
      ((cvk.lagrangeBasis.extract 0 pub.size).zip pub).foldl
        (fun acc Pp => acc + (-Pp.2).val • Pp.1[c]) 0
      + σ.h)

/-- A left fold of addition from a start is the start plus the sum. -/
private theorem foldl_add_eq {G : Type*} [AddMonoid G] (init : G) :
    ∀ l : List G, l.foldl (· + ·) init = init + l.sum
  | [] => by simp
  | x :: l => by
    rw [List.foldl_cons, foldl_add_eq (init + x) l, List.sum_cons, _root_.add_assoc]

/-- `publicCommitment` as a per-chunk list sum plus `h` (nonempty input): an order-free
re-association of the fold into `(… .map …).sum + h`, with no negation rewrite and no
curve-order fact. `Pickles.PublicInputCommit` works from this form. -/
theorem publicCommitment_eq_sum {nc : ℕ} (σ : SRS C.Point) (cvk : KimchiVK C nc)
    (pub : Array C.ScalarField) (hne : pub.size ≠ 0) :
    publicCommitment C σ cvk pub =
      Vector.ofFn (fun c : Fin nc =>
        (((cvk.lagrangeBasis.extract 0 pub.size).zip pub).toList.map
            (fun Pp => (-Pp.2).val • Pp.1[c])).sum + σ.h) := by
  unfold publicCommitment
  rw [if_neg hne]
  refine congrArg Vector.ofFn (funext fun c => ?_)
  rw [← Array.foldl_toList, ← List.foldl_map, foldl_add_eq, _root_.zero_add]

/-! ## The stream combinators -/

/-- One logical batch row's per-chunk segment triples: the chunk commitments zipped
with the per-chunk claims at `(ζ, ζω)`. -/
def zipSeg {nc : ℕ} (comm : Vector C.Point nc)
    (ev : PointEvaluations (Vector C.ScalarField nc)) :
    Vector (C.Point × C.ScalarField × C.ScalarField) nc :=
  Vector.ofFn fun c => (comm[c], ev.zeta[c], ev.zetaOmega[c])

/-- The literal single-column head block of the batch tail, in batch order: the
accumulator `z` and the six selectors — the `litRowCount` rows whose commitments are
single named record fields. The one place this vector literal is written. -/
def litRowsOf {nc k : ℕ} (cvk : KimchiVK C nc) (cp : KimchiProof C nc k) :
    Vector (Vector (C.Point × C.ScalarField × C.ScalarField) nc) litRowCount :=
  ⟨#[zipSeg C cp.zComm cp.evals.z,
     zipSeg C cvk.genericComm cp.evals.genericSelector,
     zipSeg C cvk.poseidonComm cp.evals.poseidonSelector,
     zipSeg C cvk.completeAddComm cp.evals.completeAddSelector,
     zipSeg C cvk.mulComm cp.evals.mulSelector,
     zipSeg C cvk.emulComm cp.evals.emulSelector,
     zipSeg C cvk.endomulScalarComm cp.evals.endomulScalarSelector], rfl⟩

/-- The 43 tail rows of the batch stream in batch order (`z`, the six selectors,
witness `0–14`, coefficients `0–14`, σ `0–5`), each row its per-chunk segments. -/
def tailRowsOf {nc k : ℕ} (cvk : KimchiVK C nc) (cp : KimchiProof C nc k) :
    Vector (Vector (C.Point × C.ScalarField × C.ScalarField) nc) tailRowCount :=
  litRowsOf C cvk cp
  ++ (cp.wComm.zip cp.evals.w).map (fun x => zipSeg C x.1 x.2)
  ++ (cvk.coefficientsComm.zip cp.evals.coefficients).map (fun x => zipSeg C x.1 x.2)
  ++ ((cvk.sigmaComm.take sigmaRows).zip cp.evals.s).map (fun x => zipSeg C x.1 x.2)

/-! ## The verifier -/

/-- **The verifier body over checked records**, for one proof at the basic gate set. It
rejects a proof whose accumulator count differs from the key's, or whose public input
overruns the domain or the Lagrange table. It then derives the challenges, evaluates the
scalar side on chunk-combined evaluations, and collapses the linearized and quotient
commitments at `ζ^M` into the one `ft` commitment. `Ipa.verifyFrom`, from the warm sponge,
opens the old accumulators' rows, then the public, `ft` and `tailRowsOf` rows flattened to
one segment per chunk (`ft` a single segment). -/
def kimchiVerify {nc : ℕ} (σ : SRS C.Point) (cvk : KimchiVK C nc)
    (cp : KimchiProof C nc σ.k) (pub : Array C.ScalarField) : Bool :=
  let n := cvk.n
  -- The two public-input bounds stand in for upstream's exact count, which the wire key
  -- does not carry (the module docstring's scope). The accumulator count guard is
  -- upstream's own.
  if cvk.lagrangeBasis.size < pub.size || n < pub.size
      || cp.olds.size ≠ cvk.prevChallenges then
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
      cvk.endo (mdsOfParams C.frSponge.params) o.alpha o.beta o.gamma o.zeta pubEval0 e
    let fr := frOracles C cp o.digest pubEvals
    let zkpmZ := Kimchi.Protocol.Linearization.zkpmEval n cvk.zkRows cvk.omega o.zeta
    let pScalar := Kimchi.Protocol.Linearization.permScalar o.beta o.gamma o.alpha zkpmZ e
    let fComm := cvk.sigmaComm[6].map (fun P => pScalar.val • P)
    let ftComm := Ipa.combineCommitments C zetaM fComm.toArray
      - (zetaN - 1).val • Ipa.combineCommitments C zetaM cp.tComm
    let accRows : Vector (C.Point × C.ScalarField × C.ScalarField) cp.olds.size :=
      ⟨cp.olds.map (fun a => (a.sg, bPoly a.u.get o.zeta, bPoly a.u.get zetaOmega)), by simp⟩
    let stream : Vector (C.Point × C.ScalarField × C.ScalarField)
        (cp.olds.size + (nc + 1 + tailRowCount * nc)) :=
      accRows
        ++ ((Vector.ofFn fun c : Fin nc =>
              (publicComm[c], pubEvals.zeta[c], pubEvals.zetaOmega[c]))
            ++ (⟨#[(ftComm, ftEval0, cp.ftEval1)], rfl⟩
                : Vector (C.Point × C.ScalarField × C.ScalarField) 1)
            ++ (tailRowsOf C cvk cp).flatten)
    let inp : Ipa.Input C σ.k (cp.olds.size + (nc + 1 + tailRowCount * nc)) evalPts :=
      { commitments := stream.map (·.1)
        xs := ⟨#[o.zeta, zetaOmega], rfl⟩
        evals := stream.map (fun r => (⟨#[r.2.1, r.2.2], rfl⟩ : Vector _ evalPts))
        polyscale := fr.xi
        evalscale := fr.r
        proof := cp.opening }
    Ipa.verifyFrom C σ o.warm inp

end Kimchi.Verifier
