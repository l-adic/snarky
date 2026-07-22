import Bulletproof.Wire
import Kimchi.Protocol.Linearization
import Kimchi.Verifier.Reduction.Correspond
import Poseidon.FqSponge

/-!
# The executable kimchi verifier

The full kimchi verifier over wire data, transcribed from proof-systems
`kimchi/src/verifier.rs`: the Fiat-Shamir argument (`oracles`, :126–634) and the partial
verification (`to_batch`, :781–1194), finished by the batched IPA opening check at
production chunking (`chunk_size = d1 / max_poly_size`, any power-of-two `nc`;
`nc = 1` is the one-chunk case). The scalar-side closed forms are
`Kimchi.Protocol.Linearization` (`ftEval0`/`permScalar`/`zkpmEval`); the sponge layer is
`Poseidon.FqSponge`, reused at both fields; the opening finish is the `Bulletproof.Ipa`
acceptance, restarted from the **warm** fq-sponge state
(`BatchEvaluationProof { sponge: fq_sponge, .. }`, verifier.rs:1184–1193).

**The two-layer wire discipline.** Type-level facts are exactly the facts serde
enforces; runtime guards are exactly the checks the verifier executes:

* The WIRE records (`KimchiProof`, `KimchiVK`) mirror the serde types. The fixed
  dimensions — 15 witness/coefficient columns, 7 σ columns, 6 evaluated σ columns, 7
  shifts — are `Vector`s, because production's `[T; N]` arrays reject wrong lengths at
  deserialization. Chunk payloads stay `Array`s (`PolyComm.elems` is `Vec<G>` — serde
  imposes no length).
* The CHECKED records (`KimchiProof.Checked nc`, `KimchiVK.Checked nc`) carry the
  chunk counts in their types. `KimchiProof.check nc` / `KimchiVK.check nc` are the
  verifier's own length checks (`check_proof_evals_len` at `chunk_size`, the `t`
  bound, the `nc > 1` public-evaluation requirement) factored as a total parse into
  the typed core: a checked record CANNOT hold a ragged proof. `kimchiVerify` is
  literally check-then-verify; ragged input fails the check and is rejected — the
  same observable behavior as production's `Err` returns.

Scope (every deferral is declared here):

* no lookups (the wire records carry none) and no recursion (`prev_challenges`
  absent) — but the *constant* fr-sponge absorb of the empty recursion list's digest
  is transcribed (verifier.rs:290–299);
* the VK digest is an *input* (`KimchiVK.digest`); transcribing
  `VerifierIndex::digest()` (verifier_index.rs:399) is a declared deferral;
* `linearization.index_terms` is empty at the basic gate set, so `f_comm` is the
  single σ-commitment term (verifier.rs:897–956);
* `σ.k > domainLog2` — production's sub-SRS `chunk_size = 1` regime — is out of
  scope (the verifier rejects it).
-/

namespace Kimchi.Verifier

open CompElliptic.CurveForms.ShortWeierstrass
open Poseidon Poseidon.FqSponge Bulletproof

variable (C : Ipa.CommitmentCurve)

/-! ## The wire records -/

/-- An evaluation pair at the two batch points — production's `PointEvaluations`
(`proof.rs`): the column at `ζ` and at `ζω`. -/
structure PointEvaluations (F : Type*) where
  zeta : F
  zetaOmega : F
deriving Inhabited

/-- A wire polynomial commitment: the per-chunk commitment vector (`PolyComm.elems`,
`Vec<G>`). serde imposes NO length here — the chunk count is a verify-time check
(`checkChunks` against the run's `chunk_size`). -/
abbrev PolyComm (C : Ipa.CommitmentCurve) := Array C.Point

/-- The proof's claimed evaluations, one `PointEvaluations` per column family
(`ProofEvaluations`, proof.rs), generic in the per-point payload `E`: `Array F` on the
wire (chunk vectors of unchecked length), `Vector F nc` after `check`. The fixed
column counts (15 witness, 6 evaluated σ, 15 coefficient) are `[Evals; N]` in
production — serde-enforced, so type-level here. Optional gates and lookup data are
declared deferrals. -/
structure ProofEvaluations (E : Type*) where
  /-- The 15 witness-column evaluation pairs, `w[i] = (wᵢ(ζ), wᵢ(ζω))`. -/
  w : Vector (PointEvaluations E) 15
  /-- The permutation-aggregation evaluation pair. -/
  z : PointEvaluations E
  /-- The first 6 σ-polynomial evaluation pairs (the 7th is commitment-only). -/
  s : Vector (PointEvaluations E) 6
  /-- The 15 coefficient-column evaluation pairs. -/
  coefficients : Vector (PointEvaluations E) 15
  genericSelector : PointEvaluations E
  poseidonSelector : PointEvaluations E
  completeAddSelector : PointEvaluations E
  mulSelector : PointEvaluations E
  emulSelector : PointEvaluations E
  endomulScalarSelector : PointEvaluations E

/-- The kimchi proof wire record (`ProverProof` + `ProofEvaluations`, proof.rs:50–170),
basic gate set: fixed dimensions serde-typed, chunk payloads unchecked arrays. Lookup
data and `prev_challenges` are absent — declared deferrals of this transcription. -/
structure KimchiProof (C : Ipa.CommitmentCurve) where
  /-- The 15 witness-column commitments (`w_comm: [PolyComm; COLUMNS]`). -/
  wComm : Vector (PolyComm C) 15
  /-- The permutation-aggregation commitment (`z_comm`). -/
  zComm : PolyComm C
  /-- The quotient commitment (`t_comm`); its chunk count is checked `≤ 7 · nc`
  (verifier.rs:260–264). -/
  tComm : PolyComm C
  /-- The claimed evaluations, per column family and per chunk. -/
  evals : ProofEvaluations (Array C.ScalarField)
  /-- The carried public evaluations (production's `evals.public`, proof.rs:52 —
  `public` is a Lean keyword; carried at proof level rather than inside `evals`, a
  flattening choice only): REQUIRED when `nc > 1`; when present they take precedence
  over the barycentric computation at any `nc` (verifier.rs:332). -/
  pubEvals : Option (PointEvaluations (Array C.ScalarField))
  /-- `ft(ζω)` (Maller's optimization; proof.rs:170) — the ft row is single-chunk. -/
  ftEval1 : C.ScalarField
  /-- The batched IPA opening proof. -/
  opening : Ipa.Proof C

/-- The kimchi verifier index wire record (`VerifierIndex`, verifier_index.rs): fixed
dimensions serde-typed (`sigma_comm: [PolyComm; PERMUTS]`,
`coefficients_comm: [PolyComm; COLUMNS]`, `shift: [F; PERMUTS]`), chunk payloads
unchecked arrays. The SRS stays separate and universal; `nc` is derived in
`kimchiVerify` from the domain and the SRS width (`chunk_size = d1 / max_poly_size`,
verifier.rs:145–152). -/
structure KimchiVK (C : Ipa.CommitmentCurve) where
  /-- The domain size exponent: `n = 2 ^ domainLog2`. -/
  domainLog2 : ℕ
  /-- The domain generator `ω` (`domain.group_gen`). -/
  omega : C.ScalarField
  /-- The 7 permutation commitments (`sigma_comm`). -/
  sigmaComm : Vector (PolyComm C) 7
  /-- The 15 coefficient commitments (`coefficients_comm`). -/
  coefficientsComm : Vector (PolyComm C) 15
  genericComm : PolyComm C
  poseidonComm : PolyComm C
  completeAddComm : PolyComm C
  mulComm : PolyComm C
  emulComm : PolyComm C
  endomulScalarComm : PolyComm C
  /-- The 7 permutation shifts (`shift`). -/
  shifts : Vector C.ScalarField 7
  /-- The number of zero-knowledge rows (`zk_rows`) — nc-dependent in production
  (constraints.rs:774–784), carried as data here. -/
  zkRows : ℕ
  /-- `verifier_index.endo`, the `ft_eval0` endo coefficient. -/
  endo : C.ScalarField
  /-- The precomputed `VerifierIndex::digest()` — an input here. -/
  digest : C.BaseField
  /-- The Lagrange-basis commitments (`get_lagrange_basis` over a sub-domain SRS
  chunks every basis polynomial). -/
  lagrangeBasis : Array (PolyComm C)
  /-- The scalar-side Poseidon parameters (`G::sponge_params()`), for the fr-sponge. -/
  frParams : Params C.ScalarField

/-- The domain size `n = 2 ^ domainLog2` (`domain.size`). -/
def KimchiVK.n {C : Ipa.CommitmentCurve} (vk : KimchiVK C) : ℕ := 2 ^ vk.domainLog2

/-! ## The checked records

`check nc` is the verifier's own family of length checks — `check_proof_evals_len` at
`chunk_size` (verifier.rs:823–831), the `t` bound (:260–264), the `nc > 1`
public-evaluation requirement (:332–335) — factored as a total parse into a typed
core: a `Checked nc` record cannot hold a ragged proof, so every downstream read is
total and uniformity is definitional, not a proposition to re-derive. -/

/-- A chunk vector validated to the run's chunk count. -/
def checkChunks {α : Type*} (nc : ℕ) (a : Array α) : Option (Vector α nc) :=
  if h : a.size = nc then some ⟨a, h⟩ else none

/-- Validate an evaluation pair's chunk vectors. -/
def PointEvaluations.check {F : Type*} (nc : ℕ) (e : PointEvaluations (Array F)) :
    Option (PointEvaluations (Vector F nc)) := do
  return { zeta := ← checkChunks nc e.zeta, zetaOmega := ← checkChunks nc e.zetaOmega }

/-- Validate every evaluation pair of the record (`check_proof_evals_len`'s sweep). -/
def ProofEvaluations.check {F : Type*} (nc : ℕ) (e : ProofEvaluations (Array F)) :
    Option (ProofEvaluations (Vector F nc)) := do
  return { w := ← e.w.mapM (PointEvaluations.check nc)
           z := ← e.z.check nc
           s := ← e.s.mapM (PointEvaluations.check nc)
           coefficients := ← e.coefficients.mapM (PointEvaluations.check nc)
           genericSelector := ← e.genericSelector.check nc
           poseidonSelector := ← e.poseidonSelector.check nc
           completeAddSelector := ← e.completeAddSelector.check nc
           mulSelector := ← e.mulSelector.check nc
           emulSelector := ← e.emulSelector.check nc
           endomulScalarSelector := ← e.endomulScalarSelector.check nc }

/-- The public-evaluation source, resolving production's control flow
(verifier.rs:332–379): carried evaluations are accepted at any `nc` and REQUIRED at
`nc > 1`; the barycentric fallback exists only at `nc = 1` (it needs `ζ`, so it is
computed in the verifier body). -/
inductive PubEvalSrc (C : Ipa.CommitmentCurve) (nc : ℕ) where
  | carried (pe : PointEvaluations (Vector C.ScalarField nc))
  | barycentric (h : nc = 1)

/-- A chunk-validated proof: what `KimchiProof.check nc` returns, and the only thing
the verifier body and the soundness layer ever read. -/
structure KimchiProof.Checked (C : Ipa.CommitmentCurve) (nc : ℕ) where
  wComm : Vector (Vector C.Point nc) 15
  zComm : Vector C.Point nc
  /-- The quotient chunks: genuinely variable-length, so the bound is carried. -/
  tComm : Array C.Point
  tComm_le : tComm.size ≤ 7 * nc
  evals : ProofEvaluations (Vector C.ScalarField nc)
  pubEvals : PubEvalSrc C nc
  ftEval1 : C.ScalarField
  opening : Ipa.Proof C

/-- **The proof check** (`check_proof_evals_len` + the commitment-length checks, which
in production take `expected_size` as an argument — exactly this `nc`). -/
def KimchiProof.check {C : Ipa.CommitmentCurve} (nc : ℕ) (p : KimchiProof C) :
    Option (KimchiProof.Checked C nc) := do
  let wComm ← p.wComm.mapM (checkChunks nc)
  let zComm ← checkChunks nc p.zComm
  if htc : p.tComm.size ≤ 7 * nc then
    let evals ← p.evals.check nc
    let pubEvals ← match p.pubEvals with
      | some pe => (pe.check nc).map .carried
      | none => if h : nc = 1 then some (.barycentric h) else none
    return { wComm, zComm, tComm := p.tComm, tComm_le := htc, evals, pubEvals,
             ftEval1 := p.ftEval1, opening := p.opening }
  else none

/-- A chunk-validated verifier key. -/
structure KimchiVK.Checked (C : Ipa.CommitmentCurve) (nc : ℕ) where
  domainLog2 : ℕ
  omega : C.ScalarField
  sigmaComm : Vector (Vector C.Point nc) 7
  coefficientsComm : Vector (Vector C.Point nc) 15
  genericComm : Vector C.Point nc
  poseidonComm : Vector C.Point nc
  completeAddComm : Vector C.Point nc
  mulComm : Vector C.Point nc
  emulComm : Vector C.Point nc
  endomulScalarComm : Vector C.Point nc
  shifts : Vector C.ScalarField 7
  zkRows : ℕ
  endo : C.ScalarField
  digest : C.BaseField
  lagrangeBasis : Array (Vector C.Point nc)
  frParams : Params C.ScalarField

/-- **The key check**: every committed column validated to `nc` chunks. The Lagrange
basis is validated in FULL (production computes it from the SRS, where the chunking is
structural — `get_lagrange_basis` chunks every basis polynomial identically; a wire
key with ragged Lagrange data corresponds to no SRS and is rejected). -/
def KimchiVK.check {C : Ipa.CommitmentCurve} (nc : ℕ) (vk : KimchiVK C) :
    Option (KimchiVK.Checked C nc) := do
  return { domainLog2 := vk.domainLog2, omega := vk.omega
           sigmaComm := ← vk.sigmaComm.mapM (checkChunks nc)
           coefficientsComm := ← vk.coefficientsComm.mapM (checkChunks nc)
           genericComm := ← checkChunks nc vk.genericComm
           poseidonComm := ← checkChunks nc vk.poseidonComm
           completeAddComm := ← checkChunks nc vk.completeAddComm
           mulComm := ← checkChunks nc vk.mulComm
           emulComm := ← checkChunks nc vk.emulComm
           endomulScalarComm := ← checkChunks nc vk.endomulScalarComm
           shifts := vk.shifts, zkRows := vk.zkRows, endo := vk.endo
           digest := vk.digest
           lagrangeBasis := ← vk.lagrangeBasis.mapM (checkChunks nc)
           frParams := vk.frParams }

/-- `check` copies the scalar data: the checked key's domain exponent is the wire
key's. The one projection the run-level roots need across the check boundary (the
chunk count `runNc` is computed from the WIRE key). -/
theorem KimchiVK.check_domainLog2 {C : Ipa.CommitmentCurve} {nc : ℕ}
    {vk : KimchiVK C} {cvk : KimchiVK.Checked C nc}
    (h : vk.check nc = some cvk) : cvk.domainLog2 = vk.domainLog2 := by
  unfold KimchiVK.check at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq] at h
  obtain ⟨a1, -, a2, -, a3, -, a4, -, a5, -, a6, -, a7, -, a8, -, a9, -, heq⟩ := h
  subst heq
  rfl

/-- The domain size of a checked key. -/
def KimchiVK.Checked.n {C : Ipa.CommitmentCurve} {nc : ℕ}
    (cvk : KimchiVK.Checked C nc) : ℕ := 2 ^ cvk.domainLog2

/-- The fr-sponge spec of a checked key. -/
def KimchiVK.Checked.frSpec {C : Ipa.CommitmentCurve} {nc : ℕ}
    (cvk : KimchiVK.Checked C nc) : FqSponge.Spec C.scalar C.scalar :=
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
def frDigest (sp : FqSponge.Spec C.scalar C.scalar) (s : FqSponge.S C.scalar) :
    C.ScalarField :=
  (challengeFq sp s).1

/-- The fq-sponge digest (`DefaultFqSponge::digest`, sponge.rs:388–397): squeeze one base
element and cast it to the scalar field by `from_bigint`, which returns **zero when the
value does not fit** — not a modular reduction. The state is consumed (production takes
`mut self`); the caller keeps its pre-digest copy. -/
def fqDigest (s : FqSponge.S C.base) : C.ScalarField :=
  let (x, _) := challengeFq C.sponge s
  if x.val < C.scalar then ((x.val : ℕ) : C.ScalarField) else 0

/-! ## The Fiat-Shamir schedules -/

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
def pubDot {F : Type*} [Field F] (omega pt : F) (pub : Array F) : F :=
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

/-- The IPA acceptance from a **warm** sponge state: production hands the post-`ζ`
fq-sponge to the opening verifier (`BatchEvaluationProof { sponge: fq_sponge, .. }`,
verifier.rs:1184–1193). This is the verbatim body of `Ipa.transcript` + `Ipa.verify`
(Ipa.lean:158–229) with `FqSponge.init` replaced by `s₀` — duplicated because
`Kimchi/Verifier/Ipa.lean` is frozen and its `verify` (validated standalone against the
opening fixture) hard-codes the fresh start; unify later. The duplication, like the rest
of this module, is adjudicated by the production fixture. -/
def Ipa.verifyFrom (σ : SRS C.Point) (s₀ : FqSponge.S C.base) (inp : Ipa.Input C) :
    Bool :=
  if inp.proof.lr.size != σ.k || inp.evals.size != inp.commitments.size
      || inp.evals.any (·.size != inp.xs.size) then
    false
  else
    let s := absorbFr C.sponge s₀ (Ipa.shiftScalar C (Ipa.cipOf inp))
    let (t, s) := challengeFq C.sponge s
    let uBase := C.toGroup t
    let (chals, s) := inp.proof.lr.foldl
      (fun (acc : Array C.ScalarField × FqSponge.S C.base) LR =>
        let s := absorbG C.sponge (absorbG C.sponge acc.2 LR.1) LR.2
        let (u, s) := squeezeChallenge C.sponge s
        (acc.1.push u, s))
      (#[], s)
    let s := absorbG C.sponge s inp.proof.delta
    let (c, _) := squeezeChallenge C.sponge s
    let chal : Fin σ.k → C.ScalarField := fun i => chals[i.val]!
    let b0 := combinedB chal inp.evalscale (fun j : Fin inp.xs.size => inp.xs[j.val]!)
    let v := Ipa.cipOf inp
    let P := Ipa.combineCommitments C inp.polyscale inp.commitments
    let Q := (inp.proof.lr.zip chals).foldl
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
def fqOracles {nc : ℕ} (cvk : KimchiVK.Checked C nc) (cp : KimchiProof.Checked C nc)
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
def frOracles {nc : ℕ} (cvk : KimchiVK.Checked C nc) (cp : KimchiProof.Checked C nc)
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
def publicEvalChunks {C : Ipa.CommitmentCurve} {nc : ℕ} (cp : KimchiProof.Checked C nc)
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
def KimchiProof.Checked.linEvals {C : Ipa.CommitmentCurve} {nc : ℕ}
    (cp : KimchiProof.Checked C nc) (zetaM zetaOmegaM : C.ScalarField) :
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
def publicCommitment {nc : ℕ} (σ : SRS C.Point) (cvk : KimchiVK.Checked C nc)
    (pub : Array C.ScalarField) : Vector C.Point nc :=
  if pub.size = 0 then Vector.replicate nc σ.h
  else
    Vector.ofFn (fun (c : Fin nc) =>
      ((cvk.lagrangeBasis.extract 0 pub.size).zip pub).foldl
        (fun acc Pp => acc + (-Pp.2).val • Pp.1[c]) 0
      + σ.h)

/-! ## The verifier -/

/-- **The verifier body over checked records** (`to_batch` + the opening check,
verifier.rs:781–1194, one proof, basic gate set): the two remaining argument-dependent
guards (the public input against the domain and the Lagrange table); the per-chunk
public commitment; the Fiat-Shamir schedules at chunk absorbs; the scalar side on
chunk-COMBINED evaluations; the `ft_comm` double collapse at `ζ^max_poly_size`
(:960–965); the 45 logical rows in `to_batch` order flattened to the SEGMENT stream
(one flat row per chunk, ft single — the per-chunk polyscale walk of
`combined_inner_product`/`combine_commitments`); the warm-sponge IPA finish. -/
def verifyChecked {nc : ℕ} (σ : SRS C.Point) (cvk : KimchiVK.Checked C nc)
    (cp : KimchiProof.Checked C nc) (pub : Array C.ScalarField) : Bool :=
  let n := cvk.n
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
    let shifts : Fin 7 → C.ScalarField := fun i => cvk.shifts[i]
    let ftEval0 := Kimchi.Protocol.Linearization.ftEval0 n cvk.zkRows cvk.omega shifts
      cvk.endo (mdsOfParams cvk.frParams) o.alpha o.beta o.gamma o.zeta pubEval0 e
    let (v, u) := frOracles C cvk cp o.digest pubEvals
    let zkpmZ := Kimchi.Protocol.Linearization.zkpmEval n cvk.zkRows cvk.omega o.zeta
    let pScalar := Kimchi.Protocol.Linearization.permScalar o.beta o.gamma o.alpha zkpmZ e
    let fComm := cvk.sigmaComm[6].map (fun P => pScalar.val • P)
    let ftComm := Ipa.combineCommitments C zetaM fComm.toArray
      - (zetaN - 1).val • Ipa.combineCommitments C zetaM cp.tComm
    let logical : Array (Array C.Point × Array C.ScalarField × Array C.ScalarField) :=
      #[(publicComm.toArray, pubEvals.zeta.toArray, pubEvals.zetaOmega.toArray),
        (#[ftComm], #[ftEval0], #[cp.ftEval1]),
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
    let rows := logical.flatMap (fun r =>
      (r.1.zip (r.2.1.zip r.2.2)).map (fun ce => (ce.1, ce.2.1, ce.2.2)))
    let inp : Ipa.Input C :=
      { commitments := rows.map (·.1)
        xs := #[o.zeta, zetaOmega]
        evals := rows.map (fun r => #[r.2.1, r.2.2])
        polyscale := v
        evalscale := u
        proof := cp.opening }
    Ipa.verifyFrom C σ o.warm inp

/-- **The kimchi verifier**: check-then-verify. The SRS pin is
`n = nc · 2 ^ σ.k` with `nc = 2 ^ (domainLog2 − σ.k)` (production `chunk_size`,
uniform across the batch); `σ.k > domainLog2` — production's sub-SRS `chunk_size = 1`
regime — is rejected. Ragged wire data fails `check` and is rejected, the same
observable behavior as production's `Err` returns. -/
def kimchiVerify (σ : SRS C.Point) (vk : KimchiVK C) (p : KimchiProof C)
    (pub : Array C.ScalarField) : Bool :=
  if σ.k ≤ vk.domainLog2 then
    match vk.check (2 ^ (vk.domainLog2 - σ.k)), p.check (2 ^ (vk.domainLog2 - σ.k)) with
    | some cvk, some cp => verifyChecked C σ cvk cp pub
    | _, _ => false
  else false

/-! ## The wire views -/

/-- The committed-column view of a checked verifier key: the `IndexComms` over
per-chunk carriers (`Fin nc → C.Point`) the reduction speaks about — every read
total. The glue between the checked wire and the abstract capstones. -/
def KimchiVK.Checked.comms {C : Ipa.CommitmentCurve} {nc : ℕ}
    (cvk : KimchiVK.Checked C nc) : Kimchi.Verifier.IndexComms (Fin nc → C.Point) where
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

/-! ## The Pasta instantiations -/

namespace Kimchi.Verifier.KimchiVesta

open CompElliptic.Fields.Pasta Poseidon Kimchi.Verifier Bulletproof

abbrev Proof := KimchiProof IpaVesta.curve
abbrev VK := KimchiVK IpaVesta.curve

/-- The Vesta-side fr-sponge Poseidon parameters: the scalar field is `Fp`, so the
production `G::sponge_params()` is the `fp_kimchi` table. The fixture decoder pins
`KimchiVK.frParams` to this value. -/
def frParams : Params Fp := fpParams

def verify : Bulletproof.SRS IpaVesta.Point → VK → Proof → Array Fp → Bool :=
  kimchiVerify IpaVesta.curve

end Kimchi.Verifier.KimchiVesta

namespace Kimchi.Verifier.KimchiPallas

open CompElliptic.Fields.Pasta Poseidon Kimchi.Verifier Bulletproof

abbrev Proof := KimchiProof IpaPallas.curve
abbrev VK := KimchiVK IpaPallas.curve

/-- The Pallas-side fr-sponge Poseidon parameters: the scalar field is `Fq`, so the
production `G::sponge_params()` is the `fq_kimchi` table. The fixture decoder pins
`KimchiVK.frParams` to this value. -/
def frParams : Params Fq := fqParams

def verify : Bulletproof.SRS IpaPallas.Point → VK → Proof → Array Fq → Bool :=
  kimchiVerify IpaPallas.curve

end Kimchi.Verifier.KimchiPallas
