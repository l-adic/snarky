import Kimchi.Verifier.Kimchi

/-!
# The chunked executable kimchi verifier (`nc ≥ 1`)

The kimchi verifier over wire data in the production CHUNKED regime: domain size
`n = nc · max_poly_size` with `max_poly_size = 2 ^ σ.k` the SRS width, every
degree-`< n` column committed and evaluated in `nc` chunks (`chunk_size`,
verifier.rs:145–152). This module generalizes `Kimchi/Verifier/Kimchi.lean` — the
`nc = 1` transcription pinned by the guard `2 ^ σ.k = n` — to any power-of-two `nc`,
transcribing the chunked paths of proof-systems `kimchi/src/verifier.rs`:

* wire records mirror `PolyComm`: a committed column is its chunk vector
  (`Array C.Point`), an evaluation is per-chunk (`PointEvaluations (Array F)`), and the
  proof carries the production-optional `public` evaluations — REQUIRED when `nc > 1`
  (`MissingPublicInputEvaluation`, verifier.rs:332–335; the barycentric fallback exists
  only at one chunk);
* the scalar side runs on chunk-COMBINED evaluations
  (`evals.combine(&powers_of_eval_points_for_chunks)`, :409): every column combined at
  `ζ^max_poly_size` / `(ζω)^max_poly_size` (`combineAt`), including the public term of
  `ft_eval0` (:441–443);
* `ft_comm` collapses BOTH sides at `ζ^max_poly_size` (:960–965): `f_comm` — the
  `pScalar`-scaled `sigma_comm[6]`, itself `nc` chunks — and `t_comm` (up to `7·nc`
  chunks, :260–264) each `chunk_commitment`-folded to one point;
* the IPA input is the flat SEGMENT stream: `combined_inner_product` and
  `combine_commitments` (poly-commitment/src/commitment.rs:612–734) walk the batch rows
  in order and advance one polyscale power PER CHUNK, so each logical row contributes
  its `nc` chunks as consecutive flat rows (the ft row: one).

This is a TRANSITIONAL parallel module: the `nc = 1` verifier and its reflection
(`Reflect.lean`, the capstones) stay in place until the reduction and terminals are
restated at the chunked wire; this verifier is adjudicated now, against the `nc = 2`
production fixtures AND the one-chunk fixture (the no-regression check). Lookups,
optional gates, and recursion stay declared deferrals, as does the `max_poly_size > n`
regime (production's `chunk_size = 1` short-circuit for sub-SRS domains).

## Contents

* `KimchiProof`, `KimchiVK` — the chunked wire records.
* `fqOracles`, `frOracles` — the Fiat-Shamir schedules at chunk absorbs.
* `combineAt`, `publicEvalChunks`, `KimchiProof.linEvals` — the combined scalar side.
* `publicCommitment` — the per-chunk public-input commitment.
* `kimchiVerify` — the chunked verifier.
* `KimchiVesta`, `KimchiPallas` — the Pasta instantiations.
-/

open Bulletproof

namespace Kimchi.Verifier.Chunked

open CompElliptic.CurveForms.ShortWeierstrass
open Poseidon Poseidon.FqSponge Bulletproof

variable (C : Ipa.CommitmentCurve)

/-! ## The wire records -/

/-- The kimchi proof wire record (`ProverProof` + `ProofEvaluations`, proof.rs:50–170)
in chunk shape, basic gate set: each committed column is its chunk vector, each
evaluation a per-chunk `PointEvaluations (Array F)` (the parent record at the array
payload), plus the production-optional carried `public` evaluations. Lookup data and
`prev_challenges` are absent — declared deferrals of this transcription. -/
structure KimchiProof (C : Ipa.CommitmentCurve) where
  /-- The 15 witness-column commitments (`w_comm`), each `nc` chunks. -/
  wComm : Array (Array C.Point)
  /-- The permutation-aggregation commitment (`z_comm`), `nc` chunks. -/
  zComm : Array C.Point
  /-- The quotient chunks (`t_comm`), at most `7 · nc` (verifier.rs:260–264). -/
  tComm : Array C.Point
  /-- The claimed evaluations, per column family and per chunk. -/
  evals : ProofEvaluations (Array C.ScalarField)
  /-- The carried public evaluations (production's `evals.public`, proof.rs:52 —
  `public` is a Lean keyword): REQUIRED when `nc > 1`; when present they take
  precedence over the barycentric computation at any `nc` (verifier.rs:332). -/
  pubEvals : Option (PointEvaluations (Array C.ScalarField))
  /-- `ft(ζω)` (Maller's optimization; proof.rs:170) — the ft row is single-chunk. -/
  ftEval1 : C.ScalarField
  /-- The batched IPA opening proof. -/
  opening : Ipa.Proof C

/-- The kimchi verifier index wire record (`VerifierIndex`, verifier_index.rs) in chunk
shape: as the `nc = 1` `KimchiVK`, with every committed column an `Array C.Point` of
chunks and each Lagrange-basis commitment a chunk vector. The SRS stays separate and
universal; `nc` is derived in `kimchiVerify` from the domain and the SRS width
(`chunk_size = d1 / max_poly_size`, verifier.rs:145–152). See the `nc = 1` record for
the `endo`/`digest`/`frParams` notes — unchanged here. -/
structure KimchiVK (C : Ipa.CommitmentCurve) where
  /-- The domain size exponent: `n = 2 ^ domainLog2`. -/
  domainLog2 : ℕ
  /-- The domain generator `ω` (`domain.group_gen`). -/
  omega : C.ScalarField
  /-- The 7 permutation commitments (`sigma_comm`), each `nc` chunks. -/
  sigmaComm : Array (Array C.Point)
  /-- The 15 coefficient commitments (`coefficients_comm`), each `nc` chunks. -/
  coefficientsComm : Array (Array C.Point)
  genericComm : Array C.Point
  poseidonComm : Array C.Point
  completeAddComm : Array C.Point
  mulComm : Array C.Point
  emulComm : Array C.Point
  endomulScalarComm : Array C.Point
  /-- The 7 permutation shifts (`shift`). -/
  shifts : Array C.ScalarField
  /-- The number of zero-knowledge rows (`zk_rows`) — nc-dependent in production
  (constraints.rs:774–784), carried as data here. -/
  zkRows : ℕ
  /-- `verifier_index.endo`, the `ft_eval0` endo coefficient. -/
  endo : C.ScalarField
  /-- The precomputed `VerifierIndex::digest()` — an input here. -/
  digest : C.BaseField
  /-- The Lagrange-basis commitments, each `nc` chunks (`get_lagrange_basis` over a
  sub-domain SRS chunks every basis polynomial). -/
  lagrangeBasis : Array (Array C.Point)
  /-- The scalar-side Poseidon parameters (`G::sponge_params()`), for the fr-sponge. -/
  frParams : Params C.ScalarField

/-- The domain size `n = 2 ^ domainLog2` (`domain.size`). -/
def KimchiVK.n {C : Ipa.CommitmentCurve} (vk : KimchiVK C) : ℕ := 2 ^ vk.domainLog2

/-- The fr-sponge spec, as in the `nc = 1` key: the scalar-side parameters, `lam`
unread. -/
def KimchiVK.frSpec {C : Ipa.CommitmentCurve} (vk : KimchiVK C) :
    FqSponge.Spec C.scalar C.scalar :=
  ⟨vk.frParams, 0⟩

/-! ## The Fiat-Shamir schedules -/

/-- The fq-sponge schedule of `oracles` (verifier.rs:156–283) at chunked commitments:
identical structure to the `nc = 1` schedule — `absorb_commitment` is chunk-wise
`absorbG`, so the public-commitment and per-column absorbs become chunk folds and the
absorb streams lengthen; the squeeze schedule is unchanged. -/
def fqOracles (vk : KimchiVK C) (p : KimchiProof C) (publicComm : Array C.Point) :
    FqOracles C :=
  let s := absorbFq C.sponge FqSponge.init [vk.digest]
  let s := publicComm.foldl (absorbG C.sponge) s
  let s := p.wComm.foldl (fun s col => col.foldl (absorbG C.sponge) s) s
  let (beta, s) := challenge C.sponge s
  let (gamma, s) := challenge C.sponge s
  let s := p.zComm.foldl (absorbG C.sponge) s
  let (alpha, s) := squeezeChallenge C.sponge s
  let s := p.tComm.foldl (absorbG C.sponge) s
  let (zeta, s) := squeezeChallenge C.sponge s
  ⟨beta, gamma, alpha, zeta, fqDigest C s, s⟩

/-- The fr-sponge schedule (verifier.rs:284–405) at chunked evaluations: as the `nc = 1`
schedule, with every absorb widened to the column's chunk vector — the two public
chunk vectors via `absorb_multiple` (:391–392), then per column the `ζ`-chunk vector
and the `ζω`-chunk vector (`absorb_evaluations`, plonk_sponge.rs: one `sponge.absorb`
per point vector), in the `absorb_evaluations` order. -/
def frOracles (vk : KimchiVK C) (p : KimchiProof C) (fqDig : C.ScalarField)
    (pubEvals : PointEvaluations (Array C.ScalarField)) :
    C.ScalarField × C.ScalarField :=
  let sp := vk.frSpec
  let ab := fun (s : FqSponge.S C.scalar) (e : PointEvaluations (Array C.ScalarField)) =>
    absorbFq sp (absorbFq sp s e.zeta.toList) e.zetaOmega.toList
  let s := absorbFq sp FqSponge.init [fqDig]
  let s := absorbFq sp s [frDigest C sp FqSponge.init]
  let s := absorbFq sp s [p.ftEval1]
  let s := absorbFq sp s pubEvals.zeta.toList
  let s := absorbFq sp s pubEvals.zetaOmega.toList
  let s := ab s p.evals.z
  let s := ab s p.evals.genericSelector
  let s := ab s p.evals.poseidonSelector
  let s := ab s p.evals.completeAddSelector
  let s := ab s p.evals.mulSelector
  let s := ab s p.evals.emulSelector
  let s := ab s p.evals.endomulScalarSelector
  let s := p.evals.w.foldl ab s
  let s := p.evals.coefficients.foldl ab s
  let s := p.evals.s.foldl ab s
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
barycentric computation (the `nc = 1`-only branch — `kimchiVerify` guards
`nc = 1` when `public` is absent). -/
def publicEvalChunks {C : Ipa.CommitmentCurve} (p : KimchiProof C) (n : ℕ)
    (omega zeta zetaOmega zetaN zetaOmegaN : C.ScalarField) (pub : Array C.ScalarField) :
    PointEvaluations (Array C.ScalarField) :=
  match p.pubEvals with
  | some pe => pe
  | none =>
    let (e0, e1) := publicEvals n omega zeta zetaOmega zetaN zetaOmegaN pub
    ⟨#[e0], #[e1]⟩

/-- The proof's evaluations, chunk-combined, as the linearization's `Evals` record —
the verifier's `evals.combine(&powers_of_eval_points_for_chunks)` (verifier.rs:409):
every column combined at `ζ^max_poly_size` (`ζω`-side values at `(ζω)^max_poly_size`).
Indexing is `getElem!` — the shape guards of `kimchiVerify` run first. -/
def KimchiProof.linEvals {C : Ipa.CommitmentCurve} (p : KimchiProof C)
    (zetaM zetaOmegaM : C.ScalarField) :
    Kimchi.Protocol.Linearization.Evals C.ScalarField where
  w i := combineAt zetaM (p.evals.w[i.val]!).zeta
  wOmega i := combineAt zetaOmegaM (p.evals.w[i.val]!).zetaOmega
  z := combineAt zetaM p.evals.z.zeta
  zOmega := combineAt zetaOmegaM p.evals.z.zetaOmega
  s i := combineAt zetaM (p.evals.s[i.val]!).zeta
  coeffs i := combineAt zetaM (p.evals.coefficients[i.val]!).zeta
  genericSelector := combineAt zetaM p.evals.genericSelector.zeta
  poseidonSelector := combineAt zetaM p.evals.poseidonSelector.zeta
  completeAddSelector := combineAt zetaM p.evals.completeAddSelector.zeta
  mulSelector := combineAt zetaM p.evals.mulSelector.zeta
  emulSelector := combineAt zetaM p.evals.emulSelector.zeta
  endoScalarSelector := combineAt zetaM p.evals.endomulScalarSelector.zeta

/-! ## The group side -/

/-- The public-input commitment, per chunk (verifier.rs:833–858): empty input gives
`nc` copies of the blinding commitment `srs.h` (:845); else chunk `c` is the MSM of the
`c`-chunks of the Lagrange-basis commitments against the negated public input
(`PolyComm::multi_scalar_mul` is chunk-wise, commitment.rs:348–378), plus `srs.h` from
the all-ones `mask_custom` blinder applied per chunk (:849–856; ipa.rs:497–514). -/
def publicCommitment (σ : SRS C.Point) (vk : KimchiVK C) (nc : ℕ)
    (pub : Array C.ScalarField) : Array C.Point :=
  if pub.size = 0 then Array.replicate nc σ.h
  else
    (Array.range nc).map (fun c =>
      ((vk.lagrangeBasis.extract 0 pub.size).zip pub).foldl
        (fun acc Pp => acc + (-Pp.2).val • Pp.1.getD c 0) 0
      + σ.h)

/-! ## The verifier -/

/-- **The chunked kimchi verifier** (`to_batch` + the opening check,
verifier.rs:781–1194, one proof, basic gate set, any power-of-two `nc`): shape guards
(the per-column chunk counts — `check_proof_evals_len` at `chunk_size`, :823–831 — the
`t` bound `≤ 7·nc`, :260–264, and the `nc > 1` public-evaluation requirement,
:332–335); the per-chunk public commitment; the Fiat-Shamir schedules at chunk absorbs;
the scalar side on chunk-COMBINED evaluations through the landed closed forms; the
`ft_comm` double collapse at `ζ^max_poly_size` (:960–965); the 45 logical rows in
`to_batch` order flattened to the SEGMENT stream (one flat row per chunk, ft single —
the per-chunk polyscale walk of `combined_inner_product`/`combine_commitments`); the
warm-sponge IPA finish.

The SRS pin generalizes to `n = nc · 2 ^ σ.k` with `nc = 2 ^ (domainLog2 − σ.k)`
(production `chunk_size`, uniform across the batch); `σ.k > domainLog2` — production's
sub-SRS `chunk_size = 1` regime — stays out of scope. -/
def kimchiVerify (σ : SRS C.Point) (vk : KimchiVK C) (p : KimchiProof C)
    (pub : Array C.ScalarField) : Bool :=
  let n := vk.n
  let nc := 2 ^ (vk.domainLog2 - σ.k)
  let comm1 := fun (a : Array C.Point) => a.size == nc
  let commN := fun (a : Array (Array C.Point)) (m : ℕ) => a.size == m && a.all comm1
  let evalN := fun (e : PointEvaluations (Array C.ScalarField)) =>
    e.zeta.size == nc && e.zetaOmega.size == nc
  if decide (vk.domainLog2 < σ.k) || !commN p.wComm 15 || !comm1 p.zComm
      || decide (7 * nc < p.tComm.size)
      || p.evals.w.size != 15 || p.evals.s.size != 6 || p.evals.coefficients.size != 15
      || !(p.evals.w.all evalN) || !(p.evals.s.all evalN)
      || !(p.evals.coefficients.all evalN)
      || !evalN p.evals.z || !evalN p.evals.genericSelector
      || !evalN p.evals.poseidonSelector || !evalN p.evals.completeAddSelector
      || !evalN p.evals.mulSelector || !evalN p.evals.emulSelector
      || !evalN p.evals.endomulScalarSelector
      || !(match p.pubEvals with | some pe => evalN pe | none => nc == 1)
      || !commN vk.sigmaComm 7 || !commN vk.coefficientsComm 15
      || !comm1 vk.genericComm || !comm1 vk.poseidonComm || !comm1 vk.completeAddComm
      || !comm1 vk.mulComm || !comm1 vk.emulComm || !comm1 vk.endomulScalarComm
      || vk.shifts.size != 7
      || decide (vk.lagrangeBasis.size < pub.size)
      || !((vk.lagrangeBasis.extract 0 pub.size).all comm1)
      || decide (n < pub.size) then
    false
  else
    let publicComm := publicCommitment C σ vk nc pub
    let o := fqOracles C vk p publicComm
    let zetaOmega := o.zeta * vk.omega
    let zetaN := powPow2 o.zeta vk.domainLog2
    let zetaOmegaN := powPow2 zetaOmega vk.domainLog2
    let zetaM := powPow2 o.zeta σ.k
    let zetaOmegaM := powPow2 zetaOmega σ.k
    let pubEvals := publicEvalChunks p n vk.omega o.zeta zetaOmega zetaN zetaOmegaN pub
    let pubEval0 := combineAt zetaM pubEvals.zeta
    let e := p.linEvals zetaM zetaOmegaM
    let shifts : Fin 7 → C.ScalarField := fun i => vk.shifts[i.val]!
    let ftEval0 := Kimchi.Protocol.Linearization.ftEval0 n vk.zkRows vk.omega shifts vk.endo
      (mdsOfParams vk.frParams) o.alpha o.beta o.gamma o.zeta pubEval0 e
    let (v, u) := frOracles C vk p o.digest pubEvals
    let zkpmZ := Kimchi.Protocol.Linearization.zkpmEval n vk.zkRows vk.omega o.zeta
    let pScalar := Kimchi.Protocol.Linearization.permScalar o.beta o.gamma o.alpha zkpmZ e
    let fComm := (vk.sigmaComm.getD 6 #[]).map (fun P => pScalar.val • P)
    let ftComm := Ipa.combineCommitments C zetaM fComm
      - (zetaN - 1).val • Ipa.combineCommitments C zetaM p.tComm
    let logical : Array (Array C.Point × Array C.ScalarField × Array C.ScalarField) :=
      #[(publicComm, pubEvals.zeta, pubEvals.zetaOmega),
        (#[ftComm], #[ftEval0], #[p.ftEval1]),
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
    let rows := logical.flatMap (fun r =>
      (r.1.zip (r.2.1.zip r.2.2)).map (fun ce => (ce.1, ce.2.1, ce.2.2)))
    let inp : Ipa.Input C :=
      { commitments := rows.map (·.1)
        xs := #[o.zeta, zetaOmega]
        evals := rows.map (fun r => #[r.2.1, r.2.2])
        polyscale := v
        evalscale := u
        proof := p.opening }
    Ipa.verifyFrom C σ o.warm inp

/-! ## The wire views -/

/-- The committed-column view of a chunked wire verifier key at chunk count `nc`: the
`IndexComms` over per-chunk carriers (`Fin nc → C.Point`) the chunked reduction speaks
about, read off the key's chunk arrays (`getD` at the checked sizes). The glue between
the chunked wire `KimchiVK` and the abstract capstones. -/
def KimchiVK.comms {C : Ipa.CommitmentCurve} (vk : KimchiVK C) (nc : ℕ) :
    Kimchi.Verifier.IndexComms (Fin nc → C.Point) where
  sigma i c := (vk.sigmaComm.getD (i : ℕ) #[]).getD (c : ℕ) 0
  coefficients cc c := (vk.coefficientsComm.getD (cc : ℕ) #[]).getD (c : ℕ) 0
  generic c := vk.genericComm.getD (c : ℕ) 0
  poseidon c := vk.poseidonComm.getD (c : ℕ) 0
  completeAdd c := vk.completeAddComm.getD (c : ℕ) 0
  varBaseMul c := vk.mulComm.getD (c : ℕ) 0
  endoMul c := vk.emulComm.getD (c : ℕ) 0
  endoScalar c := vk.endomulScalarComm.getD (c : ℕ) 0

end Kimchi.Verifier.Chunked

/-! ## The Pasta instantiations -/

namespace Kimchi.Verifier.Chunked.KimchiVesta

open CompElliptic.Fields.Pasta Poseidon Kimchi.Verifier

abbrev Proof := Chunked.KimchiProof IpaVesta.curve
abbrev VK := Chunked.KimchiVK IpaVesta.curve

def verify : Bulletproof.SRS IpaVesta.Point → VK → Proof → Array Fp → Bool :=
  Chunked.kimchiVerify IpaVesta.curve

end Kimchi.Verifier.Chunked.KimchiVesta

namespace Kimchi.Verifier.Chunked.KimchiPallas

open CompElliptic.Fields.Pasta Poseidon Kimchi.Verifier

abbrev Proof := Chunked.KimchiProof IpaPallas.curve
abbrev VK := Chunked.KimchiVK IpaPallas.curve

def verify : Bulletproof.SRS IpaPallas.Point → VK → Proof → Array Fq → Bool :=
  Chunked.kimchiVerify IpaPallas.curve

end Kimchi.Verifier.Chunked.KimchiPallas
