import Bulletproof.Wire
import Kimchi.Protocol.Linearization
import Poseidon.FqSponge

/-!
# The executable kimchi verifier

The full kimchi verifier over wire data, transcribed from proof-systems
`kimchi/src/verifier.rs`: the Fiat-Shamir argument (`oracles`, :126–634) and the partial
verification (`to_batch`, :781–1194), finished by the batched IPA opening check. The
scalar-side closed forms are the landed `Kimchi.Protocol.Linearization`
(`ftEval0`/`permScalar`/`zkpmEval`); the sponge layer is the landed
`Poseidon.FqSponge` machinery, reused at both fields; the opening finish is the
landed `Bulletproof.Ipa` acceptance, restarted from the **warm** fq-sponge state
(`BatchEvaluationProof { sponge: fq_sponge, .. }`, verifier.rs:1184–1193).

Scope (shape violations return `false`; every deferral is declared here):

* one evaluation chunk per column (`nc = 1`): the domain size is pinned to the SRS size
  by the guard `2 ^ σ.k = n` (the production `max_poly_size = n` regime), so `combine`
  is the identity and `ζ^max_poly_size = ζ^n`;
* no lookups (the wire records carry none) and no recursion (`prev_challenges` absent) —
  but the *constant* fr-sponge absorb of the empty recursion list's digest is
  transcribed (verifier.rs:290–299);
* the VK digest is an *input* (`KimchiVK.digest`); transcribing `VerifierIndex::digest()`
  (verifier_index.rs:399) is a declared deferral;
* `linearization.index_terms` is empty at the basic gate set, so `f_comm` is the single
  σ-commitment term (verifier.rs:897–956).

Fidelity is adjudicated against a production fixture outside this development; the
structure is kept verbatim (straight-line `let` schedules, per-column absorbs, the
production fold shapes) so any divergence localizes.

## Contents

* `KimchiProof`, `KimchiVK` — the wire records.
* `KimchiVK.frSpec`, `frDigest`, `fqDigest` — the fr-sponge instantiation and the two
  sponge digests.
* `FqOracles`, `fqOracles`, `frOracles` — the two Fiat-Shamir schedules.
* `powPow2`, `pubDot`, `publicEvals`, `KimchiProof.linEvals` — the scalar side.
* `publicCommitment` — the public-input commitment.
* `Ipa.verifyFrom` — the opening acceptance from a warm sponge state.
* `kimchiVerify` — the verifier.
* `KimchiVesta`, `KimchiPallas` — the Pasta instantiations.
-/

open Bulletproof

namespace Kimchi.Verifier

open Kimchi.Protocol

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

/-- The proof's claimed evaluations, one `PointEvaluations` per column family
(`ProofEvaluations`, proof.rs): the witness/permutation/coefficient columns and the six
gate selectors, each evaluated at `ζ` and `ζω`. At one chunk per column and the basic
gate set — optional gates and lookup data are declared deferrals. -/
structure ProofEvaluations (F : Type*) where
  /-- The 15 witness-column evaluation pairs, `w[i] = (wᵢ(ζ), wᵢ(ζω))`. -/
  w : Array (PointEvaluations F)
  /-- The permutation-aggregation evaluation pair. -/
  z : PointEvaluations F
  /-- The first 6 σ-polynomial evaluation pairs (the 7th is commitment-only). -/
  s : Array (PointEvaluations F)
  /-- The 15 coefficient-column evaluation pairs. -/
  coefficients : Array (PointEvaluations F)
  genericSelector : PointEvaluations F
  poseidonSelector : PointEvaluations F
  completeAddSelector : PointEvaluations F
  mulSelector : PointEvaluations F
  emulSelector : PointEvaluations F
  endomulScalarSelector : PointEvaluations F

/-- The kimchi proof wire record (`ProverProof` + `ProofEvaluations`, proof.rs:50–170),
at one chunk per column and the basic gate set: the witness/permutation/quotient
commitments, each evaluated column's pair `(at ζ, at ζω)`, `ft(ζω)`, and the IPA
opening. Optional gates, lookup data, carried `public` evaluations, and
`prev_challenges` are absent — declared deferrals of this transcription. -/
structure KimchiProof (C : Ipa.CommitmentCurve) where
  /-- The 15 witness-column commitments (`w_comm`). -/
  wComm : Array C.Point
  /-- The permutation-aggregation commitment (`z_comm`). -/
  zComm : C.Point
  /-- The 7 quotient chunks (`t_comm`). -/
  tComm : Array C.Point
  /-- The claimed evaluations at `(ζ, ζω)` per column family (`ProofEvaluations`). -/
  evals : ProofEvaluations C.ScalarField
  /-- `ft(ζω)` (Maller's optimization; proof.rs:170). -/
  ftEval1 : C.ScalarField
  /-- The batched IPA opening proof. -/
  opening : Ipa.Proof C

/-- The kimchi verifier index wire record (`VerifierIndex`, verifier_index.rs), reduced
to what the basic-gate verifier reads. `domainLog2` fixes the domain size
`n = 2 ^ domainLog2`. The SRS is NOT part of the key: it is universal, passed to
`kimchiVerify` separately (as in `Ipa.verify`) and pinned to the domain size there by
the `2 ^ σ.k = n` guard (`max_poly_size = n`). `endo` is the production `verifier_index.endo`
consumed by `ft_eval0` ONLY — challenge expansion uses the sponge spec's `C.sponge.lam`
(the curve's `endo_r`); the two agree in production but stay distinct here, as in the
sources. `digest` is the precomputed `VerifierIndex::digest()` (verifier_index.rs:399) —
an input, its computation a declared deferral. `frParams` are the scalar-side Poseidon
parameters (production `G::sponge_params()`), which the curve bundle does not carry. -/
structure KimchiVK (C : Ipa.CommitmentCurve) where
  /-- The domain size exponent: `n = 2 ^ domainLog2`. -/
  domainLog2 : ℕ
  /-- The domain generator `ω` (`domain.group_gen`). -/
  omega : C.ScalarField
  /-- The 7 permutation commitments (`sigma_comm`). -/
  sigmaComm : Array C.Point
  /-- The 15 coefficient commitments (`coefficients_comm`). -/
  coefficientsComm : Array C.Point
  genericComm : C.Point
  poseidonComm : C.Point
  completeAddComm : C.Point
  mulComm : C.Point
  emulComm : C.Point
  endomulScalarComm : C.Point
  /-- The 7 permutation shifts (`shift`). -/
  shifts : Array C.ScalarField
  /-- The number of zero-knowledge rows (`zk_rows`). -/
  zkRows : ℕ
  /-- `verifier_index.endo`, the `ft_eval0` endo coefficient (see the header note). -/
  endo : C.ScalarField
  /-- The precomputed `VerifierIndex::digest()` — an input here. -/
  digest : C.BaseField
  /-- The Lagrange-basis commitments for the public-input commitment. -/
  lagrangeBasis : Array C.Point
  /-- The scalar-side Poseidon parameters (`G::sponge_params()`), for the fr-sponge. -/
  frParams : Params C.ScalarField

/-- The domain size `n = 2 ^ domainLog2` (`domain.size`). -/
def KimchiVK.n {C : Ipa.CommitmentCurve} (vk : KimchiVK C) : ℕ := 2 ^ vk.domainLog2

/-! ## The fr-sponge and the sponge digests -/

/-- The fr-sponge (`DefaultFrSponge`, kimchi/src/plonk_sponge.rs): the generic `FqSponge`
machinery instantiated at the *scalar* field in both slots, over the VK's scalar-side
Poseidon parameters. This is the verbatim mirror: `DefaultFrSponge` is the same
`ArithmeticSponge` + `last_squeezed` limb buffer as `DefaultFqSponge`, at the scalar
field — its `absorb` is the buffer-clearing element absorb (`absorbFq`, one-element
lists; `absorb_multiple` folds it), its `challenge` the 128-bit limb-packed prechallenge
(`challengeNat`). The `lam` slot is never read by those ops (the fr-side endo expansion
happens at the *fq*-spec eigenvalue, in the schedule), so it is set to `0`. -/
def KimchiVK.frSpec {C : Ipa.CommitmentCurve} (vk : KimchiVK C) :
    FqSponge.Spec C.scalar C.scalar :=
  ⟨vk.frParams, 0⟩

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

/-- The fq-sponge schedule of `oracles` (verifier.rs:156–283), lookups and recursion
elided at scope: absorb the VK digest (:162–163), the public commitment (:171,
`absorb_commitment` is chunk-wise `absorbG` — one chunk here), the 15 witness
commitments (:174–177); squeeze the plain challenges `β` (:233) and `γ` (:236); absorb
`z_comm` (:250); squeeze the endo challenge `α` (:254–257); absorb the 7 quotient chunks
(:269); squeeze the endo challenge `ζ` (:273–276). The digest is of a copy (:283
clones); the warm state is returned alongside. -/
def fqOracles (vk : KimchiVK C) (p : KimchiProof C) (publicComm : C.Point) :
    FqOracles C :=
  let s := absorbFq C.sponge FqSponge.init [vk.digest]
  let s := absorbG C.sponge s publicComm
  let s := p.wComm.foldl (fun s P => absorbG C.sponge s P) s
  let (beta, s) := challenge C.sponge s
  let (gamma, s) := challenge C.sponge s
  let s := absorbG C.sponge s p.zComm
  let (alpha, s) := squeezeChallenge C.sponge s
  let s := p.tComm.foldl (fun s P => absorbG C.sponge s P) s
  let (zeta, s) := squeezeChallenge C.sponge s
  ⟨beta, gamma, alpha, zeta, fqDigest C s, s⟩

/-- The fr-sponge schedule (verifier.rs:284–405, `absorb_evaluations` from
kimchi/src/plonk_sponge.rs): fresh fr-sponge; absorb the fq digest (:287); absorb the
digest of a fresh fr-sponge that absorbed the — empty — recursion challenge list, a
required constant absorb (:290–299); absorb `ft(ζω)` (:382), then the two public
evaluations (:391–392, one-element `absorb_multiple`s at one chunk); absorb every
evaluation pair, column-`ζ` then column-`ζω`, in the `absorb_evaluations` order — `z`,
the six selectors (generic, poseidon, completeAdd, mul, emul, endomulScalar),
`w[0..15]`, `coefficients[0..15]`, `s[0..6]`; squeeze the endo challenges `v`
(:396–399) and `u` (:402–405) — 128-bit prechallenges expanded at the fq-spec
eigenvalue `C.sponge.lam` (the curve's `endo_r`). -/
def frOracles (vk : KimchiVK C) (p : KimchiProof C)
    (fqDig pubEval0 pubEval1 : C.ScalarField) : C.ScalarField × C.ScalarField :=
  let sp := vk.frSpec
  let ab := fun (s : FqSponge.S C.scalar) (e : PointEvaluations C.ScalarField) =>
    absorbFq sp (absorbFq sp s [e.zeta]) [e.zetaOmega]
  let s := absorbFq sp FqSponge.init [fqDig]
  let s := absorbFq sp s [frDigest C sp FqSponge.init]
  let s := absorbFq sp s [p.ftEval1]
  let s := absorbFq sp s [pubEval0]
  let s := absorbFq sp s [pubEval1]
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

/-- The proof's evaluation pairs as the linearization's `Evals` record (the verifier's
`evals.combine`, identity at one chunk — verifier.rs:409): `ζ`-components everywhere,
`ζω`-components for the witness and `z`. Indexing is `getElem!` — the shape guards of
`kimchiVerify` run first. -/
def KimchiProof.linEvals {C : Ipa.CommitmentCurve} (p : KimchiProof C) :
    Linearization.Evals C.ScalarField where
  w i := (p.evals.w[i.val]!).zeta
  wOmega i := (p.evals.w[i.val]!).zetaOmega
  z := p.evals.z.zeta
  zOmega := p.evals.z.zetaOmega
  s i := (p.evals.s[i.val]!).zeta
  coeffs i := (p.evals.coefficients[i.val]!).zeta
  genericSelector := p.evals.genericSelector.zeta
  poseidonSelector := p.evals.poseidonSelector.zeta
  completeAddSelector := p.evals.completeAddSelector.zeta
  mulSelector := p.evals.mulSelector.zeta
  emulSelector := p.evals.emulSelector.zeta
  endoScalarSelector := p.evals.endomulScalarSelector.zeta

/-! ## The group side -/

/-- The public-input commitment (verifier.rs:833–858): `srs.h` for empty input (the
`blinding_commitment()` chunk, :845); else the MSM of the Lagrange-basis commitments
against the **negated** public input (:847–848), masked with the all-ones blinder
(`mask_custom`, :849–856) — which adds `srs.h`. `commitment.rs` is not staged; the
`mask_custom` semantics (`+ 1 • h`) is corroborated by the empty-input branch and
adjudicated by the fixture. -/
def publicCommitment (σ : SRS C.Point) (vk : KimchiVK C)
    (pub : Array C.ScalarField) : C.Point :=
  if pub.size = 0 then σ.h
  else
    ((vk.lagrangeBasis.extract 0 pub.size).zip pub).foldl
      (fun acc Pp => acc + (-Pp.2).val • Pp.1) 0
    + σ.h

/-! ## The warm-start opening finish -/

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

/-! ## The verifier -/

/-- **The kimchi verifier** (`to_batch` + the opening check, verifier.rs:781–1194, one
proof, basic gate set): shape guards; the public commitment; the two Fiat-Shamir
schedules; the scalar side through the landed closed forms (`Linearization.ftEval0` /
`permScalar` / `zkpmEval`); `f_comm` (:897–956 — `linearization.index_terms` is empty at
this gate set, so the single σ-commitment term) and the chunked `ft_comm` (:960–965, at
`ζ^max_poly_size = ζⁿ` under the SRS pin; `f_comm` is one chunk, so its chunking is the
identity); the 45 evaluation rows in the `to_batch` order (:967–1071: public, ft, `z`,
the six selectors, `w[0..15]`, `coefficients[0..15]`, `sigma[0..6]`; recursion rows
absent at scope); the warm-sponge IPA finish (:1183–1193).

The guard `2 ^ σ.k = n` is the `max_poly_size = n` pin: every polynomial is one chunk
(`nc = 1`), `chunk_commitment` collapses to a `ζⁿ`-power fold, and the chunk-combination
of evaluations is the identity. -/
def kimchiVerify (σ : SRS C.Point) (vk : KimchiVK C) (p : KimchiProof C)
    (pub : Array C.ScalarField) : Bool :=
  let n := vk.n
  if p.wComm.size != 15 || p.tComm.size != 7 || p.evals.w.size != 15 || p.evals.s.size != 6
      || p.evals.coefficients.size != 15 || vk.sigmaComm.size != 7
      || vk.coefficientsComm.size != 15 || vk.shifts.size != 7
      || decide (vk.lagrangeBasis.size < pub.size) || decide (n < pub.size)
      || 2 ^ σ.k != n then
    false
  else
    let publicComm := publicCommitment C σ vk pub
    let o := fqOracles C vk p publicComm
    let zetaOmega := o.zeta * vk.omega
    let zetaN := powPow2 o.zeta vk.domainLog2
    let zetaOmegaN := powPow2 zetaOmega vk.domainLog2
    let (pubEval0, pubEval1) :=
      publicEvals n vk.omega o.zeta zetaOmega zetaN zetaOmegaN pub
    let e := p.linEvals
    let shifts : Fin 7 → C.ScalarField := fun i => vk.shifts[i.val]!
    let ftEval0 := Linearization.ftEval0 n vk.zkRows vk.omega shifts vk.endo
      o.alpha o.beta o.gamma o.zeta pubEval0 e
    let (v, u) := frOracles C vk p o.digest pubEval0 pubEval1
    let zkpmZ := Linearization.zkpmEval n vk.zkRows vk.omega o.zeta
    let pScalar := Linearization.permScalar o.beta o.gamma o.alpha zkpmZ e
    let fComm := pScalar.val • vk.sigmaComm.getD 6 0
    let ftComm := fComm - (zetaN - 1).val • Ipa.combineCommitments C zetaN p.tComm
    let rows : Array (C.Point × C.ScalarField × C.ScalarField) :=
      #[(publicComm, pubEval0, pubEval1),
        (ftComm, ftEval0, p.ftEval1),
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
    let inp : Ipa.Input C :=
      { commitments := rows.map (·.1)
        xs := #[o.zeta, zetaOmega]
        evals := rows.map (fun r => #[r.2.1, r.2.2])
        polyscale := v
        evalscale := u
        proof := p.opening }
    Ipa.verifyFrom C σ o.warm inp

end Kimchi.Verifier

/-! ## The Pasta instantiations -/

namespace Kimchi.Verifier.KimchiVesta

open CompElliptic.Fields.Pasta Poseidon Kimchi.Verifier

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

open CompElliptic.Fields.Pasta Poseidon Kimchi.Verifier

abbrev Proof := KimchiProof IpaPallas.curve
abbrev VK := KimchiVK IpaPallas.curve

/-- The Pallas-side fr-sponge Poseidon parameters: the scalar field is `Fq`, so the
production `G::sponge_params()` is the `fq_kimchi` table. The fixture decoder pins
`KimchiVK.frParams` to this value. -/
def frParams : Params Fq := fqParams


def verify : Bulletproof.SRS IpaPallas.Point → VK → Proof → Array Fq → Bool :=
  kimchiVerify IpaPallas.curve

end Kimchi.Verifier.KimchiPallas
