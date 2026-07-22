import Bulletproof.Wire
import Kimchi.Protocol.Linearization
import Kimchi.Verifier.Reduction.Correspond
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
plain first squeeze — same field, no cast. Shared with the chunked verifier
(`Kimchi/Verifier/Chunked.lean`). -/
def frDigest (sp : FqSponge.Spec C.scalar C.scalar) (s : FqSponge.S C.scalar) :
    C.ScalarField :=
  (challengeFq sp s).1

/-- The fq-sponge digest (`DefaultFqSponge::digest`, sponge.rs:388–397): squeeze one base
element and cast it to the scalar field by `from_bigint`, which returns **zero when the
value does not fit** — not a modular reduction. The state is consumed (production takes
`mut self`); the caller keeps its pre-digest copy. Shared with the chunked verifier
(`Kimchi/Verifier/Chunked.lean`). -/
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

/-! ## The verifier -/

/-- The public-input array as the `Fin idx.publicCount`-indexed function the circuit
model consumes (`getD`, total; the capstones pin `pub.size = idx.publicCount`, so the
view reads only genuine entries). The wire-to-abstract public view. -/
def pubView {F : Type*} [Field F] {n : ℕ} (idx : Index F n) (pub : Array F) :
    Fin idx.publicCount → F :=
  fun i => pub.getD (i : ℕ) 0

end Kimchi.Verifier
