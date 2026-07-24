import Kimchi.Verifier.Kimchi

/-!
# W2 · The Fiat–Shamir transcript domain (fq-sponge side)

The deployed verifier derives its challenges by threading a concrete Poseidon sponge
(`fqOracles`, `Kimchi.Verifier.Kimchi`). The soundness proof needs those challenges as
reads of an abstract oracle at *transcript prefixes*, so that "the challenge is a fresh
draw made after the commitments are fixed" is visible in the domain and a random-oracle
idealization can be applied per challenge (`ironwood`'s `Forking.Oracle`).

This module supplies the domain: an inductive transcript-element type and the four fq-side
prefixes — the exact absorb sequences `fqOracles` runs before each of `β`, `γ`, `α`, `ζ`,
with an explicit squeeze marker per prior challenge (so consecutive squeezes read distinct
points, matching a duplex sponge's state consumption). `Forking.OracleRun` interprets a
prefix through the real sponge and proves these prefixes reproduce `fqOracles`'s
challenges; `Forking.Model` frames the game and states the random-oracle assumption.

The fr-sponge side (`v`, `u`) extends the same pattern in the second half of this module.
-/

namespace Kimchi.Verifier.Forking

open Bulletproof

variable {C : Ipa.CommitmentCurve} {nc k : ℕ}

/-- A single element written to the fq-sponge Fiat–Shamir transcript.

`fqPoint`/`fqBase` are the two absorb kinds `fqOracles` performs (a curve point via
`absorbG`, a base-field element via `absorbFq` — the verifying-key digest); `fqCast` and
`fqEndo` are the two squeeze kinds, marking a `challenge` (128-bit cast: `β`, `γ`) and a
`squeezeChallenge` (endomorphism expansion: `α`, `ζ`) respectively. A squeeze marker is
not re-absorbed; it records that a challenge was drawn, so a prefix ending in `n` markers
denotes the `n`-th squeeze. -/
inductive KimchiTranscriptElt (C : Ipa.CommitmentCurve) where
  /-- Absorb a curve point (`absorb_g`). -/
  | fqPoint : C.Point → KimchiTranscriptElt C
  /-- Absorb a base-field element (`absorb_fq`) — the verifying-key digest. -/
  | fqBase : C.BaseField → KimchiTranscriptElt C
  /-- A 128-bit cast squeeze (`challenge`): `β`, `γ`. -/
  | fqCast : KimchiTranscriptElt C
  /-- An endomorphism-expanded squeeze (`squeezeChallenge`): `α`, `ζ`. -/
  | fqEndo : KimchiTranscriptElt C

namespace KimchiTranscriptElt

open Poseidon

/-- The state action of a transcript element on the fq-sponge: the `.1` (state) component
of the interpreter step, isolated so it never mentions the running challenge value. Absorbs
absorb; squeezes advance the sponge past the squeezed challenge. -/
def absorbInto (C : Ipa.CommitmentCurve) :
    KimchiTranscriptElt C → FqSponge.S C.base → FqSponge.S C.base
  | fqPoint P, s => FqSponge.absorbG C.sponge s P
  | fqBase x, s => FqSponge.absorbFq C.sponge s [x]
  | fqCast, s => (FqSponge.challenge C.sponge s).2
  | fqEndo, s => (FqSponge.squeezeChallenge C.sponge s).2

/-- The `w_comm` witness commitments flattened to their point-absorb sequence, column by
column and chunk by chunk — `fqOracles`'s `cp.wComm.foldl (fun s col => col.foldl …)`. -/
def wCommAbsorbs (cp : KimchiProof C nc k) : List (KimchiTranscriptElt C) :=
  cp.wComm.toList.flatMap (fun col => col.toList.map fqPoint)

/-- The fq-sponge's pre-`β` absorb sequence: the VK digest, the public-input commitment
chunks, then the witness-column commitment chunks — verbatim the head of `fqOracles`. -/
def preAbsorbs (cvk : KimchiVK C nc) (cp : KimchiProof C nc k)
    (publicComm : Vector C.Point nc) : List (KimchiTranscriptElt C) :=
  fqBase cvk.digest :: (publicComm.toList.map fqPoint ++ wCommAbsorbs cp)

/-- The `β` prefix: the pre-absorbs then one cast squeeze. -/
def preBeta (cvk : KimchiVK C nc) (cp : KimchiProof C nc k)
    (publicComm : Vector C.Point nc) : List (KimchiTranscriptElt C) :=
  preAbsorbs cvk cp publicComm ++ [fqCast]

/-- The `γ` prefix: `β`'s prefix then a second cast squeeze. -/
def preGamma (cvk : KimchiVK C nc) (cp : KimchiProof C nc k)
    (publicComm : Vector C.Point nc) : List (KimchiTranscriptElt C) :=
  preBeta cvk cp publicComm ++ [fqCast]

/-- The `α` prefix: `γ`'s prefix, then the `z_comm` chunks, then an endo squeeze. -/
def preAlpha (cvk : KimchiVK C nc) (cp : KimchiProof C nc k)
    (publicComm : Vector C.Point nc) : List (KimchiTranscriptElt C) :=
  preGamma cvk cp publicComm ++ cp.zComm.toList.map fqPoint ++ [fqEndo]

/-- The `ζ` prefix: `α`'s prefix, then the `t_comm` chunks, then an endo squeeze. -/
def preZeta (cvk : KimchiVK C nc) (cp : KimchiProof C nc k)
    (publicComm : Vector C.Point nc) : List (KimchiTranscriptElt C) :=
  preAlpha cvk cp publicComm ++ cp.tComm.toList.map fqPoint ++ [fqEndo]

/-! ## Prefix distinctness

The four prefixes are pairwise distinct — each extends the previous by at least one element
(a squeeze marker, and for `α`/`ζ` a commitment segment too), so their lengths strictly
increase. Distinct transcript points is what makes a uniform oracle's four reads
independent, the hypothesis `Forking.Model`'s per-challenge freshness bounds consume. -/

theorem preBeta_ne_preGamma (cvk : KimchiVK C nc) (cp : KimchiProof C nc k)
    (publicComm : Vector C.Point nc) :
    preBeta cvk cp publicComm ≠ preGamma cvk cp publicComm := by
  intro h
  have hlen := congrArg List.length h
  simp only [preBeta, preGamma, preAbsorbs, wCommAbsorbs,
    List.length_append, List.length_cons, List.length_map, List.length_nil] at hlen
  omega

theorem preGamma_ne_preAlpha (cvk : KimchiVK C nc) (cp : KimchiProof C nc k)
    (publicComm : Vector C.Point nc) :
    preGamma cvk cp publicComm ≠ preAlpha cvk cp publicComm := by
  intro h
  have hlen := congrArg List.length h
  simp only [preBeta, preGamma, preAlpha, preAbsorbs, wCommAbsorbs,
    List.length_append, List.length_cons, List.length_map, List.length_nil] at hlen
  omega

theorem preAlpha_ne_preZeta (cvk : KimchiVK C nc) (cp : KimchiProof C nc k)
    (publicComm : Vector C.Point nc) :
    preAlpha cvk cp publicComm ≠ preZeta cvk cp publicComm := by
  intro h
  have hlen := congrArg List.length h
  simp only [preBeta, preGamma, preAlpha, preZeta, preAbsorbs, wCommAbsorbs,
    List.length_append, List.length_cons, List.length_map, List.length_nil] at hlen
  omega

theorem preBeta_ne_preAlpha (cvk : KimchiVK C nc) (cp : KimchiProof C nc k)
    (publicComm : Vector C.Point nc) :
    preBeta cvk cp publicComm ≠ preAlpha cvk cp publicComm := by
  intro h
  have hlen := congrArg List.length h
  simp only [preBeta, preGamma, preAlpha, preAbsorbs, wCommAbsorbs,
    List.length_append, List.length_cons, List.length_map, List.length_nil] at hlen
  omega

theorem preBeta_ne_preZeta (cvk : KimchiVK C nc) (cp : KimchiProof C nc k)
    (publicComm : Vector C.Point nc) :
    preBeta cvk cp publicComm ≠ preZeta cvk cp publicComm := by
  intro h
  have hlen := congrArg List.length h
  simp only [preBeta, preGamma, preAlpha, preZeta, preAbsorbs, wCommAbsorbs,
    List.length_append, List.length_cons, List.length_map, List.length_nil] at hlen
  omega

theorem preGamma_ne_preZeta (cvk : KimchiVK C nc) (cp : KimchiProof C nc k)
    (publicComm : Vector C.Point nc) :
    preGamma cvk cp publicComm ≠ preZeta cvk cp publicComm := by
  intro h
  have hlen := congrArg List.length h
  simp only [preBeta, preGamma, preAlpha, preZeta, preAbsorbs, wCommAbsorbs,
    List.length_append, List.length_cons, List.length_map, List.length_nil] at hlen
  omega

end KimchiTranscriptElt

/-! ## The fr-sponge side

The scalar-side (fr-)sponge derives the two batch challenges `v` (polyscale) and `u`
(evalscale). It is a *separate* Poseidon sponge (`frSpec C`, over `C.ScalarField`), fed the
fq-sponge digest and the proof's evaluations. Unlike the fq side it absorbs whole scalar
*lists* per `absorb_fr` call, so a transcript element carries a list; both squeezes are
endo-expanded (`challengeNat` then `endoExpand`), so there is one squeeze marker. -/

/-- A single element of the fr-sponge transcript: an `absorb_fr` of a whole scalar list (one
`absorbFq` call — the fr-sponge absorbs chunk vectors, not single elements), or an
endo-expanded squeeze (`challengeNat` then `endoExpand`): the `v`/`u` challenges. -/
inductive FrTranscriptElt (C : Ipa.CommitmentCurve) where
  /-- Absorb a scalar list in one `absorb_fr` call. -/
  | frAbsorb : List C.ScalarField → FrTranscriptElt C
  /-- An endo-expanded squeeze (`challengeNat` ∘ `endoExpand`): `v`, `u`. -/
  | frEndo : FrTranscriptElt C

namespace FrTranscriptElt

open Poseidon

/-- The state action of an fr element on the fr-sponge (the `.1` of the interpreter step). -/
def frAbsorbInto (C : Ipa.CommitmentCurve) :
    FrTranscriptElt C → FqSponge.S C.scalar → FqSponge.S C.scalar
  | frAbsorb xs, s => FqSponge.absorbFq (frSpec C) s xs
  | frEndo, s => (FqSponge.challengeNat (frSpec C) s).2

/-- `frOracles`'s `ab` for one evaluation pair, as two `absorb_fr` elements: the `ζ`-chunk
list then the `ζω`-chunk list. -/
def absorbEval (e : PointEvaluations (Vector C.ScalarField nc)) : List (FrTranscriptElt C) :=
  [frAbsorb e.zeta.toList, frAbsorb e.zetaOmega.toList]

/-- The fr-sponge's pre-`v` absorb sequence — verbatim `frOracles`'s absorbs before the first
squeeze: the fq digest, the fresh fr digest, `ft(ζω)`, the two public chunk vectors, then per
column the `ζ`/`ζω` chunk vectors in `absorb_evaluations` order (`z`, the six single
selectors, then the witness / coefficient / σ column folds). -/
def preVAbsorbs (cp : KimchiProof C nc k) (fqDig : C.ScalarField)
    (pubEvals : PointEvaluations (Vector C.ScalarField nc)) : List (FrTranscriptElt C) :=
  [frAbsorb [fqDig],
   frAbsorb [frDigest C (frSpec C) FqSponge.init],
   frAbsorb [cp.ftEval1],
   frAbsorb pubEvals.zeta.toList,
   frAbsorb pubEvals.zetaOmega.toList]
  ++ absorbEval cp.evals.z
  ++ absorbEval cp.evals.genericSelector
  ++ absorbEval cp.evals.poseidonSelector
  ++ absorbEval cp.evals.completeAddSelector
  ++ absorbEval cp.evals.mulSelector
  ++ absorbEval cp.evals.emulSelector
  ++ absorbEval cp.evals.endomulScalarSelector
  ++ cp.evals.w.toList.flatMap absorbEval
  ++ cp.evals.coefficients.toList.flatMap absorbEval
  ++ cp.evals.s.toList.flatMap absorbEval

/-- The `v` prefix: the pre-absorbs then one endo squeeze. -/
def preV (cp : KimchiProof C nc k) (fqDig : C.ScalarField)
    (pubEvals : PointEvaluations (Vector C.ScalarField nc)) : List (FrTranscriptElt C) :=
  preVAbsorbs cp fqDig pubEvals ++ [frEndo]

/-- The `u` prefix: `v`'s prefix then a second endo squeeze. -/
def preU (cp : KimchiProof C nc k) (fqDig : C.ScalarField)
    (pubEvals : PointEvaluations (Vector C.ScalarField nc)) : List (FrTranscriptElt C) :=
  preV cp fqDig pubEvals ++ [frEndo]

/-- `v` and `u` are read at distinct transcript points (`u` has one more squeeze marker). -/
theorem preV_ne_preU (cp : KimchiProof C nc k) (fqDig : C.ScalarField)
    (pubEvals : PointEvaluations (Vector C.ScalarField nc)) :
    preV cp fqDig pubEvals ≠ preU cp fqDig pubEvals := by
  intro h
  have hlen := congrArg List.length h
  simp only [preV, preU, List.length_append, List.length_cons, List.length_nil] at hlen
  omega

end FrTranscriptElt

end Kimchi.Verifier.Forking
