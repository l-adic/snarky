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

The fr-sponge side (`v`, `u`) extends the same pattern and is developed separately.
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
  sorry

theorem preGamma_ne_preAlpha (cvk : KimchiVK C nc) (cp : KimchiProof C nc k)
    (publicComm : Vector C.Point nc) :
    preGamma cvk cp publicComm ≠ preAlpha cvk cp publicComm := by
  sorry

theorem preAlpha_ne_preZeta (cvk : KimchiVK C nc) (cp : KimchiProof C nc k)
    (publicComm : Vector C.Point nc) :
    preAlpha cvk cp publicComm ≠ preZeta cvk cp publicComm := by
  sorry

theorem preBeta_ne_preAlpha (cvk : KimchiVK C nc) (cp : KimchiProof C nc k)
    (publicComm : Vector C.Point nc) :
    preBeta cvk cp publicComm ≠ preAlpha cvk cp publicComm := by
  sorry

theorem preBeta_ne_preZeta (cvk : KimchiVK C nc) (cp : KimchiProof C nc k)
    (publicComm : Vector C.Point nc) :
    preBeta cvk cp publicComm ≠ preZeta cvk cp publicComm := by
  sorry

theorem preGamma_ne_preZeta (cvk : KimchiVK C nc) (cp : KimchiProof C nc k)
    (publicComm : Vector C.Point nc) :
    preGamma cvk cp publicComm ≠ preZeta cvk cp publicComm := by
  sorry

end KimchiTranscriptElt

end Kimchi.Verifier.Forking
