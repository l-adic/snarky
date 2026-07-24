import Kimchi.Verifier.Forking.Transcript

/-!
# W2 · Interpreting a transcript prefix through the real sponge (fq side)

`poseidonO` folds a transcript prefix through the deployed fq-sponge, returning the last
squeezed challenge. The bridge theorems (`poseidonO_pre*`) prove that reading `poseidonO`
at the four fq-side prefixes reproduces `fqOracles`'s `β`, `γ`, `α`, `ζ` — i.e. the real
verifier is the `O := poseidonO` instance of the abstract oracle game. This is what lets
`Forking.Model`'s uniform-oracle statement be *about* the deployed verifier.
-/

namespace Kimchi.Verifier.Forking

open Bulletproof Poseidon

variable {C : Ipa.CommitmentCurve} {nc k : ℕ}

/-- One interpreter step: absorbs update the fq-sponge state (`.1`), squeezes overwrite the
running challenge value (`.2`) and advance the state. -/
def step (acc : FqSponge.S C.base × C.ScalarField) :
    KimchiTranscriptElt C → FqSponge.S C.base × C.ScalarField
  | .fqPoint P => (FqSponge.absorbG C.sponge acc.1 P, acc.2)
  | .fqBase x => (FqSponge.absorbFq C.sponge acc.1 [x], acc.2)
  | .fqCast => ((FqSponge.challenge C.sponge acc.1).2, (FqSponge.challenge C.sponge acc.1).1)
  | .fqEndo => ((FqSponge.squeezeChallenge C.sponge acc.1).2,
      (FqSponge.squeezeChallenge C.sponge acc.1).1)

/-- The real sponge as an oracle: fold a transcript prefix, return the last challenge. -/
def poseidonO (t : List (KimchiTranscriptElt C)) : C.ScalarField :=
  (t.foldl step (FqSponge.init, 0)).2

/-- The four fq-side challenges read from an abstract oracle at the transcript prefixes. -/
def oracleChallenges (O : List (KimchiTranscriptElt C) → C.ScalarField)
    (cvk : KimchiVK C nc) (cp : KimchiProof C nc k) (publicComm : Vector C.Point nc) :
    C.ScalarField × C.ScalarField × C.ScalarField × C.ScalarField :=
  (O (KimchiTranscriptElt.preBeta cvk cp publicComm),
   O (KimchiTranscriptElt.preGamma cvk cp publicComm),
   O (KimchiTranscriptElt.preAlpha cvk cp publicComm),
   O (KimchiTranscriptElt.preZeta cvk cp publicComm))

/-! ## The bridge: `poseidonO` at each prefix is `fqOracles`'s challenge -/

open KimchiTranscriptElt (absorbInto wCommAbsorbs preAbsorbs preBeta preGamma preAlpha preZeta)

/-- The interpreter's state component evolves independently of the running challenge value:
folding `step` and projecting the state equals folding the pure state action `absorbInto`.
This is the spine shared by all four bridges. -/
theorem foldl_step_fst (l : List (KimchiTranscriptElt C)) (s : FqSponge.S C.base)
    (v : C.ScalarField) :
    (l.foldl step (s, v)).1 = l.foldl (fun s e => absorbInto C e s) s := by
  induction l generalizing s v with
  | nil => rfl
  | cons e l ih =>
    have hstep : (step (s, v) e).1 = absorbInto C e s := by cases e <;> rfl
    rw [List.foldl_cons, List.foldl_cons, ih, hstep]

/-- The interpreter's state after an absorb-only prefix is `fqOracles`'s pre-`β` sponge
state: the digest absorb, the public-input commitment fold, then the witness fold. -/
theorem foldl_absorbInto_preAbsorbs (cvk : KimchiVK C nc) (cp : KimchiProof C nc k)
    (publicComm : Vector C.Point nc) :
    (preAbsorbs cvk cp publicComm).foldl (fun s e => absorbInto C e s) FqSponge.init
      = cp.wComm.foldl (fun s col => col.foldl (FqSponge.absorbG C.sponge) s)
          (publicComm.foldl (FqSponge.absorbG C.sponge)
            (FqSponge.absorbFq C.sponge FqSponge.init [cvk.digest])) := by
  unfold preAbsorbs wCommAbsorbs
  simp only [List.foldl_cons, List.foldl_append, List.foldl_map, List.foldl_flatMap,
    absorbInto, Vector.foldl_toList]

theorem poseidonO_preBeta (cvk : KimchiVK C nc) (cp : KimchiProof C nc k)
    (publicComm : Vector C.Point nc) :
    poseidonO (KimchiTranscriptElt.preBeta cvk cp publicComm)
      = (fqOracles C cvk cp publicComm).beta := by
  rw [poseidonO, preBeta, List.foldl_append, List.foldl_cons, List.foldl_nil]
  simp only [step, foldl_step_fst, foldl_absorbInto_preAbsorbs, fqOracles]

theorem poseidonO_preGamma (cvk : KimchiVK C nc) (cp : KimchiProof C nc k)
    (publicComm : Vector C.Point nc) :
    poseidonO (KimchiTranscriptElt.preGamma cvk cp publicComm)
      = (fqOracles C cvk cp publicComm).gamma := by
  rw [poseidonO, preGamma, preBeta]
  simp only [List.foldl_append, List.foldl_cons, List.foldl_nil, step, foldl_step_fst,
    foldl_absorbInto_preAbsorbs, fqOracles]

theorem poseidonO_preAlpha (cvk : KimchiVK C nc) (cp : KimchiProof C nc k)
    (publicComm : Vector C.Point nc) :
    poseidonO (KimchiTranscriptElt.preAlpha cvk cp publicComm)
      = (fqOracles C cvk cp publicComm).alpha := by
  rw [poseidonO, preAlpha, preGamma, preBeta]
  simp only [List.foldl_append, List.foldl_cons, List.foldl_nil, step, foldl_step_fst,
    foldl_absorbInto_preAbsorbs]
  simp only [absorbInto, List.foldl_map, Vector.foldl_toList, fqOracles]

theorem poseidonO_preZeta (cvk : KimchiVK C nc) (cp : KimchiProof C nc k)
    (publicComm : Vector C.Point nc) :
    poseidonO (KimchiTranscriptElt.preZeta cvk cp publicComm)
      = (fqOracles C cvk cp publicComm).zeta := by
  rw [poseidonO, preZeta, preAlpha, preGamma, preBeta]
  simp only [List.foldl_append, List.foldl_cons, List.foldl_nil, step, foldl_step_fst,
    foldl_absorbInto_preAbsorbs]
  simp only [absorbInto, List.foldl_map, Vector.foldl_toList, Array.foldl_toList, fqOracles]

/-- **Faithfulness (W2 acceptance gate).** Reading the sponge-as-oracle `poseidonO` at the
four fq-side transcript prefixes reproduces the deployed verifier's `(β, γ, α, ζ)` exactly.
This witnesses that the abstract oracle game (`Forking.Model`) specializes to the real
verifier at `O := poseidonO`, so the uniform-oracle soundness statement is *about* it. -/
theorem oracleChallenges_poseidonO (cvk : KimchiVK C nc) (cp : KimchiProof C nc k)
    (publicComm : Vector C.Point nc) :
    oracleChallenges poseidonO cvk cp publicComm
      = ((fqOracles C cvk cp publicComm).beta, (fqOracles C cvk cp publicComm).gamma,
         (fqOracles C cvk cp publicComm).alpha, (fqOracles C cvk cp publicComm).zeta) := by
  simp only [oracleChallenges, poseidonO_preBeta, poseidonO_preGamma, poseidonO_preAlpha,
    poseidonO_preZeta]

end Kimchi.Verifier.Forking
