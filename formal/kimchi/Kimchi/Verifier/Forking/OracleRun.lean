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

/-! ## The fr-sponge side: `poseidonOFr` at `preV`/`preU` is `frOracles`'s `(v, u)` -/

open FrTranscriptElt (frAbsorbInto absorbEval preVAbsorbs preV preU)

/-- One fr-interpreter step: `frAbsorb` absorbs its list, `frEndo` endo-expands a squeeze. -/
def frStep (acc : FqSponge.S C.scalar × C.ScalarField) :
    FrTranscriptElt C → FqSponge.S C.scalar × C.ScalarField
  | .frAbsorb xs => (FqSponge.absorbFq (frSpec C) acc.1 xs, acc.2)
  | .frEndo => ((FqSponge.challengeNat (frSpec C) acc.1).2,
      FqSponge.endoExpand C.sponge.lam (FqSponge.challengeNat (frSpec C) acc.1).1)

/-- The fr-sponge as an oracle: fold a transcript prefix, return the last challenge. -/
def poseidonOFr (t : List (FrTranscriptElt C)) : C.ScalarField :=
  (t.foldl frStep (FqSponge.init, 0)).2

/-- The two fr-side challenges read from an abstract oracle at the `v`/`u` prefixes. -/
def oracleVU (O : List (FrTranscriptElt C) → C.ScalarField) (cp : KimchiProof C nc k)
    (fqDig : C.ScalarField) (pubEvals : PointEvaluations (Vector C.ScalarField nc)) :
    C.ScalarField × C.ScalarField :=
  (O (preV cp fqDig pubEvals), O (preU cp fqDig pubEvals))

/-- The fr-interpreter's state component folds `frAbsorbInto`, independent of the value. -/
theorem foldl_frStep_fst (l : List (FrTranscriptElt C)) (s : FqSponge.S C.scalar)
    (v : C.ScalarField) :
    (l.foldl frStep (s, v)).1 = l.foldl (fun s e => frAbsorbInto C e s) s := by
  induction l generalizing s v with
  | nil => rfl
  | cons e l ih =>
    have hstep : (frStep (s, v) e).1 = frAbsorbInto C e s := by cases e <;> rfl
    rw [List.foldl_cons, List.foldl_cons, ih, hstep]

/-- The fr-interpreter's state after the pre-`v` absorbs is `frOracles`'s pre-squeeze state:
the fq/fr digests, `ft(ζω)`, the public chunk vectors, then the `absorb_evaluations` folds. -/
theorem foldl_frAbsorbInto_preVAbsorbs (cp : KimchiProof C nc k) (fqDig : C.ScalarField)
    (pubEvals : PointEvaluations (Vector C.ScalarField nc)) :
    (preVAbsorbs cp fqDig pubEvals).foldl (fun s e => frAbsorbInto C e s) FqSponge.init
      = (let sp := frSpec C
         let ab := fun (s : FqSponge.S C.scalar)
             (e : PointEvaluations (Vector C.ScalarField nc)) =>
           FqSponge.absorbFq sp (FqSponge.absorbFq sp s e.zeta.toList) e.zetaOmega.toList
         let s := FqSponge.absorbFq sp FqSponge.init [fqDig]
         let s := FqSponge.absorbFq sp s [frDigest C sp FqSponge.init]
         let s := FqSponge.absorbFq sp s [cp.ftEval1]
         let s := FqSponge.absorbFq sp s pubEvals.zeta.toList
         let s := FqSponge.absorbFq sp s pubEvals.zetaOmega.toList
         let s := ab s cp.evals.z
         let s := ab s cp.evals.genericSelector
         let s := ab s cp.evals.poseidonSelector
         let s := ab s cp.evals.completeAddSelector
         let s := ab s cp.evals.mulSelector
         let s := ab s cp.evals.emulSelector
         let s := ab s cp.evals.endomulScalarSelector
         let s := cp.evals.w.foldl ab s
         let s := cp.evals.coefficients.foldl ab s
         cp.evals.s.foldl ab s) := by
  simp only [preVAbsorbs, absorbEval, frAbsorbInto, List.foldl_cons, List.foldl_append,
    List.foldl_nil, List.foldl_flatMap, Vector.foldl_toList]

theorem poseidonOFr_preV (cp : KimchiProof C nc k) (fqDig : C.ScalarField)
    (pubEvals : PointEvaluations (Vector C.ScalarField nc)) :
    poseidonOFr (preV cp fqDig pubEvals) = (frOracles C cp fqDig pubEvals).1 := by
  rw [poseidonOFr, preV, List.foldl_append, List.foldl_cons, List.foldl_nil]
  simp only [frStep, foldl_frStep_fst, foldl_frAbsorbInto_preVAbsorbs, frOracles]

theorem poseidonOFr_preU (cp : KimchiProof C nc k) (fqDig : C.ScalarField)
    (pubEvals : PointEvaluations (Vector C.ScalarField nc)) :
    poseidonOFr (preU cp fqDig pubEvals) = (frOracles C cp fqDig pubEvals).2 := by
  rw [poseidonOFr, preU, preV]
  simp only [List.foldl_append, List.foldl_cons, List.foldl_nil, frStep, foldl_frStep_fst,
    foldl_frAbsorbInto_preVAbsorbs, frOracles]

/-- **Faithfulness (fr side).** Reading `poseidonOFr` at the `v`/`u` prefixes reproduces the
deployed verifier's batch challenges `(v, u)` from `frOracles`. -/
theorem oracleVU_poseidonOFr (cp : KimchiProof C nc k) (fqDig : C.ScalarField)
    (pubEvals : PointEvaluations (Vector C.ScalarField nc)) :
    oracleVU poseidonOFr cp fqDig pubEvals = frOracles C cp fqDig pubEvals := by
  rw [oracleVU, poseidonOFr_preV, poseidonOFr_preU]

end Kimchi.Verifier.Forking
