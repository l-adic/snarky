import Bulletproof.Wire

/-!
# The IPA opening transcript as an oracle domain

`Ipa.transcriptFrom` derives the opening challenges by threading a concrete Poseidon sponge.
Discharging `poseidon_fiat_shamir_*` by a forking argument needs those challenges to be *reads
of an oracle at transcript prefixes* instead: forking rewinds the adversary and reprograms the
oracle, which is only meaningful if the verifier reads from one.

This module supplies the domain, following the pattern proved out for the kimchi fq-sponge in
`Kimchi/Verifier/Forking/`: an element type for the deployed absorb/squeeze schedule, the
prefixes at which each challenge is drawn, an interpreter that runs the *real* sponge along a
prefix, and bridge theorems pinning the interpreter's reads to `transcriptFrom`'s outputs.

The schedule (`transcriptFrom`, the round loop of `SRS::verify`) is linear:

1. `absorb_fr` the shifted combined inner product;
2. squeeze `t` and map it to the `U` base (`challengeFq`, then `toGroup`);
3. per round: absorb `L` and `R`, squeeze `uᵢ` (`squeezeChallenge`);
4. absorb `δ`, squeeze the Schnorr challenge `c` (`squeezeChallenge`).

Unlike the kimchi fq side, the challenges do **not** share a codomain: `t` is a base-field
element (`challengeFq`) while `uᵢ` and `c` are scalar-field elements (`squeezeChallenge`,
endo-expanded). So the model carries two oracles rather than one — `spongeOBase` for the `U`
base and `spongeOScalar` for the round and Schnorr challenges.

Everything here is stated at the **cold** start (`FqSponge.init`), which is what `Ipa.verify`
— and hence the axiom being targeted — is anchored on. The warm start kimchi hands in is the
harder case and is not modelled here.
-/

namespace Bulletproof.Ipa.Forking

open CompElliptic.CurveForms.ShortWeierstrass
open Poseidon Poseidon.FqSponge Bulletproof

variable {C : Ipa.CommitmentCurve} {k m p : ℕ}

/-- A single element of the IPA opening transcript: the two absorb kinds the deployed
schedule performs, and the two squeeze kinds (a raw base-field squeeze for the `U` base, an
endo-expanded squeeze for the round and Schnorr challenges). A squeeze marker records that a
challenge was drawn; it is not re-absorbed. -/
inductive IpaTranscriptElt (C : Ipa.CommitmentCurve) where
  /-- `absorb_fr` of a scalar — the shifted combined inner product. -/
  | frScalar : C.ScalarField → IpaTranscriptElt C
  /-- `absorb_g` of a point — `L`, `R`, or `δ`. -/
  | point : C.Point → IpaTranscriptElt C
  /-- A raw base-field squeeze (`challengeFq`): the `U`-base preimage `t`. -/
  | sqBase : IpaTranscriptElt C
  /-- An endo-expanded squeeze (`squeezeChallenge`): a round challenge `uᵢ`, or `c`. -/
  | sqEndo : IpaTranscriptElt C

namespace IpaTranscriptElt

/-- The state action of a transcript element on the sponge — the interpreter's state
component, isolated so it never mentions a challenge value. -/
def stepState (C : Ipa.CommitmentCurve) :
    IpaTranscriptElt C → FqSponge.S C.base → FqSponge.S C.base
  | frScalar x, s => FqSponge.absorbFr C.sponge s x
  | point P, s => FqSponge.absorbG C.sponge s P
  | sqBase, s => (FqSponge.challengeFq C.sponge s).2
  | sqEndo, s => (FqSponge.squeezeChallenge C.sponge s).2

/-- The absorbs preceding the `U`-base squeeze: the shifted combined inner product. -/
def preTAbsorbs (inp : Ipa.Input C k m p) : List (IpaTranscriptElt C) :=
  [frScalar (Ipa.shiftScalar C (Ipa.cipOf inp))]

/-- The `U`-base prefix: the cip absorb, then the raw squeeze marker. -/
def preT (inp : Ipa.Input C k m p) : List (IpaTranscriptElt C) :=
  preTAbsorbs inp ++ [sqBase]

/-- Rounds `0 … j-1` of the fold, each absorbing `L`, `R` and squeezing a challenge. -/
def roundBlock (inp : Ipa.Input C k m p) (j : ℕ) : List (IpaTranscriptElt C) :=
  (inp.proof.lr.toList.take j).flatMap fun LR => [point LR.1, point LR.2, sqEndo]

/-- The prefix at which round `i`'s challenge `uᵢ` is drawn: the `U`-base prefix, then rounds
`0 … i`, the last of which ends in this round's squeeze marker. -/
def preU (inp : Ipa.Input C k m p) (i : Fin k) : List (IpaTranscriptElt C) :=
  preT inp ++ roundBlock inp (i + 1)

/-- The Schnorr prefix: the `U`-base prefix, all `k` rounds, the `δ` absorb, then a squeeze. -/
def preC (inp : Ipa.Input C k m p) : List (IpaTranscriptElt C) :=
  preT inp ++ roundBlock inp k ++ [point inp.proof.delta, sqEndo]

end IpaTranscriptElt

open IpaTranscriptElt

/-! ## The deployed sponge as a pair of oracles

A prefix ends with the marker of the challenge being read, so both oracles fold the *real*
sponge along everything before that marker and then perform the squeeze it denotes. They differ
only in which squeeze that is, matching the two challenge codomains. (The kimchi model threads a
`(state, value)` pair instead; that does not transfer here, because `t` and `uᵢ`/`c` do not share
a codomain.) -/

/-- The base-field oracle: the raw squeeze the `U` base is derived from. -/
def spongeOBase (t : List (IpaTranscriptElt C)) : C.BaseField :=
  (FqSponge.challengeFq C.sponge (t.dropLast.foldl (fun s e => stepState C e s) FqSponge.init)).1

/-- The scalar-field oracle: the endo-expanded squeeze of the round and Schnorr challenges. -/
def spongeOScalar (t : List (IpaTranscriptElt C)) : C.ScalarField :=
  (FqSponge.squeezeChallenge C.sponge
    (t.dropLast.foldl (fun s e => stepState C e s) FqSponge.init)).1

/-! ## Bridges: the oracle reads are `transcriptFrom`'s outputs

These pin the hand-written prefixes to the deployed schedule — a mis-transcription makes them
false, so they are the statements that make the model *about* the real verifier. -/

/-- **The `U` base.** Mapping the base oracle's read at `preT` through `toGroup` gives
`transcriptFrom`'s `U`. -/
theorem toGroup_spongeOBase_preT (inp : Ipa.Input C k m p) :
    C.toGroup (spongeOBase (preT inp)) = (Ipa.transcriptFrom C FqSponge.init inp).1 := by
  simp only [spongeOBase, preT, preTAbsorbs, List.dropLast_concat, List.foldl_cons,
    List.foldl_nil, stepState, Ipa.transcriptFrom]

/-! ## Round-fold helpers for the two scalar bridges

The scalar bridges are `k`-indexed, so — unlike the fixed-length kimchi fq helpers — they need
a genuine induction over the round list. `rstep` is the deployed per-round step (definitionally
`Ipa.roundChallengesAux`'s fold body); `mstate`/`mchals` are the model's post-`j`-rounds sponge
state and the list of pushed challenges, and the lemmas below tie the deployed `Array.foldl` to
the model `List.foldl`. -/

/-- The deployed per-round step, named so the fold rewrites cleanly. Definitionally the body of
`Ipa.roundChallengesAux`. -/
private def rstep (C : Ipa.CommitmentCurve)
    (acc : Array C.ScalarField × FqSponge.S C.base) (LR : C.Point × C.Point) :
    Array C.ScalarField × FqSponge.S C.base :=
  (acc.1.push (FqSponge.squeezeChallenge C.sponge
      (FqSponge.absorbG C.sponge (FqSponge.absorbG C.sponge acc.2 LR.1) LR.2)).1,
    (FqSponge.squeezeChallenge C.sponge
      (FqSponge.absorbG C.sponge (FqSponge.absorbG C.sponge acc.2 LR.1) LR.2)).2)

/-- `Ipa.roundChallengesAux` as a `List.foldl` of the named step over the array's list. -/
private theorem roundChallengesAux_eq_foldl (s : FqSponge.S C.base)
    (lr : Array (C.Point × C.Point)) :
    Ipa.roundChallengesAux C s lr = lr.toList.foldl (rstep C) (#[], s) := by
  unfold Ipa.roundChallengesAux
  rw [← Array.foldl_toList]
  rfl

/-- The model sponge state after folding the round block of `L` from `s`. -/
private def mstate (C : Ipa.CommitmentCurve) (s : FqSponge.S C.base)
    (L : List (C.Point × C.Point)) : FqSponge.S C.base :=
  match L with
  | [] => s
  | LR :: t =>
    mstate C (FqSponge.squeezeChallenge C.sponge
      (FqSponge.absorbG C.sponge (FqSponge.absorbG C.sponge s LR.1) LR.2)).2 t

/-- The model list of round challenges pushed while folding the round block of `L` from `s`. -/
private def mchals (C : Ipa.CommitmentCurve) (s : FqSponge.S C.base)
    (L : List (C.Point × C.Point)) : List C.ScalarField :=
  match L with
  | [] => []
  | LR :: t =>
    (FqSponge.squeezeChallenge C.sponge
      (FqSponge.absorbG C.sponge (FqSponge.absorbG C.sponge s LR.1) LR.2)).1 ::
      mchals C (FqSponge.squeezeChallenge C.sponge
        (FqSponge.absorbG C.sponge (FqSponge.absorbG C.sponge s LR.1) LR.2)).2 t

/-- The deployed round fold's post-state is the model state (independent of the accumulator). -/
private theorem rstep_foldl_state (L : List (C.Point × C.Point)) :
    ∀ (pre : Array C.ScalarField) (s : FqSponge.S C.base),
    (L.foldl (rstep C) (pre, s)).2 = mstate C s L := by
  induction L with
  | nil => intro pre s; rfl
  | cons LR t ih =>
    intro pre s
    rw [List.foldl_cons]
    have hr : rstep C (pre, s) LR =
        (pre.push (FqSponge.squeezeChallenge C.sponge
            (FqSponge.absorbG C.sponge (FqSponge.absorbG C.sponge s LR.1) LR.2)).1,
         (FqSponge.squeezeChallenge C.sponge
            (FqSponge.absorbG C.sponge (FqSponge.absorbG C.sponge s LR.1) LR.2)).2) := rfl
    rw [hr, ih]
    simp only [mstate]

/-- The deployed round fold's array is the accumulator prepended to the model challenge list. -/
private theorem rstep_foldl_toList (L : List (C.Point × C.Point)) :
    ∀ (pre : Array C.ScalarField) (s : FqSponge.S C.base),
    (L.foldl (rstep C) (pre, s)).1.toList = pre.toList ++ mchals C s L := by
  induction L with
  | nil => intro pre s; simp [mchals]
  | cons LR t ih =>
    intro pre s
    rw [List.foldl_cons]
    have hr : rstep C (pre, s) LR =
        (pre.push (FqSponge.squeezeChallenge C.sponge
            (FqSponge.absorbG C.sponge (FqSponge.absorbG C.sponge s LR.1) LR.2)).1,
         (FqSponge.squeezeChallenge C.sponge
            (FqSponge.absorbG C.sponge (FqSponge.absorbG C.sponge s LR.1) LR.2)).2) := rfl
    rw [hr, ih]
    simp only [mchals, Array.toList_push, List.append_assoc, List.singleton_append]

/-- The deployed round fold's post-state, as the model state over the round list. -/
private theorem roundChallengesAux_snd (s : FqSponge.S C.base)
    (lr : Array (C.Point × C.Point)) :
    (Ipa.roundChallengesAux C s lr).2 = mstate C s lr.toList := by
  rw [roundChallengesAux_eq_foldl, rstep_foldl_state]

/-- The deployed round fold's challenge array, as the model challenge list over the round list. -/
private theorem roundChallengesAux_fst_toList (s : FqSponge.S C.base)
    (lr : Array (C.Point × C.Point)) :
    (Ipa.roundChallengesAux C s lr).1.toList = mchals C s lr.toList := by
  rw [roundChallengesAux_eq_foldl, rstep_foldl_toList]
  simp

/-- Folding the model step over `L`'s round block from `s` yields the model state `mstate`. -/
private theorem flatMap_block_foldl (M : List (C.Point × C.Point)) (s : FqSponge.S C.base) :
    (M.flatMap (fun LR => [point LR.1, point LR.2, sqEndo])).foldl
      (fun s e => stepState C e s) s = mstate C s M := by
  induction M generalizing s with
  | nil => simp [mstate]
  | cons LR t ih =>
    rw [List.flatMap_cons, List.foldl_append]
    have hb : ([point LR.1, point LR.2, sqEndo] : List (IpaTranscriptElt C)).foldl
        (fun s e => stepState C e s) s
        = (FqSponge.squeezeChallenge C.sponge
            (FqSponge.absorbG C.sponge (FqSponge.absorbG C.sponge s LR.1) LR.2)).2 := by
      simp only [List.foldl_cons, List.foldl_nil, stepState]
    rw [hb, ih]
    simp only [mstate]

/-- The `i`-th model challenge is the endo-squeeze after absorbing round `i`'s `L`, `R` on top of
the model state after `i` rounds. Stated with `getElem?` to sidestep the length side-goal. -/
private theorem mchals_getElem? (L : List (C.Point × C.Point)) :
    ∀ (i : ℕ) (s : FqSponge.S C.base) (hi : i < L.length),
    (mchals C s L)[i]? = some (FqSponge.squeezeChallenge C.sponge
      (FqSponge.absorbG C.sponge (FqSponge.absorbG C.sponge
        (mstate C s (L.take i)) (L[i]'hi).1) (L[i]'hi).2)).1 := by
  induction L with
  | nil => intro i s hi; simp at hi
  | cons LR t ih =>
    intro i s hi
    cases i with
    | zero =>
      simp only [mchals, List.getElem?_cons_zero, List.take_zero, mstate,
        List.getElem_cons_zero]
    | succ j =>
      simp only [mchals, List.getElem?_cons_succ, List.take_succ_cons,
        List.getElem_cons_succ, mstate]
      exact ih j _ (by simp only [List.length_cons] at hi; omega)

/-- The `idx`-th deployed round challenge, characterised through `getElem?`. -/
private theorem roundChallengesAux_getElem? (s : FqSponge.S C.base)
    (lr : Array (C.Point × C.Point)) (idx : ℕ) (h : idx < lr.toList.length) :
    (Ipa.roundChallengesAux C s lr).1[idx]? = some (FqSponge.squeezeChallenge C.sponge
      (FqSponge.absorbG C.sponge (FqSponge.absorbG C.sponge
        (mstate C s (lr.toList.take idx)) (lr.toList[idx]'h).1) (lr.toList[idx]'h).2)).1 := by
  rw [← Array.getElem?_toList, roundChallengesAux_fst_toList]
  exact mchals_getElem? lr.toList idx s h

/-- `roundBlock` at `i+1` is `roundBlock` at `i` with round `i`'s block appended. -/
private theorem roundBlock_succ (inp : Ipa.Input C k m p) (i : Fin k)
    (hik : (i : ℕ) < inp.proof.lr.toList.length) :
    roundBlock inp ((i : ℕ) + 1) = roundBlock inp (i : ℕ) ++
      [point (inp.proof.lr.toList[(i : ℕ)]).1, point (inp.proof.lr.toList[(i : ℕ)]).2,
        sqEndo] := by
  simp only [roundBlock]
  rw [List.take_succ_eq_append_getElem hik, List.flatMap_append]
  simp

/-- **The round challenges.** The scalar oracle at `preU i` is round `i`'s challenge. -/
theorem spongeOScalar_preU (inp : Ipa.Input C k m p) (i : Fin k) :
    spongeOScalar (preU inp i) = (Ipa.transcriptFrom C FqSponge.init inp).2.1[i] := by
  have hik : (i : ℕ) < inp.proof.lr.toList.length := by simp
  -- The post-`challengeFq` state feeding the rounds (shared, verbatim, by both sides).
  have hpreT : (preT inp).foldl (fun s e => stepState C e s) FqSponge.init
      = (FqSponge.challengeFq C.sponge (FqSponge.absorbFr C.sponge FqSponge.init
          (Ipa.shiftScalar C (Ipa.cipOf inp)))).2 := by
    simp only [preT, preTAbsorbs, List.cons_append, List.nil_append, List.foldl_cons,
      List.foldl_nil, stepState]
  -- LHS: reduce the model fold to the endo-squeeze after round `i`'s two absorbs.
  have hLHS : spongeOScalar (preU inp i)
      = (FqSponge.squeezeChallenge C.sponge (FqSponge.absorbG C.sponge (FqSponge.absorbG C.sponge
          (mstate C (FqSponge.challengeFq C.sponge (FqSponge.absorbFr C.sponge FqSponge.init
              (Ipa.shiftScalar C (Ipa.cipOf inp)))).2 (inp.proof.lr.toList.take (i : ℕ)))
          (inp.proof.lr.toList[(i : ℕ)]'hik).1) (inp.proof.lr.toList[(i : ℕ)]'hik).2)).1 := by
    simp only [spongeOScalar, preU]
    rw [roundBlock_succ inp i hik, List.dropLast_append_of_ne_nil (by simp),
      List.dropLast_append_of_ne_nil (by simp)]
    rw [show ([point (inp.proof.lr.toList[(i : ℕ)]'hik).1,
          point (inp.proof.lr.toList[(i : ℕ)]'hik).2, sqEndo] :
          List (IpaTranscriptElt C)).dropLast
        = [point (inp.proof.lr.toList[(i : ℕ)]'hik).1,
          point (inp.proof.lr.toList[(i : ℕ)]'hik).2] from rfl]
    rw [List.foldl_append, List.foldl_append, hpreT]
    rw [show (roundBlock inp (i : ℕ)).foldl (fun s e => stepState C e s)
          (FqSponge.challengeFq C.sponge (FqSponge.absorbFr C.sponge FqSponge.init
            (Ipa.shiftScalar C (Ipa.cipOf inp)))).2
        = mstate C (FqSponge.challengeFq C.sponge (FqSponge.absorbFr C.sponge FqSponge.init
            (Ipa.shiftScalar C (Ipa.cipOf inp)))).2 (inp.proof.lr.toList.take (i : ℕ)) from by
        simp only [roundBlock]; exact flatMap_block_foldl _ _]
    simp only [List.foldl_cons, List.foldl_nil, stepState]
  -- RHS: the deployed challenge array read at `i`, via `roundChallengesAux_getElem?`.
  have hRHS : (Ipa.transcriptFrom C FqSponge.init inp).2.1[i]
      = (FqSponge.squeezeChallenge C.sponge (FqSponge.absorbG C.sponge (FqSponge.absorbG C.sponge
          (mstate C (FqSponge.challengeFq C.sponge (FqSponge.absorbFr C.sponge FqSponge.init
              (Ipa.shiftScalar C (Ipa.cipOf inp)))).2 (inp.proof.lr.toList.take (i : ℕ)))
          (inp.proof.lr.toList[(i : ℕ)]'hik).1) (inp.proof.lr.toList[(i : ℕ)]'hik).2)).1 := by
    simp only [Ipa.transcriptFrom, Ipa.roundChallenges]
    have hsize : (i : ℕ) < (Ipa.roundChallengesAux C
        (FqSponge.challengeFq C.sponge (FqSponge.absorbFr C.sponge FqSponge.init
          (Ipa.shiftScalar C (Ipa.cipOf inp)))).2 inp.proof.lr.toArray).1.size := by
      rw [Ipa.roundChallengesAux_size]; simp
    have hg := roundChallengesAux_getElem? (FqSponge.challengeFq C.sponge
      (FqSponge.absorbFr C.sponge FqSponge.init (Ipa.shiftScalar C (Ipa.cipOf inp)))).2
      inp.proof.lr.toArray (i : ℕ) hik
    rw [Array.getElem?_eq_getElem hsize] at hg
    exact Option.some.inj hg
  rw [hLHS, hRHS]

/-- **The Schnorr challenge.** The scalar oracle at `preC` is `c`. -/
theorem spongeOScalar_preC (inp : Ipa.Input C k m p) :
    spongeOScalar (preC inp) = (Ipa.transcriptFrom C FqSponge.init inp).2.2 := by
  have hlen : inp.proof.lr.toList.length = k := by simp
  have hpreT : (preT inp).foldl (fun s e => stepState C e s) FqSponge.init
      = (FqSponge.challengeFq C.sponge (FqSponge.absorbFr C.sponge FqSponge.init
          (Ipa.shiftScalar C (Ipa.cipOf inp)))).2 := by
    simp only [preT, preTAbsorbs, List.cons_append, List.nil_append, List.foldl_cons,
      List.foldl_nil, stepState]
  -- LHS: after dropping the trailing `sqEndo`, the fold ends by absorbing `δ` on the
  -- post-`k`-rounds model state.
  have hLHS : spongeOScalar (preC inp)
      = (FqSponge.squeezeChallenge C.sponge (FqSponge.absorbG C.sponge
          (mstate C (FqSponge.challengeFq C.sponge (FqSponge.absorbFr C.sponge FqSponge.init
              (Ipa.shiftScalar C (Ipa.cipOf inp)))).2 inp.proof.lr.toList) inp.proof.delta)).1 := by
    simp only [spongeOScalar, preC]
    rw [List.dropLast_append_of_ne_nil (by simp)]
    rw [show ([point inp.proof.delta, sqEndo] : List (IpaTranscriptElt C)).dropLast
        = [point inp.proof.delta] from rfl]
    rw [List.foldl_append, List.foldl_append, hpreT]
    rw [show (roundBlock inp k).foldl (fun s e => stepState C e s)
          (FqSponge.challengeFq C.sponge (FqSponge.absorbFr C.sponge FqSponge.init
            (Ipa.shiftScalar C (Ipa.cipOf inp)))).2
        = mstate C (FqSponge.challengeFq C.sponge (FqSponge.absorbFr C.sponge FqSponge.init
            (Ipa.shiftScalar C (Ipa.cipOf inp)))).2 inp.proof.lr.toList from by
        simp only [roundBlock]
        rw [show inp.proof.lr.toList.take k = inp.proof.lr.toList from by
          conv_rhs => rw [← List.take_length (l := inp.proof.lr.toList)]
          rw [hlen]]
        exact flatMap_block_foldl _ _]
    simp only [List.foldl_cons, List.foldl_nil, stepState]
  -- RHS: `c` is the endo-squeeze after absorbing `δ` on the deployed post-round state.
  have hRHS : (Ipa.transcriptFrom C FqSponge.init inp).2.2
      = (FqSponge.squeezeChallenge C.sponge (FqSponge.absorbG C.sponge
          (mstate C (FqSponge.challengeFq C.sponge (FqSponge.absorbFr C.sponge FqSponge.init
              (Ipa.shiftScalar C (Ipa.cipOf inp)))).2 inp.proof.lr.toList) inp.proof.delta)).1 := by
    simp only [Ipa.transcriptFrom, Ipa.roundChallenges]
    rw [roundChallengesAux_snd]
    rfl
  rw [hLHS, hRHS]

end Bulletproof.Ipa.Forking
