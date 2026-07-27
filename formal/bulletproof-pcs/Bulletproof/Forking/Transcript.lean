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

Everything is developed **from an arbitrary start state** `s₀` (`spongeOBaseFrom`,
`spongeOScalarFrom`, and the bridges against `Ipa.transcriptFrom C s₀`). The **cold** statements
(`spongeOBase`, `spongeOScalar`, and their three bridges) — which `Ipa.verify`, and hence the
axiom being targeted, is anchored on — are recovered verbatim as the specialisation at
`s₀ = FqSponge.init`. The generality is the point: kimchi hands the opening verifier a sponge
that has already absorbed the whole kimchi transcript and emitted `β, γ, α, ζ`, so its opening
challenges are *not* functions of the opening transcript alone; parameterising over the start
state is exactly what makes this suffix model reusable there.
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
a codomain.)

Each oracle comes in two forms: the `…From` form at an arbitrary start state `s₀`, and the cold
form at `FqSponge.init`. The cold forms are kept as standalone definitions — the frozen
`Forking/Deployed.lean` phrases the transcript-derived base `uBaseOf` through `spongeOBase` —
and `spongeOBase_eq_from` / `spongeOScalar_eq_from` record that they are the specialisations. -/

/-- The base-field oracle **at an arbitrary start state**: the raw squeeze the `U` base is
derived from, taken after folding the real sponge from `s₀` along everything before the
trailing marker. -/
def spongeOBaseFrom (s₀ : FqSponge.S C.base) (t : List (IpaTranscriptElt C)) : C.BaseField :=
  (FqSponge.challengeFq C.sponge (t.dropLast.foldl (fun s e => stepState C e s) s₀)).1

/-- The scalar-field oracle **at an arbitrary start state**: the endo-expanded squeeze of the
round and Schnorr challenges, taken after folding the real sponge from `s₀` along everything
before the trailing marker. -/
def spongeOScalarFrom (s₀ : FqSponge.S C.base) (t : List (IpaTranscriptElt C)) :
    C.ScalarField :=
  (FqSponge.squeezeChallenge C.sponge (t.dropLast.foldl (fun s e => stepState C e s) s₀)).1

/-- The base-field oracle: the raw squeeze the `U` base is derived from. -/
def spongeOBase (t : List (IpaTranscriptElt C)) : C.BaseField :=
  (FqSponge.challengeFq C.sponge (t.dropLast.foldl (fun s e => stepState C e s) FqSponge.init)).1

/-- The scalar-field oracle: the endo-expanded squeeze of the round and Schnorr challenges. -/
def spongeOScalar (t : List (IpaTranscriptElt C)) : C.ScalarField :=
  (FqSponge.squeezeChallenge C.sponge
    (t.dropLast.foldl (fun s e => stepState C e s) FqSponge.init)).1

/-- The cold base oracle is the start-state-general one at `FqSponge.init`. -/
theorem spongeOBase_eq_from (t : List (IpaTranscriptElt C)) :
    spongeOBase t = spongeOBaseFrom FqSponge.init t := rfl

/-- The cold scalar oracle is the start-state-general one at `FqSponge.init`. -/
theorem spongeOScalar_eq_from (t : List (IpaTranscriptElt C)) :
    spongeOScalar t = spongeOScalarFrom FqSponge.init t := rfl

/-! ### Prefix shift

A start state that is itself reached by folding along a prefix `t₀` can be traded for that
prefix: reading at `t` from `δ*(s₀, t₀)` is reading at `t₀ ++ t` from `s₀`. This is the
formal content of "the opening transcript is a *suffix*" — it is what lets a warm-start read
be re-expressed against the enclosing protocol's transcript. The `t ≠ []` side condition is
real: the trailing marker being dropped must come from `t`, not from `t₀`. -/

/-- **Prefix shift, base oracle.** Reading at `t` from the state reached along `t₀` is reading
at `t₀ ++ t` from the earlier state. -/
theorem spongeOBaseFrom_append (s₀ : FqSponge.S C.base) (t₀ t : List (IpaTranscriptElt C))
    (ht : t ≠ []) :
    spongeOBaseFrom s₀ (t₀ ++ t)
      = spongeOBaseFrom (t₀.foldl (fun s e => stepState C e s) s₀) t := by
  simp only [spongeOBaseFrom, List.dropLast_append_of_ne_nil ht, List.foldl_append]

/-- **Prefix shift, scalar oracle.** Reading at `t` from the state reached along `t₀` is reading
at `t₀ ++ t` from the earlier state. -/
theorem spongeOScalarFrom_append (s₀ : FqSponge.S C.base) (t₀ t : List (IpaTranscriptElt C))
    (ht : t ≠ []) :
    spongeOScalarFrom s₀ (t₀ ++ t)
      = spongeOScalarFrom (t₀.foldl (fun s e => stepState C e s) s₀) t := by
  simp only [spongeOScalarFrom, List.dropLast_append_of_ne_nil ht, List.foldl_append]

/-! ## Bridges: the oracle reads are `transcriptFrom`'s outputs

These pin the hand-written prefixes to the deployed schedule — a mis-transcription makes them
false, so they are the statements that make the model *about* the real verifier. Each is proved
at an arbitrary start state `s₀` and then specialised to the cold start. -/

/-- **The `U` base, from any start state.** Mapping the base oracle's read at `preT` through
`toGroup` gives `transcriptFrom`'s `U`. -/
theorem toGroup_spongeOBaseFrom_preT (s₀ : FqSponge.S C.base) (inp : Ipa.Input C k m p) :
    C.toGroup (spongeOBaseFrom s₀ (preT inp)) = (Ipa.transcriptFrom C s₀ inp).1 := by
  simp only [spongeOBaseFrom, preT, preTAbsorbs, List.dropLast_concat, List.foldl_cons,
    List.foldl_nil, stepState, Ipa.transcriptFrom]

/-- **The `U` base.** Mapping the base oracle's read at `preT` through `toGroup` gives
`transcriptFrom`'s `U`. -/
theorem toGroup_spongeOBase_preT (inp : Ipa.Input C k m p) :
    C.toGroup (spongeOBase (preT inp)) = (Ipa.transcriptFrom C FqSponge.init inp).1 :=
  toGroup_spongeOBaseFrom_preT FqSponge.init inp

/-! ## Round-fold helpers for the two scalar bridges

The scalar bridges are `k`-indexed, so — unlike the fixed-length kimchi fq helpers — they need
a genuine induction over the round list. `rstep` is the deployed per-round step (definitionally
`Ipa.roundChallengesAux`'s fold body); `mstate`/`mchals` are the model's post-`j`-rounds sponge
state and the list of pushed challenges, and the lemmas below tie the deployed `Array.foldl` to
the model `List.foldl`.

The whole engine is public: every statement already carries the start state as a parameter, so
it transfers verbatim to the warm start kimchi hands the opening verifier. -/

/-- The deployed per-round step, named so the fold rewrites cleanly. Definitionally the body of
`Ipa.roundChallengesAux`. -/
def rstep (C : Ipa.CommitmentCurve)
    (acc : Array C.ScalarField × FqSponge.S C.base) (LR : C.Point × C.Point) :
    Array C.ScalarField × FqSponge.S C.base :=
  (acc.1.push (FqSponge.squeezeChallenge C.sponge
      (FqSponge.absorbG C.sponge (FqSponge.absorbG C.sponge acc.2 LR.1) LR.2)).1,
    (FqSponge.squeezeChallenge C.sponge
      (FqSponge.absorbG C.sponge (FqSponge.absorbG C.sponge acc.2 LR.1) LR.2)).2)

/-- `Ipa.roundChallengesAux` as a `List.foldl` of the named step over the array's list. -/
theorem roundChallengesAux_eq_foldl (s : FqSponge.S C.base)
    (lr : Array (C.Point × C.Point)) :
    Ipa.roundChallengesAux C s lr = lr.toList.foldl (rstep C) (#[], s) := by
  unfold Ipa.roundChallengesAux
  rw [← Array.foldl_toList]
  rfl

/-- The model sponge state after folding the round block of `L` from `s`. -/
def mstate (C : Ipa.CommitmentCurve) (s : FqSponge.S C.base)
    (L : List (C.Point × C.Point)) : FqSponge.S C.base :=
  match L with
  | [] => s
  | LR :: t =>
    mstate C (FqSponge.squeezeChallenge C.sponge
      (FqSponge.absorbG C.sponge (FqSponge.absorbG C.sponge s LR.1) LR.2)).2 t

/-- The model list of round challenges pushed while folding the round block of `L` from `s`. -/
def mchals (C : Ipa.CommitmentCurve) (s : FqSponge.S C.base)
    (L : List (C.Point × C.Point)) : List C.ScalarField :=
  match L with
  | [] => []
  | LR :: t =>
    (FqSponge.squeezeChallenge C.sponge
      (FqSponge.absorbG C.sponge (FqSponge.absorbG C.sponge s LR.1) LR.2)).1 ::
      mchals C (FqSponge.squeezeChallenge C.sponge
        (FqSponge.absorbG C.sponge (FqSponge.absorbG C.sponge s LR.1) LR.2)).2 t

/-- The deployed round fold's post-state is the model state (independent of the accumulator). -/
theorem rstep_foldl_state (L : List (C.Point × C.Point)) :
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
theorem rstep_foldl_toList (L : List (C.Point × C.Point)) :
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
theorem roundChallengesAux_snd (s : FqSponge.S C.base)
    (lr : Array (C.Point × C.Point)) :
    (Ipa.roundChallengesAux C s lr).2 = mstate C s lr.toList := by
  rw [roundChallengesAux_eq_foldl, rstep_foldl_state]

/-- The deployed round fold's challenge array, as the model challenge list over the round list. -/
theorem roundChallengesAux_fst_toList (s : FqSponge.S C.base)
    (lr : Array (C.Point × C.Point)) :
    (Ipa.roundChallengesAux C s lr).1.toList = mchals C s lr.toList := by
  rw [roundChallengesAux_eq_foldl, rstep_foldl_toList]
  simp

/-- Folding the model step over `L`'s round block from `s` yields the model state `mstate`. -/
theorem flatMap_block_foldl (M : List (C.Point × C.Point)) (s : FqSponge.S C.base) :
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
theorem mchals_getElem? (L : List (C.Point × C.Point)) :
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
theorem roundChallengesAux_getElem? (s : FqSponge.S C.base)
    (lr : Array (C.Point × C.Point)) (idx : ℕ) (h : idx < lr.toList.length) :
    (Ipa.roundChallengesAux C s lr).1[idx]? = some (FqSponge.squeezeChallenge C.sponge
      (FqSponge.absorbG C.sponge (FqSponge.absorbG C.sponge
        (mstate C s (lr.toList.take idx)) (lr.toList[idx]'h).1) (lr.toList[idx]'h).2)).1 := by
  rw [← Array.getElem?_toList, roundChallengesAux_fst_toList]
  exact mchals_getElem? lr.toList idx s h

/-- `roundBlock` at `i+1` is `roundBlock` at `i` with round `i`'s block appended. -/
theorem roundBlock_succ (inp : Ipa.Input C k m p) (i : Fin k)
    (hik : (i : ℕ) < inp.proof.lr.toList.length) :
    roundBlock inp ((i : ℕ) + 1) = roundBlock inp (i : ℕ) ++
      [point (inp.proof.lr.toList[(i : ℕ)]).1, point (inp.proof.lr.toList[(i : ℕ)]).2,
        sqEndo] := by
  simp only [roundBlock]
  rw [List.take_succ_eq_append_getElem hik, List.flatMap_append]
  simp

/-! ## The two scalar bridges -/

/-- **The round challenges, from any start state.** The scalar oracle at `preU i` is round `i`'s
challenge of the derivation started at `s₀`. -/
theorem spongeOScalarFrom_preU (s₀ : FqSponge.S C.base) (inp : Ipa.Input C k m p) (i : Fin k) :
    spongeOScalarFrom s₀ (preU inp i) = (Ipa.transcriptFrom C s₀ inp).2.1[i] := by
  have hik : (i : ℕ) < inp.proof.lr.toList.length := by simp
  -- The post-`challengeFq` state feeding the rounds (shared, verbatim, by both sides).
  have hpreT : (preT inp).foldl (fun s e => stepState C e s) s₀
      = (FqSponge.challengeFq C.sponge (FqSponge.absorbFr C.sponge s₀
          (Ipa.shiftScalar C (Ipa.cipOf inp)))).2 := by
    simp only [preT, preTAbsorbs, List.cons_append, List.nil_append, List.foldl_cons,
      List.foldl_nil, stepState]
  -- LHS: reduce the model fold to the endo-squeeze after round `i`'s two absorbs.
  have hLHS : spongeOScalarFrom s₀ (preU inp i)
      = (FqSponge.squeezeChallenge C.sponge (FqSponge.absorbG C.sponge (FqSponge.absorbG C.sponge
          (mstate C (FqSponge.challengeFq C.sponge (FqSponge.absorbFr C.sponge s₀
              (Ipa.shiftScalar C (Ipa.cipOf inp)))).2 (inp.proof.lr.toList.take (i : ℕ)))
          (inp.proof.lr.toList[(i : ℕ)]'hik).1) (inp.proof.lr.toList[(i : ℕ)]'hik).2)).1 := by
    simp only [spongeOScalarFrom, preU]
    rw [roundBlock_succ inp i hik, List.dropLast_append_of_ne_nil (by simp),
      List.dropLast_append_of_ne_nil (by simp)]
    rw [show ([point (inp.proof.lr.toList[(i : ℕ)]'hik).1,
          point (inp.proof.lr.toList[(i : ℕ)]'hik).2, sqEndo] :
          List (IpaTranscriptElt C)).dropLast
        = [point (inp.proof.lr.toList[(i : ℕ)]'hik).1,
          point (inp.proof.lr.toList[(i : ℕ)]'hik).2] from rfl]
    rw [List.foldl_append, List.foldl_append, hpreT]
    rw [show (roundBlock inp (i : ℕ)).foldl (fun s e => stepState C e s)
          (FqSponge.challengeFq C.sponge (FqSponge.absorbFr C.sponge s₀
            (Ipa.shiftScalar C (Ipa.cipOf inp)))).2
        = mstate C (FqSponge.challengeFq C.sponge (FqSponge.absorbFr C.sponge s₀
            (Ipa.shiftScalar C (Ipa.cipOf inp)))).2 (inp.proof.lr.toList.take (i : ℕ)) from by
        simp only [roundBlock]; exact flatMap_block_foldl _ _]
    simp only [List.foldl_cons, List.foldl_nil, stepState]
  -- RHS: the deployed challenge array read at `i`, via `roundChallengesAux_getElem?`.
  have hRHS : (Ipa.transcriptFrom C s₀ inp).2.1[i]
      = (FqSponge.squeezeChallenge C.sponge (FqSponge.absorbG C.sponge (FqSponge.absorbG C.sponge
          (mstate C (FqSponge.challengeFq C.sponge (FqSponge.absorbFr C.sponge s₀
              (Ipa.shiftScalar C (Ipa.cipOf inp)))).2 (inp.proof.lr.toList.take (i : ℕ)))
          (inp.proof.lr.toList[(i : ℕ)]'hik).1) (inp.proof.lr.toList[(i : ℕ)]'hik).2)).1 := by
    simp only [Ipa.transcriptFrom, Ipa.roundChallenges]
    have hsize : (i : ℕ) < (Ipa.roundChallengesAux C
        (FqSponge.challengeFq C.sponge (FqSponge.absorbFr C.sponge s₀
          (Ipa.shiftScalar C (Ipa.cipOf inp)))).2 inp.proof.lr.toArray).1.size := by
      rw [Ipa.roundChallengesAux_size]; simp
    have hg := roundChallengesAux_getElem? (FqSponge.challengeFq C.sponge
      (FqSponge.absorbFr C.sponge s₀ (Ipa.shiftScalar C (Ipa.cipOf inp)))).2
      inp.proof.lr.toArray (i : ℕ) hik
    rw [Array.getElem?_eq_getElem hsize] at hg
    exact Option.some.inj hg
  rw [hLHS, hRHS]

/-- **The round challenges.** The scalar oracle at `preU i` is round `i`'s challenge. -/
theorem spongeOScalar_preU (inp : Ipa.Input C k m p) (i : Fin k) :
    spongeOScalar (preU inp i) = (Ipa.transcriptFrom C FqSponge.init inp).2.1[i] :=
  spongeOScalarFrom_preU FqSponge.init inp i

/-- **The Schnorr challenge, from any start state.** The scalar oracle at `preC` is the `c` of
the derivation started at `s₀`. -/
theorem spongeOScalarFrom_preC (s₀ : FqSponge.S C.base) (inp : Ipa.Input C k m p) :
    spongeOScalarFrom s₀ (preC inp) = (Ipa.transcriptFrom C s₀ inp).2.2 := by
  have hlen : inp.proof.lr.toList.length = k := by simp
  have hpreT : (preT inp).foldl (fun s e => stepState C e s) s₀
      = (FqSponge.challengeFq C.sponge (FqSponge.absorbFr C.sponge s₀
          (Ipa.shiftScalar C (Ipa.cipOf inp)))).2 := by
    simp only [preT, preTAbsorbs, List.cons_append, List.nil_append, List.foldl_cons,
      List.foldl_nil, stepState]
  -- LHS: after dropping the trailing `sqEndo`, the fold ends by absorbing `δ` on the
  -- post-`k`-rounds model state.
  have hLHS : spongeOScalarFrom s₀ (preC inp)
      = (FqSponge.squeezeChallenge C.sponge (FqSponge.absorbG C.sponge
          (mstate C (FqSponge.challengeFq C.sponge (FqSponge.absorbFr C.sponge s₀
              (Ipa.shiftScalar C (Ipa.cipOf inp)))).2 inp.proof.lr.toList)
          inp.proof.delta)).1 := by
    simp only [spongeOScalarFrom, preC]
    rw [List.dropLast_append_of_ne_nil (by simp)]
    rw [show ([point inp.proof.delta, sqEndo] : List (IpaTranscriptElt C)).dropLast
        = [point inp.proof.delta] from rfl]
    rw [List.foldl_append, List.foldl_append, hpreT]
    rw [show (roundBlock inp k).foldl (fun s e => stepState C e s)
          (FqSponge.challengeFq C.sponge (FqSponge.absorbFr C.sponge s₀
            (Ipa.shiftScalar C (Ipa.cipOf inp)))).2
        = mstate C (FqSponge.challengeFq C.sponge (FqSponge.absorbFr C.sponge s₀
            (Ipa.shiftScalar C (Ipa.cipOf inp)))).2 inp.proof.lr.toList from by
        simp only [roundBlock]
        rw [show inp.proof.lr.toList.take k = inp.proof.lr.toList from by
          conv_rhs => rw [← List.take_length (l := inp.proof.lr.toList)]
          rw [hlen]]
        exact flatMap_block_foldl _ _]
    simp only [List.foldl_cons, List.foldl_nil, stepState]
  -- RHS: `c` is the endo-squeeze after absorbing `δ` on the deployed post-round state.
  have hRHS : (Ipa.transcriptFrom C s₀ inp).2.2
      = (FqSponge.squeezeChallenge C.sponge (FqSponge.absorbG C.sponge
          (mstate C (FqSponge.challengeFq C.sponge (FqSponge.absorbFr C.sponge s₀
              (Ipa.shiftScalar C (Ipa.cipOf inp)))).2 inp.proof.lr.toList)
          inp.proof.delta)).1 := by
    simp only [Ipa.transcriptFrom, Ipa.roundChallenges]
    rw [roundChallengesAux_snd]
    rfl
  rw [hLHS, hRHS]

/-- **The Schnorr challenge.** The scalar oracle at `preC` is `c`. -/
theorem spongeOScalar_preC (inp : Ipa.Input C k m p) :
    spongeOScalar (preC inp) = (Ipa.transcriptFrom C FqSponge.init inp).2.2 :=
  spongeOScalarFrom_preC FqSponge.init inp

/-! ## The abstract Fiat–Shamir interface, and Poseidon as one instance

The bridges above say the deployed challenges *are* reads of the sponge at transcript
prefixes. Since the prefixes `preT`/`preU`/`preC` are functions of the claim alone, the
challenge source becomes a parameter — the way `zcash/ironwood` writes its verifier — and the
deployed verifier is recovered as a theorem at the Poseidon source.

`verifyOracle` is the opening verifier over an arbitrary source; `spongeFSFrom C s₀` is the
deployed Poseidon one started at `s₀`, and `spongeFS C` its cold specialisation.
`verifyOracleFrom_spongeFSFrom` proves the abstract verifier at the warm Poseidon source *is*
`Ipa.verifyFrom C σ s₀`, and `verifyOracle_spongeFS` is that statement at the cold start, i.e.
`Ipa.verify`. Substituting a uniformly random source — what a forking argument rewinds and
reprograms — is then instantiating an argument, with the deployed verifier recovered as a
theorem rather than assumed. -/

/-- A source of opening challenges: a base-field squeeze for the `U` base and a scalar-field
squeeze for the round and Schnorr challenges, each a function of the transcript prefix. Two
squeezes rather than ironwood's one, because these two codomains differ. -/
structure FiatShamir (C : Ipa.CommitmentCurve) where
  /-- The raw base-field squeeze the `U` base is derived from. -/
  squeezeBase : List (IpaTranscriptElt C) → C.BaseField
  /-- The endo-expanded scalar squeeze of the round and Schnorr challenges. -/
  squeezeScalar : List (IpaTranscriptElt C) → C.ScalarField

/-- The opening transcript derived from a challenge source, at the prefixes the deployed
schedule draws each challenge at. -/
def transcriptOf (fs : FiatShamir C) (inp : Ipa.Input C k m p) :
    C.Point × Vector C.ScalarField k × C.ScalarField :=
  (C.toGroup (fs.squeezeBase (preT inp)),
   Vector.ofFn fun i => fs.squeezeScalar (preU inp i),
   fs.squeezeScalar (preC inp))

/-- The opening verifier over an arbitrary challenge source: the deployed algebra
(`Ipa.verifyWith`) at the challenges `fs` supplies. -/
def verifyOracle (fs : FiatShamir C) (σ : SRS C.Point)
    (inp : Ipa.Input C σ.k m p) : Bool :=
  let (uBase, chals, c) := transcriptOf fs inp
  Ipa.verifyWith C σ uBase chals c inp

/-- The deployed source **at an arbitrary start state**: the Poseidon sponge read at transcript
prefixes, folding from `s₀`. This is the form kimchi needs — it hands the opening verifier the
warm post-`ζ` fq-sponge state. -/
def spongeFSFrom (C : Ipa.CommitmentCurve) (s₀ : FqSponge.S C.base) : FiatShamir C :=
  ⟨spongeOBaseFrom s₀, spongeOScalarFrom s₀⟩

/-- The deployed source: the Poseidon sponge read at transcript prefixes from the cold start. -/
def spongeFS (C : Ipa.CommitmentCurve) : FiatShamir C :=
  ⟨spongeOBase, spongeOScalar⟩

/-- The cold Poseidon source is `spongeFSFrom` at `FqSponge.init`. -/
theorem spongeFS_eq_from (C : Ipa.CommitmentCurve) :
    spongeFS C = spongeFSFrom C FqSponge.init := rfl

/-- The opening transcript the deployed Poseidon source produces from the start state `s₀` —
`transcriptOf` at `spongeFSFrom`, named so the faithfulness statement below can be stated on
the derivation alone. -/
def transcriptOfFrom (C : Ipa.CommitmentCurve) (s₀ : FqSponge.S C.base)
    (inp : Ipa.Input C k m p) : C.Point × Vector C.ScalarField k × C.ScalarField :=
  transcriptOf (spongeFSFrom C s₀) inp

/-- The opening verifier at the deployed Poseidon source started at `s₀` — `verifyOracle` at
`spongeFSFrom`, the start-state-indexed counterpart of `Ipa.verifyFrom`. -/
def verifyOracleFrom (C : Ipa.CommitmentCurve) (σ : SRS C.Point) (s₀ : FqSponge.S C.base)
    (inp : Ipa.Input C σ.k m p) : Bool :=
  verifyOracle (spongeFSFrom C s₀) σ inp

/-- **The model derivation at a start state is the deployed derivation at that start state.**
The three bridges assembled componentwise; vector equality is checked entrywise. -/
theorem transcriptOfFrom_eq (s₀ : FqSponge.S C.base) (inp : Ipa.Input C k m p) :
    transcriptOfFrom C s₀ inp = Ipa.transcriptFrom C s₀ inp := by
  refine Prod.ext (toGroup_spongeOBaseFrom_preT s₀ inp)
    (Prod.ext ?_ (spongeOScalarFrom_preC s₀ inp))
  refine Vector.ext fun i hi => ?_
  simp only [transcriptOfFrom, transcriptOf, spongeFSFrom, Vector.getElem_ofFn]
  exact spongeOScalarFrom_preU s₀ inp ⟨i, hi⟩

/-- **The abstract verifier at the warm Poseidon source is the deployed verifier from that
state.** The form kimchi consumes: `s₀` is the post-`ζ` fq-sponge state the kimchi verifier
hands the opening check. -/
theorem verifyOracle_spongeFSFrom (σ : SRS C.Point) (s₀ : FqSponge.S C.base)
    (inp : Ipa.Input C σ.k m p) :
    verifyOracle (spongeFSFrom C s₀) σ inp = Ipa.verifyFrom C σ s₀ inp := by
  have ht : transcriptOf (spongeFSFrom C s₀) inp = Ipa.transcriptFrom C s₀ inp :=
    transcriptOfFrom_eq s₀ inp
  rw [verifyOracle, ht, Ipa.verifyFrom]

/-- **Faithfulness at an arbitrary start state.** `verifyOracleFrom` — the abstract verifier
fed the Poseidon source started at `s₀` — is `Ipa.verifyFrom` started at `s₀`. This is what
makes the abstraction honest at the warm start: the challenge source is a parameter, and the
deployed verifier is recovered as a theorem rather than assumed. -/
theorem verifyOracleFrom_spongeFSFrom (σ : SRS C.Point) (s₀ : FqSponge.S C.base)
    (inp : Ipa.Input C σ.k m p) :
    verifyOracleFrom C σ s₀ inp = Ipa.verifyFrom C σ s₀ inp :=
  verifyOracle_spongeFSFrom σ s₀ inp

/-- **The abstract verifier at the Poseidon source is the deployed verifier.** The cold
specialisation of `verifyOracle_spongeFSFrom`: `Ipa.verify` is `Ipa.verifyFrom` at
`FqSponge.init`. -/
theorem verifyOracle_spongeFS (σ : SRS C.Point) (inp : Ipa.Input C σ.k m p) :
    verifyOracle (spongeFS C) σ inp = Ipa.verify C σ inp :=
  verifyOracle_spongeFSFrom σ FqSponge.init inp

end Bulletproof.Ipa.Forking
