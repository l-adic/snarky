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

/-- **The round challenges.** The scalar oracle at `preU i` is round `i`'s challenge. -/
theorem spongeOScalar_preU (inp : Ipa.Input C k m p) (i : Fin k) :
    spongeOScalar (preU inp i) = (Ipa.transcriptFrom C FqSponge.init inp).2.1[i] := by
  sorry

/-- **The Schnorr challenge.** The scalar oracle at `preC` is `c`. -/
theorem spongeOScalar_preC (inp : Ipa.Input C k m p) :
    spongeOScalar (preC inp) = (Ipa.transcriptFrom C FqSponge.init inp).2.2 := by
  sorry

end Bulletproof.Ipa.Forking
