import Kimchi.Verifier.Forking.Transcript

/-!
# W4 · The finite oracle domain

Every table measure in the toolkit — `PMF.uniformOfFintype (T → F)`, and in particular
`Zcash.Snark.uniformOfFintype_fresh_read_bound`, which transports W3's challenge-vector bounds to
oracle tables — requires `Fintype T`. Our transcript domains are lists, hence infinite.

`zcash/ironwood` meets the same wall and resolves it by bounding transcript *length*
(`BTranscript`): the alphabet is finite, so length-`≤ L` lists are finite. This module mirrors that
for our two transcripts. The bound is not a loss of substance — a query-bounded adversary reaches
only finitely many points, and every prefix the deployed verifier reads has a statically known
length (`preZeta_length_le` below pins ours).

The two sides differ:

* the fq alphabet is list-free (`fqPoint`, `fqBase`, `fqCast`, `fqEndo`), so it is finite outright,
  from `Fintype (SWPoint E)` and `Fintype (ZMod C.base)`;
* the fr alphabet is **not** — `frAbsorb` carries an unbounded `List C.ScalarField`, so no bound on
  transcript length makes it finite. `BFrElt C M` is the domain-only bounded-absorb variant
  (absorb lists of length `≤ M`); the deployed schedule only ever absorbs singletons and `nc`-chunk
  vectors, so `M := max 1 nc` is respected. The W2/W3 fr statements are untouched.
-/

namespace Kimchi.Verifier.Forking

open Bulletproof

variable {C : Ipa.CommitmentCurve}

/-! ## The fq alphabet is finite -/

instance : Finite (KimchiTranscriptElt C) :=
  Finite.of_injective
    (fun e => match e with
      | .fqPoint P => Sum.inl P
      | .fqBase x => Sum.inr (Sum.inl x)
      | .fqCast => Sum.inr (Sum.inr false)
      | .fqEndo => Sum.inr (Sum.inr true))
    (by intro a b h; cases a <;> cases b <;> simp_all)

/-- The finite fq oracle domain: transcripts of length at most `L`. -/
def BKimchiTranscript (C : Ipa.CommitmentCurve) (L : ℕ) : Type _ :=
  {l : List (KimchiTranscriptElt C) // l.length ≤ L}

namespace BKimchiTranscript

instance {L : ℕ} : Finite (BKimchiTranscript C L) := by
  refine Finite.of_injective (fun t => (fun i : Fin L => t.val[(i : ℕ)]?)) ?_
  intro a b h
  apply Subtype.ext
  apply List.ext_getElem?
  intro n
  by_cases hn : n < L
  · exact congrFun h ⟨n, hn⟩
  · rw [List.getElem?_eq_none (le_trans a.prop (not_lt.mp hn)),
      List.getElem?_eq_none (le_trans b.prop (not_lt.mp hn))]

noncomputable instance {L : ℕ} : Fintype (BKimchiTranscript C L) := Fintype.ofFinite _

noncomputable instance {L : ℕ} : DecidableEq (BKimchiTranscript C L) := Classical.decEq _

end BKimchiTranscript

/-! ## The fr alphabet: a bounded-absorb variant

`FrTranscriptElt` is infinite because `frAbsorb` carries an arbitrary list. `BFrElt C M` bounds the
absorbed list, which the deployed schedule respects (singletons and `nc`-chunk vectors). -/

/-- An fr transcript element with its absorb list bounded by `M` — the domain-only variant. -/
inductive BFrElt (C : Ipa.CommitmentCurve) (M : ℕ) where
  /-- Absorb a scalar list of length at most `M`. -/
  | frAbsorb : {l : List C.ScalarField // l.length ≤ M} → BFrElt C M
  /-- An endo-expanded squeeze. -/
  | frEndo : BFrElt C M

/-- Forget the bound: the erasure into the W2/W3 fr alphabet, so the domain variant and the
statements stay connected. -/
def BFrElt.toFrElt {M : ℕ} : BFrElt C M → FrTranscriptElt C
  | .frAbsorb l => .frAbsorb l.val
  | .frEndo => .frEndo

instance {M : ℕ} : Finite (BFrElt C M) := by
  have hfin : Finite {l : List C.ScalarField // l.length ≤ M} := by
    refine Finite.of_injective (fun t => (fun i : Fin M => t.val[(i : ℕ)]?)) ?_
    intro a b h
    apply Subtype.ext
    apply List.ext_getElem?
    intro n
    by_cases hn : n < M
    · exact congrFun h ⟨n, hn⟩
    · rw [List.getElem?_eq_none (le_trans a.prop (not_lt.mp hn)),
        List.getElem?_eq_none (le_trans b.prop (not_lt.mp hn))]
  exact Finite.of_injective
    (fun e => match e with
      | .frAbsorb l => Sum.inl l
      | .frEndo => Sum.inr ())
    (by intro a b h; cases a <;> cases b <;> simp_all)

/-- The finite fr oracle domain: bounded-absorb transcripts of length at most `L`. -/
def BFrTranscript (C : Ipa.CommitmentCurve) (M L : ℕ) : Type _ :=
  {l : List (BFrElt C M) // l.length ≤ L}

namespace BFrTranscript

instance {M L : ℕ} : Finite (BFrTranscript C M L) := by
  refine Finite.of_injective (fun t => (fun i : Fin L => t.val[(i : ℕ)]?)) ?_
  intro a b h
  apply Subtype.ext
  apply List.ext_getElem?
  intro n
  by_cases hn : n < L
  · exact congrFun h ⟨n, hn⟩
  · rw [List.getElem?_eq_none (le_trans a.prop (not_lt.mp hn)),
      List.getElem?_eq_none (le_trans b.prop (not_lt.mp hn))]

noncomputable instance {M L : ℕ} : Fintype (BFrTranscript C M L) := Fintype.ofFinite _

noncomputable instance {M L : ℕ} : DecidableEq (BFrTranscript C M L) := Classical.decEq _

end BFrTranscript

/-! ## The deployed prefixes have statically bounded length

`L` is a parameter of the W4 capstones; these give the concrete lower bound it must satisfy, so the
bound is never vacuous. -/

variable {nc k : ℕ}

open KimchiTranscriptElt in
/-- The longest fq prefix — `ζ`'s — has length `1 + nc + 15·nc + nc + |tComm| + 4`. -/
theorem preZeta_length (cvk : KimchiVK C nc) (cp : KimchiProof C nc k)
    (publicComm : Vector C.Point nc) :
    (preZeta cvk cp publicComm).length = 5 + 17 * nc + cp.tComm.size := by
  simp [preZeta, preAlpha, preGamma, preBeta, preAbsorbs, wCommAbsorbs,
    List.length_flatMap]
  omega

end Kimchi.Verifier.Forking
