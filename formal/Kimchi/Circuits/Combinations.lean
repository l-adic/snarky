import Kimchi.Circuits.VarBaseMulStep
import Kimchi.Circuits.EndoMulStep
import Kimchi.Circuits.EndoScalarStep
import Kimchi.Circuits.PoseidonStep

/-!
# Heterogeneous gate-combination examples

The `Circuits/*Step.lean` proofs each compose a *homogeneous* chain of one gate kind. Real pickles
sub-circuits interleave kinds, and the ingested `Circuit` model already supports that (its
`rowHolds` dispatches per kind). This file demonstrates it: for **every unordered pair** of the five
custom gate kinds — `CompleteAdd`, `VarBaseMul`, `EndoMul`, `EndoMulScalar`, `Poseidon` — a concrete
two-block example circuit, and a soundness lemma showing its `Satisfies` yields *both* gates'
algebraic facts (each via its own checker↔gate bridge), independently and simultaneously.

Each gate occupies a block: `CompleteAdd` / `EndoMulScalar` one row; `VarBaseMul` / `EndoMul` /
`Poseidon` a row plus its output row. Blocks are concatenated; the soundness lemma reads each block
off `gatesHold` at its offset. The residual per-kind side conditions are exactly those of the
single-gate bridges (`EndoMul`'s distinct-point `hdist`, `EndoMulScalar`'s `2, 3 ≠ 0`, `Poseidon`'s
round constants), surfaced as hypotheses.
-/

namespace Kimchi.Circuit.Combinations

open Kimchi.Circuit (Gate Circuit Witness Satisfies)

variable {F : Type*} [Field F] [DecidableEq F]

/-! ## Per-kind gate blocks and their extracted facts. -/

def zeroG : Gate F := ⟨.zero, #[], #[]⟩
def caG : Gate F := ⟨.completeAdd, #[], #[]⟩
def vbG : Gate F := ⟨.varBaseMul, #[], #[]⟩
def emG : Gate F := ⟨.endoMul, #[], #[]⟩
def esG : Gate F := ⟨.endoMulScalar, #[], #[]⟩
def poG (pc : Array F) : Gate F := ⟨.poseidon, pc, #[]⟩

/-- `CompleteAdd` at row `r` computes a genuine EC addition (its algebraic `Holds`). -/
abbrev CAFact (w : Witness F) (r : ℕ) : Prop :=
  Kimchi.Gate.AddComplete.Holds (Kimchi.Gate.AddComplete.ofRow (w.row r))

/-- `VarBaseMul` at rows `r, r+1`. -/
abbrev VBFact (w : Witness F) (r : ℕ) : Prop :=
  Kimchi.Gate.VarBaseMul.Holds (Kimchi.Gate.VarBaseMul.ofRows (w.row r) (w.row (r + 1)))

/-- `EndoMul` at rows `r, r+1` (at the checker's fixed `endo`). -/
abbrev EMFact (w : Witness F) (r : ℕ) : Prop :=
  Kimchi.Gate.EndoMul.Holds Kimchi.Checker.EndoMul.endo
    (Kimchi.Gate.EndoMul.ofRows (w.row r) (w.row (r + 1)))

/-- `EndoMulScalar` at row `r`. -/
abbrev ESFact (w : Witness F) (r : ℕ) : Prop :=
  Kimchi.Gate.EndoScalar.Holds (Kimchi.Gate.EndoScalar.ofRows (w.row r))

/-- `Poseidon` at rows `r, r+1`: the output state is one row-permutation of the input. -/
abbrev POFact (w : Witness F) (pc : Array F) (r : ℕ) : Prop :=
  ((w.row (r + 1)).getD 0 0, (w.row (r + 1)).getD 1 0, (w.row (r + 1)).getD 2 0)
    = Kimchi.Gate.Poseidon.rowPerm pc ((w.row r).getD 0 0, (w.row r).getD 1 0, (w.row r).getD 2 0)

/-- The distinct-point non-degeneracy `EndoMul`'s bridge needs at row `r`. -/
abbrev EMDist (w : Witness F) (r : ℕ) : Prop :=
  ((Kimchi.Gate.EndoMul.ofRows (w.row r) (w.row (r + 1))).xP
      - (Kimchi.Gate.EndoMul.ofRows (w.row r) (w.row (r + 1))).xR)
    * ((Kimchi.Gate.EndoMul.ofRows (w.row r) (w.row (r + 1))).xR
      - (Kimchi.Gate.EndoMul.ofRows (w.row r) (w.row (r + 1))).xS) ≠ 0

/-! ## The ten pairwise example circuits and their soundness lemmas.

`gatesHold` at each block's offset gives that row's `rowHolds`, which is *definitionally* the block
gate's checker predicate; each fact then follows by that gate's bridge. -/

/-- CompleteAdd + VarBaseMul. -/
def exCA_VB : Circuit F := ⟨0, #[caG, vbG, zeroG]⟩
theorem exCA_VB_sound (w : Witness F) (pub : Array F) (hsat : Satisfies exCA_VB w pub) :
    CAFact w 0 ∧ VBFact w 1 := by
  obtain ⟨hg, _⟩ := hsat
  exact ⟨hg 0 (by show 0 < 3; decide),
    (Kimchi.Gate.VarBaseMul.checker_holds_iff _ _).1 (hg 1 (by show 1 < 3; decide))⟩

/-- CompleteAdd + EndoMul. -/
def exCA_EM : Circuit F := ⟨0, #[caG, emG, zeroG]⟩
theorem exCA_EM_sound (w : Witness F) (pub : Array F) (hsat : Satisfies exCA_EM w pub)
    (hdist : EMDist w 1) : CAFact w 0 ∧ EMFact w 1 := by
  obtain ⟨hg, _⟩ := hsat
  exact ⟨hg 0 (by show 0 < 3; decide),
    (Kimchi.Gate.EndoMul.checker_holds_iff _ _).2 ⟨hg 1 (by show 1 < 3; decide), hdist⟩⟩

/-- CompleteAdd + EndoMulScalar. -/
def exCA_ES : Circuit F := ⟨0, #[caG, esG]⟩
theorem exCA_ES_sound (w : Witness F) (pub : Array F) (hsat : Satisfies exCA_ES w pub)
    (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) : CAFact w 0 ∧ ESFact w 1 := by
  obtain ⟨hg, _⟩ := hsat
  exact ⟨hg 0 (by show 0 < 2; decide),
    (Kimchi.Gate.EndoScalar.checker_holds_iff h2 h3 (w.row 1) (w.row 2)).2
      (hg 1 (by show 1 < 2; decide))⟩

/-- CompleteAdd + Poseidon. -/
def exCA_PO (pc : Array F) : Circuit F := ⟨0, #[caG, poG pc, zeroG]⟩
theorem exCA_PO_sound (pc : Array F) (w : Witness F) (pub : Array F)
    (hsat : Satisfies (exCA_PO pc) w pub) : CAFact w 0 ∧ POFact w pc 1 := by
  obtain ⟨hg, _⟩ := hsat
  exact ⟨hg 0 (by show 0 < 3; decide),
    Kimchi.Gate.Poseidon.holds_rowPerm pc _ _ (hg 1 (by show 1 < 3; decide))⟩

/-- VarBaseMul + EndoMul. -/
def exVB_EM : Circuit F := ⟨0, #[vbG, zeroG, emG, zeroG]⟩
theorem exVB_EM_sound (w : Witness F) (pub : Array F) (hsat : Satisfies exVB_EM w pub)
    (hdist : EMDist w 2) : VBFact w 0 ∧ EMFact w 2 := by
  obtain ⟨hg, _⟩ := hsat
  exact ⟨(Kimchi.Gate.VarBaseMul.checker_holds_iff _ _).1 (hg 0 (by show 0 < 4; decide)),
    (Kimchi.Gate.EndoMul.checker_holds_iff _ _).2 ⟨hg 2 (by show 2 < 4; decide), hdist⟩⟩

/-- VarBaseMul + EndoMulScalar. -/
def exVB_ES : Circuit F := ⟨0, #[vbG, zeroG, esG]⟩
theorem exVB_ES_sound (w : Witness F) (pub : Array F) (hsat : Satisfies exVB_ES w pub)
    (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) : VBFact w 0 ∧ ESFact w 2 := by
  obtain ⟨hg, _⟩ := hsat
  exact ⟨(Kimchi.Gate.VarBaseMul.checker_holds_iff _ _).1 (hg 0 (by show 0 < 3; decide)),
    (Kimchi.Gate.EndoScalar.checker_holds_iff h2 h3 (w.row 2) (w.row 3)).2
      (hg 2 (by show 2 < 3; decide))⟩

/-- VarBaseMul + Poseidon. -/
def exVB_PO (pc : Array F) : Circuit F := ⟨0, #[vbG, zeroG, poG pc, zeroG]⟩
theorem exVB_PO_sound (pc : Array F) (w : Witness F) (pub : Array F)
    (hsat : Satisfies (exVB_PO pc) w pub) : VBFact w 0 ∧ POFact w pc 2 := by
  obtain ⟨hg, _⟩ := hsat
  exact ⟨(Kimchi.Gate.VarBaseMul.checker_holds_iff _ _).1 (hg 0 (by show 0 < 4; decide)),
    Kimchi.Gate.Poseidon.holds_rowPerm pc _ _ (hg 2 (by show 2 < 4; decide))⟩

/-- EndoMul + EndoMulScalar. -/
def exEM_ES : Circuit F := ⟨0, #[emG, zeroG, esG]⟩
theorem exEM_ES_sound (w : Witness F) (pub : Array F) (hsat : Satisfies exEM_ES w pub)
    (hdist : EMDist w 0) (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) : EMFact w 0 ∧ ESFact w 2 := by
  obtain ⟨hg, _⟩ := hsat
  exact ⟨(Kimchi.Gate.EndoMul.checker_holds_iff _ _).2 ⟨hg 0 (by show 0 < 3; decide), hdist⟩,
    (Kimchi.Gate.EndoScalar.checker_holds_iff h2 h3 (w.row 2) (w.row 3)).2
      (hg 2 (by show 2 < 3; decide))⟩

/-- EndoMul + Poseidon. -/
def exEM_PO (pc : Array F) : Circuit F := ⟨0, #[emG, zeroG, poG pc, zeroG]⟩
theorem exEM_PO_sound (pc : Array F) (w : Witness F) (pub : Array F)
    (hsat : Satisfies (exEM_PO pc) w pub) (hdist : EMDist w 0) :
    EMFact w 0 ∧ POFact w pc 2 := by
  obtain ⟨hg, _⟩ := hsat
  exact ⟨(Kimchi.Gate.EndoMul.checker_holds_iff _ _).2 ⟨hg 0 (by show 0 < 4; decide), hdist⟩,
    Kimchi.Gate.Poseidon.holds_rowPerm pc _ _ (hg 2 (by show 2 < 4; decide))⟩

/-- EndoMulScalar + Poseidon. -/
def exES_PO (pc : Array F) : Circuit F := ⟨0, #[esG, poG pc, zeroG]⟩
theorem exES_PO_sound (pc : Array F) (w : Witness F) (pub : Array F)
    (hsat : Satisfies (exES_PO pc) w pub) (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) :
    ESFact w 0 ∧ POFact w pc 1 := by
  obtain ⟨hg, _⟩ := hsat
  exact ⟨(Kimchi.Gate.EndoScalar.checker_holds_iff h2 h3 (w.row 0) (w.row 1)).2
      (hg 0 (by show 0 < 3; decide)),
    Kimchi.Gate.Poseidon.holds_rowPerm pc _ _ (hg 1 (by show 1 < 3; decide))⟩

end Kimchi.Circuit.Combinations
