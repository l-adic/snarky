import Pickles.CheckBulletproof

/-!
# The shifted scalars a group half scales by

Every shifted scalar a deployed group half scales by is one its ladder reads
(`IvpSide.ClaimOk`): the ladders' tops are below `4·order − 4`, where no accumulator meets
`±T` (`HasCurve.LadderRegime`), so no scalar value is excluded. What remains is the step side's
well-formedness: the parity cell of a split scalar reads as a bit, which the deployed circuit
gets from the split type's allocation check.

## Main results

* `wrapSide_claimOk`: every wrap-side scalar satisfies `IvpSide.ClaimOk`;
* `stepSide_claimOk_of_bit`: a step-side scalar with a boolean parity cell satisfies
  `IvpSide.ClaimOk`.
-/

namespace Pickles

open Std.Do Snarky Snarky.Kimchi Bulletproof Bulletproof.Ipa
open CompElliptic.Fields.Pasta

/-- A pinned ladder input's top `2z + 2^255 + 1` is below `4·order − 4` at either Pasta order. -/
private theorem top_lt_of_pinned {q : ℕ} (hq : 2 ^ 254 < q) {z : ℤ} (hlt : z < 2 ^ 254) :
    Pasta.Shifted.unshiftType1 255 z < 4 * q - 4 := by
  have hqZ : (2 : ℤ) ^ 254 < q := by exact_mod_cast hq
  simp only [Pasta.Shifted.unshiftType1]
  have h255 : (2 : ℤ) ^ 255 = 2 * 2 ^ 254 := by norm_num
  have h1 : (2 : ℤ) ^ 254 + 1 ≤ q := by omega
  linarith

/-- Every wrap-side scalar is one the ladder reads: its witness is below `2^254`. -/
theorem wrapSide_claimOk (V : Valuation Fq) (x : Type1 (FVar Fq)) : (wrapSide V).ClaimOk x := by
  change True ∧ ∀ z : ℤ, WrapLadderPre V x z → WrapLadderReg z
  refine ⟨trivial, fun z hpre => ?_⟩
  exact HasCurve.vesta_ladderRegime _
    (top_lt_of_pinned (by norm_num [PALLAS_BASE_CARD]) hpre.2.1)

/-- A step-side scalar whose parity cell reads as a bit is one the ladder reads: the ladders'
tops are below `4·order − 4` at every pinned input. -/
theorem stepSide_claimOk_of_bit {V : Valuation Fp} (x : Type2 (SplitField (FVar Fp) (BoolVar Fp)))
    (hb : ∃ bb : Bool, (↑x.val.sOdd : CVar Fp).val V = bit bb) : (stepSide V).ClaimOk x := by
  change (∃ bb : Bool, (↑x.val.sOdd : CVar Fp).val V = bit bb) ∧
    ∀ w : ℤ × Bool, StepLadderPre V x w → StepLadderReg w
  exact ⟨hb, fun w hpre => HasCurve.pallas_ladderRegime _
    (top_lt_of_pinned (by norm_num [PALLAS_SCALAR_CARD]) hpre.2.2.1)⟩

variable {c : Type}

end Pickles
