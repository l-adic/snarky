import Mathlib.Algebra.Field.Defs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! # The pickles `Shifted_value` algebra

Pure, field-level: the Type1/Type2 shift used to feed a scalar to the `VarBaseMul`
gate. None of this depends on the curve or the scalar-mul circuit — it is exactly the
`Shifted_value.to_field` / `of_field` arithmetic, so the circuit theorems can take it as a
primitive. -/

namespace Pasta.Shifted

variable {F : Type*} [Field F]

/-- `Shifted_value.Type1.to_field`: a scalar held as the shifted register `t` (over
    `numBits` bits) is recovered as `2·t + 2^numBits + 1`. -/
def unshiftType1 (numBits : ℕ) (t : F) : F := 2 * t + 2 ^ numBits + 1

/-- `Shifted_value.Type1.of_field`: the shifted register holding the scalar `s`,
    `(s − 2^numBits − 1) / 2` — the inverse of `unshiftType1`. It is also the encoding of a
    scalar absorbed into the Fiat-Shamir transcript when the scalar modulus is below the
    base modulus (`shift_scalar`, proof-systems `poly-commitment/src/commitment.rs`). -/
def shiftType1 (numBits : ℕ) (s : F) : F := (s - 2 ^ numBits - 1) / 2

/-- `Shifted_value.Type2` value `2·sHi + sOdd + 2^numBits` — the scalar `s + 2^numBits`
    for `s = 2·sHi + sOdd`, used when the scalar field is larger than the circuit
    field (so `s` is split into high bits `sHi` and low bit `sOdd`). -/
def unshiftType2 (numBits : ℕ) (sHi sOdd : F) : F := 2 * sHi + sOdd + 2 ^ numBits

/-- The Type2 shift `s − 2^numBits` — the transcript encoding of an absorbed scalar when
    the scalar field is the larger of the pair (`shift_scalar`,
    `poly-commitment/src/commitment.rs`, else branch). -/
def shiftType2 (numBits : ℕ) (s : F) : F := s - 2 ^ numBits

/-- The Type1 maps are mutually inverse (outside characteristic 2), unshift after shift. -/
theorem unshiftType1_shiftType1 (h2 : (2 : F) ≠ 0) (numBits : ℕ) (s : F) :
    unshiftType1 numBits (shiftType1 numBits s) = s := by
  unfold unshiftType1 shiftType1
  field_simp
  ring

/-- The Type1 maps are mutually inverse (outside characteristic 2), shift after unshift. -/
theorem shiftType1_unshiftType1 (h2 : (2 : F) ≠ 0) (numBits : ℕ) (t : F) :
    shiftType1 numBits (unshiftType1 numBits t) = t := by
  unfold unshiftType1 shiftType1
  field_simp
  ring

/-- The Type2 shift undoes the Type2 value, recovering the split scalar. -/
theorem shiftType2_unshiftType2 (numBits : ℕ) (sHi sOdd : F) :
    shiftType2 numBits (unshiftType2 numBits sHi sOdd) = 2 * sHi + sOdd := by
  unfold shiftType2 unshiftType2
  ring

end Pasta.Shifted
