import Mathlib.Algebra.Field.Defs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! # The pickles `Shifted_value` algebra

The two shifts that encode a scalar for the `VarBaseMul` gate, with their inverses and
round-trip lemmas. Which one applies is fixed by which field of the pair is larger: Type1
when the scalar modulus is below the base modulus, Type2 when it is above.

Nothing here mentions the curve or the scalar-mul circuit. It transcribes
`Shifted_value.to_field` / `of_field` directly, so the circuit theorems can take it as a
primitive. The unshifts are semiring polynomials — the ladder laws read them over the
circuit field for the wire pin and over `ℤ` for the group scalar; the shifts and the
round trips need a field. -/

namespace Pasta.Shifted

variable {F : Type*}

/-- Recover a scalar from the shifted register `t` that holds it over `numBits` bits:
    `2·t + 2^numBits + 1`. This is `Shifted_value.Type1.to_field`. -/
def unshiftType1 [Semiring F] (numBits : ℕ) (t : F) : F := 2 * t + 2 ^ numBits + 1

/-- The shifted register holding the scalar `s`, `(s − 2^numBits − 1) / 2` — the inverse of
    `unshiftType1`, and `Shifted_value.Type1.of_field`. It is also how a scalar is encoded
    when absorbed into the Fiat–Shamir transcript and the scalar modulus is below the base
    modulus (`shift_scalar`, proof-systems `poly-commitment/src/commitment.rs`). -/
def shiftType1 [Field F] (numBits : ℕ) (s : F) : F := (s - 2 ^ numBits - 1) / 2

/-- The `Shifted_value.Type2` value `2·sHi + sOdd + 2^numBits`, which is `s + 2^numBits` for
    the scalar `s = 2·sHi + sOdd`. The scalar arrives already split into high bits `sHi` and
    low bit `sOdd`, because the scalar field is larger than the circuit field. -/
def unshiftType2 [Semiring F] (numBits : ℕ) (sHi sOdd : F) : F :=
  2 * sHi + sOdd + 2 ^ numBits

/-- The Type2 shift `s − 2^numBits` — how an absorbed scalar is encoded into the transcript
    when the scalar field is the larger of the pair (`shift_scalar`, the else branch in
    proof-systems `poly-commitment/src/commitment.rs`). -/
def shiftType2 [Field F] (numBits : ℕ) (s : F) : F := s - 2 ^ numBits

variable [Field F]

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
