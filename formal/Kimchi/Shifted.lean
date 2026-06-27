import Mathlib

/-! # The pickles `Shifted_value` algebra

Pure, field-level: the Type1/Type2 shift used to feed a scalar to the `VarBaseMul`
gate. None of this depends on the curve or the scalar-mul circuit — it is exactly the
`Shifted_value.to_field` arithmetic, so the circuit theorems can take it as a primitive. -/

namespace Kimchi.Shifted

variable {F : Type*} [Field F]

/-- `Shifted_value.Type1.to_field`: a scalar held as the shifted register `t` (over
    `numBits` bits) is recovered as `2·t + 2^numBits + 1`. -/
def unshiftType1 (numBits : ℕ) (t : F) : F := 2 * t + 2 ^ numBits + 1

/-- `Shifted_value.Type2` value `2·sHi + sOdd + 2^numBits` — the scalar `s + 2^numBits`
    for `s = 2·sHi + sOdd`, used when the scalar field is larger than the circuit
    field (so `s` is split into high bits `sHi` and low bit `sOdd`). -/
def unshiftType2 (numBits : ℕ) (sHi sOdd : F) : F := 2 * sHi + sOdd + 2 ^ numBits

end Kimchi.Shifted
