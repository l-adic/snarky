import Mathlib.Algebra.Field.Defs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! # The pickles shifted-value algebra

The two shifts that encode a scalar for the `VarBaseMul` gate and for the Fiat–Shamir
transcript, with their inverses and round-trip lemmas. Type1 applies when the scalar modulus
is below the base modulus, Type2 when it is above.

Transcribes Mina's `plonkish_prelude/shifted_value.ml` and the scalar shift in proof-systems
`poly-commitment/src/commitment.rs`. The unshifts are semiring polynomials, read over the
circuit field for the wire pin and over `ℤ` for the group scalar; the shifts and round trips
need a field. -/

namespace Pasta.Shifted

variable {F : Type*}

/-- Recover a scalar from the shifted register `t` that holds it over `numBits` bits:
    `2·t + 2^numBits + 1`. -/
def unshiftType1 [Semiring F] (numBits : ℕ) (t : F) : F := 2 * t + 2 ^ numBits + 1

/-- The shifted register holding the scalar `s`, `(s − 2^numBits − 1) / 2`, inverse to
    `unshiftType1`. -/
def shiftType1 [Field F] (numBits : ℕ) (s : F) : F := (s - 2 ^ numBits - 1) / 2

/-- The Type2 value `s + 2^numBits` of the scalar `s = 2·sHi + sOdd`, which arrives split
    into high bits `sHi` and low bit `sOdd` because the scalar field is the larger one. -/
def unshiftType2 [Semiring F] (numBits : ℕ) (sHi sOdd : F) : F :=
  2 * sHi + sOdd + 2 ^ numBits

/-- The Type2 shift `s − 2^numBits`. -/
def shiftType2 [Field F] (numBits : ℕ) (s : F) : F := s - 2 ^ numBits

variable [Field F]

/-- Type1 unshift after shift is the identity outside characteristic 2. -/
theorem unshiftType1_shiftType1 (h2 : (2 : F) ≠ 0) (numBits : ℕ) (s : F) :
    unshiftType1 numBits (shiftType1 numBits s) = s := by
  unfold unshiftType1 shiftType1
  field_simp
  ring

/-- Type1 shift after unshift is the identity outside characteristic 2. -/
theorem shiftType1_unshiftType1 (h2 : (2 : F) ≠ 0) (numBits : ℕ) (t : F) :
    shiftType1 numBits (unshiftType1 numBits t) = t := by
  unfold unshiftType1 shiftType1
  field_simp
  ring

/-- The Type2 shift recovers the split scalar from its Type2 value. -/
theorem shiftType2_unshiftType2 (numBits : ℕ) (sHi sOdd : F) :
    shiftType2 numBits (unshiftType2 numBits sHi sOdd) = 2 * sHi + sOdd := by
  unfold shiftType2 unshiftType2
  ring

end Pasta.Shifted
