import Mathlib

/-! # The pickles `Shifted_value` algebra

Pure, field-level: the Type1/Type2 shift used to feed a scalar to the `VarBaseMul`
gate, its round-trip, and the cross-field range coincidence. None of this depends on
the curve or the scalar-mul circuit — it is exactly the `Shifted_value.{to_field,
of_field}` arithmetic, so the circuit theorems can take it as a primitive. -/

namespace Kimchi.Shifted

variable {F : Type*} [Field F]

/-- `Shifted_value.Type1.to_field`: a scalar held as the shifted register `t` (over
    `numBits` bits) is recovered as `2·t + 2^numBits + 1`. -/
def unshiftType1 (numBits : ℕ) (t : F) : F := 2 * t + 2 ^ numBits + 1

/-- `Shifted_value.Type1.of_field`: `(s − 2^numBits − 1)/2`, the left inverse of
    `unshiftType1` (needs char ≠ 2). -/
def shiftType1 (numBits : ℕ) (s : F) : F := (s - 2 ^ numBits - 1) / 2

/-- Round-trip `unshift ∘ shift = id` (char ≠ 2): `to_field`/`of_field` recover `s`. -/
theorem unshiftType1_shiftType1 (h2 : (2 : F) ≠ 0) (numBits : ℕ) (s : F) :
    unshiftType1 numBits (shiftType1 numBits s) = s := by
  rw [unshiftType1, shiftType1]
  field_simp
  ring

/-- `Shifted_value.Type2` value `2·sHi + sOdd + 2^numBits` — the scalar `s + 2^numBits`
    for `s = 2·sHi + sOdd`, used when the scalar field is larger than the circuit
    field (so `s` is split into high bits `sHi` and low bit `sOdd`). -/
def unshiftType2 (numBits : ℕ) (sHi sOdd : F) : F := 2 * sHi + sOdd + 2 ^ numBits

/-- Cross-field coincidence: in characteristic `p`, two integers whose images agree
    and whose difference is smaller than `p` are equal. This upgrades a coordinate-
    field equation to an honest integer equality once a `Shifted_value` range bound
    `|n − s| < p` holds — the base- and scalar-field reductions then coincide. -/
theorem intCast_inj_of_sub_lt {p : ℕ} [CharP F p] {n s : ℤ}
    (h : (n : F) = (s : F)) (hlt : (n - s).natAbs < p) : n = s := by
  have hz : ((n - s : ℤ) : F) = 0 := by push_cast; rw [h]; ring
  have hdvd : (p : ℤ) ∣ (n - s) := (CharP.intCast_eq_zero_iff F p (n - s)).mp hz
  have h0 : n - s = 0 :=
    Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hdvd (by rw [Int.natAbs_natCast]; exact hlt)
  omega

end Kimchi.Shifted
