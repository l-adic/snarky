import Mathlib.Tactic.Ring

/-!
# Bit-vector values

The ℕ value of an LSB-first bit list, in Horner form — the one representation of
"the integer these bits spell" that the gate semantics (the `VarBaseMul` ladder's
register) and the circuit DSL (`unpack`, the canonicity locks) share. Everything
that reads bits as a number reads through `natLsbVal`; a consumer holding a
different orientation or carrier converts at its own seam, once.
-/

namespace Kimchi

/-- The ℕ value of bits, LSB first, in Horner form. -/
def natLsbVal : List Bool → Nat
  | [] => 0
  | b :: bs => b.toNat + 2 * natLsbVal bs

/-- The bits' value fits their width. -/
theorem natLsbVal_lt : ∀ l : List Bool, natLsbVal l < 2 ^ l.length := by
  intro l
  induction l with
  | nil => simp [natLsbVal]
  | cons b bs ih =>
    simp only [natLsbVal, List.length_cons, pow_succ]
    cases b <;> simp only [Bool.toNat_false, Bool.toNat_true] <;> omega

/-- The Horner form reconstructs a number from its bits, `ofFn` form. -/
theorem natLsbVal_ofFn_testBit :
    ∀ (n m : Nat), m < 2 ^ n →
      natLsbVal (List.ofFn fun i : Fin n => m.testBit i.val) = m := by
  intro n
  induction n with
  | zero =>
    intro m hm
    have h0 : m = 0 := by omega
    subst h0
    rfl
  | succ n ih =>
    intro m hm
    simp only [List.ofFn_succ, Fin.val_zero, Fin.val_succ]
    have htail : (List.ofFn fun i : Fin n => m.testBit (i.val + 1))
        = List.ofFn fun i : Fin n => (m / 2).testBit i.val := by
      congr 1
      funext i
      simp [Nat.testBit_add_one]
    rw [htail, natLsbVal, ih (m / 2) (by rw [pow_succ] at hm; omega)]
    have hbit := Nat.bit_testBit_zero_shiftRight_one m
    rw [Nat.shiftRight_one] at hbit
    cases htb : m.testBit 0 <;> rw [htb] at hbit <;> simp [Nat.bit] at hbit <;>
      simp <;> omega

/-- A number below `2^n` is the Horner fold of its first `n` bits, range-map form. -/
theorem natLsbVal_testBit_range {m n : Nat} (h : m < 2 ^ n) :
    natLsbVal ((List.range n).map m.testBit) = m := by
  rw [show (List.range n).map m.testBit = List.ofFn fun i : Fin n => m.testBit i.val by
    apply List.ext_getElem (by simp)
    intro i h1 h2
    simp]
  exact natLsbVal_ofFn_testBit n m h

/-- The Horner value splits at any position: low bits plus the shifted high bits. -/
theorem natLsbVal_take_drop : ∀ (k : Nat) (l : List Bool),
    natLsbVal l = natLsbVal (l.take k) + 2 ^ k * natLsbVal (l.drop k) := by
  intro k
  induction k with
  | zero => intro l; simp [natLsbVal]
  | succ k ih =>
    intro l
    cases l with
    | nil => simp [natLsbVal]
    | cons b bs =>
      simp only [List.take_succ_cons, List.drop_succ_cons, natLsbVal, ih bs, pow_succ]
      ring

/-- All-false bits carry the value zero. -/
theorem natLsbVal_eq_zero : ∀ {l : List Bool}, (∀ b ∈ l, b = false) → natLsbVal l = 0 := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons b bs ih =>
    intro h
    rw [natLsbVal, h b (List.mem_cons_self ..),
      ih fun x hx => h x (List.mem_cons_of_mem _ hx)]
    rfl

/-- A value whose bits vanish from position `k` on fits in `k` bits. -/
theorem natLsbVal_lt_of_drop_false {l : List Bool} {k : Nat}
    (h : ∀ b ∈ l.drop k, b = false) : natLsbVal l < 2 ^ k := by
  rw [natLsbVal_take_drop k l, natLsbVal_eq_zero h, Nat.mul_zero, Nat.add_zero]
  exact lt_of_lt_of_le (natLsbVal_lt _)
    (Nat.pow_le_pow_right (by omega) (List.length_take_le k l))

end Kimchi
