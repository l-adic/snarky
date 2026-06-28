import Mathlib

/-!
# Base-4 digit recovery (the `EndoScalar` uniqueness kernel)

The number-theoretic kernel behind `EndoScalar`'s self-contained soundness: a list of
field crumbs, each a 2-bit value in `{0,1,2,3}`, reconstructs to a challenge base-4
(MSB-first), and that decoding is *injective* once it does not wrap past the field size.

It is pure positional arithmetic — independent of the gate, the curve, and the circuit's
`nReconstruct`/`decomposeA` folds — so it lives apart from `Kimchi.Circuit.EndoScalar`,
which imports it and bridges its `valNat` shadow to the field-valued `nReconstruct`.

## Main results

* `digit_cast` — on a valid crumb the `ℕ` digit casts back to the field element.
* `valNat_cons` / `valNat_lt` — the Horner step of the base-4 value, and its `< 4 ^ len`
  bound (the no-wrap budget).
* `euclid_split` — the digit-recovery step: `high · M + low` with `low < M` recovers
  `high` and `low` uniquely.
* `valNat_inj` — same-length valid crumb lists with equal value are equal.
-/

namespace Kimchi.Circuit.EndoScalar

variable {F : Type*} [Field F] [DecidableEq F]

/-- The base-4 digit a crumb stands for (`0` off the valid set). -/
def digit (x : F) : ℕ := if x = 1 then 1 else if x = 2 then 2 else if x = 3 then 3 else 0

/-- The natural-number value a crumb list reconstructs to, base-4 MSB-first — the `ℕ`
    shadow of `nReconstruct`, used to transport the field equality to an integer one where
    the no-wrap bound makes base-4 decoding injective. -/
def valNat (xs : List F) : ℕ := xs.foldl (fun n x => 4 * n + digit x) 0

theorem digit_lt_four (x : F) : digit x < 4 := by
  unfold digit; split_ifs <;> omega

/-- On a valid crumb the digit casts back to the crumb. -/
theorem digit_cast (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) {x : F}
    (hx : x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3) : ((digit x : ℕ) : F) = x := by
  have h1 : (1 : F) ≠ 0 := one_ne_zero
  rcases hx with rfl | rfl | rfl | rfl
  · unfold digit
    rw [if_neg (fun h => h1 h.symm), if_neg (fun h => h2 h.symm),
      if_neg (fun h => h3 h.symm), Nat.cast_zero]
  · unfold digit; rw [if_pos rfl, Nat.cast_one]
  · unfold digit
    rw [if_neg (fun h => h1 (by linear_combination h)), if_pos rfl, Nat.cast_ofNat]
  · unfold digit
    rw [if_neg (fun h => h2 (by linear_combination h)),
      if_neg (fun h => h1 (by linear_combination h)), if_pos rfl, Nat.cast_ofNat]

/-- Peeling the most significant crumb: `valNat (x :: xs) = digit x · 4^|xs| + valNat xs`. -/
theorem valNat_cons (x : F) (xs : List F) :
    valNat (x :: xs) = digit x * 4 ^ xs.length + valNat xs := by
  -- `gen`: folding from an arbitrary carry is that carry shifted up by `4^|ys|`, plus `valNat`
  have gen : ∀ (ys : List F) (acc : ℕ),
      ys.foldl (fun n x => 4 * n + digit x) acc = acc * 4 ^ ys.length + valNat ys := by
    intro ys
    induction ys with
    | nil => intro acc; simp [valNat]
    | cons y ys ihy =>
      intro acc
      have hv : valNat (y :: ys) = digit y * 4 ^ ys.length + valNat ys := by
        rw [show valNat (y :: ys)
            = ys.foldl (fun n x => 4 * n + digit x) (4 * 0 + digit y) from rfl, ihy]
        ring
      rw [List.foldl_cons, ihy (4 * acc + digit y), List.length_cons, pow_succ, hv]
      ring
  rw [show valNat (x :: xs)
      = xs.foldl (fun n x => 4 * n + digit x) (4 * 0 + digit x) from rfl, gen]
  ring

theorem valNat_lt (xs : List F) : valNat xs < 4 ^ xs.length := by
  induction xs with
  | nil => simp [valNat]
  | cons x xs ih =>
    rw [valNat_cons, List.length_cons, pow_succ]
    have hx := digit_lt_four x
    nlinarith [ih, Nat.zero_le (valNat xs), Nat.zero_le (4 ^ xs.length)]

omit [Field F] [DecidableEq F] in
/-- Euclidean split at base `M`: a low part below `M` and a high digit are uniquely
    recoverable from `high · M + low`. The base-4 digit-recovery step. -/
theorem euclid_split {a b c d M : ℕ} (hb : b < M) (hd : d < M)
    (h : a * M + b = c * M + d) : a = c ∧ b = d := by
  have hM : 0 < M := lt_of_le_of_lt (Nat.zero_le b) hb
  have ha : (a * M + b) / M = a := by
    rw [add_comm (a * M) b, Nat.add_mul_div_right b a hM, Nat.div_eq_of_lt hb, Nat.zero_add]
  have hc : (c * M + d) / M = c := by
    rw [add_comm (c * M) d, Nat.add_mul_div_right d c hM, Nat.div_eq_of_lt hd, Nat.zero_add]
  have hac : a = c := by rw [← ha, ← hc, h]
  subst hac; exact ⟨rfl, by omega⟩

/-- Nat-level base-4 uniqueness: valid same-length crumb lists with equal `valNat` are
    equal. The crumbs being digits `< 4` makes each `valNat_cons` layer a `euclid_split`. -/
theorem valNat_inj (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (xs ys : List F)
    (hx : ∀ x ∈ xs, x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3)
    (hy : ∀ x ∈ ys, x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3)
    (hlen : xs.length = ys.length) (hnat : valNat xs = valNat ys) : xs = ys := by
  induction xs generalizing ys with
  | nil => cases ys with
    | nil => rfl
    | cons y ys => simp at hlen
  | cons x xs ih => cases ys with
    | nil => simp at hlen
    | cons y ys =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
      rw [valNat_cons, valNat_cons, hlen] at hnat
      obtain ⟨hdig, htail⟩ := euclid_split (hlen ▸ valNat_lt xs) (valNat_lt ys) hnat
      have hxy : x = y := by
        rw [← digit_cast h2 h3 (hx x (by simp)), ← digit_cast h2 h3 (hy y (by simp)), hdig]
      rw [hxy, ih ys (fun z hz => hx z (by simp [hz])) (fun z hz => hy z (by simp [hz]))
        hlen htail]

end Kimchi.Circuit.EndoScalar
