import Kimchi.Domain

/-!
# Shifted columns: the two-row-gate mechanism

Polynomial-algebra infrastructure. **Commitment-free**: everything lives over
an abstract field `[Field F]` with a primitive `n`-th root of unity supplied as a hypothesis.
This file provides the "next row" access that a two-row custom gate (`VarBaseMul`, `EndoMul`)
needs on the polynomial side.

**NOTE:** this is a NEW file `Kimchi/Shifted.lean`, distinct from the read-only
`Kimchi/Shifted.lean`.

A two-row custom gate constrains cells of the current row *and* of the next row. On the
polynomial side, the "next row" of a column polynomial `W` is read by pre-composing with the
rotation `X ↦ ω·X`: evaluating `shift ω W` at the node `ω^i` yields `W (ω^(i+1))`, the column's
value one row down.

Here `i + 1 : Fin n` is taken **cyclically**: at the last row `i = n - 1` it wraps to `0`. This
loses nothing for honest circuits — a two-row gate is never placed on the last row of the
domain — so the cyclic convention agrees with the intended semantics on every row a two-row
gate actually occupies.

## Contents

* `shift` — the column-shift operator `W ↦ W ∘ (C ω · X)`.
* `eval_shift` — `(shift ω W)(x) = W(ω·x)`.
* `eval_shift_columnPoly` — the shift reads the next column value: `(shift ω (columnPoly ω v))
  (ω^i) = v (i + 1)` (cyclic).
-/

namespace Kimchi

open Polynomial

variable {F : Type*} [Field F] {n : ℕ} {ω : F}

/-! ## The shift operator -/

/-- **Column shift.** For `ω : F` and `W ∈ F[X]`, `shift ω W = W ∘ (C ω · X)` — the composition
of `W` with the linear rotation `X ↦ ω·X`. -/
noncomputable def shift (ω : F) (W : Polynomial F) : Polynomial F :=
  W.comp (C ω * X)

/-- **The shift evaluates at the rotated point.** For every `ω x : F` and `W ∈ F[X]`,
`(shift ω W)(x) = W(ω·x)`. -/
private theorem eval_shift (ω : F) (W : Polynomial F) (x : F) :
    (shift ω W).eval x = W.eval (ω * x) := by
  unfold shift
  rw [eval_comp, eval_mul, eval_C, eval_X]

/-! ## Reading the next row of a column polynomial -/

/-- **The shift reads the next column value.** With `[NeZero n]` and a primitive `n`-th root
`ω`, for a column `v : Fin n → F` and `i : Fin n`,
`(shift ω (columnPoly ω v))(ω^i) = v (i + 1)`, where `i + 1 : Fin n` is cyclic. -/
theorem eval_shift_columnPoly [NeZero n] (hω : IsPrimitiveRoot ω n) (v : Fin n → F) (i : Fin n) :
    (shift ω (columnPoly ω v)).eval (ω ^ (i : ℕ)) = v (i + 1) := by
  rw [eval_shift]
  have hmod : ∀ a : ℕ, ω ^ a = ω ^ (a % n) := by
    intro a
    conv_lhs => rw [← Nat.div_add_mod a n, pow_add, pow_mul, hω.pow_eq_one, one_pow, one_mul]
  have key : ω * ω ^ (i : ℕ) = ω ^ (((i + 1 : Fin n) : ℕ)) := by
    rw [← pow_succ', hmod ((i : ℕ) + 1), hmod (((i + 1 : Fin n) : ℕ))]
    congr 1
    have h1 : ((i + 1 : Fin n) : ℕ) = ((i : ℕ) + (1 : Fin n).val) % n := Fin.val_add i 1
    rw [h1, Nat.mod_mod, Fin.val_one']
    conv_rhs => rw [Nat.add_mod, Nat.mod_mod]
    conv_lhs => rw [Nat.add_mod]
  rw [key, eval_columnPoly hω]

end Kimchi
