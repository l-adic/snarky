import Mathlib.Algebra.Field.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic

/-! # The generic gate: two linear+bilinear constraints on one row, the "all rows
    hold" relation, and the executable checker that decides it.

    kimchi has a single generic gate — the *double* generic gate (`generic.rs`,
    `CONSTRAINTS = 2`). One row carries 15 witness cells `w` and 15 coefficient
    cells `q`, and packs two constraints:

      q₀·w₀ + q₁·w₁ + q₂·w₂ + q₃·(w₀·w₁) + q₄ = 0     -- registers w₀ w₁ w₂, coeffs q₀…q₄
      q₅·w₃ + q₆·w₄ + q₇·w₅ + q₈·(w₃·w₄) + q₉ = 0     -- registers w₃ w₄ w₅, coeffs q₅…q₉

    (`q₁₀…q₁₄` are unused.) There is no standalone single-constraint gate; the
    polynomial lift (`Kimchi/Quotient/Generic.lean`) consumes `Generic.Holds`. -/

namespace Kimchi.Gate

variable {F : Type*} [Field F]

/-- A generic gate row: 15 coefficient cells `q` and 15 witness cells `w`. -/
structure Generic (F : Type*) where
  /-- The 15 coefficient cells (`q 10 … q 14` unused). -/
  q : Fin 15 → F
  /-- The 15 witness cells. -/
  w : Fin 15 → F

/-- Relational spec — both packed constraints hold (a `Prop`). -/
def Generic.Holds (g : Generic F) : Prop :=
  g.q 0 * g.w 0 + g.q 1 * g.w 1 + g.q 2 * g.w 2 + g.q 3 * (g.w 0 * g.w 1) + g.q 4 = 0
    ∧ g.q 5 * g.w 3 + g.q 6 * g.w 4 + g.q 7 * g.w 5 + g.q 8 * (g.w 3 * g.w 4) + g.q 9 = 0

/-- Executable checker — both constraints as a `Bool`. -/
def Generic.ok [DecidableEq F] (g : Generic F) : Bool :=
  (g.q 0 * g.w 0 + g.q 1 * g.w 1 + g.q 2 * g.w 2 + g.q 3 * (g.w 0 * g.w 1) + g.q 4 == 0)
    && (g.q 5 * g.w 3 + g.q 6 * g.w 4 + g.q 7 * g.w 5 + g.q 8 * (g.w 3 * g.w 4) + g.q 9 == 0)

theorem Generic.ok_iff [DecidableEq F] (g : Generic F) : g.ok = true ↔ g.Holds := by
  simp [Generic.ok, Generic.Holds]

/-- **Soundness:** a row accepted by the executable checker satisfies both constraints.
    (The gate is a decidable predicate, so soundness is one direction of `ok_iff`; the
    other is `complete`.) -/
theorem Generic.sound [DecidableEq F] (g : Generic F) : g.ok = true → g.Holds := g.ok_iff.mp

/-- **Completeness:** a row satisfying both constraints is accepted by the executable
    checker. (The converse direction of `ok_iff`.) -/
theorem Generic.complete [DecidableEq F] (g : Generic F) : g.Holds → g.ok = true := g.ok_iff.mpr

/-- A generic circuit is a list of rows; it holds when every row does. -/
def Satisfies (rows : List (Generic F)) : Prop := ∀ g ∈ rows, g.Holds

/-- Executable checker for a whole circuit. -/
def satisfies [DecidableEq F] (rows : List (Generic F)) : Bool := rows.all (·.ok)

theorem satisfies_iff [DecidableEq F] (rows : List (Generic F)) :
    satisfies rows = true ↔ Satisfies rows := by
  simp [satisfies, Satisfies, List.all_eq_true, Generic.ok_iff]

/-! ## Runnable example over `ZMod 17`

A row whose first half asserts `w₀ · w₁ = w₂` (as `w₂ − w₀·w₁ = 0`: coefficients
`q₂ = 1`, `q₃ = -1`) and whose second half is the trivial `0 = 0`. -/

instance : Fact (Nat.Prime 17) := ⟨by norm_num⟩

/-- Coefficient cells asserting `w₀ · w₁ = w₂` on the first half, trivial on the second. -/
def egQ : Fin 15 → ZMod 17 := ![0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- A satisfying row: `3 · 4 = 12` in `ZMod 17`. -/
def egGood : Generic (ZMod 17) :=
  { q := egQ, w := ![3, 4, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

/-- A failing row: `3 · 4 ≠ 13`. -/
def egBad : Generic (ZMod 17) :=
  { q := egQ, w := ![3, 4, 13, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

#eval satisfies [egGood]   -- true
#eval satisfies [egBad]    -- false

end Kimchi.Gate
