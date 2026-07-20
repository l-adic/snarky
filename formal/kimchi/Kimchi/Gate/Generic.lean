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
    polynomial lift (`Kimchi/Quotient/Gate/Generic.lean`) consumes `Generic.Holds`. -/

namespace Kimchi.Gate

variable {F : Type*} [Field F]

/-- A generic gate row: 15 coefficient cells `q` and 15 witness cells `w`. -/
structure Generic (F : Type*) where
  /-- The 15 coefficient cells (`q 10 … q 14` unused). -/
  q : Fin 15 → F
  /-- The 15 witness cells. -/
  w : Fin 15 → F

/-- Relabel both cell families through `f` — the functorial action of `Generic`. Instantiating
    at a ring homomorphism moves a row between rings, in particular between
    `Generic (Polynomial F)` (the quotient layer's column polynomials) and `Generic F` (their
    values at a domain node). -/
def Generic.map {R S : Type*} (f : R → S) (g : Generic R) : Generic S :=
  ⟨f ∘ g.q, f ∘ g.w⟩

/-- The two constraint expressions, as ring elements — the single transcription; the relational
    spec (`Holds`), the checker (`ok`), and the quotient layer's constraint polynomials are all
    read from it. -/
def Generic.constraints {R : Type*} [CommRing R] (g : Generic R) : List R :=
  [ g.q 0 * g.w 0 + g.q 1 * g.w 1 + g.q 2 * g.w 2 + g.q 3 * (g.w 0 * g.w 1) + g.q 4
  , g.q 5 * g.w 3 + g.q 6 * g.w 4 + g.q 7 * g.w 5 + g.q 8 * (g.w 3 * g.w 4) + g.q 9 ]

/-- Relational spec — both constraint expressions vanish (a `Prop`). -/
def Generic.Holds (g : Generic F) : Prop :=
  ∀ e ∈ g.constraints, e = 0

/-- The row with a public input folded in: kimchi's row check subtracts `public[row]`
from the *first* operation's constraint (`verify_generic`:
`sum + mul + qC − public = 0`), which is the plain constraint of the row whose first
constant coefficient — `q 4` in the packed `[l, r, o, m, c | l', r', o', m', c']`
layout — absorbs the public value. -/
def Generic.withPublic (g : Generic F) (p : F) : Generic F :=
  ⟨Function.update g.q 4 (g.q 4 - p), g.w⟩

/-- Folding in a zero public input is the identity — the sanity check of the layout. -/
theorem Generic.withPublic_zero (g : Generic F) : g.withPublic 0 = g := by
  simp [withPublic]

instance [DecidableEq F] (g : Generic F) : Decidable g.Holds := by
  unfold Generic.Holds
  infer_instance

/-- `Holds` as the two readable cell equations. -/
theorem Generic.holds_iff (g : Generic F) :
    g.Holds ↔
      (g.q 0 * g.w 0 + g.q 1 * g.w 1 + g.q 2 * g.w 2 + g.q 3 * (g.w 0 * g.w 1) + g.q 4 = 0
        ∧ g.q 5 * g.w 3 + g.q 6 * g.w 4 + g.q 7 * g.w 5 + g.q 8 * (g.w 3 * g.w 4) + g.q 9 = 0) := by
  simp only [Generic.Holds, Generic.constraints, List.forall_mem_cons, List.not_mem_nil,
    false_implies, implies_true, and_true]

/-- `Holds` of a public-folded row, as the *plain* cell equations with the public value
moved across the first equality: folding `p` into `q 4` is exactly requiring the plain
first constraint to evaluate to `p`. This is how the aggregate family's slot-`0` public
subtraction meets `rowSatisfies`' `withPublic` semantics. -/
theorem Generic.withPublic_holds_iff (g : Generic F) (p : F) :
    (g.withPublic p).Holds ↔
      (g.q 0 * g.w 0 + g.q 1 * g.w 1 + g.q 2 * g.w 2 + g.q 3 * (g.w 0 * g.w 1) + g.q 4 = p
        ∧ g.q 5 * g.w 3 + g.q 6 * g.w 4 + g.q 7 * g.w 5 + g.q 8 * (g.w 3 * g.w 4) + g.q 9
            = 0) := by
  have h4 : (g.withPublic p).q 4 = g.q 4 - p := Function.update_self 4 _ g.q
  have hne : ∀ j : Fin 15, j ≠ 4 → (g.withPublic p).q j = g.q j := fun j hj =>
    Function.update_of_ne hj _ g.q
  have hw : (g.withPublic p).w = g.w := rfl
  rw [Generic.holds_iff, h4, hne 0 (by decide), hne 1 (by decide), hne 2 (by decide),
    hne 3 (by decide), hne 5 (by decide), hne 6 (by decide), hne 7 (by decide),
    hne 8 (by decide), hne 9 (by decide), hw]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨by linear_combination h1, h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨by linear_combination h1, h2⟩

/-- Executable checker — every constraint expression evaluates to zero. -/
def Generic.ok [DecidableEq F] (g : Generic F) : Bool :=
  g.constraints.all (· == 0)

theorem Generic.ok_iff [DecidableEq F] (g : Generic F) : g.ok = true ↔ g.Holds := by
  simp only [Generic.ok, Generic.Holds, List.all_eq_true, beq_iff_eq]

/-- Naturality: the constraint expressions commute with ring homomorphisms applied cellwise
    via `Generic.map`. At `f = eval (ω^i) : F[X] →+* F` this turns the quotient layer's
    constraint polynomials' values at a domain node into the gate constraints of that row. -/
theorem Generic.constraints_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (g : Generic R) : g.constraints.map f = (g.map f).constraints := by
  simp [Generic.constraints, Generic.map]

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
