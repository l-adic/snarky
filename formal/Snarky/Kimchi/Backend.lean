import Snarky.Constraint.Basic
import Snarky.Prover
import Kimchi.Gate.Generic

/-!
# A Kimchi Generic-gate backend for the DSL

The DSL of `Snarky.*` keeps its constraint type `c` abstract. This module instantiates it
at a constraint that maps to Kimchi's **Generic gate** (`Kimchi.Gate.Generic`), building
the bridge the `prove_sound` docstring points at: the constraints a DSL circuit emits
become Generic gate rows whose `Holds` predicate is exactly what `Kimchi.Index.rowSatisfies`
dispatches to for generic rows.

## The constraint type: a symbolic Generic gate

`GateConstraint` is one Generic-gate row *symbolically*: the five coefficients `q₀…q₄` of
the first packed constraint, plus three operand expressions `a b o` that will sit in
witness cells `w₀ w₁ w₂`. Its meaning is exactly that constraint,
`q₀·⟦a⟧ + q₁·⟦b⟧ + q₂·⟦o⟧ + q₃·(⟦a⟧·⟦b⟧) + q₄ = 0` (⟦·⟧ = eval against the assignment),
and `toRow` writes it to a `Gate.Generic` row verbatim. This mirrors kimchi's real gate:
the coefficient cells carry the affine structure, so linear/equality constraints can fold
constants into `q₄` rather than into a witness cell.

The two `BasicSystem` constructors are special cases: `r1cs a b prod` is
`(a·b) − prod = 0` (`q₃ = 1, q₂ = -1`), and `boolean x` is `x² − x = 0` (same coefficients,
all three operands `x`). The richer type is deliberately Index-ready — carrying the
coefficients is what the wired `Kimchi.Index` bridge (`Snarky.Kimchi.Compile`) needs to
place operands in cells and fold constants, and it is why `c` is the symbolic gate rather
than a bare `a·b = prod` triple.

## What is (and isn't) bridged here

This module bridges to the **un-wired Generic gate list** (`Gate.Satisfies : List (Generic
F) → Prop`). Because every row is evaluated against the *same* assignment, a variable
shared across constraints gets the same value in each row it appears in — so
variable-sharing holds by construction, but it is **not** enforced as a copy constraint.
Enforcing sharing via the wiring permutation is the wired `Kimchi.Index` bridge (domain
synthesis + placement), which builds on this constraint type.

This module (and everything under `Snarky.Kimchi.*`) imports Mathlib via `Kimchi`; the
core `Snarky` library (`import Snarky`) stays Mathlib-free.
-/

namespace Snarky.Kimchi

open Snarky Kimchi.Gate

variable {F : Type*} [Field F] [DecidableEq F]

/-! ## The constraint type -/

/-- One Generic-gate row, symbolically: the five coefficients `q₀…q₄` of the first packed
constraint and three operand expressions `a b o` for witness cells `w₀ w₁ w₂`. Its meaning
is `q₀·⟦a⟧ + q₁·⟦b⟧ + q₂·⟦o⟧ + q₃·(⟦a⟧·⟦b⟧) + q₄ = 0`. Explicit `qᵢ` fields (not
`Fin 5 → F`) so `DecidableEq` derives and the row reduces under `decide`. -/
structure GateConstraint (F : Type*) where
  q0 : F
  q1 : F
  q2 : F
  q3 : F
  q4 : F
  a : CVar F
  b : CVar F
  o : CVar F
  deriving Repr, DecidableEq

/-- `r1cs a b prod` is `(a·b) − prod = 0` (`q₃ = 1`, `q₂ = -1`); `boolean x` is `x² − x = 0`
(the same coefficients on the three operands `x`). -/
instance : BasicSystem F (GateConstraint F) where
  r1cs a b prod := { q0 := 0, q1 := 0, q2 := -1, q3 := 1, q4 := 0, a := a, b := b, o := prod }
  boolean x := { q0 := 0, q1 := 0, q2 := -1, q3 := 1, q4 := 0, a := x, b := x, o := x }

/-- The affine-bilinear form of a constraint, as a field value — the single transcription
shared by `holds`, `toRow`, and the correspondence. -/
def GateConstraint.form (con : GateConstraint F) (x y z : F) : F :=
  con.q0 * x + con.q1 * y + con.q2 * z + con.q3 * (x * y) + con.q4

/-- Decide a constraint against an assignment: the three operands evaluate and the
affine-bilinear form vanishes. The constraint checker the prover runs. -/
def GateConstraint.holds (con : GateConstraint F) (env : Assignments F) : Bool :=
  match con.a.eval env, con.b.eval env, con.o.eval env with
  | .ok x, .ok y, .ok z => decide (con.form x y z = 0)
  | _, _, _ => false

/-- `holds` is monotone in the assignment-extension order — the hypothesis
`Snarky.prove_sound` needs, discharged via `CVar.eval_le`. -/
theorem GateConstraint.holds_mono {con : GateConstraint F} {env env' : Assignments F}
    (hle : env.Le env') (h : con.holds env = true) : con.holds env' = true := by
  unfold GateConstraint.holds at h ⊢
  split at h
  · next hx hy hz =>
    rw [CVar.eval_le hle hx, CVar.eval_le hle hy, CVar.eval_le hle hz]
    exact h
  · cases h

/-! ## Translation to a Generic gate row -/

/-- Translate a constraint, evaluated against `env`, into a Generic gate row: the operand
values fill witness cells `w₀ w₁ w₂`, the constraint's own coefficients fill `q₀…q₄` (the
second packed constraint's cells and coefficients are `0`, so it holds trivially). `none`
exactly when an operand fails to evaluate (an unassigned variable). -/
def GateConstraint.toRow (con : GateConstraint F) (env : Assignments F) :
    Option (Generic F) :=
  match con.a.eval env, con.b.eval env, con.o.eval env with
  | .ok x, .ok y, .ok z =>
    some { q := ![con.q0, con.q1, con.q2, con.q3, con.q4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
           w := ![x, y, z, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }
  | _, _, _ => none

/-- **The correspondence.** The prover's decidable check on a constraint agrees exactly
with the Generic gate's `Holds` on the row it translates to: `holds` succeeds iff the
constraint evaluates and the resulting row is a satisfying Generic gate. This is the
per-constraint core of the soundness bridge (`Snarky.Kimchi.satisfies_of_prove`). -/
theorem GateConstraint.holds_iff_row (con : GateConstraint F) (env : Assignments F) :
    con.holds env = true ↔ ∃ row, con.toRow env = some row ∧ row.Holds := by
  unfold GateConstraint.holds GateConstraint.toRow
  cases hx : con.a.eval env with
  | error e => simp
  | ok x =>
    cases hy : con.b.eval env with
    | error e => simp
    | ok y =>
      cases hz : con.o.eval env with
      | error e => simp
      | ok z =>
        simp only [Option.some.injEq, exists_eq_left']
        rw [Generic.holds_iff]
        -- the row's first constraint is `con.form x y z` definitionally (the `![…] i`
        -- cell lookups are `rfl`), and its second is `0 = 0` up to `simp`
        exact ⟨fun h => ⟨of_decide_eq_true h, by simp⟩, fun h => decide_eq_true h.1⟩

end Snarky.Kimchi
