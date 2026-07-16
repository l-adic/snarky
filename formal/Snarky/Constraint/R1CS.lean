import Snarky.Constraint.Basic

/-!
# The plain R1CS constraint model

A minimal concrete backend for the DSL: rank-1 constraints `a · b = prod` over affine
expressions, with a decidable checker and its monotonicity in the assignment-extension
order — everything `Snarky.prove` and `Snarky.prove_sound` need from a backend. Core
Lean only, so the whole model stays `decide`-friendly; `Snarky.Example` exercises it end
to end.
-/

namespace Snarky.Constraint

open Snarky

/-- A rank-1 constraint `a * b = prod` over affine expressions. -/
structure R1CS (F : Type u) where
  a : CVar F
  b : CVar F
  prod : CVar F
  deriving Repr, DecidableEq

instance {F : Type u} : BasicSystem F (R1CS F) where
  r1cs a b prod := ⟨a, b, prod⟩
  boolean x := ⟨x, x, x⟩

/-- Decide a constraint against an assignment: all three expressions evaluate and the
product identity holds. -/
def R1CS.holds {F : Type u} [Add F] [Mul F] [DecidableEq F] (con : R1CS F)
    (env : Assignments F) : Bool :=
  match con.a.eval env, con.b.eval env, con.prod.eval env with
  | .ok x, .ok y, .ok z => decide (x * y = z)
  | _, _, _ => false

/-- `R1CS.holds` is monotone in the assignment-extension order — the hypothesis
`Snarky.prove_sound` needs, discharged once per backend via `CVar.eval_le`. -/
theorem R1CS.holds_mono {F : Type u} [Add F] [Mul F] [DecidableEq F] {con : R1CS F}
    {env env' : Assignments F} (hle : env.Le env') (h : con.holds env = true) :
    con.holds env' = true := by
  unfold R1CS.holds at h ⊢
  split at h
  · next hx hy hz =>
    rw [CVar.eval_le hle hx, CVar.eval_le hle hy, CVar.eval_le hle hz]
    exact h
  · cases h

end Snarky.Constraint
