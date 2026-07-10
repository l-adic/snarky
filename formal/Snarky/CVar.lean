/-!
# Circuit variables and affine expressions

Port of `Snarky.Circuit.CVar` (packages/snarky/src/Snarky/Circuit/CVar.purs): the `CVar`
type of affine expressions over allocated circuit variables, together with the prover-side
partial assignment (`Assignments`) they are evaluated against.

Everything here is core Lean (no Mathlib): evaluation only needs `Add`/`Mul` on the field,
and the whole `Snarky` library stays executable and fast to build.
-/

namespace Snarky

/-- A circuit variable: an index into the wire assignment, allocated sequentially by the
interpreters (PS `Variable`). -/
abbrev Variable := Nat

/-- A partial assignment of field values to variables — the prover's witness table
(PS `Assignments f`). -/
abbrev Assignments (F : Type u) := Variable → Option F

/-- Errors arising while running witness code or checking constraints during a prover run
(PS `EvaluationError`, extended with the prover-side failure modes). -/
inductive EvalError where
  /-- A variable was read before being assigned. -/
  | unassigned (v : Variable)
  /-- A variable was assigned twice (assignments may only grow). -/
  | conflict (v : Variable)
  /-- A constraint added via `addConstraint` does not hold on the current assignment. -/
  | unsatisfiedConstraint
  /-- A witness computation failed with a message (PS `throwAsProver`). -/
  | custom (msg : String)
  deriving Repr, DecidableEq

/-! ## Affine expressions -/

/-- Affine expressions over circuit variables (PS `CVar`): variables, constants, sums and
scalings. `sub x y` is expressible as `add x (scale (-1) y)` when `F` has negation, so it is
not a separate constructor. -/
inductive CVar (F : Type u) where
  | var (v : Variable)
  | const (c : F)
  | add (a b : CVar F)
  | scale (k : F) (x : CVar F)
  deriving Repr, DecidableEq

namespace CVar

/-- Evaluate an affine expression against a partial assignment, failing on the first
unassigned variable (PS `evalCVar`). Written with explicit `match` (not `do`) so proofs can
`split` on the intermediate results. -/
def eval [Add F] [Mul F] : CVar F → Assignments F → Except EvalError F
  | .var v, env =>
    match env v with
    | some x => .ok x
    | none => .error (.unassigned v)
  | .const k, _ => .ok k
  | .add a b, env =>
    match a.eval env with
    | .error e => .error e
    | .ok x =>
      match b.eval env with
      | .error e => .error e
      | .ok y => .ok (x + y)
  | .scale k x, env =>
    match x.eval env with
    | .error e => .error e
    | .ok y => .ok (k * y)

end CVar

/-! ## Assignments -/

namespace Assignments

/-- The empty assignment. -/
def empty : Assignments F := fun _ => none

/-- Assign `x` to `v`, leaving every other variable unchanged. -/
def extend (a : Assignments F) (v : Variable) (x : F) : Assignments F :=
  fun w => if w = v then some x else a w

end Assignments

end Snarky
