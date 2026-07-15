/-!
# Circuit variables and affine expressions

Port of `Snarky.Circuit.CVar` (packages/snarky/src/Snarky/Circuit/CVar.purs): the `CVar`
type of affine expressions over allocated circuit variables, together with the prover-side
partial assignment (`Assignments`) they are evaluated against.

Everything here is core Lean (no Mathlib): evaluation only needs `Add`/`Mul` on the field,
and the whole `Snarky` library stays executable and fast to build.

The `Assignments.Le` order ("every assigned variable keeps its value") is the backbone of
the completeness proof in `Snarky.Laws`: the prover only ever *extends* assignments (the
guarded `extendPairs` errors on any re-assignment), so constraint checks performed early in a
run remain valid against the final assignment.
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

/-! ## The extension order on assignments -/

namespace Assignments

/-- The empty assignment. -/
def empty : Assignments F := fun _ => none

/-- Assign `x` to `v`, leaving every other variable unchanged. -/
def extend (a : Assignments F) (v : Variable) (x : F) : Assignments F :=
  fun w => if w = v then some x else a w

/-- Guarded batch extension: assign each `(variable, value)` pair left to right, erroring
on any variable that is already assigned — this is what makes prover runs monotone in
`Assignments.Le`. Callers zip equal-length allocation and witness vectors, so pairing is
total by construction and the only failure mode is a re-assignment. -/
def extendPairs (a : Assignments F) : List (Variable × F) → Except EvalError (Assignments F)
  | [] => .ok a
  | (v, x) :: rest =>
    match a v with
    | some _ => .error (.conflict v)
    | none => (a.extend v x).extendPairs rest

/-- `a.Le a'` iff every variable assigned in `a` has the same value in `a'` — assignments
only ever grow during a prover run. -/
protected def Le (a a' : Assignments F) : Prop :=
  ∀ v x, a v = some x → a' v = some x

protected theorem Le.refl (a : Assignments F) : a.Le a := fun _ _ h => h

protected theorem Le.trans {a b c : Assignments F} (h₁ : a.Le b) (h₂ : b.Le c) : a.Le c :=
  fun v x h => h₂ v x (h₁ v x h)

theorem le_extend {a : Assignments F} {v : Variable} (hv : a v = none) (x : F) :
    a.Le (a.extend v x) := by
  intro w y hw
  simp only [extend]
  split
  · next hwv => rw [hwv, hv] at hw; cases hw
  · exact hw

theorem le_extendPairs {a a' : Assignments F} :
    ∀ {l : List (Variable × F)}, a.extendPairs l = .ok a' → a.Le a' := by
  intro l
  induction l generalizing a with
  | nil =>
    intro h
    simp only [extendPairs, Except.ok.injEq] at h
    subst h
    exact Assignments.Le.refl a
  | cons vx rest ih =>
    obtain ⟨v, x⟩ := vx
    intro h
    simp only [extendPairs] at h
    split at h
    · cases h
    · next hnone => exact (le_extend hnone x).trans (ih h)

end Assignments

/-! ## Evaluation is monotone in the extension order -/

namespace CVar

/-- Successful evaluations are stable under assignment extension: the value of an affine
expression cannot change once all its variables are assigned. -/
theorem eval_le [Add F] [Mul F] {a a' : Assignments F} (hle : a.Le a') {x : CVar F} {v : F}
    (h : x.eval a = .ok v) : x.eval a' = .ok v := by
  induction x generalizing v with
  | var w =>
    simp only [eval] at h ⊢
    split at h
    · next y hy => rw [hle w y hy]; exact h
    · cases h
  | const k => exact h
  | add p q ihp ihq =>
    simp only [eval] at h ⊢
    split at h
    · cases h
    · next xa hxa =>
      split at h
      · cases h
      · next xb hxb => rw [ihp hxa, ihq hxb]; exact h
  | scale k p ih =>
    simp only [eval] at h ⊢
    split at h
    · cases h
    · next y hy => rw [ih hy]; exact h

end CVar

end Snarky
