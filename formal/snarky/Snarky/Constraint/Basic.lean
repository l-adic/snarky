import Snarky.Backend.Assignments

/-!
# The basic constraint vocabulary

Port of `Snarky.Constraint.Basic` (packages/snarky/src/Snarky/Constraint/Basic.purs): the
concrete `Basic` constraint type — the four fundamental constraints most ZK backends
support — its decidable satisfaction check, and the `BasicSystem` class abstracting over
backend constraint representations so the DSL can emit constraints without naming a
backend. `Basic` is the reference instance; gadgets are written against `BasicSystem`,
never against `Basic` (the PS discipline).

Deviations from the PS original (ledger: `formal/docs/snarky-ps-alignment.md`):
- PS `eval : (Variable -> m f) -> Basic f -> m Boolean` is `Basic.holds : Basic F →
  Assignments F → Bool` — an evaluation failure reads as "unsatisfied" (`false`)
  rather than a monadic error.
- PS `r1cs` takes a record `{left, right, output}`; here three positional arguments.
- `debugCheck` (PS debug-mode message rendering) and `genWithAssignments` (the
  QuickCheck generator) are not ported.
- The PS functional dependency `c -> f` is not modelled; the class stays
  two-parameter.
-/

namespace Snarky

/-- The basic constraint type over the field `F` (PS `Basic f`): the fundamental
constraints supported by most ZK backends. -/
inductive Basic (F : Type u) where
  /-- Rank-1 constraint: `left * right = output`. -/
  | r1cs (left right output : CVar F)
  /-- Equality constraint: the two expressions must be equal. -/
  | equal (a b : CVar F)
  /-- Square constraint: `a * a = c`. -/
  | square (a c : CVar F)
  /-- Booleanity constraint: the expression must evaluate to `0` or `1`. -/
  | boolean (v : CVar F)
  deriving Repr, DecidableEq

/-- Decide a constraint against an assignment (PS `eval`, with evaluation failure read as
"unsatisfied"): every operand evaluates and the case's identity holds. Written with
explicit `match` so proofs can `split` on the evaluations. -/
def Basic.holds [Add F] [Mul F] [Zero F] [One F] [DecidableEq F] :
    Basic F → Assignments F → Bool
  | .r1cs l r o, env =>
    match l.eval env, r.eval env, o.eval env with
    | .ok x, .ok y, .ok z => decide (x * y = z)
    | _, _, _ => false
  | .equal a b, env =>
    match a.eval env, b.eval env with
    | .ok x, .ok y => decide (x = y)
    | _, _ => false
  | .square a c, env =>
    match a.eval env, c.eval env with
    | .ok x, .ok z => decide (x * x = z)
    | _, _ => false
  | .boolean v, env =>
    match v.eval env with
    | .ok x => decide (x = 0) || decide (x = 1)
    | _ => false

/-- `Basic.holds` is monotone in the assignment-extension order, by `CVar.eval_le`. -/
theorem Basic.holds_mono [Add F] [Mul F] [Zero F] [One F] [DecidableEq F] {con : Basic F}
    {env env' : Assignments F} (hle : env.Le env') (h : con.holds env = true) :
    con.holds env' = true := by
  cases con with
  | r1cs l r o =>
    simp only [holds] at h ⊢
    split at h
    · next hx hy hz =>
      rw [CVar.eval_le hle hx, CVar.eval_le hle hy, CVar.eval_le hle hz]
      exact h
    · cases h
  | equal a b =>
    simp only [holds] at h ⊢
    split at h
    · next hx hy =>
      rw [CVar.eval_le hle hx, CVar.eval_le hle hy]
      exact h
    · cases h
  | square a c =>
    simp only [holds] at h ⊢
    split at h
    · next hx hz =>
      rw [CVar.eval_le hle hx, CVar.eval_le hle hz]
      exact h
    · cases h
  | boolean v =>
    simp only [holds] at h ⊢
    split at h
    · next hx =>
      rw [CVar.eval_le hle hx]
      exact h
    · cases h

/-- The constraint constructors every backend supplies (PS `class BasicSystem f c`).
Backends instantiate this at their concrete constraint type; `Basic` below is the
reference instance. -/
class BasicSystem (F c : Type u) where
  /-- The rank-1 constraint `left * right = output`. -/
  r1cs : (left right output : CVar F) → c
  /-- The equality constraint `a = b`. -/
  equal : (a b : CVar F) → c
  /-- The square constraint `a * a = sq`. -/
  square : (a sq : CVar F) → c
  /-- The booleanity constraint: `x` must evaluate to `0` or `1`. -/
  boolean : (x : CVar F) → c

/-- Inversion for a satisfied `r1cs` row: all three operands evaluate and the product
identity holds. -/
theorem Basic.r1cs_inv [Add F] [Mul F] [Zero F] [One F] [DecidableEq F]
    {l r o : CVar F} {env : Assignments F}
    (h : (Basic.r1cs l r o).holds env = true) :
    ∃ x y z, l.eval env = .ok x ∧ r.eval env = .ok y ∧ o.eval env = .ok z ∧ x * y = z := by
  have h' : (match l.eval env, r.eval env, o.eval env with
      | .ok x, .ok y, .ok z => decide (x * y = z)
      | _, _, _ => false) = true := h
  split at h'
  · next x y z hx hy hz => exact ⟨x, y, z, hx, hy, hz, by simpa using h'⟩
  · cases h'

/-- Inversion for a satisfied `equal` row: both operands evaluate, to the same value. -/
theorem Basic.equal_inv [Add F] [Mul F] [Zero F] [One F] [DecidableEq F]
    {a b : CVar F} {env : Assignments F}
    (h : (Basic.equal a b).holds env = true) :
    ∃ x y, a.eval env = .ok x ∧ b.eval env = .ok y ∧ x = y := by
  have h' : (match a.eval env, b.eval env with
      | .ok x, .ok y => decide (x = y)
      | _, _ => false) = true := h
  split at h'
  · next x y hx hy => exact ⟨x, y, hx, hy, by simpa using h'⟩
  · cases h'

/-- Inversion for a satisfied `square` row: both operands evaluate and the square
identity holds. -/
theorem Basic.square_inv [Add F] [Mul F] [Zero F] [One F] [DecidableEq F]
    {a c' : CVar F} {env : Assignments F}
    (h : (Basic.square a c').holds env = true) :
    ∃ x z, a.eval env = .ok x ∧ c'.eval env = .ok z ∧ x * x = z := by
  have h' : (match a.eval env, c'.eval env with
      | .ok x, .ok z => decide (x * x = z)
      | _, _ => false) = true := h
  split at h'
  · next x z hx hz => exact ⟨x, z, hx, hz, by simpa using h'⟩
  · cases h'

/-- Inversion for a satisfied `boolean` row: the operand evaluates, to `0` or `1`. -/
theorem Basic.boolean_inv [Add F] [Mul F] [Zero F] [One F] [DecidableEq F]
    {v : CVar F} {env : Assignments F}
    (h : (Basic.boolean v).holds env = true) :
    ∃ x, v.eval env = .ok x ∧ (x = 0 ∨ x = 1) := by
  have h' : (match v.eval env with
      | .ok x => (decide (x = 0) || decide (x = 1))
      | _ => false) = true := h
  split at h'
  · next x hx =>
    refine ⟨x, hx, ?_⟩
    simpa using h'
  · cases h'

/-- `Basic` is the reference `BasicSystem` instance: each method is its constructor. -/
instance : BasicSystem F (Basic F) where
  r1cs := .r1cs
  equal := .equal
  square := .square
  boolean := .boolean

end Snarky
