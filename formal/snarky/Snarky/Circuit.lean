namespace Snarky

universe u v

/-- A circuit variable: an index into the prover's assignment table. -/
abbrev Variable := Nat

/-- Why a witness computation ended without a value. -/
inductive EvalError where
  /-- A variable was read before being assigned. -/
  | unassigned (v : Variable)
  /-- A witness computation failed with a message (PS `throwAsProver`). -/
  | custom (msg : String)
  deriving Repr

/-- The prover's advice language, reified: read an assigned variable, or fail. Pure syntax —
running it needs a table (`AsProver.run`). -/
inductive AsProver (F : Type u) : Type u → Type u where
  /-- Return `a`. -/
  | pure {α : Type u} (a : α) : AsProver F α
  /-- Read variable `v`'s value, then run `k` on it. -/
  | read {α : Type u} (v : Variable) (k : F → AsProver F α) : AsProver F α
  /-- Fail with `e`. -/
  | fail {α : Type u} (e : EvalError) : AsProver F α

/-- The circuit monad, reified: a tree whose only effects are emitting a constraint and
allocating variables against a witness computation. The constraint type `c` is a parameter,
so the tree is backend-agnostic; the two interpreters are `build` and `prove`. -/
inductive CircuitM (F c : Type u) (α : Type v) : Type (max u v) where
  /-- Return a value (the monad's `pure`). -/
  | pure (a : α)
  /-- Emit a constraint (PS `addConstraintOp`). -/
  | addConstraintOp (con : c) (k : CircuitM F c α)
  /-- Allocate `n` fresh variables, to be assigned by the witness computation `wit` during
  prover runs (PS `existsOp`). The builder ignores `wit`. -/
  | existsOp (n : Nat) (wit : AsProver F (Vector F n)) (k : Vector Variable n → CircuitM F c α)

end Snarky

namespace Snarky

universe u v

namespace AsProver

variable {F : Type u} {α β γ : Type u}

/-- Sequencing: run the first computation, then `f` on its result. -/
protected def bind : AsProver F α → (α → AsProver F β) → AsProver F β
  | .pure a, f => f a
  | .read v k, f => .read v fun x => AsProver.bind (k x) f
  | .fail e, _ => .fail e

instance : Monad (AsProver F) where
  pure := .pure
  bind := AsProver.bind

/-- A `do`-block over `AsProver` normalises to its constructors: these equations push
`pure`, `>>=` and `<$>` through to `.pure`, `.read` and `.fail`, so that anything
defined on the constructors computes on a block written with `do`. -/
@[simp] theorem pure_eq (a : α) : (Pure.pure a : AsProver F α) = .pure a := rfl

@[simp] theorem bind_eq (x : AsProver F α) (f : α → AsProver F β) :
    x >>= f = AsProver.bind x f := rfl

@[simp] theorem map_eq (f : α → β) (x : AsProver F α) :
    f <$> x = AsProver.bind x fun a => .pure (f a) := rfl

private theorem bind_pure' (x : AsProver F α) : AsProver.bind x .pure = x := by
  induction x with
  | pure a => rfl
  | read v k ih => simp only [AsProver.bind]; exact congrArg _ (funext ih)
  | fail e => rfl

private theorem bind_assoc' (x : AsProver F α) (f : α → AsProver F β)
    (g : β → AsProver F γ) :
    AsProver.bind (AsProver.bind x f) g = AsProver.bind x fun a => AsProver.bind (f a) g := by
  induction x with
  | pure a => rfl
  | read v k ih => simp only [AsProver.bind]; exact congrArg _ (funext ih)
  | fail e => rfl

instance : LawfulMonad (AsProver F) :=
  LawfulMonad.mk' _ (id_map := bind_pure') (pure_bind := fun _ _ => rfl)
    (bind_assoc := bind_assoc')

/-- Fail with a message (PS `throwAsProver`). -/
def throw (msg : String) : AsProver F α := .fail (.custom msg)

end AsProver

namespace CircuitM

variable {F c : Type u} {α β γ : Type v}

/-- Sequencing: graft `f` onto every leaf of the op tree. -/
protected def bind : CircuitM F c α → (α → CircuitM F c β) → CircuitM F c β
  | .pure a, f => f a
  | .addConstraintOp con k, f => .addConstraintOp con (k.bind f)
  | .existsOp n wit k, f => .existsOp n wit fun vs => (k vs).bind f

instance : Monad (CircuitM F c) where
  pure := CircuitM.pure
  bind := CircuitM.bind

/-- A `do`-block's trailing `pure` elaborates through `<$>`; push it back to `bind`. -/
@[simp] protected theorem map_eq {β : Type v} (f : α → β) (m : CircuitM F c α) :
    f <$> m = m >>= fun a => pure (f a) := rfl

private theorem bind_pure (m : CircuitM F c α) : m.bind CircuitM.pure = m := by
  induction m with
  | pure a => rfl
  | addConstraintOp con k ih => simp only [CircuitM.bind]; exact congrArg _ ih
  | existsOp n wit k ih => simp only [CircuitM.bind]; exact congrArg _ (funext ih)

private theorem bind_assoc (m : CircuitM F c α) (f : α → CircuitM F c β)
    (g : β → CircuitM F c γ) :
    (m.bind f).bind g = m.bind fun a => (f a).bind g := by
  induction m with
  | pure a => rfl
  | addConstraintOp con k ih => simp only [CircuitM.bind]; exact congrArg _ ih
  | existsOp n wit k ih => simp only [CircuitM.bind]; exact congrArg _ (funext ih)

instance : LawfulMonad (CircuitM F c) :=
  LawfulMonad.mk'
    (id_map := fun m => CircuitM.bind_pure m)
    (pure_bind := fun _ _ => rfl)
    (bind_assoc := CircuitM.bind_assoc)

end CircuitM

variable {F c : Type u}

/-- Emit one constraint (PS `addConstraint`). -/
def addConstraint (con : c) : CircuitM F c PUnit :=
  .addConstraintOp con (.pure PUnit.unit)

end Snarky
