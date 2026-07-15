import Snarky.AsProver

/-!
# The circuit-building monad, deep-embedded

Port of the `Snarky` monad from `Snarky.Circuit.DSL.Monad`
(packages/snarky/src/Snarky/Circuit/DSL/Monad.purs, lines 226–256). The PureScript
original is final-tagless: `Snarky f c r a = CircuitOps f c r -> Effect a`, a bind is a
closure, and the two interpreters (constraint builder, witness prover) are `CircuitOps`
records over mutable refs. That shape is uninspectable, so this port reifies the op tree
instead: one constructor per `CircuitOps` field, with continuations stored explicitly.

The embedding is deep in the *circuit structure* only — the witness payloads at
`existsOp`/`assignOp` are semantic `AsProver` functions, not syntax. Continuations receive
only freshly allocated `Variable`s, never field values, so the shape of a circuit provably
cannot depend on witness data.

The interpreters land as pure recursive functions in follow-up modules: `Snarky.Builder`
(constraint generation, PS `Snarky.Backend.Builder`) and `Snarky.Prover` (witness
generation, PS `Snarky.Backend.Prover`), together with the interpreter laws
(witness-independence, allocation agreement, completeness).

Deviations from PS: `pushLabelOp`/`popLabelOp` collapse into one scoped `labelOp` node;
`MonadRec` is unnecessary (Lean recursion over build-time data produces a fixed tree);
the advice row `r` is dropped (see `Snarky.AsProver`).
-/

namespace Snarky

/-- A circuit computation over field `F` and constraint type `c`, returning `α` — the
deep-embedded counterpart of PS `Snarky f c r a`. Constructors mirror the `CircuitOps`
record fields. -/
inductive CircuitM (F c : Type u) (α : Type v) : Type (max u v) where
  /-- Return a value (the monad's `pure`). -/
  | pure (a : α)
  /-- Allocate a fresh variable (PS `freshOp`). -/
  | freshOp (k : Variable → CircuitM F c α)
  /-- Emit a constraint (PS `addConstraintOp`). -/
  | addConstraintOp (con : c) (k : CircuitM F c α)
  /-- Allocate `n` fresh variables, to be assigned by the witness computation `wit` during
  prover runs (PS `existsOp`). The builder ignores `wit`. -/
  | existsOp (n : Nat) (wit : AsProver F (Vector F n)) (k : Vector Variable n → CircuitM F c α)
  /-- Back-fill existing variables from a witness computation during prover runs
  (PS `assignOp`). The builder ignores it entirely. -/
  | assignOp {n : Nat} (vs : Vector Variable n) (wit : AsProver F (Vector F n))
      (k : CircuitM F c α)
  /-- A labelled scope, for error attribution (PS `pushLabelOp`/`popLabelOp`). -/
  | labelOp (s : String) (k : CircuitM F c α)

namespace CircuitM

variable {F c : Type u}

/-- Sequencing: graft `f` onto every leaf of the op tree. In PS a bind is a closure; here
it is a structural recursion, which is what makes the interpreter proofs inductions. -/
protected def bind : CircuitM F c α → (α → CircuitM F c β) → CircuitM F c β
  | .pure a, f => f a
  | .freshOp k, f => .freshOp fun v => (k v).bind f
  | .addConstraintOp con k, f => .addConstraintOp con (k.bind f)
  | .existsOp n wit k, f => .existsOp n wit fun vs => (k vs).bind f
  | .assignOp vs wit k, f => .assignOp vs wit (k.bind f)
  | .labelOp s k, f => .labelOp s (k.bind f)

instance : Monad (CircuitM F c) where
  pure := CircuitM.pure
  bind := CircuitM.bind

/-! ## Monad laws -/

protected theorem bind_pure (m : CircuitM F c α) : m.bind CircuitM.pure = m := by
  induction m with
  | pure a => rfl
  | freshOp k ih => simp only [CircuitM.bind]; exact congrArg _ (funext ih)
  | addConstraintOp con k ih => simp only [CircuitM.bind]; exact congrArg _ ih
  | existsOp n wit k ih => simp only [CircuitM.bind]; exact congrArg _ (funext ih)
  | assignOp vs wit k ih => simp only [CircuitM.bind]; exact congrArg _ ih
  | labelOp s k ih => simp only [CircuitM.bind]; exact congrArg _ ih

protected theorem bind_assoc (m : CircuitM F c α) (f : α → CircuitM F c β)
    (g : β → CircuitM F c γ) :
    (m.bind f).bind g = m.bind fun a => (f a).bind g := by
  induction m with
  | pure a => rfl
  | freshOp k ih => simp only [CircuitM.bind]; exact congrArg _ (funext ih)
  | addConstraintOp con k ih => simp only [CircuitM.bind]; exact congrArg _ ih
  | existsOp n wit k ih => simp only [CircuitM.bind]; exact congrArg _ (funext ih)
  | assignOp vs wit k ih => simp only [CircuitM.bind]; exact congrArg _ ih
  | labelOp s k ih => simp only [CircuitM.bind]; exact congrArg _ ih

instance : LawfulMonad (CircuitM F c) :=
  LawfulMonad.mk'
    (id_map := fun m => CircuitM.bind_pure m)
    (pure_bind := fun _ _ => rfl)
    (bind_assoc := CircuitM.bind_assoc)

end CircuitM

/-! ## Smart constructors (the user-facing ops) -/

variable {F c : Type u}

/-- Allocate one fresh variable (PS `fresh`). -/
def fresh : CircuitM F c Variable :=
  .freshOp .pure

/-- Emit one constraint (PS `addConstraint`). Returns `PUnit` rather than `Unit` so it can
sit in `do`-blocks at any universe. -/
def addConstraint (con : c) : CircuitM F c PUnit :=
  .addConstraintOp con (.pure PUnit.unit)

/-- Allocate `n` variables whose values the prover computes with `wit` (raw PS `existsOp`;
the typed, `check`-inserting wrapper is `Snarky.witness` in `Snarky.DSL`). -/
def existsVars (n : Nat) (wit : AsProver F (Vector F n)) : CircuitM F c (Vector Variable n) :=
  .existsOp n wit .pure

/-- Back-fill already-allocated variables from a witness computation (PS `assignVars`). -/
def assignVars {n : Nat} (vs : Vector Variable n) (wit : AsProver F (Vector F n)) :
    CircuitM F c PUnit :=
  .assignOp vs wit (.pure PUnit.unit)

/-- Run a computation under a label, for error attribution (PS `label`). -/
def label (s : String) (m : CircuitM F c α) : CircuitM F c α :=
  .labelOp s m

end Snarky
