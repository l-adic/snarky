import Snarky.Backend.Assignments
import Snarky.Circuit.Types
import Snarky.Constraint.Basic
import Snarky.Vec

/-!
# The circuit monad and core DSL operations

Port of `Snarky.Circuit.DSL.Monad` (packages/snarky/src/Snarky/Circuit/DSL/Monad.purs):
the witness monad `AsProver`, the circuit monad `CircuitM`, the core operations
(`fresh`, `addConstraint`, `existsVars`/`witness`, `assignVars`, `label`, `readVar`),
and the `CheckedType` class with its base instances.

## The one deliberate architectural deviation

The PS original is DIRECT (final-tagless): `Snarky f c r a = CircuitOps f c r -> Effect a`
— a bind is a closure, an op is a record-field call, and an interpreter is a record of
mutable-ref operations. That shape is uninspectable, so no law about interpretation
would even be statable. This port reifies the op tree instead: `CircuitM` has one
constructor per `CircuitOps` field, with continuations stored explicitly, so an
interpreter is a structural recursion and laws about it are inductions. The embedding
is deep in the *circuit structure* only — witness payloads at `existsOp`/`assignOp` are
semantic `AsProver` functions, not syntax. Continuations receive only freshly allocated
`Variable`s, never field values, so a circuit's shape cannot depend on witness data.

## Disposition of the rest of the PS module

- The advice row `r` (`AsProverCtx`, `liftAdvice`, `runAdvice`, the `Run` encoding) is
  dropped; `AsProver` is the pure reader-except stack over `Assignments`. Compilation
  is unaffected: advice is only reachable from witness payloads, which building never
  evaluates. If an advice-consuming circuit ever lands, the rendering is an extra
  reader component of `AsProver` ONLY — never a circuit-level function argument
  `A → CircuitM …`, which would let the circuit's shape depend on advice.
- PS `pushLabelOp`/`popLabelOp` collapse into one scoped `labelOp` node; `MonadRec` is
  unnecessary (recursion over build-time data produces a fixed tree); `MonadEffect`,
  `liftEffectSnarky`, and `mkWitnessTable` are `Effect` machinery with no analogue in
  the pure embedding.
- The numeric-tower instances on `Snarky`-actions are not ported; the underlying
  combinators land as plain functions. PS defines the field and boolean primitives here
  only to dodge orphan instances; Lean has no orphan restriction, so they live with
  their families. This module is the monad alone, and stays plain core Lean.
- PS `exists` is `witness` (`exists` is a Lean keyword). PS `read` is `readVar` (`read`
  is core's `MonadReader` primitive). `readCVar` keeps its PS name.

The `LawfulMonad (CircuitM F c)` instance is proved by induction — PS gets the monad
laws for free from function composition; the deep embedding must prove them.
-/

namespace Snarky

/-! ## Witness (prover-side) computations -/

/-- A prover-only witness computation: read the current assignments, produce a value or
fail (PS `AsProver f r a`, minus the advice row). `ReaderT`/`Except` supply the `Monad` and
`LawfulMonad` instances. -/
abbrev AsProver (F : Type u) : Type u → Type u :=
  ReaderT (Assignments F) (Except EvalError)

namespace AsProver

/-- Read the value of an affine expression from the current assignments (PS `readCVar`). -/
def readCVar [Add F] [Mul F] (x : CVar F) : AsProver F F :=
  fun env => x.eval env

/-- Fail with a message (PS `throwAsProver`). -/
def throw (msg : String) : AsProver F α :=
  fun _ => .error (.custom msg)

/-- Run a witness computation against an assignment (PS `runAsProver`, minus `Effect`). -/
def run (p : AsProver F α) (env : Assignments F) : Except EvalError α :=
  p env

end AsProver

/-! ## The circuit monad -/

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

/-! ## The core operations -/

variable {F c : Type u}

/-- Allocate one fresh variable (PS `fresh`). -/
def fresh : CircuitM F c Variable :=
  .freshOp .pure

/-- Emit one constraint (PS `addConstraint`). Returns `PUnit` rather than `Unit` so it can
sit in `do`-blocks at any universe. -/
def addConstraint (con : c) : CircuitM F c PUnit :=
  .addConstraintOp con (.pure PUnit.unit)

/-- Allocate `n` variables whose values the prover computes with `wit` (raw PS `existsOp`;
the typed, `check`-inserting wrapper is `witness` below). -/
def existsVars (n : Nat) (wit : AsProver F (Vector F n)) : CircuitM F c (Vector Variable n) :=
  .existsOp n wit .pure

/-- Back-fill already-allocated variables from a witness computation (PS `assignVars`).
"Already-allocated" is enforced: an interpreter may refuse targets at or above its
counter. -/
def assignVars {n : Nat} (vs : Vector Variable n) (wit : AsProver F (Vector F n)) :
    CircuitM F c PUnit :=
  .assignOp vs wit (.pure PUnit.unit)

/-- Run a computation under a label, for error attribution (PS `label`). -/
def label (s : String) (m : CircuitM F c α) : CircuitM F c α :=
  .labelOp s m

/-! ## CheckedType -/

/-- Variable bundles whose well-formedness is enforced by constraints: `check` is emitted
by `witness` under *both* interpreters, exactly like PS `CheckedType`'s `check`. -/
class CheckedType (F c : Type u) (var : Type u) where
  /-- The circuit that constrains the bundle to well-formed values (PS `check`). -/
  check : var → CircuitM F c PUnit

/-- A field element carries no well-formedness constraint (PS `CheckedType` instance for
`FVar`: `check = const (pure unit)`). -/
instance : CheckedType F c (FVar F) where
  check _ := .pure PUnit.unit

/-- A freshly witnessed boolean must be constrained to `{0, 1}` (PS `CheckedType`
instance for `BoolVar`: `check = boolean`). -/
instance [BasicSystem F c] : CheckedType F c (BoolVar F) where
  check b := addConstraint (BasicSystem.boolean b.toCVar)

/-- An `UnChecked` bundle skips its checks — for values whose constraints are guaranteed
elsewhere (PS `CheckedType` instance for `UnChecked`). -/
instance {var : Type u} : CheckedType F c (UnChecked var) where
  check _ := .pure PUnit.unit

/-- A pair is checked componentwise, first component first (PS `CheckedType` instance
for `Tuple`, via `genericCheck`). -/
instance {avar bvar : Type u} [CheckedType F c avar] [CheckedType F c bvar] :
    CheckedType F c (avar × bvar) where
  check p := do
    CheckedType.check (c := c) p.1
    CheckedType.check (c := c) p.2

/-- A vector is checked elementwise, in index order (PS `CheckedType` instance for
`Vector`: `traverse_ check`). -/
instance {var : Type u} [CheckedType F c var] {n : Nat} :
    CheckedType F c (Vector var n) where
  check v := v.toList.forM (CheckedType.check (c := c))

/-! ## The typed combinators -/

variable {val var : Type u}

/-- Witness a typed value — the existential introduction of prover-supplied data, the
circuit model's nondeterminism primitive (PS/OCaml `exists`; o1js `Provable.witness`).
The circuit asserts "there exist `size` field values for this bundle": the builder
allocates the variables and emits the type's `check` constraints; only prover runs
execute `compute`, whose output is — in the NP sense — the witness justifying the
existential. Renamed because `exists` is Lean's `∃` keyword. -/
def witness [inst : CircuitType F val var] [CheckedType F c var]
    (compute : AsProver F val) : CircuitM F c var :=
  .existsOp inst.size (fun env => (compute env).map inst.valueToFields) fun vs => do
    let v := inst.fieldsToVar (mapVec CVar.var vs)
    CheckedType.check (c := c) v
    pure v

/-- Read a typed variable bundle back to its value during a prover run (PS `read`). The
length check is dynamic (it always succeeds) to keep the definition kernel-reducible
without a `mapM`-length lemma. -/
def readVar [Add F] [Mul F] [inst : CircuitType F val var] (v : var) : AsProver F val :=
  fun env => do
    let fields ← (inst.varToFields v).toList.mapM (CVar.eval · env)
    if h : fields.length = inst.size then
      pure (inst.fieldsToValue ⟨⟨fields⟩, by simpa using h⟩)
    else
      .error (.custom "readVar: size mismatch")

/-- Successful `mapM`-evaluation is stable under assignment extension — the list form
of `CVar.eval_le`. -/
private theorem mapM_eval_le [Add F] [Mul F] {env env' : Assignments F} (hle : env.Le env') :
    ∀ {l : List (CVar F)} {res : List F},
      l.mapM (CVar.eval · env) = .ok res → l.mapM (CVar.eval · env') = .ok res := by
  intro l
  induction l with
  | nil => intro res h; exact h
  | cons x l ih =>
    intro res h
    rw [List.mapM_cons] at h ⊢
    cases hx : CVar.eval x env with
    | error e => rw [hx] at h; cases h
    | ok v =>
      rw [hx] at h
      rw [CVar.eval_le hle hx]
      cases hrest : l.mapM (CVar.eval · env) with
      | error e => rw [hrest] at h; cases h
      | ok vs =>
        rw [hrest] at h
        rw [ih hrest]
        exact h

/-- Successful `readVar`s are stable under assignment extension — the bundle form of
`CVar.eval_le`. -/
theorem readVar_le [Add F] [Mul F] [inst : CircuitType F val var] {v : var}
    {env env' : Assignments F} (hle : env.Le env') {x : val}
    (h : readVar (F := F) v env = .ok x) : readVar (F := F) v env' = .ok x := by
  unfold readVar at h ⊢
  cases hm : (inst.varToFields v).toList.mapM (CVar.eval · env) with
  | error e => rw [hm] at h; cases h
  | ok fields =>
    rw [hm] at h
    rw [mapM_eval_le hle hm]
    exact h

end Snarky
