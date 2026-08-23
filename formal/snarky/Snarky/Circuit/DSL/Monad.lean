import Snarky.Backend.Assignments
import Mathlib.Logic.Equiv.Defs
import Snarky.Circuit.Types
import Snarky.Constraint.Basic
import Snarky.Vec

/-!
# The circuit monad and core DSL operations

Port of `Snarky.Circuit.DSL.Monad` (packages/snarky/src/Snarky/Circuit/DSL/Monad.purs):
the witness monad `AsProver`, the circuit monad `CircuitM`, the core operations
(`addConstraint`, `existsVars`/`witness`, `assignVars`, `label`, `readVar`),
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

/-- A prover-only witness computation, as syntax (PS `AsProver f r a`, minus the advice
row): return a value, read a variable from the current assignments and continue with
its value, or fail. A computation can read the table and nothing else — there is no
instruction that observes a failed read and carries on — which is PS's surface
(`readCVar`, `throwAsProver`, the monad) and nothing more. `run` is its evaluation
against a table. -/
inductive AsProver (F : Type u) : Type u → Type u where
  /-- Return `a`. -/
  | pure {α : Type u} (a : α) : AsProver F α
  /-- Read variable `v`'s value, then run `k` on it. -/
  | read {α : Type u} (v : Variable) (k : F → AsProver F α) : AsProver F α
  /-- Fail with `e`. -/
  | fail {α : Type u} (e : EvalError) : AsProver F α

namespace AsProver

variable {F : Type u} {α β : Type u}

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

@[simp] theorem bind_pure (a : α) (f : α → AsProver F β) :
    AsProver.bind (.pure a) f = f a := rfl

@[simp] theorem bind_read (v : Variable) (k : F → AsProver F α) (f : α → AsProver F β) :
    AsProver.bind (.read v k) f = .read v fun x => AsProver.bind (k x) f := rfl

@[simp] theorem bind_fail (e : EvalError) (f : α → AsProver F β) :
    AsProver.bind (.fail e : AsProver F α) f = .fail e := rfl

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

/-- Read the value of an affine expression from the current assignments (PS
`readCVar`): read its variables and combine — the prover's evaluation of the term. -/
def readCVar [Add F] [Mul F] : CVar F → AsProver F F
  | .var v => .read v .pure
  | .const k => .pure k
  | .add a b => do
    let x ← readCVar a
    let y ← readCVar b
    pure (x + y)
  | .scale k y => do
    let x ← readCVar y
    pure (k * x)

/-- Fail with a message (PS `throwAsProver`). -/
def throw (msg : String) : AsProver F α := .fail (.custom msg)

/-- Run a witness computation against an assignment (PS `runAsProver`, minus `Effect`):
a read of an assigned variable continues with its value; one of an unassigned
variable, or a `fail`, ends the run. -/
def run : AsProver F α → Assignments F → Except EvalError α
  | .pure a, _ => .ok a
  | .read v k, env =>
    match env v with
    | some x => (k x).run env
    | none => .error (.unassigned v)
  | .fail e, _ => .error e

/-- `run` computes by its three equations and the sequencing law; a `do`-block reaches
them through the normal forms above. -/
@[simp] theorem run_pure (a : α) (env : Assignments F) :
    (AsProver.pure a : AsProver F α).run env = .ok a := rfl

@[simp] theorem run_read (v : Variable) (k : F → AsProver F α) (env : Assignments F) :
    (AsProver.read v k).run env = match env v with
      | some x => (k x).run env
      | none => .error (.unassigned v) := by
  rcases h : env v with _ | x <;> simp [run, h]

@[simp] theorem run_fail (e : EvalError) (env : Assignments F) :
    (AsProver.fail e : AsProver F α).run env = .error e := rfl

@[simp] theorem run_bind (x : AsProver F α) (f : α → AsProver F β) (env : Assignments F) :
    (AsProver.bind x f).run env = (x.run env).bind fun a => (f a).run env := by
  induction x with
  | pure a => rfl
  | read v k ih =>
    simp only [AsProver.bind, run]
    cases env v with
    | none => rfl
    | some x => exact ih x
  | fail e => rfl

/-- Reading an affine expression is evaluating it. -/
@[simp] theorem run_readCVar [Add F] [Mul F] (x : CVar F) (env : Assignments F) :
    (readCVar x).run env = x.eval env := by
  induction x with
  | var v =>
    simp only [readCVar, run_read, run_pure, CVar.eval]
    rcases env v with _ | x <;> rfl
  | const k => rfl
  | add a b iha ihb =>
    simp only [readCVar, bind_eq, run_bind, iha, ihb, run_pure, CVar.eval]
    rcases a.eval env with e | x
    · rfl
    · rcases b.eval env with e | y <;> rfl
  | scale k y ih =>
    simp only [readCVar, bind_eq, run_bind, ih, run_pure, CVar.eval]
    rcases y.eval env with e | x <;> rfl

/-- Evaluate against a total reading of the table: every read succeeds, only `fail`
fails. The value a scoped block's run computes (`run_eq_eval`, beside `ProverState`). -/
def eval (V : Valuation F) : AsProver F α → Except EvalError α
  | .pure a => .ok a
  | .read v k => (k (V v)).eval V
  | .fail e => .error e

@[simp] theorem eval_pure (V : Valuation F) (a : α) :
    (AsProver.pure a : AsProver F α).eval V = .ok a := rfl

@[simp] theorem eval_read (V : Valuation F) (v : Variable) (k : F → AsProver F α) :
    (AsProver.read v k).eval V = (k (V v)).eval V := rfl

@[simp] theorem eval_fail (V : Valuation F) (e : EvalError) :
    (AsProver.fail e : AsProver F α).eval V = .error e := rfl

@[simp] theorem eval_bind (V : Valuation F) (x : AsProver F α) (f : α → AsProver F β) :
    (AsProver.bind x f).eval V = (x.eval V).bind fun a => (f a).eval V := by
  induction x with
  | pure a => rfl
  | read v k ih => exact ih _
  | fail e => rfl

/-- Reading an affine expression at a total reading is its value there. -/
@[simp] theorem eval_readCVar [Add F] [Mul F] (x : CVar F) (V : Valuation F) :
    (readCVar x).eval V = .ok (x.val V) := by
  induction x with
  | var v => rfl
  | const k => rfl
  | add a b iha ihb => simp [readCVar, iha, ihb, CVar.val, Except.bind]
  | scale k y ih => simp [readCVar, ih, CVar.val, Except.bind]

/-- The prover-side list read is the elementwise read. -/
theorem run_mapM_readCVar [Add F] [Mul F] (env : Assignments F) :
    ∀ xs : List (CVar F), (xs.mapM readCVar).run env = xs.mapM (CVar.eval · env)
  | [] => rfl
  | x :: xs => by
    simp only [List.mapM_cons, bind_eq, pure_eq, run_bind, run_readCVar, run_pure,
      run_mapM_readCVar env xs]
    rcases x.eval env with e | v
    · rfl
    · rcases xs.mapM (CVar.eval · env) with e | vs <;> rfl

/-- A successful elementwise read is a successful list read. -/
theorem readAll_ok [Add F] [Mul F] {env : Assignments F} {xs : List (CVar F)} {vs : List F}
    (h : xs.mapM (CVar.eval · env) = .ok vs) : (xs.mapM readCVar).run env = .ok vs := by
  rw [run_mapM_readCVar]; exact h

end AsProver

/-! ## The circuit monad -/

/-- A circuit computation over field `F` and constraint type `c`, returning `α` — the
deep-embedded counterpart of PS `Snarky f c r a`. Constructors mirror the `CircuitOps`
record fields that library code reaches; `freshOp` (allocate without a value) is
outside the fragment, since every allocation is an `exists`. -/
inductive CircuitM (F c : Type u) (α : Type v) : Type (max u v) where
  /-- Return a value (the monad's `pure`). -/
  | pure (a : α)
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
  | addConstraintOp con k ih => simp only [CircuitM.bind]; exact congrArg _ ih
  | existsOp n wit k ih => simp only [CircuitM.bind]; exact congrArg _ (funext ih)
  | assignOp vs wit k ih => simp only [CircuitM.bind]; exact congrArg _ ih
  | labelOp s k ih => simp only [CircuitM.bind]; exact congrArg _ ih

protected theorem bind_assoc (m : CircuitM F c α) (f : α → CircuitM F c β)
    (g : β → CircuitM F c γ) :
    (m.bind f).bind g = m.bind fun a => (f a).bind g := by
  induction m with
  | pure a => rfl
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

/-- The checks of `var`, run on an isomorphic `var'` — the leaf a nominal structure
declares through its field-product equivalence. -/
@[reducible] def CheckedType.ofEquiv {var var' : Type u} [CheckedType F c var]
    (er : var' ≃ var) : CheckedType F c var' :=
  ⟨fun r => CheckedType.check (c := c) (er r)⟩

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
  .existsOp inst.size (inst.valueToFields <$> compute) fun vs => do
    let v := inst.fieldsToVar (mapVec CVar.var vs)
    CheckedType.check (c := c) v
    pure v

/-- Read a typed variable bundle back to its value during a prover run (PS `read`). The
length check is dynamic (it always succeeds) to keep the definition kernel-reducible
without a `mapM`-length lemma. -/
def readVar [Add F] [Mul F] [inst : CircuitType F val var] (v : var) : AsProver F val := do
  let fields ← (inst.varToFields v).toList.mapM AsProver.readCVar
  if h : fields.length = inst.size then
    pure (inst.fieldsToValue ⟨⟨fields⟩, by simpa using h⟩)
  else
    AsProver.throw "readVar: size mismatch"

/-- Successful `readVar`s are stable under assignment extension — the bundle form of
`CVar.eval_le`. -/
theorem readVar_le [Add F] [Mul F] [inst : CircuitType F val var] {v : var}
    {env env' : Assignments F} (hle : env.Le env') {x : val}
    (h : (readVar (F := F) v).run env = .ok x) : (readVar (F := F) v).run env' = .ok x := by
  simp only [readVar, AsProver.bind_eq, AsProver.run_bind, AsProver.run_mapM_readCVar] at h ⊢
  cases hm : (inst.varToFields v).toList.mapM (CVar.eval · env) with
  | error e => rw [hm] at h; cases h
  | ok fields =>
    rw [hm] at h
    rw [mapM_eval_le hle hm]
    simp only [Except.bind] at h ⊢
    split at h <;> split <;> simp_all [AsProver.throw]

end Snarky
