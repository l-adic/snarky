import Mathlib.Algebra.Field.Defs
import Snarky.Backend.Assignments
import Snarky.Circuit.Types
import Snarky.Constraint.Basic
import Snarky.Vec

/-!
# The circuit monad and core DSL operations

Port of `Snarky.Circuit.DSL.Monad` (packages/snarky/src/Snarky/Circuit/DSL/Monad.purs):
the witness monad `AsProver`, the circuit monad `CircuitM`, the core operations
(`fresh`, `addConstraint`, `existsVars`/`witness`, `assignVars`, `label`, `readVar`,
`mul`), and the `CheckedType` class with its base instances.

## The one deliberate architectural deviation

The PS original is DIRECT (final-tagless): `Snarky f c r a = CircuitOps f c r -> Effect a`
— a bind is a closure, an op is a record-field call, and the two interpreters are just two
`CircuitOps` records over mutable refs. That shape is uninspectable, so none of the
interpreter laws would even be statable. This port reifies the op tree
instead: `CircuitM` has one constructor per `CircuitOps` field, with continuations stored
explicitly. The embedding is deep in the *circuit structure* only — witness payloads at
`existsOp`/`assignOp` are semantic `AsProver` functions, not syntax. Continuations receive
only freshly allocated `Variable`s, never field values, so a circuit's shape provably
cannot depend on witness data (`Snarky.build_eq_of_eraseWitness`). The interpreters
are pure recursive functions: `Snarky.build` (PS `Backend.Builder`) and `Snarky.prove`
(PS `Backend.Prover`).

## Disposition of the rest of the PS module

- The advice row `r` (`AsProverCtx`, `liftAdvice`, `runAdvice`, the `Run` encoding) is
  dropped; `AsProver` is the pure reader-except stack over `Assignments`. Compilation is
  unaffected: advice is only reachable from witness payloads, which `build` never
  evaluates (PS compiles with the throwing `badAdvice` for the same reason; here
  `Snarky.build_eq_of_eraseWitness` proves it). If an advice-consuming circuit ever
  lands, the rendering is an extra reader component of `AsProver` ONLY — never a
  circuit-level function argument `A → CircuitM …`, which would demand advice at compile
  time and let the circuit's shape depend on it, destroying both properties above.
- PS `pushLabelOp`/`popLabelOp` collapse into one scoped `labelOp` node; `MonadRec` is
  unnecessary (recursion over build-time data produces a fixed tree); `MonadEffect`,
  `liftEffectSnarky`, and `mkWitnessTable` are `Effect`-machinery with no analogue in the
  pure embedding (memoization is an interpreter concern here, not a circuit one).
- The numeric-tower instances on `Snarky`-actions (`Semiring (Snarky f c r (FVar f))` …,
  with their `Newtype` fallbacks) are not ported (D8); the underlying combinators land as
  plain functions.
- The field primitives `inv_`/`div_` defined here in PS are here as `inv`/`div` (D7
  names), on the targeted `Mathlib.Algebra.Field.Defs` import (D6: `[Field F]`, the
  weakest fitting class for an inverse); the boolean primitives `not_`/`and_`/`or_`
  are here as `not`/`and`/`or` (D7 names; they shadow core's Bool functions inside the
  namespace — type-directed resolution disambiguates), on the D11 doors settled at
  step 9: `and` is `mul` under the `BoolVar.unchecked` retag (a product of bits is a
  bit), `or` is De Morgan over `and`/`not`, `not` the pure retag `1 − b`.
- `CheckedType` instances: `FVar`, `BoolVar`, `UnChecked`, and the `Tuple` pair (step 9,
  `equals`'s witness pair) are here; `Unit`, `NoInput`/`NoOutput`, `Const`, `Product`,
  `Vector`, and `Record` land with their `CircuitType` partners (steps 10/14);
  `GCheckedType`/`RCheckedType`/`genericCheck` are the deriving machinery, out of scope
  (D8).
- PS `exists` is `witness` (`exists` is a Lean keyword). PS `read` is `readVar`: `read`
  is core Lean's `MonadReader` primitive, and `AsProver` is a `ReaderT`, so the bare name
  already means "fetch the assignment table" inside exactly the witness blocks that call
  it. (`readCVar` keeps its PS name; it is the single-expression primitive `readVar`
  generalizes through `CircuitType`.)

Public results: the `LawfulMonad (CircuitM F c)` instance (PS gets the monad laws for
free from function composition; the deep embedding must prove them).
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

/-- Back-fill already-allocated variables from a witness computation (PS `assignVars`). -/
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

/-- `mul`'s witness computation: the product of the operands' values. Public only for
the gadget laws. -/
def mulWit [Add F] [Mul F] (x y : FVar F) : AsProver F F := do
  let xv ← AsProver.readCVar x
  let yv ← AsProver.readCVar y
  pure (xv * yv)

/-- `mul`'s witnessing branch: witness the product, pin it with one `r1cs` constraint.
Split out so the gadget laws (in `DSL/Field`, its family module) quantify over it uniformly. -/
def mulCore [Add F] [Mul F] [BasicSystem F c] (x y : FVar F) : CircuitM F c (FVar F) := do
  let z ← witness (val := F) (mulWit x y)
  addConstraint (BasicSystem.r1cs x y z)
  pure z

/-- Multiply two field variables (PS `mul_`). Constants fold without constraining: two
constants multiply out, and a constant times an expression is `scale_`. Otherwise the
product is witnessed and pinned with one `r1cs` constraint. -/
def mul [Add F] [Mul F] [Zero F] [One F] [DecidableEq F] [BasicSystem F c] (x y : FVar F) :
    CircuitM F c (FVar F) :=
  match x, y with
  | .const a, .const b => pure (.const (a * b))
  | .const a, y => pure (CVar.scale_ a y)
  | x, .const b => pure (CVar.scale_ b x)
  | x, y => mulCore x y

/-- `inv`'s witness computation: the inverse, failing on zero (PS `DivisionByZero`).
Public only for the gadget laws. -/
def invWit [Field F] [DecidableEq F] (x : FVar F) : AsProver F F := do
  let xv ← AsProver.readCVar x
  if xv = 0 then AsProver.throw "inv: division by zero"
  else pure xv⁻¹

/-- `inv`'s witnessing branch: witness the inverse, pin it with `x · xInv = 1`. Split
out so the gadget laws (in `DSL/Field`) quantify over it uniformly. -/
def invCore [Field F] [DecidableEq F] [BasicSystem F c] (x : FVar F) :
    CircuitM F c (FVar F) := do
  let xInv ← witness (val := F) (invWit x)
  addConstraint (BasicSystem.r1cs x xInv (.const 1))
  pure xInv

/-- Invert a field variable: witness the inverse, pin it with `x · xInv = 1` (PS `inv_`).
A constant folds to its constant inverse — total where PS crashes on the constant zero
(Lean's `0⁻¹ = 0`); either way no constraint is emitted. During a prover run a zero
argument fails the witness computation, as in PS (`DivisionByZero`). -/
def inv [Field F] [DecidableEq F] [BasicSystem F c] (x : FVar F) : CircuitM F c (FVar F) :=
  match x with
  | .const a => pure (.const a⁻¹)
  | x => invCore x

/-- Divide field variables: `x · y⁻¹`, one `inv` then one `mul` (PS `div_`). A zero
divisor fails in `inv`'s witness computation. -/
def div [Field F] [DecidableEq F] [BasicSystem F c] (x y : FVar F) :
    CircuitM F c (FVar F) := do
  let yInv ← inv y
  mul x yInv

/-- Negate a boolean variable: `1 − b`, pure — no constraint (PS `not_`), through the
`BoolVar.unchecked` door (D11): boolean because `b` is. The name shadows core `not`
inside the `Snarky` namespace; type-directed resolution disambiguates at use sites. -/
def not [Add F] [Sub F] [Zero F] [One F] [Neg F] [DecidableEq F] (b : BoolVar F) :
    BoolVar F :=
  .unchecked (CVar.sub_ (.const 1) ↑b)

/-- Conjoin boolean variables: the product, retagged (PS `and_` is `mul_` under
`coerce`) — boolean because a product of bits is a bit (`Snarky.and_sound`). -/
def and [Add F] [Mul F] [Zero F] [One F] [DecidableEq F] [BasicSystem F c]
    (a b : BoolVar F) : CircuitM F c (BoolVar F) := do
  let r ← mul ↑a ↑b
  pure (.unchecked r)

/-- Disjoin boolean variables by De Morgan: `¬(¬a ∧ ¬b)` (PS `or_`). -/
def or [Add F] [Sub F] [Mul F] [Zero F] [One F] [Neg F] [DecidableEq F] [BasicSystem F c]
    (a b : BoolVar F) : CircuitM F c (BoolVar F) := do
  let r ← and (Snarky.not a) (Snarky.not b)
  pure (Snarky.not r)

/-- `not` computes boolean negation: the bit encoding of `!bb` (the `CircuitType Bool`
encoding — the relation the gadget laws speak through). Pure gadget, so its law is
evaluation-level, like `sum_eval`. -/
theorem not_eval [CommRing F] [DecidableEq F] {b : BoolVar F} {env : Assignments F}
    {bb : Bool} (hb : (↑b : CVar F).eval env = .ok (if bb then 1 else 0)) :
    (↑(Snarky.not b) : CVar F).eval env = .ok (if !bb then 1 else 0) := by
  have h := CVar.eval_sub_ (rfl : (CVar.const (1 : F)).eval env = .ok 1) hb
  show (CVar.sub_ (.const 1) ↑b).eval env = _
  rw [h]
  cases bb <;> simp

end Snarky
