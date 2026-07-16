import Snarky.Types

/-!
# The user-facing combinators

Port of the user-facing surface of `Snarky.Circuit.DSL`
(packages/snarky/src/Snarky/Circuit/DSL.purs and its `Monad`/`Field`/`Assert`
submodules): the typed `witness` combinator (PS `exists`, renamed — `exists` is a Lean
keyword), the prover-side `readVar` (PS `read`), and the first field combinators
(`mul` from PS `mul_`, `assertEq` from PS `assertEqual_`). Everything here is sugar over
the `CircuitM` smart constructors and the `Snarky.Types`/`Snarky.BasicSystem` classes;
the PS numeric-tower instances (`Semiring (Snarky f c r (FVar f))` …) are deliberately
not ported — their underlying combinators live here as plain functions.
-/

namespace Snarky

variable {F c val var : Type u}

/-- Witness a typed value (PS `exists`, renamed — `exists` is a Lean keyword): allocate
`size` fresh variables, record the witness computation for prover runs, assemble the
variable bundle, and emit its `check` constraints under both interpreters. -/
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

/-- Multiply two field variables: witness the product, constrain it with `r1cs`
(PS `mul_`). -/
def mul [Add F] [Mul F] [BasicSystem F c] (x y : FVar F) : CircuitM F c (FVar F) := do
  let z ← witness (val := F) do
    let xv ← AsProver.readCVar x
    let yv ← AsProver.readCVar y
    pure (xv * yv)
  addConstraint (BasicSystem.r1cs x y z)
  pure z

/-- Assert that two field variables are equal, via `x * 1 = y` (PS `assertEqual_`). -/
def assertEq [One F] [BasicSystem F c] (x y : FVar F) : CircuitM F c PUnit :=
  addConstraint (BasicSystem.r1cs x (.const 1) y)

end Snarky
