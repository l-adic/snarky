import Snarky.Example

/-!
# The executable edges the triple laws do not state

`decide` checks over `F17` for exactly the behavior no triple covers, in three classes:

- **Rejection**: the completeness triples prove the honest run ACCEPTS on good inputs;
  that it REJECTS on bad ones — a failing assertion, a non-bit where a bit is due, a
  value that does not fit its declared width — is stated nowhere else.
- **Emission shape and cost**: which constraints a gadget emits, how many, and that
  constant operands fold to NONE — the PS-parity surface the triples are silent on.
- **The pair instance**: `AssertEqual (a × b)`'s `isEqual` has no law; its exhibit
  lives here.

These are also the package's per-gadget kernel-reduction net: everything here reduces
by `decide`, which is what catches a non-reducible function slipping into a gadget
path.
-/

namespace Snarky.Example

/-! ## Helpers -/

/-- Run a circuit under the prover and evaluate the result (through `view`) against the
final assignment — `none` if the run or the evaluation fails. -/
def proverValue (view : α → CVar F17) (m : CircuitM F17 (Basic F17) α) : Option F17 :=
  match prove Basic.holds m 0 Assignments.empty with
  | .ok p => (CVar.eval (view p.result) p.assignments).toOption
  | .error _ => none

/-- Does the honest prover accept this circuit? -/
def proverOk (m : CircuitM F17 (Basic F17) PUnit) : Bool :=
  (prove Basic.holds m 0 Assignments.empty).isOk

/-! ## Emission shape and cost -/

/-- Witness `x = 3` and `y = 5`, multiply, assert the product is `15`. -/
def mulCircuit : CircuitM F17 (Basic F17) (FVar F17) := do
  let x ← witness (val := F17) (pure 3)
  let y ← witness (val := F17) (pure 5)
  let z ← mul x y
  assertEq z (.const 15)
  pure z

/-- The builder allocates three variables (`x`, `y`, and the product). -/
example : (build mulCircuit 0).nextVar = 3 := by decide

/-- The builder emits two constraints (`x * y = z` and `z = 15`), in emission order. -/
example : constraints mulCircuit =
    [ .r1cs (.var 0) (.var 1) (.var 2), .equal (.var 2) (.const 15) ] := by
  decide

/-- Witness both inputs and test equality. -/
def eqCircuit (a b : F17) : CircuitM F17 (Basic F17) (BoolVar F17) := do
  let x ← witness (val := F17) (pure a)
  let y ← witness (val := F17) (pure b)
  equals x y

/-- `equals` costs two witness variables and two constraints on top of its inputs. -/
example : (build (eqCircuit 3 5) 0).nextVar = 4 ∧
    (constraints (eqCircuit 3 5)).length = 2 := by decide

/-- A constant comparison folds — no constraints, constant answer. -/
def constEq : CircuitM F17 (Basic F17) (BoolVar F17) := equals (.const 3) (.const 4)

example : (constraints constEq).length = 0 ∧ proverValue BoolVar.toCVar constEq = some 0 := by
  decide

/-- `mul` by a constant folds to `scale_` — no constraint on top of the witness. -/
def constMul : CircuitM F17 (Basic F17) (FVar F17) := do
  mul (.const 3) (← witness (val := F17) (pure 5))

example : proverValue id constMul = some 15 ∧ (constraints constMul).length = 0 := by decide

/-! ## Rejection -/

/-- A false equality assertion stops the run at the constraint check. -/
example :
    (prove Basic.holds (do let z ← mulCircuit; assertEq z (.const 14))
      0 Assignments.empty).isOk = false := by
  decide

/-- `assertNonZero` rejects zero: the inverse witness fails. -/
example : proverOk (do assertNonZero (← witness (val := F17) (pure 0))) = false := by decide

/-- `assertNotEqual` rejects equal values. -/
example : proverOk (do
    assertNotEqual (← witness (val := F17) (pure 4)) (← witness (val := F17) (pure 4)))
    = false := by decide

/-- `assertSquare` rejects a false square. -/
example : proverOk (do
    assertSquare (← witness (val := F17) (pure 4)) (← witness (val := F17) (pure 15)))
    = false := by decide

/-- `assert` rejects a false bit. -/
example : proverOk (do assert (← witness (val := Bool) (pure false))) = false := by decide

/-- `assertExactlyOne` rejects a two-hot list. -/
example : proverOk (do
    let a ← witness (val := Bool) (pure true)
    let b ← witness (val := Bool) (pure true)
    let c ← witness (val := Bool) (pure false)
    assertExactlyOne [a, b, c]) = false := by decide

/-- The canonical representative at the concrete field: `ZMod.val` — the instance
that discharges the bit laws' `ToNat` hypotheses. -/
instance : ToNat F17 := ⟨ZMod.val⟩

/-- Too few bits: the packing row rejects the honest run (`13` does not fit in two
bits). -/
example : (prove Basic.holds
    ((do let x ← witness (val := F17) (pure 13)
         let _ ← unpack x 2
         pure PUnit.unit) : CircuitM F17 (Basic F17) PUnit)
    0 Assignments.empty).isOk = false := by decide

/-! ## The pair instance -/

/-- The `AssertEqual` pair instance: componentwise test, conjoined — the one exhibit
of a lawless instance. -/
example : proverValue BoolVar.toCVar
    (do let x ← witness (val := F17) (pure 3)
        let y ← witness (val := F17) (pure 3)
        let b₁ ← witness (val := Bool) (pure true)
        let b₂ ← witness (val := Bool) (pure true)
        isEqual (x, b₁) (y, b₂))
    = some 1 := by decide

end Snarky.Example
