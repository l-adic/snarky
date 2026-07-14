import Snarky.Kimchi.Backend
import Snarky.DSL

/-!
# End-to-end: a DSL circuit as Kimchi Generic gate rows

The `Snarky.Example` multiply circuit, rebuilt against the `GateConstraint` backend and
carried through to Kimchi's Generic gate: build the circuit, dump its constraints, run the
prover, translate each emitted constraint to a `Gate.Generic` row against the prover's
assignment, and `decide` that the whole gate list is satisfied (`Gate.satisfies`). Every
check reduces, so the file is a regression test for the bridge's executable semantics.
-/

namespace Snarky.Kimchi.Example

open Snarky Snarky.Kimchi Kimchi.Gate

abbrev F17 := ZMod 17

/-- Witness `x = 3` and `y = 5`, multiply, assert the product is `15` — the same circuit
as `Snarky.Example.mulCircuit`, now over the Generic-gate backend. -/
def mulCircuit : CircuitM F17 (GateConstraint F17) (FVar F17) := do
  let x ← witness (val := F17) (pure 3)
  let y ← witness (val := F17) (pure 5)
  let z ← mul x y
  assertEq z (.const 15)
  pure z

/-- The prover's final assignment (it succeeds, so this is the `ok` branch). -/
def solved : Assignments F17 :=
  match prove GateConstraint.holds mulCircuit 0 Assignments.empty with
  | .ok ⟨_, _, env⟩ => env
  | .error _ => Assignments.empty

/-- Translate every emitted constraint to a Generic gate row against the solved
assignment (`none` would signal an unevaluable operand — does not happen here). -/
def rows : Option (List (Generic F17)) :=
  (constraints mulCircuit).mapM (·.toRow solved)

/-! ## Running it -/

/-- The prover succeeds. -/
example : (prove GateConstraint.holds mulCircuit 0 Assignments.empty).isOk = true := by decide

/-- Two constraints are emitted (the product and the equality assertion). -/
example : (constraints mulCircuit).length = 2 := by decide

/-- Every constraint translates to a Generic row, and the resulting gate list is
satisfied — the DSL circuit is a valid Kimchi Generic-gate circuit. -/
example : ∃ gs, rows = some gs ∧ Kimchi.Gate.satisfies gs = true := by decide

end Snarky.Kimchi.Example
