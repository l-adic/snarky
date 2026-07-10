import Snarky.DSL
import Snarky.Constraint.R1CS
import Snarky.Laws

/-!
# End-to-end example: an R1CS multiplication circuit

The `Snarky.Constraint.R1CS` backend over `Fin 17`, exercising the whole stack: the typed
`witness` combinator, both interpreters, and an instantiation of the completeness
theorem. Everything here reduces by `rfl`/`decide`, so this file doubles as a regression
test for the executable semantics.

The circuit mirrors the smallest interesting PS example: witness two field elements,
multiply them (one witnessed product + one `r1cs` constraint), and assert the result
equals a constant.
-/

namespace Snarky.Example

open Snarky Snarky.Constraint

/-! ## The circuit -/

abbrev F17 := Fin 17

/-- Witness `x = 3` and `y = 5`, multiply, assert the product is `15`. -/
def mulCircuit : CircuitM F17 (R1CS F17) (FVar F17) := do
  let x ← witness (val := F17) (pure 3)
  let y ← witness (val := F17) (pure 5)
  let z ← mul x y
  assertEq z (.const 15)
  pure z

/-! ## Running it -/

/-- The builder allocates three variables (`x`, `y`, and the product). -/
example : (build mulCircuit 0).nextVar = 3 := by decide

/-- The builder emits two constraints (`x * y = z` and `z * 1 = 15`), in emission order. -/
example : constraints mulCircuit =
    [ ⟨.var 0, .var 1, .var 2⟩, ⟨.var 2, .const 1, .const 15⟩ ] := by decide

/-- The prover succeeds: every witness computation runs and every constraint holds. -/
example : (prove R1CS.holds mulCircuit 0 Assignments.empty).isOk = true := by decide

/-- Changing the asserted constant makes the prover reject at the constraint check. -/
example :
    (prove R1CS.holds (do let z ← mulCircuit; assertEq z (.const 14))
      0 Assignments.empty).isOk = false := by
  decide

/-- The completeness theorem, instantiated: any successful run of `mulCircuit` yields
assignments satisfying every built constraint. -/
example {x : FVar F17} {nv : Nat} {env : Assignments F17}
    (h : prove R1CS.holds mulCircuit 0 Assignments.empty = .ok ⟨x, nv, env⟩) :
    ∀ con ∈ constraints mulCircuit, con.holds env = true :=
  prove_sound (holds := R1CS.holds) (fun _con _ _ hle hh => R1CS.holds_mono hle hh) h

end Snarky.Example
