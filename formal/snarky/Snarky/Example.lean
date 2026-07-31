import Mathlib.Algebra.Field.ZMod
import Snarky.DSL
import Snarky.Constraint.Basic

/-!
# End-to-end examples over the `Basic` backend

The concrete `Snarky.Basic` constraint model over `ZMod 17`, exercising the whole stack:
the typed `witness` combinator, both interpreters, an instantiation of the completeness
theorem, and the field gadgets (`DSL/Field` and `DSL/Monad`) on the fixed inputs the PS
QuickCheck specs sample (D9). Everything here reduces by `rfl`/`decide`, so this file
doubles as a regression test for the executable semantics.

The first circuit mirrors the smallest interesting PS example: witness two field
elements, multiply them (one witnessed product + one `r1cs` constraint), and assert the
result equals a constant.
-/

namespace Snarky.Example

/-! ## The circuit -/

/-- The example's field: the integers mod 17 — small enough for `decide` throughout, and
a `Field` (17 is prime), which the `equals`/`inv`/`div` gadgets need. -/
abbrev F17 := ZMod 17

instance : Fact (Nat.Prime 17) := ⟨by decide⟩

/-- Witness `x = 3` and `y = 5`, multiply, assert the product is `15`. -/
def mulCircuit : CircuitM F17 (Basic F17) (FVar F17) := do
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
    [ .r1cs (.var 0) (.var 1) (.var 2), .r1cs (.var 2) (.const 1) (.const 15) ] := by
  decide

/-- The prover succeeds: every witness computation runs and every constraint holds. -/
example : (prove Basic.holds mulCircuit 0 Assignments.empty).isOk = true := by decide

/-- Changing the asserted constant makes the prover reject at the constraint check. -/
example :
    (prove Basic.holds (do let z ← mulCircuit; assertEq z (.const 14))
      0 Assignments.empty).isOk = false := by
  decide

/-- The completeness theorem, instantiated: any successful run of `mulCircuit` yields
assignments satisfying every built constraint. -/
example {x : FVar F17} {nv : Nat} {env : Assignments F17}
    (h : prove Basic.holds mulCircuit 0 Assignments.empty = .ok ⟨x, nv, env⟩) :
    ∀ con ∈ constraints mulCircuit, con.holds env = true :=
  prove_complete (holds := Basic.holds) (fun _con _ _ hle hh => Basic.holds_mono hle hh) h

/-! ## Field gadgets (walk step 9)

The fixed inputs the PS QuickCheck specs sample, as `decide` checks: run the gadget
under the prover and read the result's value from the final assignment. -/

/-- Run a circuit under the prover and evaluate the result (through `view`) against the
final assignment — `none` if the run or the evaluation fails. -/
def proverValue (view : α → CVar F17) (m : CircuitM F17 (Basic F17) α) : Option F17 :=
  match prove Basic.holds m 0 Assignments.empty with
  | .ok p => (CVar.eval (view p.result) p.assignments).toOption
  | .error _ => none

/-- Witness both inputs and test equality — the PS eq spec's circuit. -/
def eqCircuit (a b : F17) : CircuitM F17 (Basic F17) (BoolVar F17) := do
  let x ← witness (val := F17) (pure a)
  let y ← witness (val := F17) (pure b)
  equals x y

/-- Equal inputs: the prover succeeds and answers `1`. -/
example : proverValue BoolVar.toCVar (eqCircuit 7 7) = some 1 := by decide

/-- Distinct inputs: the prover succeeds (witnessing `zInv = (a − b)⁻¹`) and answers
`0`. -/
example : proverValue BoolVar.toCVar (eqCircuit 3 5) = some 0 := by decide

/-- `equals` costs two witness variables and two constraints on top of its inputs. -/
example : (build (eqCircuit 3 5) 0).nextVar = 4 ∧
    (constraints (eqCircuit 3 5)).length = 2 := by decide

/-- A constant comparison folds — no constraints, constant answer. -/
def constEq : CircuitM F17 (Basic F17) (BoolVar F17) := equals (.const 3) (.const 4)

example : (constraints constEq).length = 0 ∧ proverValue BoolVar.toCVar constEq = some 0 := by
  decide

/-- `neq` is the negated `equals` bit. -/
example : proverValue BoolVar.toCVar
    (do neq (← witness (val := F17) (pure 3)) (← witness (val := F17) (pure 5)))
    = some 1 := by decide

/-- `inv` witnesses the inverse: `3⁻¹ = 6` (mod 17). -/
example : proverValue id (do inv (← witness (val := F17) (pure 3))) = some 6 := by decide

/-- `div` composes `inv` and `mul`: `8 / 2 = 4`. -/
example : proverValue id
    (do div (← witness (val := F17) (pure 8)) (← witness (val := F17) (pure 2)))
    = some 4 := by decide

/-- `mul` by a constant folds to `scale_` — no constraint on top of the witness. -/
def constMul : CircuitM F17 (Basic F17) (FVar F17) := do
  mul (.const 3) (← witness (val := F17) (pure 5))

example : proverValue id constMul = some 15 ∧ (constraints constMul).length = 0 := by decide

/-- `square` uses the dedicated constraint: `5² = 8` (mod 17). -/
example : proverValue id (do square (← witness (val := F17) (pure 5))) = some 8 := by decide

/-- `pow` by repeated squaring: `2¹⁰ = 4` (mod 17). -/
example : proverValue id (do pow (← witness (val := F17) (pure 2)) 10) = some 4 := by decide

/-- `sum` is pure: `3 + x + 4` with `x = 5` witnessed — the PS sum spec's
`pure ∘ sum` shape. -/
example : proverValue id
    (do let x ← witness (val := F17) (pure 5); pure (sum [.const 3, x, .const 4]))
    = some 12 := by decide

/-! ## Boolean gadgets (walk step 10) -/

/-- Witness two bits (checked: `witness` at `Bool` emits the `boolean` constraints) and
combine them with a boolean gadget. -/
def bitCircuit (f : BoolVar F17 → BoolVar F17 → CircuitM F17 (Basic F17) (BoolVar F17))
    (x y : Bool) : CircuitM F17 (Basic F17) (BoolVar F17) := do
  let a ← witness (val := Bool) (pure x)
  let b ← witness (val := Bool) (pure y)
  f a b

/-- `and` is conjunction on every input pair. -/
example : (List.product [true, false] [true, false]).all (fun (x, y) =>
    proverValue BoolVar.toCVar (bitCircuit Snarky.and x y) = some (bit (x && y))) := by
  decide

/-- `or` is disjunction on every input pair. -/
example : (List.product [true, false] [true, false]).all (fun (x, y) =>
    proverValue BoolVar.toCVar (bitCircuit Snarky.or x y) = some (bit (x || y))) := by
  decide

/-- `xor` is exclusive-or on every input pair. -/
example : (List.product [true, false] [true, false]).all (fun (x, y) =>
    proverValue BoolVar.toCVar (bitCircuit Snarky.xor x y) = some (bit (x ^^ y))) := by
  decide

/-- `not` is pure negation. -/
example : proverValue BoolVar.toCVar
    (do pure (Snarky.not (← witness (val := Bool) (pure true)))) = some 0 := by decide

/-- `select` muxes field variables by the witnessed bit. -/
example : proverValue id
    (do let b ← witness (val := Bool) (pure true)
        let x ← witness (val := F17) (pure 7)
        let y ← witness (val := F17) (pure 9)
        select b x y)
    = some 7 := by decide

/-- `select` on the false bit takes the else branch. -/
example : proverValue id
    (do let b ← witness (val := Bool) (pure false)
        let x ← witness (val := F17) (pure 7)
        let y ← witness (val := F17) (pure 9)
        select b x y)
    = some 9 := by decide

/-- `any` over three witnessed bits uses the sum test. -/
example : proverValue BoolVar.toCVar
    (do let a ← witness (val := Bool) (pure false)
        let b ← witness (val := Bool) (pure true)
        let c ← witness (val := Bool) (pure false)
        Snarky.any [a, b, c])
    = some 1 := by decide

/-- `all` over three witnessed bits uses the length test. -/
example : proverValue BoolVar.toCVar
    (do let a ← witness (val := Bool) (pure true)
        let b ← witness (val := Bool) (pure true)
        let c ← witness (val := Bool) (pure false)
        Snarky.all [a, b, c])
    = some 0 := by decide

end Snarky.Example
