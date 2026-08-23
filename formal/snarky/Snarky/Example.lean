import Mathlib.Algebra.Field.ZMod
import Snarky.DSL
import Snarky.Constraint.Basic

-- `mvcgen` is experimental; this option is its acknowledged-use switch (see the
-- `Backend/WP` module docstring for the adoption rationale).
set_option mvcgen.warning false

/-!
# The framework showcase: a walked circuit

`cubic` constrains `y = x³ + x + 5` from three gadget calls. Its soundness law is proved
by walking the do-block — unfold, `mvcgen` (the registry supplies each callee's spec),
close the arithmetic — and run down to an interpreter-level statement through
`builder_spec_iff`; its completeness law is the run equation, one rewrite per callee's
run equation, with the existential read off it through `Runs.le`. The soundness law is
deliberately not `@[spec]`: `cubic` is an endpoint, not a gadget other circuits compose
with. Two `decide` examples execute both directions in the kernel.

The second half holds the executable edges no triple states: rejection (completeness
proves acceptance on good inputs; refusal on bad ones is stated nowhere else), emission
shape and cost (which rows a gadget emits; constant operands fold to none), and the one
exhibit of the lawless `AssertEqual` pair instance. Everything reduces by `decide`,
making the file the per-gadget kernel-reduction net.
-/

namespace Snarky.Example

/-- The showcase field: the integers mod 17 — small enough for `decide`, and a `Field`
(17 is prime), which the gadget laws need. -/
abbrev F17 := ZMod 17

instance : Fact (Nat.Prime 17) := ⟨by decide⟩

open Std.Do

/-- Constrain `y = x³ + x + 5` (the circuit every SNARK tutorial builds): three gadget
calls, generic over the backend. -/
def cubic {F c : Type} [Field F] [DecidableEq F] [BasicSystem F c] (x y : FVar F) :
    CircuitM F c PUnit := do
  let x2 ← square x
  let x3 ← mul x2 x
  assertEqual (sum [x3, x, .const 5]) y

/-- Any satisfying assignment forces `y = x³ + x + 5`. -/
theorem cubic_spec {F c : Type} {V : Valuation F} [Field F] [DecidableEq F]
    [BasicSystem F c] [ConstraintHolds F c] [LawfulBasicSystem F c]
    (x y : FVar F) :
    ⦃⌜True⌝⦄
    cubic (c := Builder V c) x y
    ⦃⇓ _ _ => ⌜x.val V ^ 3 + x.val V + 5 = y.val V⌝⦄ := by
  simp only [cubic]
  mvcgen                -- square_spec, mul_spec, assertEqual_spec, one walk
  rename_i x2 _ hx2 x3 _ hx3 _ _
  intro heq
  simp only [sum, List.foldl, circuitVal] at heq
  rw [← heq, hx3, hx2]
  ring

/-- On operands satisfying the equation the honest run lands at the two gadgets' states
— `square`'s, then `mul`'s; the assertion allocates nothing. The extra lines relative to
the soundness proof carry the readings along the two states. -/
theorem cubic_run {F : Type} [Field F] [DecidableEq F] {x y : FVar F} (st : ProverState F)
    (hx : x.Scoped st) (hy : y.Scoped st)
    (hcurve : x.val st.env.toValuation ^ 3 + x.val st.env.toValuation + 5
      = y.val st.env.toValuation) :
    prove (Checker.holds (F := F) (c := Basic F)) (cubic (c := Basic F) x y) st.nv st.env
      = .ok ((mulRun (squareRun st x).1 (squareRun st x).2 x).1.out ()) := by
  have hsq := squareRun_grants (st := st) hx
  have hm := mulRun_grants hsq.fvar_scoped (hx.of_le hsq.le)
  have hle := hsq.le.trans hm.le
  have hx3 : (mulRun (squareRun st x).1 (squareRun st x).2 x).2.val
      (mulRun (squareRun st x).1 (squareRun st x).2 x).1.env.toValuation
      = x.val st.env.toValuation * x.val st.env.toValuation * x.val st.env.toValuation := by
    rw [hm.fvar_val, hsq.fvar_val, CVar.val_of_le hsq.le hx]
  simp only [cubic, prove_bind, square_run st hx, Except.bind,
    mul_run _ hsq.fvar_scoped (hx.of_le hsq.le)]
  refine assertEqual_run _ (CVar.Scoped.sum (by simp [hm.fvar_scoped, hx.of_le hle]))
    (hy.of_le hle) ?_
  simp only [sum, List.foldl, CVar.val_add_, CVar.val, hx3, CVar.val_of_le hle hx,
    CVar.val_of_le hle hy]
  rw [← hcurve]
  ring

/-- `cubic_spec` run through `builder_spec_iff`: any assignment satisfying the built
constraints places the readings of `(x, y)` on the curve `y = x³ + x + 5`. -/
theorem cubic_sound {F c : Type} [Field F] [DecidableEq F]
    [BasicSystem F c] [ConstraintHolds F c] [LawfulBasicSystem F c]
    (x y : FVar F) (V : Valuation F) (nv : Nat)
    (hsat : ∀ con ∈ (build (cubic (c := c) x y) nv).constraints,
      ConstraintHolds.Holds V con) :
    x.val V ^ 3 + x.val V + 5 = y.val V :=
  (builder_spec_iff _ _).mp (cubic_spec (V := V) x y) nv hsat

/-- `cubic_run` read as an existential through `Runs.le`: from any table where the
readings of `(x, y)` form a point of the curve, the honest run succeeds, extending the
table. -/
theorem cubic_complete {F : Type} [Field F] [DecidableEq F] {x y : FVar F}
    (st : ProverState F) (hx : x.Scoped st) (hy : y.Scoped st)
    (hcurve : x.val st.env.toValuation ^ 3 + x.val st.env.toValuation + 5
      = y.val st.env.toValuation) :
    ∃ out, prove (Checker.holds (F := F) (c := Basic F)) (cubic (c := Basic F) x y)
        st.nv st.env = .ok out ∧ st.env.Le out.assignments :=
  ⟨_, cubic_run st hx hy hcurve, Runs.le (cubic_run st hx hy hcurve)⟩

/-- The laws, exercised in the kernel: the honest run accepts `x = 3, y = 35`
(`27 + 3 + 5`)… -/
example : (prove Basic.holds
    ((do let x ← witness (val := F17) (pure 3)
         cubic x (.const 35)) : CircuitM F17 (Basic F17) PUnit)
    0 Assignments.empty).isOk = true := by decide

/-- …and rejects `y = 36`. -/
example : (prove Basic.holds
    ((do let x ← witness (val := F17) (pure 3)
         cubic x (.const 36)) : CircuitM F17 (Basic F17) PUnit)
    0 Assignments.empty).isOk = false := by decide

/-! ## The executable edges the triple laws do not state -/

/-- Run a circuit under the prover and evaluate the result (through `view`) against the
final assignment — `none` if the run or the evaluation fails. -/
def proverValue (view : α → CVar F17) (m : CircuitM F17 (Basic F17) α) : Option F17 :=
  match prove Basic.holds m 0 Assignments.empty with
  | .ok p => (CVar.eval (view p.result) p.assignments).toOption
  | .error _ => none

/-- Does the honest prover accept this circuit? -/
def proverOk (m : CircuitM F17 (Basic F17) PUnit) : Bool :=
  (prove Basic.holds m 0 Assignments.empty).isOk

/-! ### Emission shape and cost -/

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

/-! ### Rejection -/

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

/-- Too few bits: the packing row rejects the honest run (`13` does not fit in two
bits). -/
example : (prove Basic.holds
    ((do let x ← witness (val := F17) (pure 13)
         let _ ← unpack x 2
         pure PUnit.unit) : CircuitM F17 (Basic F17) PUnit)
    0 Assignments.empty).isOk = false := by decide

/-! ### The pair instance -/

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
