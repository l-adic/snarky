import Mathlib.Algebra.Field.ZMod
import Snarky.Backend.Compile
import Snarky.DSL
import Snarky.Constraint.Basic

/-!
# End-to-end examples over the `Basic` backend

Showcase circuits over the concrete `Snarky.Basic` constraint model, everything reduced
by `decide` in the kernel.

The headline is snarky's canonical example — **knowledge of a cube root**. The prover
finds a root out of circuit (`cubeRoot?`, brute force — untrusted helper code that may
do anything); the circuit only *checks*, with two multiplications and an equality
against the public input. The root itself stays private (output type `PUnit`: no public
output slot), and `solve` succeeds on exactly the cubes — verified exhaustively over
the whole field. The field is `ZMod 13` because there the statement has content: `3`
divides `12`, so cubing is 3-to-1 on units and most elements are *not* cubes (at `17`
every element is a cube and the circuit could never reject).

The second circuit is the whole-circuit seam of walk step 14, concretely: `cubeCircuit`
(cube the public input) compiled to its three-row system and solved, the public slots
decoding exactly as `solve_complete` states in general.

The per-gadget D9 regression checks live in `Example/Gadgets.lean`.
-/

namespace Snarky.Example

/-! ## The fields -/

/-- The seam example's field: the integers mod 17 — small enough for `decide`
throughout, and a `Field` (17 is prime), which `Example/Gadgets`'s `equals`/`inv`/`div`
checks need. -/
abbrev F17 := ZMod 17

instance : Fact (Nat.Prime 17) := ⟨by decide⟩

/-- The knowledge example's field: the integers mod 13, where cubing is 3-to-1 on units
(`3 ∣ 12`) — so "x has a cube root" is a statement most elements FAIL. -/
abbrev F13 := ZMod 13

/-! ## Knowledge of a cube root -/

/-- Brute-force root search — the prover's out-of-circuit helper: try every field
element. Untrusted and expensive; the circuit below only checks its answer. -/
def cubeRoot? (v : F13) : Option F13 :=
  ((List.range 13).map fun n => (n : F13)).find? fun y => decide (y * y * y = v)

/-- Prove knowledge of a cube root of the public input: witness the root — computed by
`cubeRoot?`, failing the run (PS `throwAsProver`) when none exists — then constrain
`w · w · w = x` in two rows. The root stays private: the `PUnit` output claims no
public output slot, so the compiled statement is just "x is a cube". -/
def cubeRootCircuit (x : FVar F13) : CircuitM F13 (Basic F13) PUnit := do
  let w ← witness (val := F13) fun env => do
    let v ← x.eval env
    match cubeRoot? v with
    | some y => pure y
    | none => .error (.custom "no cube root")
  let w2 ← square w
  let w3 ← mul w2 w
  assertEqual w3 x

/-- One public slot (the input; `PUnit` claims no output) and three private variables:
the root and the two products. -/
example : (compile (a := F13) (b := PUnit) cubeRootCircuit).nextVar = 4 := by decide

/-- The compiled system is only the check — square, multiply, compare against the
public-input slot. No row reflects the SEARCH for the root. -/
example : (compile (a := F13) (b := PUnit) cubeRootCircuit).constraints =
    [ .square (.var 1) (.var 2), .r1cs (.var 2) (.var 1) (.var 3),
      .equal (.var 3) (.var 0) ] := by decide

/-- `8 = 2³` is a cube: the run accepts, and the root sits at the first private
variable — readable from the assignment, present in no public slot. -/
example : ((solve (a := F13) (b := PUnit) Basic.holds cubeRootCircuit 8).toOption.map
    fun r => r.2 1) = some (some 2) := by decide

/-- `2` is not a cube mod 13: the search comes up empty and the honest run stops inside
the witness computation, before any constraint is checked. -/
example : (solve (a := F13) (b := PUnit) Basic.holds cubeRootCircuit 2).isOk = false := by
  decide

/-- The statement, exhaustively: `solve` accepts exactly the five cubes among the
thirteen public inputs — the compiled circuit really means "x has a cube root". -/
example : ∀ x : F13,
    (solve (a := F13) (b := PUnit) Basic.holds cubeRootCircuit x).isOk = true
      ↔ ∃ y : F13, y * y * y = x := by decide

/-! ## Whole-circuit compile/solve (walk step 14) -/

/-- Cube the public input: one `square` row, one `r1cs` row. -/
def cubeCircuit (x : FVar F17) : CircuitM F17 (Basic F17) (FVar F17) := do
  let y ← square x
  mul y x

/-- Public slots come first — input at `0`, output at `1`; the gadgets allocate `2`
and `3`. -/
example : (compile (a := F17) (b := F17) cubeCircuit).nextVar = 4 := by decide

/-- The compiled system: the gadget rows read the public-input slot, and the final row
pins the circuit's result to the public-output slot. -/
example : (compile (a := F17) (b := F17) cubeCircuit).constraints =
    [ .square (.var 0) (.var 2), .r1cs (.var 2) (.var 0) (.var 3),
      .equal (.var 3) (.var 1) ] := by decide

/-- Solving computes the output: `2³ = 8`. -/
example : ((solve (a := F17) (b := F17) Basic.holds cubeCircuit 2).toOption.map
    Prod.fst) = some 8 := by decide

/-- The seam, concretely: the solved assignment decodes the input at slot `0` and the
output at slot `1` — the facts `solve_complete` states in general. -/
example : ((solve (a := F17) (b := F17) Basic.holds cubeCircuit 2).toOption.map
    fun r => (r.2 0, r.2 1)) = some (some 2, some 8) := by decide

/-- A failing assertion stops the solver: `2² ≠ 3`. -/
example : (solve (a := F17) (b := F17) Basic.holds
    (fun (x : FVar F17) => do let y ← square x; assertEq y (.const 3); pure y)
    2).isOk = false := by
  decide

end Snarky.Example
