import Snarky.Kimchi.Backend
import Snarky.DSL
import Kimchi.Index.Satisfies
import Kimchi.Fixture.PS

/-!
# Compiling a DSL circuit to a wired kimchi index

The wired counterpart of `Snarky.Kimchi.Backend`/`Soundness`. Those bridge to the
*un-wired* Generic gate list (`Gate.Satisfies (List Generic)`), where variable-sharing
holds only by construction. This module compiles a DSL circuit all the way to a
**wired `Kimchi.Index Fp n`**, where sharing is enforced as **copy constraints** through
the permutation — the object `Kimchi.Index.Satisfies` (and the verifier-soundness thesis,
`Kimchi.Verifier.kimchiVesta_sound`) consumes.

## The compilation

One `GateConstraint` → one Generic row: its coefficients into the row's `q₀…q₄`
(`coeffsAt`), its operand values into witness cells `w₀ w₁ w₂` (`tabOf`). The **wiring**
is read off variable occurrences: the cells holding a variable form its copy cycle
(`cellsOf`, row-major), each cell pointing to the next (`nextIn`, kimchi's
cyclic-successor encoding); cells holding constants, non-operand columns, and padding
rows self-loop (`wireOf`). Domain synthesis follows `Kimchi.Fixture.PS.build` (rows pad
to the smallest two-power holding the gates plus the zero-knowledge rows,
`ω = g^((p−1)/n)`, generator-power coset shifts), and `Index.build?` *decides* every
wellformedness law on the result — a wrong construction is a loud `.error`, never a
trusted fact.

Unlike the fixture path (which decodes JSON through `PS.Raw`), the gate table is built
directly as named functions of the constraint list — `gateTableOf`, `tabOf`, `wireOf` —
and `Index.build?` stores `gates` verbatim, so `Snarky.Kimchi.CompileSound` can reason
about the compiled index's rows and wiring definitionally.

Scope of this first cut: `publicCount = 0` (the DSL has no public-input notion yet). The
end-to-end `#eval` below is validated by `scripts/check_snarky_index.sh`; the general
`Satisfies`-of-an-honest-run theorem is `Snarky.Kimchi.satisfies_of_compile`.
-/

namespace Snarky.Kimchi.Compile

open Snarky Snarky.Kimchi Kimchi.Index CompElliptic.Fields.Pasta

/-! ## Cells: operands, variables, wiring -/

/-- The operand expression a constraint places in witness cell `k`, if any: cells `0 1 2`
hold `a b o`; the remaining cells hold nothing. Shared by the witness table (`Fin 15`
cells) and the wiring (`Fin 7` cells) through the raw `ℕ` index. -/
def operandAt (con : GateConstraint Fp) : ℕ → Option (CVar Fp)
  | 0 => some con.a
  | 1 => some con.b
  | 2 => some con.o
  | _ => none

/-- The bare variable of a `CVar`, if it is one. -/
def varOf? : CVar Fp → Option Variable
  | .var v => some v
  | _ => none

/-- The DSL variable a wiring cell holds: the bare-variable operand at column `c.1` of
constraint row `c.2`, if any. -/
def cellVar (cons : List (GateConstraint Fp)) {n : ℕ} (c : Fin 7 × Fin n) :
    Option Variable :=
  (cons[(c.2 : ℕ)]?.bind fun con => operandAt con (c.1 : ℕ)).bind varOf?

/-- Every wiring cell, row-major — the enumeration fixing the copy-cycle order. -/
def allCells (n : ℕ) : List (Fin 7 × Fin n) :=
  (List.finRange n).flatMap fun i => (List.finRange 7).map fun col => (col, i)

/-- The copy cycle of variable `v`: every cell holding `v`, row-major. -/
def cellsOf (cons : List (GateConstraint Fp)) (n : ℕ) (v : Variable) :
    List (Fin 7 × Fin n) :=
  (allCells n).filter fun c => cellVar cons c = some v

/-- The cyclic successor in a list: the element after `c`, wrapping around; `c` itself
when absent. -/
def nextIn [BEq β] (l : List β) (c : β) : β :=
  l.getD ((l.idxOf c + 1) % l.length) c

/-- The wiring successor of a cell: the next cell of its variable's copy cycle; the cell
itself for constants, non-operand columns, and padding rows. -/
def wireOf (cons : List (GateConstraint Fp)) {n : ℕ} (c : Fin 7 × Fin n) : Fin 7 × Fin n :=
  match cellVar cons c with
  | some v => nextIn (cellsOf cons n v) c
  | none => c

/-! ## The gate table and the witness table -/

/-- The coefficient cells of a row: the constraint's `q₀…q₄` over zeros; all-zero for
padding rows. -/
def coeffsAt (con? : Option (GateConstraint Fp)) : Fin 15 → Fp := fun cell =>
  match con? with
  | none => 0
  | some con =>
    match (cell : ℕ) with
    | 0 => con.q0
    | 1 => con.q1
    | 2 => con.q2
    | 3 => con.q3
    | 4 => con.q4
    | _ => 0

/-- The gate table at domain size `n`: one generic row per constraint, then
constraint-free `zero` rows, all wired by `wireOf` (padding cells hold no variable, so
they self-loop). -/
def gateTableOf (cons : List (GateConstraint Fp)) (n : ℕ) : Fin n → GateRow Fp n :=
  fun i =>
    { typ := if (i : ℕ) < cons.length then .generic else .zero
      coeffs := coeffsAt cons[(i : ℕ)]?
      wires := fun col => wireOf cons (col, i) }

/-- Evaluate an optional operand, `0` for missing or unassigned — an honest prover run
assigns every operand (`GateConstraint.holds` forces evaluation), so the default is never
read on a successful run. -/
def evalD (env : Assignments Fp) : Option (CVar Fp) → Fp
  | some x =>
    match x.eval env with
    | .ok val => val
    | .error _ => 0
  | none => 0

/-- The witness table: operand values in cells `0 1 2` of each constraint row, zeros
everywhere else. -/
def tabOf (cons : List (GateConstraint Fp)) (env : Assignments Fp) (n : ℕ) :
    Fin n → Fin 15 → Fp :=
  fun i cell => evalD env (cons[(i : ℕ)]?.bind fun con => operandAt con (cell : ℕ))

/-! ## Domain synthesis and the compiler -/

/-- The padded domain size: the smallest two-power holding the constraint rows plus the
zero-knowledge rows (as `Kimchi.Fixture.PS.build`). -/
def paddedSize (rows : ℕ) : ℕ :=
  2 ^ Nat.clog 2 (rows + Kimchi.Fixture.PS.zkRows)

/-- The domain generator `ω = g^((p−1)/n)` over the Pallas base field. -/
def domainOmega (n : ℕ) : Fp :=
  (Kimchi.Fixture.PS.powMod Kimchi.Fixture.PS.fpGenerator
    ((PALLAS_BASE_CARD - 1) / n) PALLAS_BASE_CARD : ℕ)

/-- Generator-power coset shifts (as `Kimchi.Fixture.PS.build`). -/
def domainShifts : Fin 7 → Fp := fun i =>
  (Kimchi.Fixture.PS.powMod Kimchi.Fixture.PS.fpGenerator (i : ℕ) PALLAS_BASE_CARD : ℕ)

/-- A compiled circuit: the wired index and the honest prover's witness table. -/
structure Compiled where
  n : ℕ
  nz : NeZero n
  idx : Index Fp n
  tab : Fin n → Fin 15 → Fp

/-- Compile a DSL circuit to a wired index: run the prover for the assignment, build the
gate table and wiring, and let `Index.build?` decide every wellformedness law. `.error`
if the prover fails or a law is rejected. -/
def compile {α : Type} (m : CircuitM Fp (GateConstraint Fp) α) : Except String Compiled :=
  match prove GateConstraint.holds m 0 Assignments.empty with
  | .error _ => .error "compile: the prover failed"
  | .ok ⟨_, _, env⟩ =>
    match Index.build? (gateTableOf (constraints m) (paddedSize (constraints m).length)) 0
        Kimchi.Fixture.PS.zkRows (domainOmega (paddedSize (constraints m).length))
        Kimchi.Pasta.pallas_endo domainShifts with
    | none => .error "compile: Index.build? rejected the construction"
    | some idx =>
      .ok ⟨paddedSize (constraints m).length, ⟨(Nat.two_pow_pos _).ne'⟩, idx,
        tabOf (constraints m) env (paddedSize (constraints m).length)⟩

/-! ## End-to-end example (validated by `scripts/check_snarky_index.sh`) -/

/-- Witness `x = 3`, `y = 5`, `z = x·y`, assert `z = 15` — over `Fp`, the field the index
lives in. -/
def mulCircuit : CircuitM Fp (GateConstraint Fp) (FVar Fp) := do
  let x ← witness (val := Fp) (pure 3)
  let y ← witness (val := Fp) (pure 5)
  let z ← mul x y
  assertEq z (.const 15)
  pure z

/-- `true`: the circuit compiles to a wired index whose stored witness satisfies it —
copy constraints and all. -/
def check : Bool :=
  match compile mulCircuit with
  | .error _ => false
  | .ok out =>
    haveI : NeZero out.n := out.nz
    decide (Satisfies out.idx (fun _ => 0) out.tab)

#eval check  -- expected: true

end Snarky.Kimchi.Compile
