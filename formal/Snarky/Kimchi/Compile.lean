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

Kimchi's generic gate is *double*: one physical row packs two constraint slots
(`q₀…q₄` on cells `w₀w₁w₂` and `q₅…q₉` on `w₃w₄w₅`). So the constraint stream is first
**packed** two-per-row (`pack`, the analogue of the PS reduction's pairing of pending
generic constraints) and each `RowSlots` pair becomes one Generic row: the constraints'
coefficients into the row's `q₀…q₉` (`coeffsAt`), their operand values into witness
cells `w₀…w₅` (`tabOf`, through `slotOperand`). The **wiring** is read off variable
occurrences: the cells holding a variable form its copy cycle (`cellsOf`, row-major),
each cell pointing to the next (`nextIn`, kimchi's cyclic-successor encoding); cells
holding constants, non-operand columns, and padding rows self-loop (`wireOf` — all six
operand cells sit within the seven permutable columns, so slot-2 operands wire like
slot-1's). Domain synthesis follows `Kimchi.Fixture.PS.build` (rows pad to the smallest
two-power holding the gates plus the zero-knowledge rows, `ω = g^((p−1)/n)`,
generator-power coset shifts), and `Index.build?` *decides* every wellformedness law on
the result — a wrong construction is a loud `.error`, never a trusted fact.

Unlike the fixture path (which decodes JSON through `PS.Raw`), the gate table is built
directly as named functions of the packed stream — `gateTableOf`, `tabOf`, `wireOf` —
and `Index.build?` stores `gates` verbatim, so `Snarky.Kimchi.CompileSound` can reason
about the compiled index's rows and wiring definitionally.

Scope of this first cut: `publicCount = 0` (the DSL has no public-input notion yet). The
end-to-end `#eval` below is validated by `scripts/check_snarky_index.sh`; the general
`Satisfies`-of-an-honest-run theorem is `Snarky.Kimchi.Compile.satisfies_of_compile`.
-/

namespace Snarky.Kimchi.Compile

open Snarky Snarky.Kimchi Kimchi.Index CompElliptic.Fields.Pasta

/-! ## Packing: two constraints per physical row -/

/-- One physical row's constraints: the slot-1 constraint and, when the stream had
another pending, the slot-2 constraint (kimchi's double generic gate). -/
abbrev RowSlots := GateConstraint Fp × Option (GateConstraint Fp)

/-- Pack the constraint stream two-per-row — the analogue of the PS reduction's pairing
of pending generic constraints. -/
def pack : List (GateConstraint Fp) → List RowSlots
  | c1 :: c2 :: rest => (c1, some c2) :: pack rest
  | [c] => [(c, none)]
  | [] => []

/-! ## Cells: operands, variables, wiring -/

/-- The operand expression a packed row places in witness cell `k`, if any: cells `0 1 2`
hold slot 1's `a b o`, cells `3 4 5` hold slot 2's; the remaining cells hold nothing.
Shared by the witness table (`Fin 15` cells) and the wiring (`Fin 7` cells) through the
raw `ℕ` index. -/
def slotOperand (p : RowSlots) : ℕ → Option (CVar Fp)
  | 0 => some p.1.a
  | 1 => some p.1.b
  | 2 => some p.1.o
  | 3 => p.2.map (·.a)
  | 4 => p.2.map (·.b)
  | 5 => p.2.map (·.o)
  | _ => none

/-- The bare variable of a `CVar`, if it is one. -/
def varOf? : CVar Fp → Option Variable
  | .var v => some v
  | _ => none

/-- The DSL variable a wiring cell holds: the bare-variable operand at column `c.1` of
packed row `c.2`, if any. -/
def cellVar (rows : List RowSlots) {n : ℕ} (c : Fin 7 × Fin n) : Option Variable :=
  (rows[(c.2 : ℕ)]?.bind fun p => slotOperand p (c.1 : ℕ)).bind varOf?

/-- Every wiring cell, row-major — the enumeration fixing the copy-cycle order. -/
def allCells (n : ℕ) : List (Fin 7 × Fin n) :=
  (List.finRange n).flatMap fun i => (List.finRange 7).map fun col => (col, i)

/-- The copy cycle of variable `v`: every cell holding `v`, row-major. -/
def cellsOf (rows : List RowSlots) (n : ℕ) (v : Variable) : List (Fin 7 × Fin n) :=
  (allCells n).filter fun c => cellVar rows c = some v

/-- The cyclic successor in a list: the element after `c`, wrapping around; `c` itself
when absent. -/
def nextIn [BEq β] (l : List β) (c : β) : β :=
  l.getD ((l.idxOf c + 1) % l.length) c

/-- The wiring successor of a cell: the next cell of its variable's copy cycle; the cell
itself for constants, non-operand columns, and padding rows. -/
def wireOf (rows : List RowSlots) {n : ℕ} (c : Fin 7 × Fin n) : Fin 7 × Fin n :=
  match cellVar rows c with
  | some v => nextIn (cellsOf rows n v) c
  | none => c

/-! ## The gate table and the witness table -/

/-- The coefficient cells of a packed row: slot 1's `q₀…q₄` in cells `0…4`, slot 2's in
cells `5…9`, zeros elsewhere; all-zero for padding rows. -/
def coeffsAt (p? : Option RowSlots) : Fin 15 → Fp := fun cell =>
  match p? with
  | none => 0
  | some p =>
    match (cell : ℕ), p.2 with
    | 0, _ => p.1.q0
    | 1, _ => p.1.q1
    | 2, _ => p.1.q2
    | 3, _ => p.1.q3
    | 4, _ => p.1.q4
    | 5, some c2 => c2.q0
    | 6, some c2 => c2.q1
    | 7, some c2 => c2.q2
    | 8, some c2 => c2.q3
    | 9, some c2 => c2.q4
    | _, _ => 0

/-- The gate table at domain size `n`: one generic row per packed pair, then
constraint-free `zero` rows, all wired by `wireOf` (padding cells hold no variable, so
they self-loop). -/
def gateTableOf (rows : List RowSlots) (n : ℕ) : Fin n → GateRow Fp n :=
  fun i =>
    { typ := if (i : ℕ) < rows.length then .generic else .zero
      coeffs := coeffsAt rows[(i : ℕ)]?
      wires := fun col => wireOf rows (col, i) }

/-- Evaluate an optional operand, `0` for missing or unassigned — an honest prover run
assigns every operand (`GateConstraint.holds` forces evaluation), so the default is never
read on a successful run. -/
def evalD (env : Assignments Fp) : Option (CVar Fp) → Fp
  | some x =>
    match x.eval env with
    | .ok val => val
    | .error _ => 0
  | none => 0

/-- The witness table: operand values in cells `0…5` of each packed row, zeros everywhere
else. -/
def tabOf (rows : List RowSlots) (env : Assignments Fp) (n : ℕ) :
    Fin n → Fin 15 → Fp :=
  fun i cell => evalD env (rows[(i : ℕ)]?.bind fun p => slotOperand p (cell : ℕ))

/-! ## Domain synthesis and the compiler -/

/-- The padded domain size: the smallest two-power holding the packed rows plus the
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

/-- Compile a DSL circuit to a wired index: run the prover for the assignment, pack the
constraint stream, build the gate table and wiring, and let `Index.build?` decide every
wellformedness law. `.error` if the prover fails or a law is rejected. -/
def compile {α : Type} (m : CircuitM Fp (GateConstraint Fp) α) : Except String Compiled :=
  match prove GateConstraint.holds m 0 Assignments.empty with
  | .error _ => .error "compile: the prover failed"
  | .ok ⟨_, _, env⟩ =>
    match Index.build?
        (gateTableOf (pack (constraints m)) (paddedSize (pack (constraints m)).length)) 0
        Kimchi.Fixture.PS.zkRows (domainOmega (paddedSize (pack (constraints m)).length))
        Kimchi.Pasta.pallas_endo domainShifts with
    | none => .error "compile: Index.build? rejected the construction"
    | some idx =>
      .ok ⟨paddedSize (pack (constraints m)).length, ⟨(Nat.two_pow_pos _).ne'⟩, idx,
        tabOf (pack (constraints m)) env (paddedSize (pack (constraints m)).length)⟩

/-! ## End-to-end example (validated by `scripts/check_snarky_index.sh`) -/

/-- Witness `x = 3`, `y = 5`, `z = x·y`, assert `z = 15` — over `Fp`, the field the index
lives in. Its two constraints pack into one physical row, with `z` copy-wired between
slot 1's output cell (`w₂`) and slot 2's left cell (`w₃`). -/
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
