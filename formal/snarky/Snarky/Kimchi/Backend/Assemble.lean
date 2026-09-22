import Std.Data.HashMap
import Snarky.Kimchi.Constraint

/-!
# The constraint-system assembly

Transcribes the pure fragment of packages/snarky-kimchi/src/Snarky/Backend/Kimchi.purs:
the built rows and the union-find become the gate table the circuit-diffs fixtures
record. Public-input rows are prepended, each variable class is wired as a cycle over its
cells, and the witness table is read off the assignments. The handoff to the native
constraint-system builder is out of scope.

Departures from the transcribed file:
- `Wire` is a plain `(row, col)` record; a cell outside every wired class targets itself.
- `makeWitness` returns the row-major register table; the fixture schema records its
  transpose. A missing assignment reads `0` where the original throws.

scripts/check_cs.lean runs this module's output through `Kimchi.Index.build?` and compares
it with the fixtures.
-/

namespace Snarky.Kimchi

open Snarky

/-- A wiring target: the cell `(row, col)` a permutation cell is wired to. -/
structure Wire where
  /-- The target row. -/
  row : Nat
  /-- The target column. -/
  col : Nat

/-- One assembled gate row, as the fixtures record it: the tag, the wiring targets, and
the coefficients. -/
structure AssembledGate (F : Type u) where
  /-- The gate tag. -/
  kind : GateKind
  /-- The wiring target of each permutation cell. -/
  wires : Vector Wire 7
  /-- The coefficient row. -/
  coeffs : List F

/-- The wire map: each wired permutation cell `(row, col)` goes to the next cell of its
variable's class, the last wrapping to the first. Cells are collected in row-major
order, which is already ascending, so no class needs a sort. -/
def wireMap (roots : Array Variable) (rows : List (KimchiRow F)) :
    Std.HashMap (Nat × Nat) Wire := Id.run do
  let mut classes : Std.HashMap Variable (Array (Nat × Nat)) := {}
  let mut i := 0
  for row in rows do
    let mut j := 0
    for mv in row.vars.toList.take 7 do
      if let some v := mv then
        classes := classes.alter (roots.getD v v) fun
          | none => some #[(i, j)]
          | some cs => some (cs.push (i, j))
      j := j + 1
    i := i + 1
  let mut m : Std.HashMap (Nat × Nat) Wire := {}
  for (_, cells) in classes do
    for k in [0:cells.size] do
      let t := cells[(k + 1) % cells.size]!
      m := m.insert cells[k]! ⟨t.1, t.2⟩
  return m

/-- The gate table: per row the tag, each permutation cell's wiring target (itself when
outside every class), and the coefficients. -/
def assembleGates (roots : Array Variable) (rows : List (KimchiRow F)) :
    List (AssembledGate F) :=
  let wm := wireMap roots rows
  let target (i j : Nat) : Wire := wm.getD (i, j) ⟨i, j⟩
  rows.zipIdx.map fun (row, i) =>
    { kind := row.kind,
      wires := ⟨⟨[target i 0, target i 1, target i 2, target i 3, target i 4, target i 5,
                  target i 6]⟩, by simp⟩,
      coeffs := row.coeffs }

/-- The public-input rows: one generic row per public variable, coefficient `1` on its
first cell. -/
def makePublicInputRows [Zero F] [One F] (publicInputs : List Variable) :
    List (KimchiRow F) :=
  publicInputs.map fun v =>
    { kind := .genericPlonk,
      vars := ⟨⟨[some v, none, none, none, none, none, none, none, none, none,
                 none, none, none, none, none]⟩, by simp⟩,
      coeffs := [1, 0, 0, 0, 0] }

/-- The assembled circuit data: the rows with public-input rows prepended, their gate
table wired through the union-find's roots, and the public-input count. -/
def makeGateData [Zero F] [One F] (publicInputs : List Variable)
    (constraints : List (KimchiRow F)) (uf : UnionFind) :
    List (KimchiRow F) × List (AssembledGate F) × Nat :=
  let rows := makePublicInputRows publicInputs ++ constraints
  let gates := assembleGates (UnionFind.rootOf uf) rows
  (rows, gates, publicInputs.length)

/-- The witness table, row-major: each row's register values, and the public-input
values. An absent or unassigned cell reads `0`. No stated law makes the built rows'
cells assigned, so a `0` may hide an unassigned cell; the fixture witness comparison is
the only check. -/
def makeWitness [Zero F] (A : Assignments F) (rows : List (KimchiRow F))
    (publicInputs : List Variable) : List (Vector F 15) × List F :=
  (rows.map fun row =>
    ⟨⟨(row.vars.toList.map fun mv => ((mv.bind A).getD 0))⟩, by simp⟩,
   publicInputs.map fun v => (A v).getD 0)

end Snarky.Kimchi
