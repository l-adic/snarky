import Std.Data.HashMap
import Snarky.Kimchi.Constraint

/-!
# The constraint-system assembly

Port of the pure fragment of `Snarky.Backend.Kimchi`
(packages/snarky-kimchi/src/Snarky/Backend/Kimchi.purs): rows plus the wire state
become the gate table the fixtures record — public-input rows prepended, the
union-find partition laid out as cyclic wiring, coefficients carried per row, and the
witness table read off the assignments. The napi handoff
(`makeConstraintSystemWithPrevChallenges`'s carried `prevChallengesCount`/
`maxPolySize`, the `Gate`/`Wire` FFI constructors) is out (K1); the assembled shape
here is the circuit-diffs JSON schema `KimchiFixture.PS.Raw` decodes — the D-K3
comparison seam.

Name map: `makePublicInputRows`, `makeGateData`, `makeWitness` keep their names;
`makeWireMapping`/`makeGates` become `wireMap`/`assembleGates` — the PS `ST`-pass builds
placement/class stores imperatively and then SORTS each class's cells; `wireMap`
collects the classes in row-major order, which is that sorted order, and maps each
cell to its cyclic successor.

Deviations from the PS original (per `formal/docs/snarky-kimchi-alignment.md`):
- `Wire` is a plain `(row, col)` record (the PS type is an FFI constructor); a cell
  outside every wired class targets itself, as in PS's `wireNew i j` default.
- Only permutation columns `0 … 6` wire (PS filters `j < 7`); the PS `i * 16 + j`
  frozen-store keying is an indexing artifact and drops out of the functional form.
- `makeWitness` produces the ROW-major register table (PS builds the transpose,
  `Vector 15 (Array f)` column-major, which is what the fixture schema records —
  the comparison seam transposes); missing assignments read `0` where PS throws
  (total rendering; the prover laws discharge assignedness on the reachable path).

The round-trip check against `Kimchi.Index.build?` and the fixture byte-comparison
live in `formal/scripts/check_cs.lean`; this module is the pure data path it
exercises.
-/

namespace Snarky.Kimchi

open Snarky

/-- A wiring target: the cell `(row, col)` this cell is permuted to (the PS FFI
`Wire`, as data). -/
structure Wire where
  /-- The target row. -/
  row : Nat
  /-- The target column. -/
  col : Nat
  deriving Repr, DecidableEq

/-- One assembled gate row: the tag, the seven wiring targets, and the coefficient
row — the shape the circuit-diffs schema records per row. -/
structure AssembledGate (F : Type u) where
  /-- The gate tag. -/
  kind : GateKind
  /-- The seven permutation-cell wiring targets. -/
  wires : Vector Wire 7
  /-- The coefficient row. -/
  coeffs : List F
  deriving Repr, DecidableEq

/-- The wire map (PS `makeWireMapping`): every wired permutation cell `(row, col)`,
`col < 7`, to the next cell of its variable's class, the last wrapping to the first.
One pass over the rows collects each class's cells; row-major discovery is already the
ascending cell order PS sorts into, so no class needs a sort. -/
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

/-- Assemble the gate table (PS `makeGates`): per row the tag, the seven wiring
targets (a cell outside every class targets itself), and the coefficients. -/
def assembleGates (roots : Array Variable) (rows : List (KimchiRow F)) :
    List (AssembledGate F) :=
  let wm := wireMap roots rows
  let target (i j : Nat) : Wire := wm.getD (i, j) ⟨i, j⟩
  rows.zipIdx.map fun (row, i) =>
    { kind := row.kind,
      wires := ⟨⟨[target i 0, target i 1, target i 2, target i 3, target i 4, target i 5,
                  target i 6]⟩, by simp⟩,
      coeffs := row.coeffs }

/-- The public-input rows (PS `makePublicInputRows`): one generic row per public
variable, coefficient `1` on the first cell. -/
def makePublicInputRows [Zero F] [One F] (publicInputs : List Variable) :
    List (KimchiRow F) :=
  publicInputs.map fun v =>
    { kind := .genericPlonk,
      vars := ⟨⟨[some v, none, none, none, none, none, none, none, none, none,
                 none, none, none, none, none]⟩, by simp⟩,
      coeffs := [1, 0, 0, 0, 0] }

/-- The assembled circuit data (PS `makeGateData`): public-input rows prepended, the
union-find resolved to roots, the gate table with its wiring. -/
def makeGateData [Zero F] [One F] (publicInputs : List Variable)
    (constraints : List (KimchiRow F)) (uf : UnionFind) :
    List (KimchiRow F) × List (AssembledGate F) × Nat :=
  let rows := makePublicInputRows publicInputs ++ constraints
  let gates := assembleGates (UnionFind.rootOf uf) rows
  (rows, gates, publicInputs.length)

/-- The witness table (PS `makeWitness`), row-major as the fixture schema records
it: each row's fifteen register values and the public-input values. Total where PS
throws on a missing assignment: an absent or unassigned cell reads `0`. No stated
law discharges assignedness of built rows, so a `0` cell can also be an unassigned
one — the corpus's byte comparison is the only check. -/
def makeWitness [Zero F] (A : Assignments F) (rows : List (KimchiRow F))
    (publicInputs : List Variable) : List (Vector F 15) × List F :=
  (rows.map fun row =>
    ⟨⟨(row.vars.toList.map fun mv => ((mv.bind A).getD 0))⟩, by simp⟩,
   publicInputs.map fun v => (A v).getD 0)

end Snarky.Kimchi
