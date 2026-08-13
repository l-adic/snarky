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
`makeWireMapping`/`makeGates` collapse into `wireTarget`/`assembleGates` — the PS
`ST`-pass builds placement/class stores imperatively and then SORTS each class's
cells, so the pure rendering computes each cell's successor in its class's sorted
cell list directly (the sort makes the discovery order irrelevant; what survives is
row-major cell order within the sorted class and the cyclic successor).

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
live in `scripts/check_cs_equality.lean`; this module is the pure data path it
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

/-- The permutation cells of the row list: every `(row, col)` with `col < 7` holding
a variable, tagged with that variable's class root — in row-major cell order. -/
def permCells (roots : Array Variable) (rows : List (KimchiRow F)) :
    List ((Nat × Nat) × Nat) :=
  (rows.zipIdx.map fun (row, i) =>
    ((row.vars.toList.take 7).zipIdx.filterMap fun (mv, j) =>
      mv.map fun v => ((i, j), roots.getD v v))).flatten

/-- Insertion into an ascending cell list (structural, kernel-reducible — the PS
`Array.sort` of a class's cells). -/
private def insertCell (c : Nat × Nat) : List (Nat × Nat) → List (Nat × Nat)
  | [] => [c]
  | d :: rest =>
    if c.1 < d.1 ∨ (c.1 = d.1 ∧ c.2 ≤ d.2) then c :: d :: rest
    else d :: insertCell c rest

/-- A class's cells, ascending: every permutation cell whose variable shares the
given root. -/
def classCells (roots : Array Variable) (rows : List (KimchiRow F)) (root : Variable) :
    List (Nat × Nat) :=
  ((permCells roots rows).filterMap fun (c, r) =>
    if r = root then some c else none).foldl (fun acc c => insertCell c acc) []

/-- The cyclic successor of `c` in the ascending cell list (the PS
`zip sorted (rotateLeft sorted)` pairing): the element after `c`, wrapping the last
element around to the threaded head; `c` itself when the list misses it. -/
private def cycleNextFrom (head c : Nat × Nat) : List (Nat × Nat) → Nat × Nat
  | [] => c
  | [d] => if d = c then head else c
  | d :: e :: rest => if d = c then e else cycleNextFrom head c (e :: rest)

/-- The wiring target of cell `(i, j)` (the PS wire map, functionally): the cyclic
successor within its variable's sorted class when the cell is wired, else the cell
itself. -/
def wireTarget (roots : Array Variable) (rows : List (KimchiRow F)) (i j : Nat) : Wire :=
  match (permCells roots rows).lookup (i, j) with
  | none => ⟨i, j⟩
  | some root =>
    match classCells roots rows root with
    | [] => ⟨i, j⟩
    | cells@(head :: _) =>
      let t := cycleNextFrom head (i, j) cells
      ⟨t.1, t.2⟩

/-- Assemble the gate table (PS `makeGates`): per row the tag, the seven wiring
targets, and the coefficients. -/
def assembleGates (roots : Array Variable) (rows : List (KimchiRow F)) :
    List (AssembledGate F) :=
  rows.zipIdx.map fun (row, i) =>
    { kind := row.kind,
      wires := ⟨⟨[wireTarget roots rows i 0, wireTarget roots rows i 1,
                  wireTarget roots rows i 2, wireTarget roots rows i 3,
                  wireTarget roots rows i 4, wireTarget roots rows i 5,
                  wireTarget roots rows i 6]⟩, by simp⟩,
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
