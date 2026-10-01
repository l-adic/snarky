import Std.Data.HashMap
import KimchiFixture.PS
import Snarky.Kimchi.Backend.Compile
import PicklesFixture.Satisfies

/-!
# Constraint systems against their dumps

A circuit's assembled constraint system compared with a dumped gate table: gate types,
coefficients, wiring, the public-input size, and the per-cell variable ids up to a global
renaming. The dumps carry no witness; the comparison is on the constraint system alone.

The variable-ids check is compared up to renaming because this backend numbers the
reduction's internal variables above the circuit's rather than interleaved with them, and
witnesses the public outputs rather than preallocating them (`Snarky.Kimchi.kimchiGateData`).
What the renaming-invariant form still pins, and what `wires` does not see, is the per-cell
occupancy pattern and the identification the ids induce across cells.
-/

namespace PicklesFixture

open Snarky Snarky.Kimchi Kimchi Kimchi.Fixture.PS

/-- The per-cell variable ids, compared up to a global renaming: walk both cell
sequences in row-major order building the id map both ways, and require a
well-defined injection. A cell occupied on one side and empty on the other fails
immediately, as does any pair of cells the two sides identify differently. -/
def varsAgreeUpToRenaming {F : Type} (rows : List (KimchiRow F))
    (dumped : Array (Array (Option ℕ))) : Bool := Id.run do
  let lhs := rows.map (·.vars.toList)
  let rhs := dumped.toList.map (·.toList)
  if lhs.length != rhs.length then return false
  let mut fwd : Std.HashMap ℕ ℕ := {}
  let mut bwd : Std.HashMap ℕ ℕ := {}
  for (lrow, rrow) in lhs.zip rhs do
    if lrow.length != rrow.length then return false
    for (l, r) in lrow.zip rrow do
      match l, r with
      | none, none => pure ()
      | some v, some w =>
        match fwd[v]?, bwd[w]? with
        | none, none =>
          fwd := fwd.insert v w
          bwd := bwd.insert w v
        | some w', some v' => if w' != w || v' != v then return false
        | _, _ => return false
      | _, _ => return false
  return true

/-- Compare one circuit's assembled system against its dump: types, coefficients, wires,
public size and the variable ids up to renaming. -/
def compareWith {p : ℕ} [Fact p.Prime]
    {a b avar bvar : Type} [CircuitType (ZMod p) a avar]
    [CheckedType (ZMod p) (KimchiConstraint (ZMod p)) a avar] [CircuitType (ZMod p) b bvar]
    (main : avar → CircuitM (ZMod p) (KimchiConstraint (ZMod p)) bvar) (raw : Raw (ZMod p)) :
    List (String × Bool) :=
  let (rows, gates, pubVars) := kimchiGateData (a := a) (b := b) main
  [ ("publicInputSize", pubVars.length == raw.publicInputSize),
    ("gate count", gates.length == raw.typs.size),
    ("gate types", (gates.map (kindType ·.kind)).toArray == raw.typs),
    ("coefficients", (gates.map (·.coeffs.toArray)).toArray == raw.coeffs),
    ("wires",
      (gates.map fun g =>
        (g.wires.toList.map fun w => (w.col, w.row)).toArray).toArray
        == raw.wires),
    ("gate count matches wires", gates.length == raw.wires.size),
    ("variables (up to renaming)", varsAgreeUpToRenaming rows raw.vars) ]

end PicklesFixture
