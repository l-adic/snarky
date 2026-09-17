import Snarky.Kimchi.Backend.Assemble
import KimchiFixture.PS

/-!
# From a built circuit to a decided satisfiability

The drivers that judge a circuit's table — the dump comparison and the satisfiability
check — share one path: the compiled constraint list reduced to kimchi gates, the gates
dispatched to rows and assembled with their wiring, the prover's table rendered as the
witness matrix, and the whole thing ingested by `Kimchi.Fixture.PS.build` so that
`Index.Satisfies` can be *decided* on it. The last step is the point: the checker is the
`Decidable` instance of the verified predicate itself, not a second implementation of it.

The reduction and the assembly are `Snarky.Kimchi.Backend.Compile`'s (`reduceBuilt`,
`gateDataOf`, `reduceSolved`), at the `Built` level so that a driver which keeps the
circuit's output as data — `FopOutput`'s bits, off a `build`/`prove` pair — runs the same
code as `kimchiGateData`/`kimchiSolve` do over `compile`.
-/

namespace PicklesFixture

open Snarky Snarky.Kimchi Kimchi Kimchi.Index Kimchi.Fixture.PS

/-- The emitter tag as the index model's gate type. -/
def kindType : GateKind → GateType
  | .genericPlonk => .generic
  | .addComplete => .completeAdd
  | .poseidon => .poseidon
  | .varBaseMul => .varBaseMul
  | .endoMul => .endoMul
  | .endoScalar => .endoScalar
  | .zero => .zero

/-- An assembled circuit in the fixture's `Raw` shape (witness transposed to the
column-major recording). -/
def assembledRaw {F : Type} [Zero F] (rows : List (KimchiRow F))
    (gates : List (AssembledGate F)) (pubSize : Nat) (wit : List (Vector F 15))
    (pubs : List F) : Raw F :=
  { publicInputSize := pubSize
    typs := (gates.map (kindType ·.kind)).toArray
    coeffs := (gates.map (·.coeffs.toArray)).toArray
    wires := (gates.map fun g =>
      (g.wires.toList.map fun w => (w.col, w.row)).toArray).toArray
    vars := (rows.map fun r => r.vars.toList.toArray).toArray
    witness := ((List.range 15).map fun j =>
      (wit.map fun row => row.toList.getD j 0).toArray).toArray
    pub := pubs.toArray }

/-- The round-trip law, decided per circuit: the assembled output padded into the index
model builds by decision (`Index.build?` — domain shape, wiring bijectivity, public-row
form) and the witness satisfies the verified checker. -/
def indexRoundTrip {p : ℕ} [Fact p.Prime] (side : Side p)
    (rows : List (KimchiRow (ZMod p))) (gates : List (AssembledGate (ZMod p)))
    (pubSize : Nat) (wit : List (Vector (ZMod p) 15)) (pubs : List (ZMod p)) : Bool :=
  match build side (assembledRaw rows gates pubSize wit pubs) with
  | .error _ => false
  | .ok inst =>
    haveI : NeZero inst.n := inst.nz
    decide (Satisfies inst.idx inst.wit.pub inst.wit.tab)

end PicklesFixture
