import PicklesFixture.Layout
import Snarky.Kimchi.Backend.Compile
import KimchiFixture.PS

/-!
# From a built circuit to a decided satisfiability

The drivers that judge a circuit's table — the dump comparison and the satisfiability
check — share one path: the compiled constraint list reduced to kimchi gates, the gates
dispatched to rows and assembled with their wiring, the prover's table rendered as the
witness matrix, and the whole thing ingested by `Kimchi.Fixture.PS.build` so that
`Index.Satisfies` can be *decided* on it. The last step is the point: the checker is the
`Decidable` instance of the verified predicate itself, not a second implementation of it.

`kimchiGateData`/`kimchiSolve` (`Snarky.Kimchi.Backend.Compile`) run this over `compile`,
which witnesses the circuit's output into public slots and so needs a `CircuitType` on the
output. The satisfiability driver keeps the output as data — `FopOutput`'s bits — so the
variants here run over a `build`/`prove` pair instead, generic in the result type.
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

/-- A built circuit reduced to kimchi gates, as `kimchiCompile` does after `compile`: the
builder's reduction folded over the constraint list from the build's counter, the odd
queued constraint flushed into one more packed row. -/
def reduceBuilt {F α : Type} [Field F] [DecidableEq F] (built : Built (KimchiConstraint F) α) :
    KimchiBuilt F α :=
  let red := reduceGates built.constraints built.nextVar initialAuxState
  let flush := (finalizeGateQueue red.2.2.queuedGenericGate).map KimchiGate.plonk
  ⟨built.result, red.1 ++ flush.toList, red.2.1, { red.2.2 with queuedGenericGate := none }⟩

/-- The rows and the assembled gate table of a built circuit whose public interface is
its first `pubSize` variables — a `build`-side `kimchiGateData`. -/
def gateDataOf {F α : Type} [Field F] [DecidableEq F] (built : Built (KimchiConstraint F) α)
    (pubSize : ℕ) : List (KimchiRow F) × List (AssembledGate F) × List Variable :=
  let kb := reduceBuilt built
  let rows := kb.gates.flatMap (toKimchiRows (F := F))
  let pubVars := (allocRange 0 pubSize).toList
  let assembled := makeGateData pubVars rows kb.aux.wireState.unionFind
  (assembled.1, assembled.2.1, pubVars)

/-- A proved circuit's table completed by the prover's reduction — the internal
variables the gates introduced, from the build's counter, as `kimchiSolve` does after
`solve`. -/
def reduceProved {F α : Type} [Field F] [DecidableEq F] (built : Built (KimchiConstraint F) α)
    (env : Assignments F) : Except EvalError (Assignments F) :=
  match reduceTable built.constraints ⟨built.nextVar, env⟩ with
  | .error e => .error e
  | .ok s => .ok s.assignments

/-- Whether a built circuit's proved table satisfies its own assembled system, decided:
the rows, gates and public variables of the build, the reduced table's witness matrix,
`Index.Satisfies` on the result. -/
def provedSatisfies {p : ℕ} {α : Type} [Fact p.Prime] (side : Side p)
    (built : Built (KimchiConstraint (ZMod p)) α) (env : Assignments (ZMod p))
    (pubSize : ℕ) : Except EvalError Bool := do
  let (rows, gates, pubVars) := gateDataOf built pubSize
  let env' ← reduceProved built env
  let (wit, pubs) := makeWitness env' rows pubVars
  return indexRoundTrip side rows gates pubSize wit pubs

end PicklesFixture
