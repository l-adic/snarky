import Snarky.Kimchi.Backend.Assemble
import Snarky.Kimchi.Backend.Compile
import Snarky.Kimchi.Semantics
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
code as `kimchiGateData` does over `compile`.

A main circuit runs as its capstone compiles it (`PicklesFixture.runMain`, over
`Snarky.compileWith`), and its run also decides the capstone's own hypothesis: the prover's
valuation satisfies every compiled constraint (`Snarky.Kimchi.KimchiConstraint.Holds`). The
capstones state that system at the soundness tag `Builder V`, which is the same system.
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

/-- One run of a half on its input: `build` and `prove` the harness on it, read
the named bits off the table, and decide whether the table satisfies the assembled system. -/
def runHalf {p : ℕ} [Fact p.Prime] {a av β : Type} [CircuitType (ZMod p) a av]
    (side : Kimchi.Fixture.PS.Side p)
    (harness : av → CircuitM (ZMod p) (KimchiConstraint (ZMod p)) β)
    (bitsOf : β → List (String × BoolVar (ZMod p))) (inp : a) :
    IO (Bool × List (String × ℕ)) := do
  let nv := CircuitType.size (ZMod p) a
  let m := harness (inputVar (F := ZMod p) (a := a))
  let t0 ← IO.monoMsNow
  let built := build m nv
  let nc := built.constraints.length
  let t1 ← IO.monoMsNow
  let st := seed (F := ZMod p) (avar := av) inp
  match prove m st.nv st.env with
  | .error e => throw (IO.userError s!"prove failed: {repr e}")
  | .ok pr =>
    let t2 ← IO.monoMsNow
    let read (b : BoolVar (ZMod p)) : ℕ := ((b : CVar (ZMod p)).val pr.assignments.get).val
    let bits := (bitsOf pr.result).map fun (n, b) => (n, read b)
    -- `indexRoundTrip` on the proved table, phase by phase
    let (rows, gates, pubVars) := gateDataOf (reduceBuilt built) (allocRange 0 nv).toList
    let nrows := rows.length
    let t3 ← IO.monoMsNow
    let env' ← match reduceSolved built pr.assignments with
      | .error e => throw (IO.userError s!"reduction failed: {repr e}") | .ok e => pure e
    let (wit, pubs) := makeWitness env' rows pubVars
    let nwit := wit.length
    let t4 ← IO.monoMsNow
    let raw := assembledRaw rows gates nv wit pubs
    let sat ← match Kimchi.Fixture.PS.build side raw with
      | .error e => throw (IO.userError s!"index build failed: {e}")
      | .ok inst =>
        let t5 ← IO.monoMsNow
        let sat : Bool :=
          haveI : NeZero inst.n := inst.nz
          decide (Kimchi.Index.Satisfies inst.idx inst.wit.pub inst.wit.tab)
        let t6 ← IO.monoMsNow
        IO.println s!"    phases: build {t1 - t0} ms ({nc} constraints, {built.nextVar} vars) · \
          prove {t2 - t1} ms · rows {t3 - t2} ms ({nrows} rows) · witness {t4 - t3} ms \
          ({nwit} rows) · index build {t5 - t4} ms (n = {inst.n}) · decide {t6 - t5} ms"
        pure sat
    return (sat, bits)

/-- One run of a main circuit as its capstone compiles it (`Snarky.compileWith`), proved on its
input. -/
structure MainRun (F bvar α : Type) where
  /-- The prover's valuation. -/
  V : Valuation F
  /-- Whether `V` satisfies every compiled constraint: the capstone's hypothesis, decided. -/
  holds : Bool
  /-- Whether the run's table satisfies the assembled system. -/
  satisfies : Bool
  /-- The table's public input: the input's cells, then the output's. -/
  pub : List F
  /-- The run's output and cells, and its public output. -/
  result : (bvar × α) × bvar

/-- A main circuit `body` compiled with its cells (`Snarky.compileWith`), proved on `inp`: whether
the prover's valuation satisfies every compiled constraint, and whether the table, its public
rows the input's then the output's cells, satisfies the assembled system. -/
def runMain {p : ℕ} [Fact p.Prime] {a av b bv α : Type} [A : CircuitType (ZMod p) a av]
    [CheckedType (ZMod p) (KimchiConstraint (ZMod p)) a av] [CircuitType (ZMod p) b bv]
    (side : Kimchi.Fixture.PS.Side p)
    (body : av → CircuitM (ZMod p) (KimchiConstraint (ZMod p)) (bv × α)) (inp : a) :
    IO (MainRun (ZMod p) bv α) := do
  let t0 ← IO.monoMsNow
  let built ← IO.lazyPure fun _ => compileWith (a := a) (b := b) body
  let ncons := built.constraints.length
  let t1 ← IO.monoMsNow
  let st := seed (F := ZMod p) (avar := av) inp
  let pr ← match prove (compileWithBody (a := a) (b := b) body) st.nv st.env with
    | .error e => throw (IO.userError s!"prove failed: {repr e}") | .ok pr => pure pr
  let t2 ← IO.monoMsNow
  let V := pr.assignments.get
  let holds ← IO.lazyPure fun _ => decide (∀ con ∈ built.constraints, KimchiConstraint.Holds V con)
  let t3 ← IO.monoMsNow
  let pubVars := (allocRange 0 A.size).toList ++ bundleVars (F := ZMod p) (b := b) built.result.2
  let (rows, gates, _) := gateDataOf (reduceBuilt built) pubVars
  let nrows := rows.length
  let t4 ← IO.monoMsNow
  let env' ← match reduceSolved built pr.assignments with
    | .error e => throw (IO.userError s!"reduction failed: {repr e}") | .ok e => pure e
  let (wit, pub) := makeWitness env' rows pubVars
  let nwit := wit.length
  let t5 ← IO.monoMsNow
  let (satisfies, n, t6) ← match Kimchi.Fixture.PS.build side
      (assembledRaw rows gates pubVars.length wit pub) with
    | .error e => throw (IO.userError s!"index build failed: {e}")
    | .ok inst =>
      let t6 ← IO.monoMsNow
      let sat ← IO.lazyPure fun _ =>
        haveI : NeZero inst.n := inst.nz
        decide (Kimchi.Index.Satisfies inst.idx inst.wit.pub inst.wit.tab)
      pure (sat, inst.n, t6)
  let t7 ← IO.monoMsNow
  IO.println s!"    phases: build {t1 - t0} ms ({ncons} constraints, {built.nextVar} vars) · \
    prove {t2 - t1} ms · holds {t3 - t2} ms · rows {t4 - t3} ms ({nrows} rows) · witness \
    {t5 - t4} ms ({nwit} rows) · index build {t6 - t5} ms (n = {n}) · decide {t7 - t6} ms"
  return { V, holds, satisfies, pub, result := built.result }

/-- `jobs` on `n` workers, each job's output captured on its worker thread (stdout is per
thread) and printed, flushed, in job order as soon as the jobs before it are done; the verdicts,
in order. A worker reports each job it finishes on stderr at once (`· k/N done`), so progress
shows in any order. A job that throws prints its error and fails. -/
def runPool (n : ℕ) (jobs : Array (IO Bool)) : IO (Array Bool) := do
  let work ← jobs.mapM fun job => do
    let p ← IO.Promise.new (α := String × Bool)
    pure (job, p)
  let next ← IO.mkRef 0
  let done ← IO.mkRef 0
  let stdout ← IO.getStdout
  let stderr ← IO.getStderr
  let worker : IO Unit := do
    repeat
      let i ← next.modifyGet fun i => (i, i + 1)
      if h : i < work.size then
        let (job, p) := work[i]
        let r ← IO.FS.withIsolatedStreams do
          try job catch e => do
            IO.println s!"  ✗ {e}"
            pure false
        p.resolve r
        let k ← done.modifyGet fun k => (k + 1, k + 1)
        stderr.putStrLn s!"· {k}/{work.size} done{if r.2 then "" else " ✗"}"
        stderr.flush
      else break
  let tasks ← (List.range (max n 1)).mapM fun _ => IO.asTask worker
  let mut oks := #[]
  for (_, p) in work do
    let (out, ok) ← IO.wait p.result!
    stdout.putStr out
    stdout.flush
    oks := oks.push ok
  for t in tasks do
    if let .error e ← IO.wait t then throw e
  return oks

end PicklesFixture
