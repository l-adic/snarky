import Snarky.Kimchi.Backend.Assemble
import Snarky.Kimchi.Backend.Compile
import Snarky.Kimchi.Semantics
import KimchiFixture.PS

/-!
# A main circuit's run, decided

A main circuit runs as its capstone compiles it (`PicklesFixture.runMain`, over
`Snarky.compileWith`), and its run decides the capstone's own hypothesis: the prover's
valuation satisfies every compiled constraint (`Snarky.Kimchi.KimchiConstraint.Holds`). The
capstones state that system at the soundness tag `Builder V`, which is the same system.

The run also judges the table: the compiled constraint list reduced to kimchi gates
(`reduceBuilt`, `gateDataOf`, `reduceSolved`), the gates dispatched to rows and assembled with
their wiring, the prover's table rendered as the witness matrix, and the whole ingested by
`Kimchi.Fixture.PS.build` so that `Index.Satisfies` can be *decided* on it. The checker is the
`Decidable` instance of the verified predicate itself, not a second implementation of it.

`PicklesFixture.runPool` runs a driver's jobs on worker threads, printing their output in order.
-/

namespace PicklesFixture

open Snarky Snarky.Kimchi Kimchi Kimchi.Index Kimchi.Fixture.PS

/-- An assembled circuit in the fixture's `Raw` shape (witness transposed to the
column-major recording). -/
def assembledRaw {F : Type} [Zero F] (rows : List (KimchiRow F))
    (gates : List (AssembledGate F)) (pubSize : Nat) (wit : List (Vector F 15))
    (pubs : List F) : Raw F :=
  { publicInputSize := pubSize
    typs := (gates.map (·.kind)).toArray
    coeffs := (gates.map (·.coeffs.toArray)).toArray
    wires := (gates.map fun g =>
      (g.wires.toList.map fun w => (w.col, w.row)).toArray).toArray
    vars := (rows.map fun r => r.vars.toList.toArray).toArray
    witness := ((List.range 15).map fun j =>
      (wit.map fun row => row.toList.getD j 0).toArray).toArray
    pub := pubs.toArray }

/-- One run of a main circuit as its capstone compiles it: `body` at the soundness tag of the
prover's valuation `V` (`Snarky.compileWith`), proved on its input. The run's facts are stated of
that compiled circuit, in the capstone's own terms. -/
structure MainRun {p : ℕ} [Fact p.Prime] {a av b bv α : Type} [CircuitType (ZMod p) a av]
    [∀ V : Valuation (ZMod p), CheckedType (ZMod p) (Builder V (KimchiConstraint (ZMod p))) a av]
    [CircuitType (ZMod p) b bv]
    (body : (V : Valuation (ZMod p)) → av →
      CircuitM (ZMod p) (Builder V (KimchiConstraint (ZMod p))) (bv × α)) where
  /-- The prover's valuation. -/
  V : Valuation (ZMod p)
  /-- Whether `V` satisfies every compiled constraint: the capstone's hypothesis, decided. -/
  holds : Decidable (∀ con ∈ (compileWith (a := a) (b := b) (body V)).constraints,
    ConstraintHolds.Holds V con)
  /-- Whether the run's table satisfies the assembled system. -/
  satisfies : Bool
  /-- The table's public input: the input's cells, then the output's. -/
  pub : List (ZMod p)
  /-- The run's output and cells, and its public output. -/
  result : (bv × α) × bv
  /-- They are the compiled circuit's. -/
  result_eq : result = (compileWith (a := a) (b := b) (body V)).result

/-- A main circuit `body` proved on `inp`, then compiled with its cells (`Snarky.compileWith`) at
the prover's valuation: whether that valuation satisfies every compiled constraint, and whether
the table, its public rows the input's then the output's cells, satisfies the assembled system.
The prover never reads the tag's valuation, so it runs at a placeholder. The compiled circuit is
returned beside the run, for a caller that reads its constraints or allocation count. -/
def runMainBuilt {p : ℕ} [Fact p.Prime] {a av b bv α : Type} [A : CircuitType (ZMod p) a av]
    [∀ V : Valuation (ZMod p), CheckedType (ZMod p) (Builder V (KimchiConstraint (ZMod p))) a av]
    [CircuitType (ZMod p) b bv]
    (side : Kimchi.Fixture.PS.Side p)
    (body : (V : Valuation (ZMod p)) → av →
      CircuitM (ZMod p) (Builder V (KimchiConstraint (ZMod p))) (bv × α)) (inp : a) :
    IO ((r : MainRun (a := a) (b := b) body) ×
      {built // built = compileWith (a := a) (b := b) (body r.V)}) := do
  let t0 ← IO.monoMsNow
  let st := seed (F := ZMod p) (avar := av) inp
  let pr ← match prove (compileWithBody (a := a) (b := b) (body fun _ => 0)) st.nv st.env with
    | .error e => throw (IO.userError s!"prove failed: {repr e}") | .ok pr => pure pr
  let t1 ← IO.monoMsNow
  let V := pr.assignments.get
  let built := compileWith (a := a) (b := b) (body V)
  let ncons ← IO.lazyPure fun _ => built.constraints.length
  let t2 ← IO.monoMsNow
  let holds : Decidable (∀ con ∈ built.constraints, ConstraintHolds.Holds V con) ←
    IO.lazyPure fun _ =>
      inferInstanceAs (Decidable (∀ con ∈ built.constraints, KimchiConstraint.Holds V con))
  let t3 ← IO.monoMsNow
  let pubVars := compiledPublicVars (F := ZMod p) (a := a) (b := b) built
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
  IO.println s!"    phases: prove {t1 - t0} ms · build {t2 - t1} ms ({ncons} constraints, \
    {built.nextVar} vars) · holds {t3 - t2} ms · rows {t4 - t3} ms ({nrows} rows) · witness \
    {t5 - t4} ms ({nwit} rows) · index build {t6 - t5} ms (n = {n}) · decide {t7 - t6} ms"
  return ⟨{ V, holds, satisfies, pub, result := built.result, result_eq := rfl }, built, rfl⟩

/-- `runMainBuilt`'s run alone. -/
def runMain {p : ℕ} [Fact p.Prime] {a av b bv α : Type} [CircuitType (ZMod p) a av]
    [∀ V : Valuation (ZMod p), CheckedType (ZMod p) (Builder V (KimchiConstraint (ZMod p))) a av]
    [CircuitType (ZMod p) b bv]
    (side : Kimchi.Fixture.PS.Side p)
    (body : (V : Valuation (ZMod p)) → av →
      CircuitM (ZMod p) (Builder V (KimchiConstraint (ZMod p))) (bv × α)) (inp : a) :
    IO (MainRun (a := a) (b := b) body) :=
  (·.1) <$> runMainBuilt side body inp

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
