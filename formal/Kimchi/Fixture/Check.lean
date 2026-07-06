import Kimchi.Fixture.Parse

/-!
# The trace-vector check harness

The shared driver of the op-trace vector checks (`scripts/check_sponge_vectors.lean`,
`scripts/check_fq_sponge.lean`, and the trace checks to come): a vector file is an object
with a `cases` array, each case an `ops` array; a check supplies the op decoder, an initial
state, and a step function returning the next state and that op's verdict.
-/

namespace Kimchi.Fixture

open Lean

/-- Run one trace: thread the state through `step`, conjoining each op's verdict. -/
def runTrace {σ Op : Type} (init : σ) (step : σ → Op → σ × Bool) (ops : Array Op) : Bool :=
  (ops.foldl
    (fun acc op =>
      let (s, ok) := step acc.1 op
      (s, acc.2 && ok))
    (init, true)).2

/-- Check a vector file of `cases` × `ops`: decode each op with `parseOp`, run each case
from `init` by `step`, tally and report. -/
def checkCases {σ Op : Type} (parseOp : Json → Except String Op) (init : σ)
    (step : σ → Op → σ × Bool) (path : String) : IO Bool := do
  let raw ← IO.FS.readFile path
  let cases ← match Json.parse raw >>= fun j => do
      (← (← j.getObjVal? "cases").getArr?).mapM fun c => do
        (← (← c.getObjVal? "ops").getArr?).mapM parseOp with
    | .ok cs => pure cs
    | .error e => throw (IO.userError s!"{path}: vector parse error: {e}")
  let failed := cases.foldl (fun n c => if runTrace init step c then n else n + 1) 0
  IO.println s!"{path}: {cases.size - failed}/{cases.size} OK"
  return failed = 0

end Kimchi.Fixture
