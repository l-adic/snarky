import PicklesFixture.ApplicationFromShape
import PicklesFixture.Verdicts

/-!
Reconstruct selected applications from PureScript shape sidecars and compare their complete
step and wrap constraint systems with the independent tag dumps. Run from `formal/` with
`PICKLES_DUMP_DIR=<dir> lake exe check-application-shapes`.
`APPLICATION_SHAPES` may select a comma-separated subset of TwoPhaseChain,
HeterogeneousPrevs, RecurseOverChunks, and PaddedWideSlots. This check does not run proof links.
-/

open Lean Bulletproof CompElliptic.Fields.Pasta PicklesFixture PicklesFixture.Application

def main : IO Unit := do
  let some dir ← IO.getEnv "PICKLES_DUMP_DIR"
    | throw (IO.userError "PICKLES_DUMP_DIR is not set")
  let apps := ((← IO.getEnv "APPLICATION_SHAPES").getD
    "TwoPhaseChain,HeterogeneousPrevs,RecurseOverChunks,PaddedWideSlots").splitOn ","
  let selected := apps.filter
    (· ∈ ["TwoPhaseChain", "HeterogeneousPrevs", "RecurseOverChunks", "PaddedWideSlots"])
  unless selected.length == apps.length && !selected.isEmpty do
    throw (IO.userError "APPLICATION_SHAPES contains an unknown or no application")
  let σW ← srsAt CW "pallas" pallasBase.sqrt? (← IO.mkRef []) 15
  let σS ← srsAt CS "vesta" vestaBase.sqrt? (← IO.mkRef []) 16
  let some wrap := Pickles.Srs.check σW
    | throw (IO.userError "the wrap SRS failed its invariant check")
  let some step := Pickles.Srs.check σS
    | throw (IO.userError "the step SRS failed its invariant check")
  PicklesFixture.Application.checkSelectedFromShape dir selected wrap step
