import PicklesFixture.ApplicationFromShape
import PicklesFixture.Verdicts

/-!
Reconstruct selected applications from PureScript shape sidecars and compare their complete
step and wrap constraint systems with the independent tag dumps. Run from `formal/` with
`PICKLES_DUMP_DIR=<dir> lake exe check-application-shapes`.
`APPLICATION_SHAPES` selects comma-separated names from the fixture manifest. The default is
the complete manifest, with every listed circuit dump and sidecar required.
-/

open Lean Bulletproof CompElliptic.Fields.Pasta PicklesFixture PicklesFixture.Application

def main : IO Unit := do
  let some dir ← IO.getEnv "PICKLES_DUMP_DIR"
    | throw (IO.userError "PICKLES_DUMP_DIR is not set")
  let apps ← IO.ofExcept (Manifest.select (← IO.getEnv "APPLICATION_SHAPES"))
  Manifest.checkFiles dir apps
  let σW ← srsAt CW "pallas" pallasBase.sqrt? (← IO.mkRef []) 15
  let σS ← srsAt CS "vesta" vestaBase.sqrt? (← IO.mkRef []) 16
  let some wrap := Pickles.Srs.check σW
    | throw (IO.userError "the wrap SRS failed its invariant check")
  let some step := Pickles.Srs.check σS
    | throw (IO.userError "the step SRS failed its invariant check")
  PicklesFixture.Application.checkSelectedFromShape dir apps wrap step
