import PicklesFixture.ApplicationFromShape
import PicklesFixture.ImportedIndices
import PicklesFixture.Verdicts

/-!
Certify the applications an explicit selection names: reconstruct each from its sidecar, the
SRSs and the Lagrange memo, compile its circuits once, check them at their keys' index data,
import its indices from the independent circuit dumps and certify them against the checked
application. Every application is reported, a failure located at its stage and circuit, and an
application importing a failed producer is blocked by that failure; the exit status is nonzero
if any failed. An application's missing or malformed files fail that application alone; the
selection and the shared SRSs are fatal. Run from `formal/` with `PICKLES_DUMP_DIR` set and
`APPS` naming manifest applications; the selection is never `all`. No proof cache is read.
-/

open Lean Snarky Pickles Pickles.Application PicklesFixture PicklesFixture.Application
open Bulletproof CompElliptic.Fields.Pasta Kimchi.Fixture Kimchi.Fixture.PS

def main : IO Unit := do
  let some dir ← IO.getEnv "PICKLES_DUMP_DIR"
    | throw (IO.userError "PICKLES_DUMP_DIR is not set")
  let some selection ← IO.getEnv "APPS"
    | throw (IO.userError "APPS is not set: name the manifest applications to certify")
  if selection = "all" then
    throw (IO.userError "APPS names applications explicitly; `all` is not a selection")
  let apps ← IO.ofExcept (Manifest.select (some selection))
  let σW ← srsAt CW "pallas" pallasBase.sqrt? (← IO.mkRef []) WrapIPARounds
  let σS ← srsAt CS "vesta" vestaBase.sqrt? (← IO.mkRef []) StepIPARounds
  let some wrap := Srs.check σW | throw (IO.userError "invalid wrap SRS")
  let some step := Srs.check σS | throw (IO.userError "invalid step SRS")
  reconstructApplications dir apps wrap step fun results => do
    let mut failed : List String := []
    for (name, r) in results do
      match r with
      | .error e =>
        IO.println s!"✗ {name}: {e}"
        failed := failed ++ [name]
      | .ok A =>
        let certify : IO (Certification A) := do
          let text ← try IO.FS.readFile (dir / s!"{name}.json")
            catch e => throw (IO.userError s!"{name}: dump: {e}")
          let tag ← match Json.parse text with
            | .error e => throw (IO.userError s!"{name}: dump: {e}")
            | .ok tag => pure tag
          certifyApplication name A tag
        match ← certify.toBaseIO with
        | .ok _ => IO.println s!"✓ {name}: certified"
        | .error e =>
          IO.println s!"✗ {e}"
          failed := failed ++ [name]
      (← IO.getStdout).flush
    if failed.isEmpty then
      IO.println s!"✓ {results.length} application(s) certified"
    else
      IO.println s!"✗ {failed.length} of {results.length} application(s) failed: \
        {", ".intercalate failed}"
      IO.Process.exit 1
