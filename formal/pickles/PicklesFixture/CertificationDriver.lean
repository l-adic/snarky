import PicklesFixture.ApplicationFromShape
import PicklesFixture.ImportedIndices
import PicklesFixture.Verdicts

/-!
# Manifest certification driver

Reconstruct the selected applications and certify their independent indices and every supplied
step and wrap key against their reconstructed circuits and shared SRSs. Each entry is reported;
a dependent of a producer whose certification failed is blocked. No proof cache is read.
The selection and shared SRSs are fatal; an entry's own failures remain located at that entry.
-/

open Lean Snarky Pickles Pickles.Application PicklesFixture PicklesFixture.Application
open Bulletproof CompElliptic.Fields.Pasta Kimchi.Fixture Kimchi.Fixture.PS

/-- Certify a manifest selection, including every producer before its dependents. -/
def PicklesFixture.Application.runCertification (requireExplicit : Bool)
    (defaultSelection : Option String) : IO Unit := do
  let some dir ← IO.getEnv "PICKLES_DUMP_DIR"
    | throw (IO.userError "PICKLES_DUMP_DIR is not set")
  let selection := (← IO.getEnv "APPS").or defaultSelection
  if requireExplicit && (selection.isNone || selection == some "all") then
    throw (IO.userError "APPS names the manifest applications explicitly; all is not a selection")
  let apps ← IO.ofExcept (Manifest.select selection)
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
        let failedKeys := results.filterMap fun (producer, result) =>
          match result with
          | .ok P => if producer ∈ failed then some (producer, P.assembled.wiring.backend.wrapKey)
            else none
          | .error _ => none
        let blocked := blockedBy A.importsKey failedKeys
        let certify : IO (Certification A) := do
          if let some producer := blocked then
            throw (IO.userError s!"{name}: blocked by certification failure of {producer}")
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
