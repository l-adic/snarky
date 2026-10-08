import PicklesFixture.ApplicationFromShape
import PicklesFixture.ApplicationIndices
import PicklesFixture.Verdicts

/-!
Reconstruct the applications an explicit selection names and compile each one's circuits
once: compare them with the independent circuit dumps, check them at their keys' index data
and require their rejection at data a key could not have supplied; then, from each
application's cached proofs, construct the tables the lifting theorems take against the checked
indices. Run from `formal/` with `PICKLES_DUMP_DIR` set and `APPS` naming manifest applications;
the selection is never `all`. `PICKLES_PROOF_CACHE_DIR` selects the caches.
-/

open Lean Snarky Pickles Pickles.Application PicklesFixture PicklesFixture.Application
open Bulletproof CompElliptic.Fields.Pasta Kimchi.Fixture Kimchi.Fixture.PS

def main : IO Unit := do
  let some dir ← IO.getEnv "PICKLES_DUMP_DIR"
    | throw (IO.userError "PICKLES_DUMP_DIR is not set")
  let some selection ← IO.getEnv "APPS"
    | throw (IO.userError "APPS is not set: name the manifest applications to check")
  if selection = "all" then
    throw (IO.userError "APPS names applications explicitly; `all` is not a selection")
  let apps ← IO.ofExcept (Manifest.select (some selection))
  Manifest.checkFiles dir apps
  let σW ← srsAt CW "pallas" pallasBase.sqrt? (← IO.mkRef []) WrapIPARounds
  let σS ← srsAt CS "vesta" vestaBase.sqrt? (← IO.mkRef []) StepIPARounds
  let some wrap := Srs.check σW | throw (IO.userError "invalid wrap SRS")
  let some step := Srs.check σS | throw (IO.userError "invalid step SRS")
  let cacheDir := (← IO.getEnv "PICKLES_PROOF_CACHE_DIR").getD
    "../packages/pickles/test/fixtures/proof-cache"
  loadApplications dir apps wrap step fun imported => do
    for (name, A) in imported do
      let tag ← IO.ofExcept (Json.parse (← IO.FS.readFile (dir / s!"{name}.json")))
      let checked ← checkIndices name A tag
      checkTables name A checked cacheDir
