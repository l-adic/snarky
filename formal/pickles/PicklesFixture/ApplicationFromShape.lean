import PicklesFixture.ApplicationImport
import PicklesFixture.ApplicationRun
import PicklesFixture.Manifest

/-!
# Reconstruct applications from PureScript sidecars

Applications are selected from the fixture manifest and assembled in dependency order,
using full wrap keys to resolve imports. Independent circuit dumps are opened only afterward.
-/

namespace PicklesFixture.Application

open Lean Pickles Pickles.Application

private def readJson (path : System.FilePath) : IO Json := do
  IO.ofExcept (Json.parse (← IO.FS.readFile path))

private def assembleEntries (wrap : Srs Bulletproof.IpaPallas.curve)
    (step : Srs Bulletproof.IpaVesta.curve)
    (finish : List (String × ImportedApplication) → IO Unit) :
    Nat → List (String × ApplicationDump) →
    List (String × ImportedApplication) → IO Unit
  | 0, [], known => finish known
  | 0, _, _ => throw (IO.userError "unresolved application imports or cyclic dependencies")
  | fuel + 1, pending, known => do
    if pending.isEmpty then return ← finish known
    let ready := pending.find? fun (_, dump) =>
      dump.imports.all fun imp => known.any fun (_, p) =>
        sameKey p.assembled.wiring.backend.wrapKey imp.wrapKey
    let some (name, dump) := ready
      | throw (IO.userError s!"unresolved imports in {pending.map (·.1)}")
    IO.println s!"{name}: reconstructing from sidecar and SRS"
    (← IO.getStdout).flush
    match dump.assemble wrap step (known.map (·.2)).toArray with
    | .error e => throw (IO.userError s!"{name}: {e}")
    | .ok A =>
      assembleEntries wrap step finish fuel (pending.filter (·.1 != name)) (known ++ [(name, A)])

/-- Load each selected manifest entry's required sidecars, then assemble in import order. -/
def loadApplications (dir : System.FilePath) (apps : List Manifest.Application)
    (wrap : Srs Bulletproof.IpaPallas.curve) (step : Srs Bulletproof.IpaVesta.curve)
    (finish : List (String × ImportedApplication) → IO Unit) : IO Unit := do
  unless !apps.isEmpty do throw (IO.userError "no applications selected")
  let mut entries := []
  for app in apps do
    for tag in app.tags do
      let path := dir / app.name / "shapes" / s!"{tag}.json"
      let dump ← IO.ofExcept (ApplicationDump.ofJson (← readJson path))
      entries := entries ++ [(s!"{app.name}/{tag}", dump)]
  assembleEntries wrap step finish entries.length entries []

/-- Compare every step and wrap circuit after reconstruction has finished. -/
def compareApplications (dir : System.FilePath) (apps : List (String × ImportedApplication)) :
    IO Unit := do
  for (name, A) in apps do
    checkCompiled A.assembled A.setup name (← readJson (dir / s!"{name}.json"))

/-- Reconstruct selected applications before reading their independent circuit dumps. -/
def checkSelectedFromShape (dir : System.FilePath) (apps : List Manifest.Application)
    (wrap : Srs Bulletproof.IpaPallas.curve) (step : Srs Bulletproof.IpaVesta.curve) : IO Unit := do
  loadApplications dir apps wrap step (compareApplications dir)

end PicklesFixture.Application
