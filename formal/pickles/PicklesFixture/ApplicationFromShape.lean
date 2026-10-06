import BulletproofFixture
import PicklesFixture.ApplicationImport
import PicklesFixture.ApplicationRun
import PicklesFixture.Manifest

/-!
# Reconstruct applications from PureScript sidecars

Applications are selected from the fixture manifest and assembled in dependency order,
using full wrap keys to resolve imports. Each one's Lagrange tables come from the memo under
`lagrange-cache/`, as `PicklesFixture.basisFor` keys them. Independent circuit dumps are opened
only afterward.
-/

namespace PicklesFixture.Application

open Lean Pickles Pickles.Application Bulletproof Kimchi.Verifier

private def readJson (path : System.FilePath) : IO Json := do
  IO.ofExcept (Json.parse (← IO.FS.readFile path))

/-- A key's Lagrange table at its public-input count, from the memo under `lagrange-cache/`
(`LAGRANGE_CACHE_DIR`), keyed by curve, SRS size, domain and chunk count as `basisFor` keys
it. A missing memo is computed and written, which takes minutes, so it is announced. -/
private def memoisedTable (C : Ipa.KimchiCurve) (name : String) (σ : SRS C.Point) (nc : Nat)
    (cvk : KimchiVK C nc) : IO (Array (Array C.Point)) := do
  let memoDir := (← IO.getEnv "LAGRANGE_CACHE_DIR").getD "lagrange-cache"
  let path : System.FilePath := s!"{memoDir}/{name}-k{σ.k}-2^{cvk.domainLog2}-{nc}c.json"
  unless ← path.pathExists do
    IO.println s!"  no Lagrange memo at {path}: computing it"
    (← IO.getStdout).flush
  let pts ← Fixture.lagrangeBasisCached C path σ nc (2 ^ cvk.domainLog2) cvk.omega cvk.publicCount
  return pts.map (·.toArray)

/-- An application's Lagrange tables: its wrap key's and one per step domain exponent. -/
private def tablesFor (raw : ApplicationDump) (wrap : Srs IpaPallas.curve)
    (step : Srs IpaVesta.curve) : IO LagrangeTables := do
  let wrapTable ← memoisedTable IpaPallas.curve "pallas" wrap.σ 1 raw.wrapKey.cvk
  let mut steps : List (Nat × Array (Array IpaVesta.curve.Point)) := []
  for key in raw.stepKeys do
    unless (steps.lookup key.cvk.domainLog2).isSome do
      steps := steps ++
        [(key.cvk.domainLog2, ← memoisedTable IpaVesta.curve "vesta" step.σ raw.stepChunks key.cvk)]
  return ⟨wrapTable, steps⟩

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
    IO.println s!"{name}: reconstructing from sidecar, SRS and Lagrange memo"
    (← IO.getStdout).flush
    let tables ← tablesFor dump wrap step
    match dump.assemble wrap step tables (known.map (·.2)).toArray with
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
      let path := dir / app.name / "shapes" / s!"{tag.name}.json"
      let dump ← IO.ofExcept (ApplicationDump.ofJson (← readJson path))
      entries := entries ++ [(s!"{app.name}/{tag.name}", dump)]
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
