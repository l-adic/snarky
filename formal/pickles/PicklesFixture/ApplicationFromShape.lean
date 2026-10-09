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
    IO.println s!"  no Lagrange memo at {path}"
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

/-- Reconstruct the entries in import order, continuing past a failure, and finish with each
entry's application or why it has none. A reconstruction that fails is reported at its entry;
an entry importing a failed producer, by wrap key, is blocked by that failure; an entry
importing one that has no application is blocked by it; and an entry whose import matches
nothing names the entries that failed to load, whose keys are unknown. -/
private def assembleAll (wrap : Srs Bulletproof.IpaPallas.curve)
    (step : Srs Bulletproof.IpaVesta.curve)
    (finish : List (String × Except String ImportedApplication) → IO Unit) :
    Nat → List (String × ApplicationDump) → List (String × ImportedApplication) →
    List (String × Key IpaPallas.curve 1) → List (String × Except String ImportedApplication) →
    IO Unit
  | 0, pending, _, _, done =>
    finish (done ++ pending.map fun (name, _) =>
      (name, .error "unresolved application imports or cyclic dependencies"))
  | fuel + 1, pending, known, failed, done => do
    if pending.isEmpty then return ← finish done
    let ready := pending.find? fun (_, dump) =>
      dump.imports.all fun imp => known.any fun (_, p) =>
        sameKey p.assembled.wiring.backend.wrapKey imp.wrapKey
    match ready with
    | some (name, dump) =>
      IO.println s!"{name}: reconstructing from sidecar, SRS and Lagrange memo"
      (← IO.getStdout).flush
      let rest := pending.filter (·.1 != name)
      match ← (tablesFor dump wrap step).toBaseIO with
      | .error e =>
        assembleAll wrap step finish fuel rest known (failed ++ [(name, dump.wrapKey)])
          (done ++ [(name, .error s!"Lagrange memo: {e}")])
      | .ok tables =>
        match dump.assemble wrap step tables (known.map (·.2)).toArray with
        | .error e =>
          assembleAll wrap step finish fuel rest known (failed ++ [(name, dump.wrapKey)])
            (done ++ [(name, .error e)])
        | .ok A =>
          assembleAll wrap step finish fuel rest (known ++ [(name, A)]) failed
            (done ++ [(name, .ok A)])
    | none =>
      let unloaded := done.filterMap fun (n, r) =>
        match r with
        | .error _ => if failed.any (·.1 == n) then none else some n
        | .ok _ => none
      let unmatched := if unloaded.isEmpty then
          "blocked: an import matches no application in the selection"
        else s!"blocked: an import matches no application in the selection; failed to load: \
          {", ".intercalate unloaded}"
      let blocked := pending.map fun (name, dump) =>
        match blockedBy dump.importsKey failed with
        | some producer => (name, .error s!"blocked by the failure of {producer}")
        | none =>
          let others := (pending.filter (·.1 != name)).map fun (n, d) => (n, d.wrapKey)
          match blockedBy dump.importsKey others with
          | some producer => (name, .error s!"blocked by {producer}, which has no application")
          | none => (name, .error unmatched)
      finish (done ++ blocked)

/-- Load each selected manifest entry's sidecar, reconstruct every entry in import order,
continuing past failures, and finish with each entry's application or its failure. An entry
whose sidecar is missing or does not parse fails at that stage, its key unknown; one whose
circuit dump is missing fails with its key known, so its dependents are blocked by it. The
shared SRSs are the caller's. -/
def reconstructApplications (dir : System.FilePath) (apps : List Manifest.Application)
    (wrap : Srs Bulletproof.IpaPallas.curve) (step : Srs Bulletproof.IpaVesta.curve)
    (finish : List (String × Except String ImportedApplication) → IO Unit) : IO Unit := do
  unless !apps.isEmpty do throw (IO.userError "no applications selected")
  let mut entries : List (String × ApplicationDump) := []
  let mut failures : List (String × String) := []
  let mut failedKeys : List (String × Key IpaPallas.curve 1) := []
  for app in apps do
    for tag in app.tags do
      let name := s!"{app.name}/{tag.name}"
      let dumpPath := dir / app.name / s!"{tag.name}.json"
      let sidecar := dir / app.name / "shapes" / s!"{tag.name}.json"
      if !(← sidecar.pathExists) then
        failures := failures ++ [(name, s!"missing required fixture: {sidecar}")]
      else
        match ← (do IO.ofExcept (ApplicationDump.ofJson (← readJson sidecar))).toBaseIO with
        | .error e => failures := failures ++ [(name, s!"sidecar: {e}")]
        | .ok dump =>
          if ← dumpPath.pathExists then entries := entries ++ [(name, dump)]
          else
            failures := failures ++ [(name, s!"missing required fixture: {dumpPath}")]
            failedKeys := failedKeys ++ [(name, dump.wrapKey)]
  assembleAll wrap step finish entries.length entries [] failedKeys
    (failures.map fun (name, e) => (name, Except.error e))

/-- Load and reconstruct every selected entry, failing at the first that has no application,
then continue with all of them. -/
def loadApplications (dir : System.FilePath) (apps : List Manifest.Application)
    (wrap : Srs Bulletproof.IpaPallas.curve) (step : Srs Bulletproof.IpaVesta.curve)
    (finish : List (String × ImportedApplication) → IO Unit) : IO Unit :=
  reconstructApplications dir apps wrap step fun results => do
    for (name, r) in results do
      if let .error e := r then throw (IO.userError s!"{name}: {e}")
    finish (results.filterMap fun (name, r) =>
      match r with
      | .ok A => some (name, A)
      | .error _ => none)

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
