import PicklesFixture.Manifest

/-!
Check explicit fixture selection and rejection of missing outputs. Temporary empty files suffice:
the manifest check runs before JSON parsing, SRS loading and circuit reconstruction.
-/

open PicklesFixture

private def rejects (action : IO Unit) (expected : String) : IO Unit := do
  let error ← try
    action
    pure none
  catch e => pure (some e.toString)
  let some error := error | throw (IO.userError s!"accepted {expected}")
  unless (error.splitOn expected).length > 1 do
    throw (IO.userError s!"expected error containing '{expected}', got: {error}")

def main : IO Unit := do
  let all ← IO.ofExcept (Manifest.select none)
  unless !all.isEmpty && (all.map (·.name)).eraseDups.length == all.length &&
      all.all (fun a => !a.tags.isEmpty &&
        (a.tags.map (·.name)).eraseDups.length == a.tags.length) do
    throw (IO.userError "empty or duplicate manifest entries")
  unless (← IO.ofExcept (Manifest.select (some "all"))) == all do
    throw (IO.userError "all does not select the manifest")
  for selection in ["", "TwoPhaseChain,", "TwoPhaseChain,TwoPhaseChain", "UnlistedApp"] do
    if let .ok _ := Manifest.select (some selection) then
      throw (IO.userError s!"accepted invalid selection: {selection}")
  let apps ← IO.ofExcept (Manifest.select (some "HeterogeneousPrevs,TwoPhaseChain"))
  unless apps.map (·.name) == ["HeterogeneousPrevs", "TwoPhaseChain"] do
    throw (IO.userError "selection changed the requested applications")
  IO.ofExcept (Manifest.checkCoverage "TwoPhaseChain/two_phase_chain" 3 2)
  IO.ofExcept (Manifest.checkCoverage "ExampleTransaction/transaction" 6 4)
  IO.ofExcept (Manifest.checkCoverage "HeterogeneousPrevs/child" 0 0)
  -- A base-only cache and a shortened chain must fail even if traversal covered all of them.
  for (verified, handovers) in [(0, 0), (1, 0), (3, 0), (2, 2), (4, 2)] do
    rejects (IO.ofExcept (Manifest.checkCoverage "TwoPhaseChain/two_phase_chain"
      verified handovers)) "the manifest requires 3 and 2"
  rejects (IO.ofExcept (Manifest.checkCoverage "UnlistedApp/tag" 0 0))
    "no capstone coverage declared"
  IO.FS.withTempDir fun dir => do
    for app in apps do
      IO.FS.createDirAll (dir / app.name / "shapes")
      for tag in app.tags do
        IO.FS.writeFile (dir / app.name / s!"{tag.name}.json") "{}"
        IO.FS.writeFile (dir / app.name / "shapes" / s!"{tag.name}.json") "{}"
    Manifest.checkFiles dir apps
    let sidecar := dir / "HeterogeneousPrevs" / "shapes" / "child.json"
    IO.FS.removeFile sidecar
    rejects (Manifest.checkFiles dir apps) "HeterogeneousPrevs/shapes/child.json"
    IO.FS.writeFile sidecar "{}"
    let circuit := dir / "HeterogeneousPrevs" / "application.json"
    IO.FS.removeFile circuit
    rejects (Manifest.checkFiles dir apps) "HeterogeneousPrevs/application.json"
    IO.FS.createDir circuit
    rejects (Manifest.checkFiles dir apps) "required fixture is not a file"
    IO.FS.removeDir circuit
    IO.FS.writeFile circuit "{}"
    IO.FS.removeDirAll (dir / "TwoPhaseChain")
    rejects (Manifest.checkFiles dir apps) "TwoPhaseChain/two_phase_chain.json"
    rejects (Manifest.checkFiles dir []) "no fixture applications selected"
    rejects (Manifest.checkFiles dir all) "Chunks2/chunks2.json"
  IO.println "✓ manifest: explicit selections; missing sidecars, circuits and applications rejected"
  IO.println "✓ manifest: base-only and shortened recursion coverage rejected"
