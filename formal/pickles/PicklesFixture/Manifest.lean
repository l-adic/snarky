import Lean

/-!
# Required application fixtures

The manifest names each fixture test and every tag it must export. Drivers select from this
list and open those exact paths; directory contents never determine the test corpus.
-/

namespace PicklesFixture.Manifest

/-- A fixture test and the application tags required from its compile calls. -/
structure Application where
  /-- The test's output directory and proof-cache basename. -/
  name : String
  /-- Every tag whose circuit dump and reconstruction sidecar must exist. -/
  tags : List String
  deriving BEq

private def applications : List Application :=
  [ ⟨"Chunks2", ["chunks2"]⟩
  , ⟨"Codecs", ["nrr"]⟩
  , ⟨"HeterogeneousPrevs", ["child", "application"]⟩
  , ⟨"ImportTwoPhaseChain", ["two_phase_chain", "chain"]⟩
  , ⟨"NoRecursionReturn", ["nrr"]⟩
  , ⟨"PaddedWideSlots", ["padded_wide_slots"]⟩
  , ⟨"RecurseOverChunks", ["chunks2", "recurse"]⟩
  , ⟨"SelfRecursiveChunks", ["self_recursive_chunks"]⟩
  , ⟨"SimpleChain", ["simple_chain"]⟩
  , ⟨"SimpleChainN2", ["simple_chain_n2"]⟩
  , ⟨"TreeProofReturn", ["nrr", "tree"]⟩
  , ⟨"TwoPhaseChain", ["two_phase_chain"]⟩ ]

/-- Select named manifest entries, or the complete manifest when no selection is supplied. -/
def select (selection : Option String) : Except String (List Application) := do
  let some selection := selection | return applications
  if selection = "all" then return applications
  let names := selection.splitOn ","
  unless names.all (!·.isEmpty) do throw "the fixture selection contains an empty name"
  unless names.eraseDups.length = names.length do throw "duplicate fixture selection"
  names.mapM fun name =>
    match applications.find? (·.name == name) with
    | some app => pure app
    | none => throw s!"unknown fixture application: {name}"

/-- Require both files for every selected tag before loading SRSs or reconstructing circuits. -/
def checkFiles (dir : System.FilePath) (apps : List Application) : IO Unit := do
  unless !apps.isEmpty do throw (IO.userError "no fixture applications selected")
  for app in apps do
    for tag in app.tags do
      for path in [dir / app.name / s!"{tag}.json", dir / app.name / "shapes" / s!"{tag}.json"] do
        unless ← path.pathExists do throw (IO.userError s!"missing required fixture: {path}")
        unless (← path.metadata).type == .file do
          throw (IO.userError s!"required fixture is not a file: {path}")

end PicklesFixture.Manifest
