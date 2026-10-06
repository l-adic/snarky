import Lean

/-!
# Required application fixtures

The manifest names each fixture test and every tag it must export. Drivers select from this
list and open those exact paths; directory contents never determine the test corpus.
-/

namespace PicklesFixture.Manifest

/-- A required tag and the recursive executions its fixture must exercise. -/
structure Tag where
  /-- The circuit and sidecar basename. -/
  name : String
  /-- Number of verified predecessor slots, each applying both verification capstones. -/
  verifiedSlots : Nat
  /-- Number of adjacent verified slot pairs, each applying both handover capstones. -/
  handovers : Nat
  deriving BEq

/-- A fixture test and the application tags required from its compile calls. -/
structure Application where
  /-- The test's output directory and proof-cache basename. -/
  name : String
  /-- Every tag whose circuit dump and reconstruction sidecar must exist. -/
  tags : List Tag
  deriving BEq

private def applications : List Application :=
  [ ⟨"Chunks2", [⟨"chunks2", 0, 0⟩]⟩
  , ⟨"Codecs", [⟨"nrr", 0, 0⟩]⟩
  , ⟨"ExampleTransaction", [⟨"transaction", 6, 4⟩]⟩
  , ⟨"HeterogeneousPrevs", [⟨"child", 0, 0⟩, ⟨"application", 4, 2⟩]⟩
  , ⟨"ImportTwoPhaseChain", [⟨"two_phase_chain", 1, 0⟩, ⟨"chain", 5, 4⟩]⟩
  , ⟨"NoRecursionReturn", [⟨"nrr", 0, 0⟩]⟩
  , ⟨"PaddedWideSlots", [⟨"padded_wide_slots", 1, 0⟩]⟩
  , ⟨"RecurseOverChunks", [⟨"chunks2", 0, 0⟩, ⟨"recurse", 1, 0⟩]⟩
  , ⟨"SelfRecursiveChunks", [⟨"self_recursive_chunks", 1, 0⟩]⟩
  , ⟨"SimpleChain", [⟨"simple_chain", 4, 3⟩]⟩
  , ⟨"SimpleChainN2", [⟨"simple_chain_n2", 4, 2⟩]⟩
  , ⟨"TreeProofReturn", [⟨"nrr", 0, 0⟩, ⟨"tree", 9, 7⟩]⟩
  , ⟨"TwoPhaseChain", [⟨"two_phase_chain", 3, 2⟩]⟩ ]

/-- Require a tag's pinned coverage independently of the executions present in its cache. -/
def checkCoverage (name : String) (verifiedSlots handovers : Nat) : Except String Unit := do
  let some tag := applications.findSome? (fun app =>
      app.tags.find? (fun tag => s!"{app.name}/{tag.name}" == name))
    | throw s!"no capstone coverage declared for {name}"
  unless verifiedSlots == tag.verifiedSlots && handovers == tag.handovers do
    throw s!"{name}: capstone coverage: {verifiedSlots} verified slots and {handovers} handovers; \
      the manifest requires {tag.verifiedSlots} and {tag.handovers}"

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
      for path in [dir / app.name / s!"{tag.name}.json",
          dir / app.name / "shapes" / s!"{tag.name}.json"] do
        unless ← path.pathExists do throw (IO.userError s!"missing required fixture: {path}")
        unless (← path.metadata).type == .file do
          throw (IO.userError s!"required fixture is not a file: {path}")

end PicklesFixture.Manifest
