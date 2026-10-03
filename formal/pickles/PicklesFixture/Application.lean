import Pickles.Application
import Lean.Data.Json

/-!
# Application layout fixtures

Descriptions transcribed from the PureScript tests, independently of their exported
widths and statement sizes. Compare the library's computed layouts with tag metadata;
no circuit, witness, SRS, or proof-cache computation is needed for this check.
-/

namespace PicklesFixture.Application

open Lean Snarky Snarky.Kimchi CompElliptic.Fields.Pasta Pickles.Application

private def inputSchema : Schema where
  Input := Fp
  InputVar := FVar Fp
  Output := Unit
  OutputVar := Unit
  inputEncoding := inferInstance
  outputEncoding := inferInstance
  inputCheck := inferInstance

private def pairOutputSchema : Schema where
  Input := Unit
  InputVar := Unit
  Output := Fp × Fp
  OutputVar := FVar Fp × FVar Fp
  inputEncoding := inferInstance
  outputEncoding := inferInstance
  inputCheck := inferInstance

private def unitSchema : Schema where
  Input := Unit
  InputVar := Unit
  Output := Unit
  OutputVar := Unit
  inputEncoding := inferInstance
  outputEncoding := inferInstance
  inputCheck := inferInstance

/-- `TwoPhaseChain`: a field input, a base branch, and a one-slot Self branch. -/
def twoPhaseChain : Shape where
  schema := inputSchema
  imports := #[]
  branches := 2
  branches_pos := by decide
  slots b := if b.val = 0 then 0 else 1
  source _ _ := .self

/-- The field-input child application of `HeterogeneousPrevs`, compiled first. -/
def heterogeneousChild : Shape where
  schema := inputSchema
  imports := #[]
  branches := 1
  branches_pos := by decide
  slots _ := 0
  source _ i := Fin.elim0 i

/-- The pair-output parent of `HeterogeneousPrevs`, given only the child's exported
interface. Its recursive branch takes External child and Self; its base has no slots. -/
def heterogeneousPrevs (child : LayoutInterface) : Shape where
  schema := pairOutputSchema
  imports := #[child]
  branches := 2
  branches_pos := by decide
  slots b := if b.val = 0 then 0 else 2
  source _ i := if i.val = 0 then .external ⟨0, by simp⟩ else .self

/-- The zero-slot, unit-statement child of `RecurseOverChunks`, compiled at two chunks. -/
def chunksChild : Shape where
  schema := unitSchema
  imports := #[]
  branches := 1
  branches_pos := by decide
  slots _ := 0
  source _ i := Fin.elim0 i

/-- `RecurseOverChunks` verifies one external unit-statement proof. -/
def recurseOverChunks (child : LayoutInterface) : Shape where
  schema := unitSchema
  imports := #[child]
  branches := 1
  branches_pos := by decide
  slots _ := 1
  source _ _ := .external ⟨0, by simp⟩

/-- Compare one checked application with its tag dump. Imports provide only their
exported wrap keys alongside the interfaces already in the description. -/
def checkMetadata {D : Shape} (L : Layout D) (name : String) (tag : Json)
    (importKeys : Vector Json D.imports.size) : Except String Unit := do
  let branches ← (← tag.getObjVal? "branches").getArr?
  unless branches.size = D.branches do
    throw s!"{name}: {branches.size} branches, expected {D.branches}"
  let wrapMain ← tag.getObjVal? "wrapMain"
  let ownKey ← wrapMain.getObjVal? "key"
  let wrap ← wrapMain.getObjVal? "constants"
  let wrapBranches ← (← wrap.getObjVal? "branches").getArr?
  unless wrapBranches.size = D.branches do
    throw s!"{name}: wrap branch count differs from the description"
  let heights ← (← wrap.getObjVal? "slotWidths").getArr? >>= Array.mapM Json.getNat?
  unless heights = (L.wrapWidths.map Fin.val).toArray do
    throw s!"{name}: shared wrap widths {heights}, expected {(L.wrapWidths.map Fin.val).toArray}"
  for b in List.finRange D.branches do
    let some branch := branches[b.val]? | throw s!"{name}: missing branch {b.val}"
    let some wrapBranch := wrapBranches[b.val]?
      | throw s!"{name}: missing wrap branch {b.val}"
    let n ← (← wrapBranch.getObjVal? "width").getNat?
    unless n = (D.widths[b] : Nat) do
      throw s!"{name}/{b.val}: wrap branch width {n}, expected {D.slots b}"
    let rule ← branch.getObjVal? "rule"
    let inputSize ← (← rule.getObjVal? "inputSize").getNat?
    let output ← (← rule.getObjVal? "publicOutput").getArr?
    unless inputSize = CircuitType.size Fp D.schema.Input ∧
        output.size = CircuitType.size Fp D.schema.Output do
      throw s!"{name}/{b.val}: rule input/output encoding sizes differ from the schema"
    let prevs ← (← rule.getObjVal? "prevs").getArr?
    let slots ← (← (← (← branch.getObjVal? "stepMain").getObjVal? "constants").getObjVal?
      "slots").getArr?
    unless prevs.size = D.slots b ∧ slots.size = D.slots b do
      throw s!"{name}/{b.val}: predecessor count differs from the description"
    for i in List.finRange (D.slots b) do
      let some slot := slots[i.val]? | throw s!"{name}/{b.val}: missing slot {i.val}"
      let some prev := prevs[i.val]? | throw s!"{name}/{b.val}: missing predecessor {i.val}"
      let kind ← (← slot.getObjVal? "kind").getStr?
      let (expectedKind, expectedKey) := match D.source b i with
        | .self => ("self", ownKey)
        | .external imported => ("external", importKeys[imported])
      unless kind = expectedKind do
        throw s!"{name}/{b.val}/{i.val}: source {kind}, expected {expectedKind}"
      let width ← (← slot.getObjVal? "width").getNat?
      unless width = D.slotWidth b i do
        throw s!"{name}/{b.val}/{i.val}: width {width}, expected {D.slotWidth b i}"
      let statement ← (← prev.getObjVal? "statement").getArr?
      unless statement.size = D.prevSize b i do
        throw s!"{name}/{b.val}/{i.val}: statement size {statement.size}, expected {D.prevSize b i}"
      unless (← slot.getObjVal? "key") == expectedKey do
        throw s!"{name}/{b.val}/{i.val}: key differs from the selected {expectedKind} tag"

end PicklesFixture.Application
