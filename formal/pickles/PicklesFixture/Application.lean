import Pickles.Application.Compile

/-!
# Application layout fixtures

Descriptions transcribed from the PureScript tests, independently of their exported
widths and statement sizes. Exercise the library's computed layouts;
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

end PicklesFixture.Application
