import PicklesFixture.Application

/-!
Check the first application-framework layer: description to shared circuit layout.
Run from `formal/` with `PICKLES_DUMP_DIR` pointing to the existing tag dumps:

    lake env lean --run scripts/check_application_layouts.lean

The corpus is explicitly TwoPhaseChain and HeterogeneousPrevs, including the latter's
child tag. Missing files fail. This driver never builds circuits or runs link checks.
-/

open Lean Snarky Pickles.Application PicklesFixture.Application

private def require (ok : Bool) (label : String) : IO Unit := do
  unless ok do throw (IO.userError label)

private def checked (D : Shape) : IO (PLift (Layout D)) :=
  match Layout.check D with
  | .ok L => pure L
  | .error e => throw (IO.userError e)

private def rejected (D : Shape) : Bool :=
  match Layout.check D with
  | .ok _ => false
  | .error _ => true

-- Branch 0 has one live slot at the last position; branch 1 has External followed by
-- Self. Branch 0 either repeats that Self source or uses the import at the same position.
private def overlapping (imported : LayoutInterface) (selfFirst : Bool) : Shape where
  schema := (heterogeneousPrevs imported).schema
  imports := #[imported]
  branches := 2
  branches_pos := by decide
  slots b := if b.val = 0 then 1 else 2
  source b i :=
    if (b.val = 0 ∧ selfFirst) ∨ (b.val = 1 ∧ i.val = 1) then .self
    else .external ⟨0, by simp⟩

private def oversized : Shape where
  schema := twoPhaseChain.schema
  imports := #[]
  branches := 1
  branches_pos := by decide
  slots _ := 3
  source _ _ := .self

private def checkMixed (imported : LayoutInterface) : IO Unit := do
  let D := overlapping imported false
  let ⟨L⟩ ← checked D
  let b : D.Branch := ⟨0, by simp [D, overlapping]⟩
  let i : D.Slot b := ⟨0, by simp [D, overlapping, b]⟩
  let j := D.paddedSlot b i
  require ((L.wrapWidths.map Fin.val).toArray == #[imported.width.val, 2])
    "mixed source widths must use their per-position maximum"
  require (D.slotWidth b i == imported.width.val && L.wrapWidths[j].val == 2)
    "allocating a larger capacity must preserve the source's declared width"
  require ((D.slotAt b j).map Fin.val == some i.val)
    "a live slot must remain present even when its source has width zero"
  have _ := Layout.slotWidth_le_wrapWidths L b i
  have _ := (Layout.check_ok_iff D).mpr L
  -- Reverse the branch order: capacity cannot be chosen from the first or last source.
  let reversed : Shape :=
    { D with
      slots b := D.slots b.rev
      source b i := D.source b.rev i }
  let ⟨R⟩ ← checked reversed
  require ((R.wrapWidths.map Fin.val).toArray == (L.wrapWidths.map Fin.val).toArray)
    "reordering branches must preserve shared capacities"
  IO.println s!"✓ shared slot: source widths {imported.width.val} and 2 fit capacity 2"

private def checkAssembly : IO Unit := do
  let ⟨childLayout⟩ ← checked heterogeneousChild
  let child := childLayout.export
  let D := overlapping child true
  let ⟨L⟩ ← checked D
  let b : D.Branch := ⟨0, by simp [D, overlapping]⟩
  let i : D.Slot b := ⟨0, by simp [D, overlapping, b]⟩
  let j0 : Fin D.width := ⟨0, by change 0 < 2; decide⟩
  let j1 : Fin D.width := ⟨1, by change 1 < 2; decide⟩
  require ((L.wrapWidths.map Fin.val).toArray == #[0, 2])
    "equal-width overlapping slots did not produce [0, 2]"
  require ((D.slotAt b j0).isNone && (D.slotAt b j1).map Fin.val == some 0)
    "the one-slot branch must be front-padded, not back-padded"
  require ((D.paddedSlot b i).val == 1) "the live slot must move to wrap position 1"
  have _ := Shape.slotAt_paddedSlot D b i
  have _ := Layout.slotWidth_le_wrapWidths L b i
  have _ := (Layout.check_ok_iff D).mpr L
  checkMixed child
  let ⟨chainLayout⟩ ← checked twoPhaseChain
  checkMixed chainLayout.export
  require (rejected oversized) "width 3 must exceed MaxProofsVerified"
  IO.println "✓ layout assembly: front padding, equal/mixed source widths, width bound"
  -- Import the newly checked two-slot application into a one-slot application. Its
  -- external slot must keep width 2 while the new application's own width is 1.
  let consumer : Shape :=
    { schema := twoPhaseChain.schema
      imports := #[L.export]
      branches := 1
      branches_pos := by decide
      slots _ := 1
      source _ _ := .external ⟨0, by simp⟩ }
  let ⟨consumerLayout⟩ ← checked consumer
  require (consumerLayout.export.width.val == 1 &&
      (consumerLayout.wrapWidths.map Fin.val).toArray == #[2])
    "an imported width must remain independent of its consumer's width"
  IO.println "✓ exported interfaces compose across three independently checked applications"

private def readTag (dir : System.FilePath) (name : String) : IO Json := do
  let path := dir / s!"{name}.json"
  match Json.parse (← IO.FS.readFile path) with
  | .ok j => pure j
  | .error e => throw (IO.userError s!"{path}: {e}")

private def checkApplication (D : Shape) (name : String) (tag : Json)
    (importKeys : Vector Json D.imports.size) : IO (PLift (Layout D) × Json) := do
  let ⟨L⟩ ← checked D
  match checkMetadata L name tag importKeys with
  | .error e => throw (IO.userError e)
  | .ok _ =>
    IO.println s!"✓ {name}: {D.branches} branches, width {D.width}, \
      wrap slots {(L.wrapWidths.map Fin.val).toArray}"
    match tag.getObjVal? "wrapMain" >>= (·.getObjVal? "key") with
    | .error e => throw (IO.userError e)
    | .ok key => return (⟨L⟩, key)

/-- Check synthetic assembly cases and all three explicitly selected fixture tags. -/
def main : IO Unit := do
  checkAssembly
  let some dir ← IO.getEnv "PICKLES_DUMP_DIR"
    | throw (IO.userError "PICKLES_DUMP_DIR is not set")
  let chainName := "TwoPhaseChain/two_phase_chain"
  let _ ← checkApplication twoPhaseChain chainName (← readTag dir chainName) #v[]
  let childName := "HeterogeneousPrevs/child"
  let (⟨childLayout⟩, childKey) ← checkApplication heterogeneousChild childName
    (← readTag dir childName) #v[]
  let child := childLayout.export
  let D := heterogeneousPrevs child
  let name := "HeterogeneousPrevs/application"
  let tag ← readTag dir name
  let (_, ownKey) ← checkApplication D name tag #v[childKey]
  -- A checker that only compares total widths would miss this wrong statement schema.
  let wrong : Shape := { D with schema := child.schema }
  let ⟨L⟩ ← checked wrong
  match checkMetadata L name tag #v[childKey] with
  | .error _ => IO.println "✓ metadata comparison rejects an incorrect statement schema"
  | .ok _ => throw (IO.userError "metadata comparison accepted the wrong statement schema")
  let ⟨L⟩ ← checked D
  match checkMetadata L name tag #v[ownKey] with
  | .error _ => IO.println "✓ External key mismatch is rejected even when Self has that key"
  | .ok _ => throw (IO.userError "an External slot accepted the current application's key")
  IO.println "✓ application layouts: 3 applications checked separately, 5 branches, 3 slots"
