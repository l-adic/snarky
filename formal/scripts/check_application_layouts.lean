import PicklesFixture.ApplicationWiring

/-!
Check application layout and static wiring against independently described applications.
Run from `formal/` with `PICKLES_DUMP_DIR` pointing to the existing tag dumps:

    lake env lean --run scripts/check_application_layouts.lean

The corpus is explicitly TwoPhaseChain and HeterogeneousPrevs, including the latter's
child tag. Missing files fail. This driver never builds circuits or runs link checks.
-/

open Lean Snarky Pickles Pickles.Application PicklesFixture.Application

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

private def wired {D : Shape} (L : Layout D) (name : String) (tag : Json)
    (tables : List (Nat × SlotLagrange 1 StepIPARounds))
    (imports : (t : Fin D.imports.size) → CircuitInterface D.imports[t]) : IO (Wiring D L) := do
  let A ← IO.ofExcept (backendOf D tables tag)
  let W ← IO.ofExcept (Wiring.assemble L A imports)
  for b in List.finRange D.branches do
    for i in List.finRange (D.slots b) do
      have _ := Wiring.pin_domain W b i (W.source b i).wrapIndex (W.pins_at_slot b i)
  IO.ofExcept (checkWiring W name tag)
  IO.println s!"✓ {name}: assembled keys, source domains, chunk counts, Lagrange tables and pins"
  return W

private def expectError {α : Type} (label : String) (result : Except String α) : IO Unit := do
  match result with
  | .ok _ => throw (IO.userError s!"accepted {label}")
  | .error e => IO.println s!"✓ rejects {label}: {e}"

private def oneImport {I : LayoutInterface} (C : CircuitInterface I)
    (t : Fin #[I].size) : CircuitInterface #[I][t] := by
  have h : t = 0 := Fin.eq_zero t
  subst t
  exact C

private def changeSlotField (tag : Json) (b i : Nat) (field : String) (value : Json) :
    Except String Json := do
  let branches ← (← tag.getObjVal? "branches").getArr?
  let some branch := branches[b]? | throw "missing branch to mutate"
  let step ← branch.getObjVal? "stepMain"
  let constants ← step.getObjVal? "constants"
  let slots ← (← constants.getObjVal? "slots").getArr?
  let some slot := slots[i]? | throw "missing slot to mutate"
  let slots := slots.set! i (slot.setObjVal! field value)
  let step := step.setObjVal! "constants" (constants.setObjVal! "slots" (.arr slots))
  return tag.setObjVal! "branches" (.arr (branches.set! b (branch.setObjVal! "stepMain" step)))

private def checkBackendRejections {L : Layout twoPhaseChain}
    (W : Wiring twoPhaseChain L) : IO Unit := do
  let A := W.backend
  let bad : BackendArtifacts twoPhaseChain := { A with stepKeys := A.stepKeys.reverse }
  expectError "branch keys in the wrong order" (Wiring.assemble L bad W.imports)
  let badWrap := { A.wrapKey with cvk := { A.wrapKey.cvk with prevChallenges := 0 } }
  expectError "a wrong wrap-key accumulator count"
    (Wiring.assemble L { A with wrapKey := badWrap } W.imports)
  -- A valid key can still have a domain unsupported by the recursive wrap circuit.
  let vk := { A.wrapKey.cvk with
    domainLog2 := 12
    omega := Kimchi.Verifier.domainGenerator Bulletproof.IpaPallas.curve 12
    publicCount_le := by rw [W.valid.wrapLayout.publicCount_eq]; decide }
  let some key := Key.check vk | throw (IO.userError "synthetic key failed its basic invariants")
  expectError "an unsupported wrap domain" (Wiring.assemble L { A with wrapKey := key } W.imports)
  let b : twoPhaseChain.Branch := ⟨0, by decide⟩
  let vk := { A.stepKeys[b].cvk with
    domainLog2 := 17
    omega := Kimchi.Verifier.domainGenerator Bulletproof.IpaVesta.curve 17
    publicCount_le := by rw [(W.valid.stepLayouts b).publicCount_eq]; decide }
  let some key := Key.check vk | throw (IO.userError "synthetic step key failed its invariants")
  let bad := { A with stepKeys := Vector.ofFn fun i => if i = b then key else A.stepKeys[i] }
  expectError "a step domain requiring a different chunk count" (Wiring.assemble L bad W.imports)

/-- Check synthetic assembly cases and all three explicitly selected fixture tags. -/
def main : IO Unit := do
  checkAssembly
  let some dir ← IO.getEnv "PICKLES_DUMP_DIR"
    | throw (IO.userError "PICKLES_DUMP_DIR is not set")
  let chainName := "TwoPhaseChain/two_phase_chain"
  let childName := "HeterogeneousPrevs/child"
  let name := "HeterogeneousPrevs/application"
  let chainTag ← readTag dir chainName
  let childTag ← readTag dir childName
  let tag ← readTag dir name
  let tables ← IO.ofExcept (wrapTablesOf #[chainTag, childTag, tag])
  let (⟨chainLayout⟩, _) ← checkApplication twoPhaseChain chainName chainTag #v[]
  let chainW ← wired chainLayout chainName chainTag tables (fun t => Fin.elim0 t)
  checkBackendRejections chainW
  let (⟨childLayout⟩, childKey) ← checkApplication heterogeneousChild childName
    childTag #v[]
  let childW ← wired childLayout childName childTag tables (fun t => Fin.elim0 t)
  let child := childLayout.export
  let D := heterogeneousPrevs child
  let (⟨layout⟩, ownKey) ← checkApplication D name tag #v[childKey]
  let imports : (t : Fin D.imports.size) → CircuitInterface D.imports[t] :=
    oneImport childW.export
  let W ← wired layout name tag tables imports
  let wrongKey ← IO.ofExcept (changeSlotField tag 1 0 "key" ownKey)
  expectError "an External slot using the current application's key" (checkWiring W name wrongKey)
  let wrongDomains ← IO.ofExcept (changeSlotField tag 1 0 "domains" (toJson [10, 15]))
  expectError "source domains from the wrong application" (checkWiring W name wrongDomains)
  let wrongChunks ← IO.ofExcept (changeSlotField tag 1 0 "numChunks" (toJson (2 : Nat)))
  expectError "an incorrect source chunk count" (checkWiring W name wrongChunks)
  let originalBranches ← IO.ofExcept ((tag.getObjVal? "branches") >>= Json.getArr?)
  let originalStep ← IO.ofExcept (originalBranches[1]!.getObjVal? "stepMain")
  let originalConstants ← IO.ofExcept (originalStep.getObjVal? "constants")
  let originalSlots ← IO.ofExcept ((originalConstants.getObjVal? "slots") >>= Json.getArr?)
  let ownTable ← IO.ofExcept (originalSlots[1]!.getObjVal? "lagrange")
  let wrongTable ← IO.ofExcept (changeSlotField tag 1 0 "lagrange" ownTable)
  expectError "a Lagrange table selected from the wrong source" (checkWiring W name wrongTable)
  let wc ← IO.ofExcept (tag.getObjVal? "wrapMain")
  let constants ← IO.ofExcept (wc.getObjVal? "constants")
  let wrongPins := tag.setObjVal! "wrapMain"
    (wc.setObjVal! "constants" (constants.setObjVal! "pins" (toJson [[1, 1], [1, 1]])))
  expectError "a pin selecting the wrong source domain" (checkWiring W name wrongPins)
  -- Source chunk counts remain independent even within one branch.
  -- This synthetic interface is not a proof fixture for a mixed-chunk circuit.
  let domains : KnownDomains 2 :=
    { log2s := [17]
      log2s_le := by simp; decide
      log2s_zkRows := by simp [zkRowsOf] }
  let mixed : CircuitInterface child :=
    { childW.export with
      stepChunks := 2
      stepDomains := domains
      stepDomains_nonempty := by simp [domains]
      stepChunkDomains := by simp [domains, Kimchi.Verifier.chunkCount, StepIPARounds] }
  let mixedW ← IO.ofExcept (Wiring.assemble layout W.backend
    (oneImport mixed))
  let b : D.Branch := ⟨1, by change 1 < 2; decide⟩
  let i0 : D.Slot b := ⟨0, by change 0 < 2; decide⟩
  let i1 : D.Slot b := ⟨1, by change 1 < 2; decide⟩
  require (mixedW.sourceChunks b i0 == 2 && mixedW.sourceChunks b i1 == 1)
    "static wiring incorrectly imposed a shared predecessor chunk count"
  IO.println "✓ synthetic imported interface preserves mixed 2/1 source chunks"
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
  IO.println "✓ application layouts and wiring: 3 applications, 5 branches, 3 slots"
