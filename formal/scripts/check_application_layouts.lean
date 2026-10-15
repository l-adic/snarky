import PicklesFixture.Application
import PicklesFixture.ApplicationImport

/-!
Check application layout and static wiring against independently described applications.
Run from `formal/` with `PICKLES_DUMP_DIR` pointing to the existing tag dumps:

    lake env lean --run scripts/check_application_layouts.lean

The corpus is explicitly TwoPhaseChain and HeterogeneousPrevs, including the latter's
child tag. Missing files fail. This driver never builds circuits or runs link checks.
-/

open Lean Snarky Pickles Pickles.Application PicklesFixture.Application

-- Branch 0 has one live slot at the last position; branch 1 has External followed by
-- Self. Branch 0 either repeats that Self source or uses the import at the same position.
private def overlapping (imported : LayoutInterface) (selfFirst : Bool) : Shape where
  schema := (heterogeneousPrevs imported).schema
  imports := #[imported]
  branches := 2
  branches_pos := by decide
  slots b := if b.val = 0 then 1 else 2
  slots_le := by decide
  source b i :=
    if (b.val = 0 ∧ selfFirst) ∨ (b.val = 1 ∧ i.val = 1) then .self
    else .external ⟨0, by simp⟩

private def oversized : ShapeDump where
  statement := ⟨1, 0⟩
  imports := #[]
  branches := #[#[.self, .self, .self]]

private def expectError {α : Type u} (label : String) (result : Except String α) : IO Unit := do
  match result with
  | .ok _ => throw (IO.userError s!"accepted {label}")
  | .error e => IO.println s!"✓ rejects {label}: {e}"

private def checkMixed (imported : LayoutInterface) : IO Unit := do
  let D := overlapping imported false
  let b : D.Branch := ⟨0, by simp [D, overlapping]⟩
  let i : D.Slot b := ⟨0, by simp [D, overlapping, b]⟩
  let j := D.paddedSlot b i
  let _ ← requireProof ((D.wrapWidths.map Fin.val).toArray == #[imported.width.val, 2])
    (IO.userError "mixed source widths must use their per-position maximum")
  let _ ← requireProof (D.slotWidth b i == imported.width.val && D.wrapWidths[j].val == 2)
    (IO.userError "allocating a larger capacity must preserve the source's declared width")
  let _ ← requireProof ((D.slotAt b j).map Fin.val == some i.val)
    (IO.userError "a live slot must remain present even when its source has width zero")
  -- Reverse the branch order: capacity cannot be chosen from the first or last source.
  let reversed : Shape :=
    { D with
      slots b := D.slots b.rev
      slots_le b := D.slots_le b.rev
      source b i := D.source b.rev i }
  let _ ← requireProof
    ((reversed.wrapWidths.map Fin.val).toArray == (D.wrapWidths.map Fin.val).toArray)
    (IO.userError "reordering branches must preserve shared capacities")
  IO.println s!"✓ shared slot: source widths {imported.width.val} and 2 fit capacity 2"

private def checkAssembly : IO Unit := do
  let child := heterogeneousChild.export
  let D := overlapping child true
  let b : D.Branch := ⟨0, by simp [D, overlapping]⟩
  let i : D.Slot b := ⟨0, by simp [D, overlapping, b]⟩
  let j0 : Fin D.width := ⟨0, by change 0 < 2; decide⟩
  let j1 : Fin D.width := ⟨1, by change 1 < 2; decide⟩
  let _ ← requireProof ((D.wrapWidths.map Fin.val).toArray == #[0, 2])
    (IO.userError "equal-width overlapping slots did not produce [0, 2]")
  let _ ← requireProof ((D.slotAt b j0).isNone && (D.slotAt b j1).map Fin.val == some 0)
    (IO.userError "the one-slot branch must be front-padded, not back-padded")
  let _ ← requireProof ((D.paddedSlot b i).val == 1)
    (IO.userError "the live slot must move to wrap position 1")
  checkMixed child
  checkMixed twoPhaseChain.export
  expectError "width 3 exceeding MaxProofsVerified" (oversized.load #[])
  IO.println "✓ layout assembly: front padding, equal/mixed source widths, width bound"
  -- Import the newly checked two-slot application into a one-slot application. Its
  -- external slot must keep width 2 while the new application's own width is 1.
  let consumer : Shape :=
    { schema := twoPhaseChain.schema
      imports := #[D.export]
      branches := 1
      branches_pos := by decide
      slots _ := 1
      slots_le := by decide
      source _ _ := .external ⟨0, by simp⟩ }
  let _ ← requireProof (consumer.export.width.val == 1 &&
      (consumer.wrapWidths.map Fin.val).toArray == #[2])
    (IO.userError "an imported width must remain independent of its consumer's width")
  IO.println "✓ exported interfaces compose across three independently checked applications"

private def readDump (dir : System.FilePath) (app tag : String) : IO ApplicationDump := do
  let raw ← IO.ofExcept (Json.parse (← IO.FS.readFile (dir / app / "shapes" / s!"{tag}.json")))
  IO.ofExcept (ApplicationDump.ofJson raw)

-- Layout tests do not evaluate circuits: basis values are irrelevant to these metadata checks.
private def backend (D : Shape) (raw : ApplicationDump) : Except String (BackendArtifacts D) := do
  if h : raw.stepKeys.size = D.branches then
    return { wrapKey := raw.wrapKey, stepChunks := raw.stepChunks, stepKeys := ⟨raw.stepKeys, h⟩
             wrapLagrange := Vector.replicate _ (Vector.replicate _ 0) }
  else throw "branch key count differs"

private def oneImport {I : LayoutInterface} (C : CircuitInterface I)
    (t : Fin #[I].size) : CircuitInterface #[I][t] := by
  have h : t = 0 := Fin.eq_zero t
  subst t
  exact C

private def checkBackendRejections (W : Wiring twoPhaseChain) : IO Unit := do
  let A := W.backend
  let bad : BackendArtifacts twoPhaseChain := { A with stepKeys := A.stepKeys.reverse }
  expectError "branch keys in the wrong order" (Wiring.assemble bad W.imports)
  let badWrap := { A.wrapKey with prevChallenges := 0 }
  expectError "a wrong wrap-key accumulator count"
    (Wiring.assemble { A with wrapKey := badWrap } W.imports)
  -- A valid key can still have a domain unsupported by the recursive wrap circuit.
  let vk := { Kimchi.Fixture.keyToWire A.wrapKey with
    domainLog2 := 12
    omega := Kimchi.Verifier.domainGenerator Bulletproof.IpaPallas.curve 12 }
  let some key := vk.check 1 | throw (IO.userError "synthetic key failed its basic invariants")
  expectError "an unsupported wrap domain" (Wiring.assemble { A with wrapKey := key } W.imports)
  let b : twoPhaseChain.Branch := ⟨0, by decide⟩
  let vk := { Kimchi.Fixture.keyToWire A.stepKeys[b] with
    domainLog2 := 17
    omega := Kimchi.Verifier.domainGenerator Bulletproof.IpaVesta.curve 17 }
  let some key := vk.check A.stepChunks
    | throw (IO.userError "synthetic step key failed its invariants")
  let bad := { A with stepKeys := Vector.ofFn fun i => if i = b then key else A.stepKeys[i] }
  expectError "a step domain requiring a different chunk count" (Wiring.assemble bad W.imports)

/-- Check synthetic layouts and backend metadata from the three selected sidecars. -/
def main : IO Unit := do
  checkAssembly
  let some dir ← IO.getEnv "PICKLES_DUMP_DIR"
    | throw (IO.userError "PICKLES_DUMP_DIR is not set")
  let chain ← readDump dir "TwoPhaseChain" "two_phase_chain"
  let child ← readDump dir "HeterogeneousPrevs" "child"
  let parent ← readDump dir "HeterogeneousPrevs" "application"
  let chainW ← IO.ofExcept (Wiring.assemble
    (← IO.ofExcept (backend twoPhaseChain chain))
    (fun t => Fin.elim0 t))
  checkBackendRejections chainW
  let childW ← IO.ofExcept (Wiring.assemble
    (← IO.ofExcept (backend heterogeneousChild child))
    (fun t => Fin.elim0 t))
  let D := heterogeneousPrevs heterogeneousChild.export
  let W ← IO.ofExcept (Wiring.assemble (← IO.ofExcept (backend D parent))
    (oneImport childW.export))
  for b in List.finRange D.branches do
    let some rule := parent.rules[b.val]? | throw (IO.userError "missing rule")
    let _ ← IO.ofExcept (CheckedRule.check D b rule)
  let wrong : Shape := { D with schema := heterogeneousChild.export.schema }
  let b : wrong.Branch := ⟨0, by change 0 < 2; decide⟩
  let some rule := parent.rules[0]? | throw (IO.userError "missing base rule")
  expectError "the wrong application statement schema" (CheckedRule.check wrong b rule)
  let domains : KnownDomains 2 :=
    { log2s := [17], log2s_le := by simp; decide
      log2s_zkRows := by simp [Kimchi.Verifier.zkRowsOf] }
  let mixed : CircuitInterface heterogeneousChild.export :=
    { childW.export with
      stepChunks := 2
      stepDomains := domains }
  let mixedW ← IO.ofExcept (Wiring.assemble W.backend (oneImport mixed))
  let b : D.Branch := ⟨1, by change 1 < 2; decide⟩
  let i0 : D.Slot b := ⟨0, by change 0 < 2; decide⟩
  let i1 : D.Slot b := ⟨1, by change 1 < 2; decide⟩
  let _ ← requireProof (mixedW.sourceChunks b i0 == 2 && mixedW.sourceChunks b i1 == 1)
    (IO.userError "static wiring incorrectly imposed a shared predecessor chunk count")
  IO.println "✓ application layouts, branch keys, schemas, pins and mixed source chunks"
