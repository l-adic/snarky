import PicklesFixture.ShapeDump
import PicklesFixture.ApplicationRun

/-!
# Reconstruct applications from PureScript shape sidecars

The sidecar supplies the application schema and branch/slot routing. Its imported tags are
resolved in compilation order by complete wrap key. Rule operations, backend metadata, and the
independently emitted circuits come from the tag dumps. This selected check uses no handwritten
Lean application shape.
-/

namespace PicklesFixture.Application

open Lean Pickles Pickles.Application

/-- The selected fixture applications, each in producer-before-consumer order. -/
private def selectedNames (apps : List String) : List (String × String) :=
  (if "TwoPhaseChain" ∈ apps then [("TwoPhaseChain", "two_phase_chain")] else []) ++
  (if "HeterogeneousPrevs" ∈ apps then
    [("HeterogeneousPrevs", "child"), ("HeterogeneousPrevs", "application")] else []) ++
  (if "RecurseOverChunks" ∈ apps then
    [("RecurseOverChunks", "chunks2"), ("RecurseOverChunks", "recurse")] else [])

private def readJson (path : System.FilePath) : IO Json := do
  match Json.parse (← IO.FS.readFile path) with
  | .ok j => return j
  | .error e => throw (IO.userError s!"{path}: {e}")

/-- Reconstruct each selected tag from its shape sidecar and compare every assembled step and
wrap circuit with the independently emitted PureScript constraint system. -/
private def checkEntries (S : Setup)
    (tables : List (Nat × SlotLagrange 1 StepIPARounds))
    (entries : List (String × Json × Json)) (known : Array KnownTag) : IO Unit := do
  match entries with
  | [] => pure ()
  | (name, tag, raw) :: rest =>
    let shape ← IO.ofExcept (ShapeDump.ofJson raw)
    match shape.load tag known with
    | .error e => throw (IO.userError s!"{name}: {e}")
    | .ok loaded =>
      match assembleOf loaded.shape loaded.imports tables name tag with
      | .error e => throw (IO.userError s!"{name}: {e}")
      | .ok A => do
        checkCompiled A S name tag
        let key ← IO.ofExcept ((← IO.ofExcept (tag.getObjVal? "wrapMain")).getObjVal? "key")
        checkEntries S tables rest (known.push ⟨key, A.layout.export, A.wiring.export⟩)
termination_by entries.length

def checkSelectedFromShape (dir : System.FilePath) (apps : List String) (S : Setup) : IO Unit := do
  let entries ← (selectedNames apps).mapM fun (app, tagName) => do
    let name := s!"{app}/{tagName}"
    let tag ← readJson (dir / s!"{name}.json")
    let raw ← readJson (dir / app / "shapes" / s!"{tagName}.json")
    return (name, tag, raw)
  let tables ← IO.ofExcept (wrapTablesOf (entries.map (fun (_, tag, _) => tag)).toArray)
  checkEntries S tables entries #[]

end PicklesFixture.Application
