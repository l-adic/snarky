import PicklesFixture.ApplicationImport
import PicklesFixture.ApplicationRun

/-!
# Reconstruct applications from PureScript shape sidecars

The sidecar supplies the shape, rules, resolved keys and protocol padding. Shared SRS files
supply the generators for deriving commitments and Lagrange bases. Only after assembly does
the driver open the independent circuit dump, for full step and wrap comparison.
-/

namespace PicklesFixture.Application

open Lean Pickles Pickles.Application

/-- The selected fixture applications, each in producer-before-consumer order. -/
private def selectedNames (apps : List String) : List (String × String) :=
  (if "TwoPhaseChain" ∈ apps then [("TwoPhaseChain", "two_phase_chain")] else []) ++
  (if "HeterogeneousPrevs" ∈ apps then
    [("HeterogeneousPrevs", "child"), ("HeterogeneousPrevs", "application")] else []) ++
  (if "RecurseOverChunks" ∈ apps then
    [("RecurseOverChunks", "chunks2"), ("RecurseOverChunks", "recurse")] else []) ++
  (if "PaddedWideSlots" ∈ apps then [("PaddedWideSlots", "padded_wide_slots")] else [])

private def readJson (path : System.FilePath) : IO Json := do
  match Json.parse (← IO.FS.readFile path) with
  | .ok j => return j
  | .error e => throw (IO.userError s!"{path}: {e}")

private def checkEntries (dir : System.FilePath)
    (wrap : Srs Bulletproof.IpaPallas.curve) (step : Srs Bulletproof.IpaVesta.curve)
    (entries : List (String × String)) (known : Array ImportedApplication) : IO Unit := do
  match entries with
  | [] => pure ()
  | (app, tagName) :: rest =>
    let name := s!"{app}/{tagName}"
    let raw ← readJson (dir / app / "shapes" / s!"{tagName}.json")
    let dump ← IO.ofExcept (ApplicationDump.ofJson raw)
    IO.println s!"{name}: reconstructing from sidecar and SRS"
    (← IO.getStdout).flush
    match dump.assemble wrap step known with
    | .error e => throw (IO.userError s!"{name}: {e}")
    | .ok A => do
      let tag ← readJson (dir / s!"{name}.json")
      checkCompiled A.assembled A.setup name tag
      checkEntries dir wrap step rest (known.push A)
termination_by entries.length

/-- Reconstruct the selected applications before reading their independent circuit dumps. -/
def checkSelectedFromShape (dir : System.FilePath) (apps : List String)
    (wrap : Srs Bulletproof.IpaPallas.curve) (step : Srs Bulletproof.IpaVesta.curve) : IO Unit :=
  checkEntries dir wrap step (selectedNames apps) #[]

end PicklesFixture.Application
