/-
The theorems' suite on the pickles prove tests' own dumps: for every tag the tests compiled, the
step circuit of each branch, rebuilt in Lean from the tag's constants with the branch's rule
replayed from its dump (`PicklesFixture.replayRule`), against the constraint system the tests
compiled. A tag's dump is one file, `<app>/<tag>.json` under `PICKLES_DUMP_DIR`, written by
`compileMulti` when its config names it; the prove tests write one per tag
(`PICKLES_DUMP_DIR=… npx spago test -p pickles`).

Run from `formal/`:  PICKLES_DUMP_DIR=<dir> lake exe check-tags
-/
import KimchiFixture.PS
import PicklesFixture.Compare
import PicklesFixture.Mains
import PicklesFixture.Rule

open Lean Snarky Snarky.Kimchi Kimchi Kimchi.Fixture.PS CompElliptic.Fields.Pasta
open PicklesFixture

/-- The comparisons of one branch's step circuit: the circuit `stepMainDumpCircuit` builds at the
dump's constants with the replayed rule, against the dumped gate table, at the tag's width
`w`. -/
def checkBranch (w : ℕ) (branch : Json) : Except String (List (String × Bool)) := do
  let rule ← RuleDump.ofJson (← branch.getObjVal? "rule")
  let stepMain ← branch.getObjVal? "stepMain"
  let raw : Raw Fp ← parseGates (← stepMain.getObjVal? "circuit")
  let k ← stepMainOf rule.prevs.size w stepMain
  if hw : w ≤ Pickles.MaxProofsVerified then
    return compareWith (a := Unit) (b := Pickles.StepStatement (Pickles.UnfVal 15) Fp w)
      (stepMainDumpCircuit (inVal := Vector Fp rule.inputSize)
        (outVal := Vector Fp rule.publicOutput.size) w hw k dummyUnfN0 (replayRule rule)) raw
  else throw s!"the tag's width {w} exceeds {Pickles.MaxProofsVerified}"

/-- Every branch of a tag's dump, as `(branch, comparisons)`. -/
def checkTag (j : Json) : Except String (List (ℕ × List (String × Bool))) := do
  let wrapMain ← j.getObjVal? "wrapMain"
  let w := (← (← (← constantsOf "wrapMain" wrapMain).getObjVal? "slotWidths").getArr?).size
  let branches ← (← j.getObjVal? "branches").getArr?
  branches.toList.zipIdx.mapM fun (b, i) => return (i, ← checkBranch w b)

def main : IO Unit := do
  let some dir ← IO.getEnv "PICKLES_DUMP_DIR"
    | throw (IO.userError "PICKLES_DUMP_DIR is not set")
  let apps := (← System.FilePath.readDir dir).qsort (·.fileName < ·.fileName)
  let mut failures := 0
  let mut circuits := 0
  for app in apps do
    unless ← app.path.isDir do continue
    let tags := (← app.path.readDir).qsort (·.fileName < ·.fileName)
    for tag in tags do
      unless tag.path.extension == some "json" do continue
      let name := s!"{app.fileName}/{tag.path.fileStem.getD tag.fileName}"
      match Json.parse (← IO.FS.readFile tag.path) >>= checkTag with
      | .error e =>
        failures := failures + 1
        IO.println s!"✗ {name}: {e}"
      | .ok results =>
        for (b, checks) in results do
          circuits := circuits + 1
          let bad := checks.filter (!·.2)
          if bad.isEmpty then
            IO.println s!"✓ {name} branch {b} step_main"
          else
            failures := failures + 1
            IO.println s!"✗ {name} branch {b} step_main: {String.intercalate ", " (bad.map (·.1))}"
  if failures > 0 then
    throw <| IO.userError s!"tag dumps FAILED ({failures} failure(s))"
  IO.println s!"── tag dumps OK ({circuits} circuits) ──"
