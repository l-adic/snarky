/-
The theorems' suite on the pickles prove tests' own dumps. A tag's dump is one file,
`<app>/<tag>.json` under `PICKLES_DUMP_DIR`, written by `compileMulti` when its config names it;
the prove tests write one per tag (`PICKLES_DUMP_DIR=… npx spago test -p pickles`).

Per tag: the wrap circuit, rebuilt in Lean at the dump's constants (`wrapMainCircuitOf`), and each
branch's step circuit, rebuilt at its constants with the branch's rule replayed from its dump
(`replayRule`), against the systems the tests compiled; and the capstones' constant premises on
those constants (`wrapMainHyps`, `stepMainHyps`), with each branch's slot count its rule's.

Across tags: each slot verifies a dumped tag's proofs — its own tag's for a self slot, the tag
whose wrap key it carries for an external one (keys are matched by digest, which the key check
ties to the commitments) — at that tag's width and step chunk count, and reads a previous
statement of the size every branch of that tag emits; and every wrap circuit pads with one set of
challenges.

Run from `formal/`:  PICKLES_DUMP_DIR=<dir> lake exe check-tags
(`BULLETPROOF_FIXTURES_DIR` overrides the blinding bases' fixtures.)
-/
import KimchiFixture.PS
import PicklesFixture.Compare
import PicklesFixture.Mains
import PicklesFixture.Premises
import PicklesFixture.Rule

open Lean Snarky Snarky.Kimchi Kimchi Kimchi.Fixture.PS CompElliptic.Fields.Pasta
open PicklesFixture

/-- A wrap key's digest. -/
abbrev Digest := Bulletproof.IpaPallas.curve.BaseField

/-- What the cross-tag checks read of a slot: whether it verifies its own tag, the digest of the
wrap key it verifies against, its width, the chunk count of the step proofs it finalizes, and the
size of the previous statement it reads. -/
structure SlotSummary where
  /-- Whether the slot verifies its own tag's proofs. -/
  self : Bool
  /-- The digest of the wrap key it verifies against. -/
  digest : Digest
  /-- Its width. -/
  width : ℕ
  /-- The chunk count of the step proofs it finalizes. -/
  chunks : ℕ
  /-- The size of the previous statement it reads. -/
  readSize : ℕ

/-- What the cross-tag checks read of a tag: its name, its wrap key's digest, its width, its step
proofs' chunk count, its padding challenges, each branch's application-state size, and each
branch's slots. -/
structure TagSummary where
  /-- `app/tag`. -/
  name : String
  /-- The digest of its wrap key. -/
  digest : Digest
  /-- Its width, the wrap circuit's slot count. -/
  width : ℕ
  /-- Its step proofs' chunk count. -/
  stepChunks : ℕ
  /-- Its wrap circuit's padding challenges. -/
  dummy : Vector Fq 15
  /-- Each branch's application state size: its rule's input and output cells. -/
  appSizes : List ℕ
  /-- Each branch's slots. -/
  slots : List (List SlotSummary)

/-- The chunk count of a step main's slots' step proofs, which the step circuit takes as one count
for all its slots; a step circuit with no slot finalizes no step proof, so any count builds it. -/
def slotChunks (stepMain : Json) : Except String ℕ := do
  let slots ← (← (← constantsOf "stepMain" stepMain).getObjVal? "slots").getArr?
  let counts ← slots.toList.mapM fun s => do (← s.getObjVal? "numChunks").getNat?
  match counts with
  | [] => return 1
  | c :: cs =>
    unless cs.all (· == c) do throw s!"the slots' step chunk counts {counts} differ"
    return c

/-- One branch: its step circuit's comparisons, the premises on its constants, and its slots. -/
def checkBranch (w : ℕ) (stepWidth : Option ℕ) (h : XhatStepCurve.Point) (branch : Json) :
    Except String (List (String × Bool) × ℕ × List SlotSummary) := do
  let rule ← RuleDump.ofJson (← branch.getObjVal? "rule")
  let n := rule.prevs.size
  unless stepWidth == some n do
    throw s!"the wrap circuit gives the branch {stepWidth} slots, its rule has {n}"
  let stepMain ← branch.getObjVal? "stepMain"
  let raw : Raw Fp ← parseGates (← stepMain.getObjVal? "circuit")
  let ncs ← slotChunks stepMain
  let k ← stepMainOf n w ncs stepMain
  stepMainHyps k h
  let slots := (List.finRange n).map fun i =>
    let s := k.slots[i]
    { self := s.self, digest := s.key.digest, width := s.source.width w, chunks := ncs
      readSize := rule.prevs[i].1.size }
  if hw : w ≤ Pickles.MaxProofsVerified then
    let checks := compareWith (a := Unit) (b := Pickles.StepStatement (Pickles.UnfVal 15) Fp w)
      (stepMainDumpCircuit (inVal := Vector Fp rule.inputSize)
        (outVal := Vector Fp rule.publicOutput.size) w hw k dummyUnfN0 (replayRule rule)) raw
    return (checks, rule.inputSize + rule.publicOutput.size, slots)
  else throw s!"the tag's width {w} exceeds {Pickles.MaxProofsVerified}"

/-- One tag: its circuits' comparisons, by label, and its summary. A failed premise or a malformed
dump is an error. -/
def checkTag (name : String) (hWrap : XhatCurve.Point) (hStep : XhatStepCurve.Point) (j : Json) :
    Except String (List (String × List (String × Bool)) × TagSummary) := do
  let wrapMain ← j.getObjVal? "wrapMain"
  let wc ← constantsOf "wrapMain" wrapMain
  let w := (← (← wc.getObjVal? "slotWidths").getArr?).size
  let branches ← (← j.getObjVal? "branches").getArr?
  if branches.isEmpty then throw "the tag has no branch"
  let bp := branches.size - 1
  let some b0 := (← (← wc.getObjVal? "branches").getArr?)[0]?
    | throw "the wrap circuit has no branch"
  let some l0 := (← (← b0.getObjVal? "lagrange").getArr?)[0]? | throw "the branch has no table"
  let nc := (← l0.getArr?).size
  let k ← wrapMainOf nc wrapMain
  let main ← wrapMainCircuitOf bp w nc k
  let m := CircuitType.size Fp (Pickles.StepStatement (Pickles.UnfVal 15) Fp w)
  let some tables := wrapMainTables? bp nc m k.lagrange | throw "the tables' shape"
  wrapMainHyps k tables hWrap
  let key ← checkedKey Bulletproof.IpaPallas.curve 15 1 (← wrapMain.getObjVal? "key")
  let wrapRaw : Raw Fq ← parseGates (← wrapMain.getObjVal? "circuit")
  let wrapChecks := compareWith (a := Pickles.StatementPacked 16 (Type1 Fq) Fq) (b := Unit)
    main wrapRaw
  let mut circuits := [("wrap_main", wrapChecks)]
  let mut appSizes := []
  let mut slots := []
  for (bj, b) in branches.toList.zipIdx do
    let (checks, appSize, ss) ← (checkBranch w k.stepWidths[b]? hStep bj).mapError
      (s!"branch {b}: " ++ ·)
    circuits := circuits ++ [(s!"branch {b} step_main", checks)]
    appSizes := appSizes ++ [appSize]
    slots := slots ++ [ss]
  return (circuits,
    { name := name, digest := key.digest, width := w, stepChunks := nc, dummy := k.dummy
      appSizes := appSizes, slots := slots })

/-- The cross-tag checks over one app's tags: each slot's source is a dumped tag, and the slot is
at its width, finalizes step proofs at its chunk count, and reads the size its branches emit.
Returns the slots checked. -/
def checkSources (tags : List TagSummary) : Except String ℕ := do
  let mut count := 0
  for t in tags do
    for (ss, b) in t.slots.zipIdx do
      for (s, i) in ss.zipIdx do
        let where_ := s!"{t.name} branch {b} slot {i}"
        let some src := tags.find? (fun u => decide (u.digest = s.digest))
          | throw s!"{where_}: no dumped tag has the wrap key it verifies against"
        if s.self && src.name != t.name then
          throw s!"{where_}: a self slot verifying {src.name}'s key"
        unless s.width == src.width do
          throw s!"{where_}: width {s.width}, {src.name} has width {src.width}"
        unless s.chunks == src.stepChunks do
          throw s!"{where_}: step proofs at {s.chunks} chunks, {src.name}'s are at {src.stepChunks}"
        unless src.appSizes.all (· == s.readSize) do
          throw s!"{where_}: reads {s.readSize} statement cells, {src.name} emits {src.appSizes}"
        count := count + 1
  return count

def main : IO Unit := do
  let some dir ← IO.getEnv "PICKLES_DUMP_DIR"
    | throw (IO.userError "PICKLES_DUMP_DIR is not set")
  let fdir := (← IO.getEnv "BULLETPROOF_FIXTURES_DIR").getD "bulletproof-pcs/fixtures"
  let hStep ← blindingBase Bulletproof.IpaPallas.curve s!"{fdir}/ipa_batch_pallas.json"
  let hWrap ← blindingBase Bulletproof.IpaVesta.curve s!"{fdir}/ipa_batch_vesta.json"
  let apps := (← System.FilePath.readDir dir).qsort (·.fileName < ·.fileName)
  let mut failures := 0
  let mut circuits := 0
  let mut slots := 0
  let mut sourceFailures := 0
  let mut all : List TagSummary := []
  for app in apps do
    unless ← app.path.isDir do continue
    let mut tags : List TagSummary := []
    for tag in (← app.path.readDir).qsort (·.fileName < ·.fileName) do
      unless tag.path.extension == some "json" do continue
      let name := s!"{app.fileName}/{tag.path.fileStem.getD tag.fileName}"
      match Json.parse (← IO.FS.readFile tag.path) >>= checkTag name hWrap hStep with
      | .error e =>
        failures := failures + 1
        IO.println s!"✗ {name}: {e}"
      | .ok (results, summary) =>
        tags := tags ++ [summary]
        for (label, checks) in results do
          circuits := circuits + 1
          let bad := checks.filter (!·.2)
          if bad.isEmpty then
            IO.println s!"✓ {name} {label}"
          else
            failures := failures + 1
            IO.println s!"✗ {name} {label}: {String.intercalate ", " (bad.map (·.1))}"
    match checkSources tags with
    | .error e =>
      sourceFailures := sourceFailures + 1
      IO.println s!"✗ {app.fileName}: {e}"
    | .ok n => slots := slots + n
    all := all ++ tags
  if sourceFailures = 0 then
    IO.println (s!"✓ slots are at their sources' widths and chunk counts and read their " ++
      s!"statement sizes ({slots} slots)")
  failures := failures + sourceFailures
  unless all.all fun t => decide (some t.dummy = (all.head?.map (·.dummy))) do
    failures := failures + 1
    IO.println "✗ the wrap circuits' padding challenges differ"
  if failures > 0 then
    throw <| IO.userError s!"tag dumps FAILED ({failures} failure(s))"
  IO.println s!"── tag dumps OK ({circuits} circuits, {all.length} tags) ──"
