/-
The theorems' suite on the pickles prove tests' own dumps. A tag's dump is one file,
`<app>/<tag>.json` under `PICKLES_DUMP_DIR`, written by `compileMulti` when its config names it;
the prove tests write one per tag (`PICKLES_DUMP_DIR=… npx spago test -p pickles`).

Per tag: the wrap circuit, `Pickles.wrapMainCircuit` at the dump's constants, and each branch's
step circuit, `Pickles.stepMainCircuit` at its constants with the branch's rule replayed from its
dump (`replayRule`), against the systems the tests compiled; and the capstones' constant premises on
those constants (`wrapMainHyps`, `stepMainHyps`), with each branch's slot count its rule's.

Across tags: each slot verifies a dumped tag's proofs — its own tag's for a self slot, the tag
whose wrap key it carries for an external one (keys are matched by digest, which the key check
ties to the commitments) — at that tag's width and step chunk count, and reads a previous
statement of the size every branch of that tag emits; and every wrap circuit pads with one set of
challenges.

The links (`LINKS=all`, or `LINKS=<app>,…`), instead: every proof in the apps' proof caches
(`PICKLES_PROOF_CACHE_DIR`) has its circuit run through the prover at advice read off the cache —
a step proof's step circuit at its rule's witness and its slots (`stepMainAdviceOf`), a wrap
proof's wrap circuit at the step proof it wrapped (`wrapMainAdviceOf`), a base case at the cells
the cache records and a slot the rule lacks at the dump's padding — compiled as the capstones
compile it (`runMain`): the capstones' hypothesis that its constraints hold under the prover's
valuation is decided (`Snarky.Kimchi.KimchiConstraint.decidableHolds`), its table against its
assembled system, and its public input against the cached proof's; and the capstones' hypotheses
on its cells (`stepHyps`, `wrapHyps`, through `Snarky.CircuitType.decidableReads`, and
`Pickles.KeyReads.of_readPt` for a slot's key cells, compared by `Pickles.instDecidableEqVkComms`),
on `LINKS_JOBS` workers (4). A cached proof in no link fails the run.

Run from `formal/`:  PICKLES_DUMP_DIR=<dir> lake exe check-tags
(`BULLETPROOF_FIXTURES_DIR` overrides the blinding bases' fixtures.)
-/
import KimchiFixture.PS
import Pickles.StepWrap
import PicklesFixture.Compare
import PicklesFixture.Fop
import PicklesFixture.Premises
import PicklesFixture.Rule
import PicklesFixture.Advice
import PicklesFixture.Satisfies

open Lean Snarky Snarky.Kimchi Kimchi Kimchi.Fixture Kimchi.Fixture.PS CompElliptic.Fields.Pasta
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
      (fun u => Prod.fst <$> Pickles.stepMainCircuit (w := w) (ncw := 1) (ncs := ncs) (k := 15)
        (ks := Pickles.StepIPARounds) (inVal := Vector Fp rule.inputSize)
        (outVal := Vector Fp rule.publicOutput.size) (fun i => k.slots[i].source)
        (fun i => k.slots[i].width_le hw) k.h (fopStepParams ncs) k.ownDomains.list
        (Pickles.constPt dummyWrapSgPt) dummyUnfN0 (replayRule rule none) inertStepAdvice u) raw
    return (checks, rule.inputSize + rule.publicOutput.size, slots)
  else throw s!"the tag's width {w} exceeds {Pickles.MaxProofsVerified}"

/-- One tag: its circuits' comparisons, by label, and its summary. A failed premise or a malformed
dump is an error. -/
def checkTag (name : String) (hWrap : XhatWrapCurve.Point) (hStep : XhatStepCurve.Point)
    (j : Json) :
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
  let sh ← wrapMainShapesOf bp w nc k
  wrapMainHyps k sh.tables hWrap
  let key ← checkedKey Bulletproof.IpaPallas.curve 15 1 (← wrapMain.getObjVal? "key")
  let wrapRaw : Raw Fq ← parseGates (← wrapMain.getObjVal? "circuit")
  let wrapChecks := compareWith (a := Pickles.StatementPacked 16 (Type1 Fq) Fq) (b := Unit)
    (fun stmt => Prod.fst <$> Pickles.wrapMainCircuit (k := 15) (ks := 16) fopWrapParams sh.widths
      (Pickles.stepDomainLog2s sh.keys) (Pickles.stepKeyCells sh.keys) sh.pins sh.lagrange k.h
      k.dummy sh.slotWidths inertWrapAdvice stmt) wrapRaw
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

/-- A main circuit's run, judged against the cached proof it makes: its compiled constraints
hold under the prover's valuation, its table satisfies its system, its public input is the
cached proof's `pub`, and every capstone hypothesis in `hyps` holds of its cells; printed under
`tag`, with each failed hypothesis named. -/
def verdict {F bv α : Type} [DecidableEq F] (tag : String) (r : MainRun F bv α) (pub : Array F)
    (hyps : List (String × Bool)) (ms : ℕ) : IO Bool := do
  let pubOk := decide (r.pub = pub.toList)
  let failed := hyps.filter (!·.2)
  let ok := r.holds && r.satisfies && pubOk && failed.isEmpty
  IO.println s!"{if ok then "✓" else "✗"} {tag} {ms} ms: constraints hold {r.holds}, table \
    satisfies {r.satisfies}, public input is the cached proof's {pubOk}, \
    {hyps.length - failed.length}/{hyps.length} link hypotheses"
  for (label, _) in failed do IO.println s!"    ✗ {label}"
  return ok

open CompElliptic.CurveForms.ShortWeierstrass in
/-- What `stepWrap_kimchiVerify` and `wrapStep_kimchiVerify` assume of a step circuit's cells,
decided under its valuation `V`: its statement reads the step proof's public input `pub`, and per
slot verifying a cached wrap proof, the slot is marked must-verify, its key `K` (`Key.check` of
the slot's key) runs at one chunk, the slot's key cells read as `K` (`KeyReads.of_readPt`'s
premises), its proof mask reads, and the statement the slot rebuilds packs to that wrap proof's
public input. A base case is not marked must-verify. -/
def stepHyps {n w ncs : ℕ} {ss : Fin n → ℕ} {sa : ℕ} (hw : w ≤ Pickles.MaxProofsVerified)
    (k : StepMainConsts n ncs) (V : Valuation Fp)
    (out : Pickles.StepMainOut n w (Pickles.SlotSource.widths w fun i => k.slots[i].source) ss sa
      1 ncs 15 Pickles.StepIPARounds)
    (pub : Array Fp) (prevs : Vector StepPrev n) : List (String × Bool) :=
  ("its statement reads its public input",
    decide ((mapVec (·.val V) (CircuitType.varToFields (F := Fp)
      (val := Pickles.StepStatement (Pickles.UnfVal 15) Fp w) out.out)).toList = pub.toList)) ::
  (List.finRange n).flatMap fun i =>
    let mv := decide (CircuitType.Reads V (out.prevs i).mustVerify true)
    match prevs[i] with
    | .baseCase _ => [(s!"slot {i}: its base case is not must-verify", !mv)]
    | .proof W _ =>
      match Pickles.Key.check k.slots[i].key with
      | none => [(s!"slot {i}: its key is checked", false)]
      | some K =>
        let cells := k.slots[i].source.keyCells out.vk.points
        let inp := Pickles.slotInput (k.slots[i].width_le hw) (Pickles.constPt dummyWrapSgPt)
          (out.prevs i) (out.slots i) out.unfs[i] out.msgs[i]
        let ms := CircuitType.readVal V inp.proofMask
        [(s!"slot {i}: it must verify", mv),
         (s!"slot {i}: its key runs at one chunk",
           decide (1 = Kimchi.Verifier.chunkCount 15 K.cvk.domainLog2)),
         (s!"slot {i}: its key cells lie on the curve", cells.indexPoints.all fun p =>
           decide (OnCurve Bulletproof.IpaPallas.curve.E.A Bulletproof.IpaPallas.curve.E.B
             (p.x.val V, p.y.val V))),
         (s!"slot {i}: its key cells read as its key",
           decide (cells.map (Pickles.readPt (C := Bulletproof.IpaPallas.curve) V) = K.cvk.comms)),
         (s!"slot {i}: its proof mask reads", decide (CircuitType.Reads V inp.proofMask ms)),
         (s!"slot {i}: its wrap proof is made at the statement it rebuilds",
           decide ((CircuitType.valueToFields (F := Fq) (inp.packedAt K.cvk V ms)).toList =
             W.publicInput.toList))]

/-- What `stepWrap_kimchiVerify` and `wrapStep_kimchiVerify` assume of a wrap circuit's cells,
decided under its valuation `V`: its branch index reads `b`, its step statement reads as the step
proof's public input `pub` (`StepStatement.ofWrap`), and per step slot `i` verifying a cached wrap
proof, its wrap slot is pinned, on branch `b`, at the domain of the slot's key. -/
def wrapHyps {bp mpv nc n ncs : ℕ} {slotWidths : Vector (Fin (Pickles.MaxProofsVerified + 1)) mpv}
    (b : ℕ) (k : StepMainConsts n ncs) (V : Valuation Fq)
    (fin : Pickles.WrapMainFinalizeOut (bp + 1) mpv nc 15 slotWidths)
    (ver : Pickles.WrapMainVerifyOut mpv nc 15 16) (pub : Array Fp) (prevs : Vector StepPrev n) :
    List (String × Bool) :=
  ("its branch index reads its branch", decide (fin.whichBranch.val V = (b : Fq))) ::
  ("its step statement reads the step proof's public input",
    decide ((CircuitType.valueToFields (F := Fp)
      (Pickles.StepStatement.ofWrap V ver.statement)).toList = pub.toList)) ::
  (List.finRange n).flatMap fun i =>
    match prevs[i], Pickles.Key.check k.slots[i].key with
    | .baseCase _, _ => []
    | .proof _ _, none => [(s!"slot {i}: its key is checked", false)]
    | .proof _ _, some K =>
      [(s!"slot {i}: its wrap slot is pinned at its key's domain",
        match (fin.slots[mpv - n + i.val]?).bind (·.pins[b]?) with
        | some (some j) => decide (Pickles.wrapDomainLog2s[j]? = some K.cvk.domainLog2)
        | _ => true)]

/-- The links of one tag, as jobs: per cached step proof of each branch, the step circuit at
its advice, and the wrap circuit at the wrap proof that wrapped it, each through the prover and
its table decided against its system; with the cache keys of the proofs they cover. -/
def linkJobs (name : String) (j : Json) (wraps : Array (Cache.Entry CW))
    (steps : Array (Cache.Entry CS)) : IO (Array (IO Bool) × List (String × String)) := do
  let ex {α : Type} (e : Except String α) : IO α := IO.ofExcept (e.mapError (s!"{name}: " ++ ·))
  let wrapMain ← ex (j.getObjVal? "wrapMain")
  let wc ← ex (constantsOf "wrapMain" wrapMain)
  let w := (← ex ((← ex (wc.getObjVal? "slotWidths")).getArr?)).size
  let branches ← ex ((← ex (j.getObjVal? "branches")).getArr?)
  let bp := branches.size - 1
  let some b0 := (← ex ((← ex (wc.getObjVal? "branches")).getArr?))[0]? | throw (IO.userError "")
  let some l0 := (← ex ((← ex (b0.getObjVal? "lagrange")).getArr?))[0]? | throw (IO.userError "")
  let nc := (← ex l0.getArr?).size
  let k ← ex (wrapMainOf nc wrapMain)
  let pad ← ex (WrapPadding.ofJson wrapMain)
  let wrapKey ← ex (checkedKey Bulletproof.IpaPallas.curve 15 1 (← ex (wrapMain.getObjVal? "key")))
  let sh ← ex (wrapMainShapesOf bp w nc k)
  let hw' : PLift (w ≤ Pickles.MaxProofsVerified) ←
    if h : w ≤ Pickles.MaxProofsVerified then pure (PLift.up h)
    else throw (IO.userError s!"{name}: width {w}")
  have hw := hw'.down
  let mut jobs : Array (IO Bool) := #[]
  let mut covered : List (String × String) := []
  for (bj, b) in branches.toList.zipIdx do
    let rule ← ex (RuleDump.ofJson (← ex (bj.getObjVal? "rule")))
    let n := rule.prevs.size
    let stepMainJ ← ex (bj.getObjVal? "stepMain")
    let ncs ← ex (slotChunks stepMainJ)
    let kb ← ex (stepMainOf n w ncs stepMainJ)
    let some stepKey := k.keys[b]? | throw (IO.userError s!"{name}: no step key for branch {b}")
    let some pins := k.pins[b]? | throw (IO.userError s!"{name}: no pins for branch {b}")
    let digest := toString stepKey.digest.val
    for S0 in steps.filter (·.vkDigest = digest) do
      let tag := s!"{name} branch {b} step {S0.publicInputKey.take 12}…"
      let exT {α : Type} (e : Except String α) : IO α := IO.ofExcept (e.mapError (s!"{tag}: " ++ ·))
      covered := (S0.vkDigest, S0.publicInputKey) :: covered
      jobs := jobs.push do
        let prevs ← exT (stepPrevsOf n wraps steps S0)
        let some vals := S0.rule.map (·.values) | throw (IO.userError s!"{tag}: no rule witness")
        unless vals.size = rule.allocated do
          throw (IO.userError s!"{tag}: {vals.size} witness values, the rule allocates \
            {rule.allocated}")
        let adv ← exT (stepMainAdviceOf w kb rule.inputSize wrapKey S0 prevs)
        let t0 ← IO.monoMsNow
        let r ← runMain fpSide (b := Pickles.StepStatement (Pickles.UnfVal 15) Fp w)
          (fun u => Pickles.stepMainCircuit (w := w) (ncw := 1) (ncs := ncs) (k := 15)
            (ks := Pickles.StepIPARounds) (inVal := Vector Fp rule.inputSize)
            (outVal := Vector Fp rule.publicOutput.size) (fun i => kb.slots[i].source)
            (fun i => kb.slots[i].width_le hw) kb.h (fopStepParams ncs) kb.ownDomains.list
            (Pickles.constPt dummyWrapSgPt) dummyUnfN0 (replayRule rule (some vals)) adv u) ()
        verdict s!"{tag}: step circuit" r S0.publicInput
          (stepHyps hw kb r.V r.result.1.2 S0.publicInput prevs) ((← IO.monoMsNow) - t0)
      let some W0 := wraps.find? (·.step = some (S0.vkDigest, S0.publicInputKey)) | continue
      covered := (W0.vkDigest, W0.publicInputKey) :: covered
      jobs := jobs.push do
        let prevs ← exT (stepPrevsOf n wraps steps S0)
        let wprevs ← exT (wrapPrevsOf w pins W0 prevs)
        let advW ← exT (wrapMainAdviceOf nc b sh.slotWidths pad k.dummy S0 wprevs)
        let inp ← exT (wrapInputOf W0)
        let t0 ← IO.monoMsNow
        let r ← runMain fqSide (a := Pickles.StatementPacked 16 (Type1 Fq) Fq) (b := Unit)
          (fun stmt => Pickles.wrapMainCircuit (k := 15) (ks := 16) fopWrapParams sh.widths
            (Pickles.stepDomainLog2s sh.keys) (Pickles.stepKeyCells sh.keys) sh.pins sh.lagrange
            k.h k.dummy sh.slotWidths advW stmt) inp
        verdict s!"{tag}: wrap circuit" r W0.publicInput
          (wrapHyps b kb r.V r.result.1.2.1 r.result.1.2.2 S0.publicInput prevs)
          ((← IO.monoMsNow) - t0)
  return (jobs, covered)

/-- Every link of the apps `apps` under `dir`, run on `nJobs` workers against the apps' proof
caches under `cacheDir`; every cached proof must be covered and every run pass its `verdict`. -/
def runLinks (dir cacheDir : System.FilePath) (apps : List String) (nJobs : ℕ) : IO Unit := do
  let mut jobs : Array (IO Bool) := #[]
  let mut uncovered := 0
  for app in apps do
    let raw ← IO.FS.readFile (cacheDir / s!"{app}.json")
    let (wraps, _) ← IO.ofExcept (Cache.parseFile CW fqSide.endo pallasBase.sqrt? raw)
    let (steps, _) ← IO.ofExcept (Cache.parseFile CS fpSide.endo vestaBase.sqrt? raw)
    let mut covered : List (String × String) := []
    for tag in (← (dir / app).readDir).qsort (·.fileName < ·.fileName) do
      unless tag.path.extension == some "json" do continue
      let (js, cs) ← linkJobs s!"{app}/{tag.path.fileStem.getD tag.fileName}"
        (← IO.ofExcept (Json.parse (← IO.FS.readFile tag.path))) wraps steps
      jobs := jobs ++ js
      covered := cs ++ covered
    let keys := (wraps.map fun e => (e.vkDigest, e.publicInputKey)) ++
      (steps.map fun e => (e.vkDigest, e.publicInputKey))
    for (d, pi) in keys.toList.filter (· ∉ covered) do
      uncovered := uncovered + 1
      IO.println s!"✗ {app}: the cached proof {d.take 12}…/{pi.take 12}… is in no link"
  IO.println s!"{jobs.size} run(s) on {nJobs} worker(s)"
  let oks ← runPool nJobs jobs
  unless uncovered = 0 && oks.all id do
    throw (IO.userError s!"links FAILED ({oks.toList.count false} run(s), {uncovered} uncovered)")
  IO.println s!"✓ {jobs.size} run(s): every compiled system holds under its prover's valuation, \
    every table satisfies its system, every public input is its cached proof's, every link \
    hypothesis holds"

def main : IO Unit := do
  let some dir ← IO.getEnv "PICKLES_DUMP_DIR"
    | throw (IO.userError "PICKLES_DUMP_DIR is not set")
  let fdir := (← IO.getEnv "BULLETPROOF_FIXTURES_DIR").getD "bulletproof-pcs/fixtures"
  let hStep ← blindingBase Bulletproof.IpaPallas.curve s!"{fdir}/ipa_batch_pallas.json"
  let hWrap ← blindingBase Bulletproof.IpaVesta.curve s!"{fdir}/ipa_batch_vesta.json"
  let apps := (← System.FilePath.readDir dir).qsort (·.fileName < ·.fileName)
  -- `LINKS=all` (or `LINKS=<app>,…`) runs the apps' links through the prover instead
  if let some links ← IO.getEnv "LINKS" then
    let cacheDir := (← IO.getEnv "PICKLES_PROOF_CACHE_DIR").getD
      "../packages/pickles/test/fixtures/proof-cache"
    let names ← if links = "all" then
        apps.toList.filterMapM fun a => do pure (if ← a.path.isDir then some a.fileName else none)
      else pure (links.splitOn ",")
    let nJobs := ((← IO.getEnv "LINKS_JOBS").bind String.toNat?).getD 4
    runLinks dir cacheDir names nJobs
    return
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
  if all.isEmpty then
    throw <| IO.userError s!"no tag dumps under {dir}: run the pickles prove tests with \
      PICKLES_DUMP_DIR set first"
  IO.println s!"── tag dumps OK ({circuits} circuits, {all.length} tags) ──"
