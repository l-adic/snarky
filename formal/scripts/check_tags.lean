/-
The theorems' suite on the pickles prove tests' own dumps. A tag's dump is one file,
`<app>/<tag>.json` under `PICKLES_DUMP_DIR`, written by `compileMulti` when its config names it;
the prove tests write one per tag (`PICKLES_DUMP_DIR=… npx spago test -p pickles`).

Per tag: the wrap circuit, `Pickles.wrapMainCircuit` at the dump's constants, and each branch's
step circuit, `Pickles.stepMainCircuit` at its constants (its domains by
`Pickles.KnownDomains.ofList?`) with the branch's rule replayed from its dump (`replayRule`),
against the systems the tests compiled; and the capstones' constant premises on those constants
(`wrapMainHyps`, `stepMainHyps`; a key's avoidance premise as the right side of
`Pickles.Key.avoids_lagrangeRelations_iff` or `Pickles.avoids_stepRelationsAt_iff`), with each
branch's slot count its rule's.

Across tags: each slot verifies a dumped tag's proofs — its own tag's for a self slot, the tag
whose wrap key it carries for an external one (keys are matched by digest, which the key check
ties to the commitments) — at that tag's width and step chunk count, and reads a previous
statement of the size every branch of that tag emits; and every wrap circuit pads with one set of
challenges.

The links (`LINKS=all`, every app but those in `linksAllSkips`, or `LINKS=<app>,…`), instead: every
proof in the apps' proof caches (`PICKLES_PROOF_CACHE_DIR`) has its circuit run through the prover
at advice read off the cache — a step proof's step circuit at its rule's witness and its slots
(`stepMainAdviceOf`), a wrap proof's wrap circuit at the step proof it wrapped (`wrapMainAdviceOf`),
a base case at the cells the cache records and a slot the rule lacks at the dump's padding —
compiled as the capstones compile it (`runMain`): the capstones' hypothesis that its constraints
hold under the prover's valuation is decided (`Snarky.Kimchi.KimchiConstraint.decidableHolds`), its
table against its assembled system (the assignments reduced by `Snarky.Kimchi.reduceSolved`, the
witness laid out by `Snarky.Kimchi.makeWitness`), and its public input against the cached proof's;
and the capstones' hypotheses on its cells (`stepHyps`, `wrapHyps`, through
`Snarky.CircuitType.decidableReads`, and `Pickles.KeyReads.of_readPt` for a slot's key cells,
compared by `Pickles.instDecidableEqVkComms`); and what the capstones conclude, against the cache
(`stepConclusions`, `wrapConclusions`): the cells read off the cached proofs
(`Pickles.IvpProof.read_eq`, `Pickles.OldsRead.of_readPt`), the finalize cells hold their
evaluations (`Kimchi.Verifier.instDecidableEqProofEvaluations`,
`Kimchi.Verifier.instDecidableEqPointEvaluations`, at the memoised Lagrange points of
`Pickles.pubEvalsWith`, by `Pickles.pubEvalsWith_lagrangePoints`), and `Guards` and `kimchiVerify`
hold of them, which gives `SgOk` (`Pickles.sgOkWith_of_kimchiVerifyWith`); and the handover: each
verified proof's accumulator is the next proof's old accumulator of its slot
(`PicklesFixture.carries`, at the memoised points by `Pickles.carryWith_lagrangePoints`), which with
its `SgOk` passes `accOk` (`Pickles.accOk_of_carryWith`), an unlinked one passing `accOk` on its own
(`PicklesFixture.padOkMemo`). Each proof's `sg` multi-scalar multiplication runs once, inside
`kimchiVerify`, and the Lagrange points every proof reads are computed before the pool, from the SRS
(`Bulletproof.Fixture.SRSLoader.loadSRS`) and memoised under `lagrange-cache/`
(`Bulletproof.Fixture.lagrangeBasisCached`). On `LINKS_JOBS` workers (4); a cached proof in no link
fails the run.

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
import PicklesFixture.Verdicts

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

/-- What the conclusion checks share across workers: each curve's SRS, loaded once per round
count, its checked keys, and the `kimchiVerify` and `sgOk` verdicts, computed once per proof and
public input. -/
structure VerdictCtx where
  /-- The wrap proofs' SRS (Pallas commitments). -/
  pallas : IO.Ref (List (ℕ × Bulletproof.SRS CW.Point))
  /-- The step proofs' SRS (Vesta commitments). -/
  vesta : IO.Ref (List (ℕ × Bulletproof.SRS CS.Point))
  /-- The wrap proofs' checked keys. -/
  pallasKeys : IO.Ref (List (String × Checked CW))
  /-- The step proofs' checked keys. -/
  vestaKeys : IO.Ref (List (String × Checked CS))
  /-- The shared verdicts. -/
  memo : Memo

open CompElliptic.CurveForms.ShortWeierstrass in
/-- Whether every point cell lies on `C` under `V`. -/
def onCurveCells (C : Bulletproof.Ipa.KimchiCurve) (V : Valuation C.BaseField)
    (ps : List (AffinePoint (FVar C.BaseField))) : Bool :=
  ps.all fun p => decide (OnCurve C.E.A C.E.B (p.x.val V, p.y.val V))

/-- `Pickles.IvpProof.read_eq`'s premises, decided: the cells `pr` read off `cp`'s commitments
and opening (by `readPt`, the scalars by `S.decode`). -/
def readsProof {C : Bulletproof.Ipa.KimchiCurve} {V : Valuation C.BaseField} {sf : Type}
    {ops : Pickles.IpaScalarOps C.BaseField (Builder V (KimchiConstraint C.BaseField)) sf}
    {k nc : ℕ} (S : Pickles.IvpSide C V ops) (pr : Pickles.IvpProof k nc (FVar C.BaseField) sf)
    (cp : Kimchi.Verifier.KimchiProof C nc k) : Bool :=
  decide (pr.wComm.map (·.map (Pickles.readPt V)) = cp.wComm) &&
    decide (pr.zComm.map (Pickles.readPt V) = cp.zComm) &&
    decide ((pr.tComm.map (Pickles.readPt V)).toArray = cp.tComm) &&
    decide (pr.opening.lr.map (fun q => (Pickles.readPt V q.1, Pickles.readPt V q.2)) =
      cp.opening.lr) &&
    decide (Pickles.readPt V pr.opening.delta = cp.opening.delta) &&
    decide (S.decode pr.opening.z1 = cp.opening.z1) &&
    decide (S.decode pr.opening.z2 = cp.opening.z2) &&
    decide (Pickles.readPt V pr.opening.sg = cp.opening.sg)

/-- `Pickles.FopTies`' four equations, decided: the scalar half's evaluation and
previous-challenge cells are `cp`'s, its public evaluations the run's at `pub` over `σ`, at the
key's memoised Lagrange points `L` (`Pickles.pubEvalsWith_lagrangePoints`). -/
def fopTies {C : Bulletproof.Ipa.KimchiCurve} {sf' : Type} {k nc w : ℕ}
    (σ : Bulletproof.SRS C.Point) (hk : σ.k = k) (cvk : Kimchi.Verifier.KimchiVK C nc)
    (L : Array (Vector C.Point nc))
    (cp : Kimchi.Verifier.KimchiProof C nc k) (pub : Array C.ScalarField)
    (Sc : Pickles.ScalarHalf C sf' k nc w) : Bool :=
  decide ((Vector.zipWith (fun m cv => if m then [cv] else []) Sc.maskVals
      Sc.prevVals).toList.flatten = (cp.olds.map (·.u)).toList) &&
    decide (Sc.evals.ftEval1.val Sc.V = cp.ftEval1) &&
    decide (Sc.evals.evals.map (fun v => v.map (·.val Sc.V)) = cp.evals) &&
    decide (Sc.evals.pub.map (fun v => v.map (·.val Sc.V)) =
      Pickles.pubEvalsWith σ cvk L (hk ▸ cp) pub)

/-- An entry's checked key and proof at the SRS `σ` and the chunk count `nc`. -/
def checkedKeyFor (C : Bulletproof.Ipa.KimchiCurve) (nc : ℕ) (σ : Bulletproof.SRS C.Point)
    (e : Cache.Entry C) :
    IO (Kimchi.Verifier.KimchiVK C nc × Kimchi.Verifier.KimchiProof C nc σ.k) := do
  let ⟨nc', cvk, cp⟩ ← checkedAny C σ e
  if h : nc' = nc then return (h ▸ cvk, h ▸ cp)
  else throw (IO.userError s!"the entry runs at {nc'} chunks, not {nc}")

/-- An SRS at its round count, the count pinned. -/
def srsAtK (C : Bulletproof.Ipa.KimchiCurve) (name : String)
    (sqrt : C.BaseField → Option C.BaseField) (loaded : IO.Ref (List (ℕ × Bulletproof.SRS C.Point)))
    (k : ℕ) : IO ((σ : Bulletproof.SRS C.Point) ×' σ.k = k) := do
  let σ ← srsAt C name sqrt loaded k
  if h : σ.k = k then return ⟨σ, h⟩ else throw (IO.userError s!"an SRS of {σ.k} rounds, not {k}")

/-- What the capstones conclude of a step circuit's slots, decided against the cache: per slot
verifying a cached wrap proof `W` under its key `K`, the slot's public input is `W`'s, its cells
read as `W`'s (`IvpProof.read_eq`, `commReads_readPt`), `Guards` and `kimchiVerify` hold of `W`
(so `SgOk`, `Pickles.sgOkWith_of_kimchiVerifyWith`), the finalize cells hold the evaluations of
the step proof `W` wrapped (`FopTies`), and that step proof's accumulator is `S0`'s of the slot
(`carries`, so `accOk` by `Pickles.accOk_of_carryWith`); a base case's accumulator passes `accOk`
on its own (`padOkMemo`). -/
def stepConclusions (ctx : VerdictCtx) {n w ncs : ℕ} {ss : Fin n → ℕ} {sa : ℕ}
    (hw : w ≤ Pickles.MaxProofsVerified) (k : StepMainConsts n ncs) (V : Valuation Fp)
    (out : Pickles.StepMainOut n w (Pickles.SlotSource.widths w fun i => k.slots[i].source) ss sa
      1 ncs 15 Pickles.StepIPARounds)
    (S0 : Cache.Entry CS) (prevs : Vector StepPrev n) : IO (List (String × Bool)) := do
  let ⟨σW, hW⟩ ← srsAtK CW "pallas" pallasBase.sqrt? ctx.pallas 15
  let ⟨σS, hS⟩ ← srsAtK CS "vesta" vestaBase.sqrt? ctx.vesta 16
  let mut hyps := []
  for i in List.finRange n do
    let .proof W S' := prevs[i] | continue
    let some K := Pickles.Key.check k.slots[i].key | continue
    let inp := Pickles.slotInput (k.slots[i].width_le hw) (Pickles.constPt dummyWrapSgPt)
      (out.prevs i) (out.slots i) out.unfs[i] out.msgs[i]
    let ms := CircuitType.readVal V inp.proofMask
    let pub := inp.publicInputAt K.cvk V ms
    let (cvkW, cpW) ← checkedKeyFor CW 1 σW W
    let cpR : Kimchi.Verifier.KimchiProof CW 1 15 := hW ▸ cpW
    let L ← basisFor CW "pallas" σW 1 W
    let kv ← memoized ctx.memo.verify (memoKey CW "pallas" σW.k W pub) fun _ =>
      Kimchi.Verifier.kimchiVerifyWith CW σW K.cvk L cpW pub
    let (cvkS', cpS') ← checkedKeyFor CS ncs σS S'
    let LS' ← basisFor CS "vesta" σS ncs S'
    hyps := hyps ++
      [(s!"slot {i}: its key is its wrap proof's",
         decide (K.cvk.comms = cvkW.comms ∧ K.cvk.domainLog2 = cvkW.domainLog2)),
       (s!"slot {i}: its public input is its wrap proof's", decide (pub = W.publicInput)),
       (s!"slot {i}: its proof cells lie on the curve", onCurveCells CW V inp.proof.points),
       (s!"slot {i}: its proof cells read as its wrap proof",
         readsProof (Pickles.stepSide V) inp.proof cpR),
       (s!"slot {i}: its old-accumulator cells read as its wrap proof's",
         onCurveCells CW V inp.sgOld.toList &&
           decide (inp.sgOld.toList.map (Pickles.readPt V) = (cpR.olds.map (·.sg)).toList)),
       (s!"slot {i}: Guards hold of its wrap proof",
         decide (cpW.olds.size = K.cvk.prevChallenges ∧ pub.size = K.cvk.publicCount)),
       (s!"slot {i}: kimchiVerify accepts its wrap proof, and so SgOk holds of it", kv),
       (s!"slot {i}: its finalize cells hold its step proof's evaluations",
         fopTies σS hS cvkS' LS' (hS ▸ cpS') S'.publicInput (inp.finalizedHalf V))]
  for i in List.finRange n do
    match prevs[i] with
    | .baseCase _ =>
      hyps := hyps ++ [(s!"slot {i}: its base-case accumulator satisfies accOk",
        ← padOkMemo CS "vesta" vestaBase.sqrt? ctx.vesta ctx.memo S0 i)]
    | .proof _ S' =>
      hyps := hyps ++ [(s!"slot {i}: its step proof's accumulator is carried into the slot's",
        ← carries CS "vesta" vestaBase.sqrt? ctx.vesta ctx.vestaKeys S' S0 i)]
  return hyps

/-- What the capstones conclude of a wrap circuit's cells, decided against the cache: its step
proof `S0`'s public input is the one its statement packs to (`wrapPublicInput`), its cells read as
`S0`'s (`IvpProof.read_eq`, `OldsRead.of_readPt`), `Guards` and `kimchiVerify` hold of `S0` (so
`SgOk`), and per slot of `S0` verifying a cached wrap proof, its finalize slot holds that proof's
evaluations (`FopTies`) and the proof's accumulator is `W0`'s of the slot, past the front pads
(`carries`); a pad or base case's accumulator passes `accOk` on its own (`padOkMemo`). -/
def wrapConclusions (ctx : VerdictCtx) {bp mpv nc n ncs : ℕ}
    {slotWidths : Vector (Fin (Pickles.MaxProofsVerified + 1)) mpv} (b : ℕ)
    (keys : Vector (Kimchi.Verifier.KimchiVK Bulletproof.IpaVesta.curve nc) (bp + 1))
    (k : StepMainConsts n ncs) (V : Valuation Fq)
    (fin : Pickles.WrapMainFinalizeOut (bp + 1) mpv nc 15 slotWidths)
    (ver : Pickles.WrapMainVerifyOut mpv nc 15 16) (S0 : Cache.Entry CS) (W0 : Cache.Entry CW)
    (prevs : Vector StepPrev n) : IO (List (String × Bool)) := do
  let ⟨σW, hW⟩ ← srsAtK CW "pallas" pallasBase.sqrt? ctx.pallas 15
  let ⟨σS, hS⟩ ← srsAtK CS "vesta" vestaBase.sqrt? ctx.vesta 16
  let some cvk := keys[b]? | throw (IO.userError s!"no step key for branch {b}")
  let some KStep := Pickles.Key.check cvk | return [("its step key is checked", false)]
  let pub := Pickles.wrapPublicInput σS KStep.cvk V ver.statement
  let cpV ← checkedFor CS nc σS S0
  let cpR : Kimchi.Verifier.KimchiProof CS nc 16 := hS ▸ cpV
  let L ← basisFor CS "vesta" σS nc S0
  let kv ← memoized ctx.memo.verify (memoKey CS "vesta" σS.k S0 pub) fun _ =>
    Kimchi.Verifier.kimchiVerifyWith CS σS KStep.cvk L cpV pub
  let pr : Pickles.IvpProof 16 nc (FVar Fq) (Type1 (FVar Fq)) :=
    ⟨ver.cells.wComm, ver.cells.zComm, ver.cells.tComm, ver.cells.opening⟩
  let sgOld := ver.cells.sgOld
  let keep (m : Option (BoolVar Fq)) : Bool := match m with
    | none => true
    | some b => decide ((↑b : CVar Fq).val V = 1)
  let oldsW := sgOld.map fun m => (Pickles.readPt V m.2, keep m.1)
  let bitsOk := (List.finRange sgOld.size).all fun i => match sgOld[i].1 with
    | none => true
    | some b => decide ((↑b : CVar Fq).val V = bit oldsW[i].2)
  let mut hyps :=
    [("its step proof's public input is the one its statement packs to",
       decide (pub = S0.publicInput)),
     ("its proof cells lie on the curve", onCurveCells CS V pr.points),
     ("its proof cells read as its step proof", readsProof (Pickles.wrapSide V) pr cpR),
     ("its old-accumulator cells read as its step proof's",
       onCurveCells CS V (sgOld.toList.map (·.2)) && bitsOk &&
         decide ((oldsW.toList.filter (·.2)).map (·.1) = (cpR.olds.map (·.sg)).toList)),
     ("Guards hold of its step proof",
       decide (cpV.olds.size = KStep.cvk.prevChallenges ∧ pub.size = KStep.cvk.publicCount)),
     ("kimchiVerify accepts its step proof, and so SgOk holds of it", kv)]
  for i in List.finRange n do
    let .proof Wi _ := prevs[i] | continue
    let some K := Pickles.Key.check k.slots[i].key | continue
    let some sl := fin.slots[mpv - n + i.val]? | continue
    let (_, cpWi) ← checkedKeyFor CW 1 σW Wi
    let LWi ← basisFor CW "pallas" σW 1 Wi
    hyps := hyps ++
      [(s!"slot {i}: its finalize slot holds its wrap proof's evaluations",
         fopTies σW hW K.cvk LWi (hW ▸ cpWi) Wi.publicInput
           (Pickles.ScalarHalf.wrap V sl.unfinalized sl.evals sl.prevChallenges))]
  let pad := W0.proof.prevChallenges.size - n
  for j in List.range pad do
    hyps := hyps ++ [(s!"pad accumulator {j} satisfies accOk",
      ← padOkMemo CW "pallas" pallasBase.sqrt? ctx.pallas ctx.memo W0 j)]
  for i in List.finRange n do
    match prevs[i] with
    | .baseCase _ =>
      hyps := hyps ++ [(s!"slot {i}: its base-case accumulator satisfies accOk",
        ← padOkMemo CW "pallas" pallasBase.sqrt? ctx.pallas ctx.memo W0 (pad + i))]
    | .proof Wi _ =>
      hyps := hyps ++ [(s!"slot {i}: its wrap proof's accumulator is carried into the slot's",
        ← carries CW "pallas" pallasBase.sqrt? ctx.pallas ctx.pallasKeys Wi W0 (pad + i))]
  return hyps

/-- The links of one tag, as jobs: per cached step proof of each branch, the step circuit at
its advice, and the wrap circuit at the wrap proof that wrapped it, each through the prover and
its table decided against its system; with the cache keys of the proofs they cover. -/
def linkJobs (ctx : VerdictCtx) (name : String) (j : Json) (wraps : Array (Cache.Entry CW))
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
        let concl ← stepConclusions ctx hw kb r.V r.result.1.2 S0 prevs
        verdict s!"{tag}: step circuit" r S0.publicInput
          (stepHyps hw kb r.V r.result.1.2 S0.publicInput prevs ++ concl) ((← IO.monoMsNow) - t0)
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
        let concl ← wrapConclusions ctx b sh.keys kb r.V r.result.1.2.1 r.result.1.2.2 S0 W0
          prevs
        verdict s!"{tag}: wrap circuit" r W0.publicInput
          (wrapHyps b kb r.V r.result.1.2.1 r.result.1.2.2 S0.publicInput prevs ++ concl)
          ((← IO.monoMsNow) - t0)
  return (jobs, covered)

/-- Every link of the apps `apps` under `dir`, run on `nJobs` workers against the apps' proof
caches under `cacheDir`; every cached proof must be covered and every run pass its `verdict`. -/
def runLinks (dir cacheDir : System.FilePath) (apps : List String) (nJobs : ℕ) : IO Unit := do
  let ctx : VerdictCtx :=
    { pallas := ← IO.mkRef [], vesta := ← IO.mkRef [], pallasKeys := ← IO.mkRef []
      vestaKeys := ← IO.mkRef [], memo := ← Memo.new }
  -- both SRSes, and every Lagrange memo the proofs read, built before the pool, so no two
  -- workers compute one
  let σW ← srsAt CW "pallas" pallasBase.sqrt? ctx.pallas 15
  let σS ← srsAt CS "vesta" vestaBase.sqrt? ctx.vesta 16
  let t0 ← IO.monoMsNow
  let mut warmed : List String := []
  for app in apps do
    let raw ← IO.FS.readFile (cacheDir / s!"{app}.json")
    let (wraps, _) ← IO.ofExcept (Cache.parseFile CW fqSide.endo pallasBase.sqrt? raw)
    let (steps, _) ← IO.ofExcept (Cache.parseFile CS fpSide.endo vestaBase.sqrt? raw)
    for e in wraps do
      let ⟨nc, _, _⟩ ← checkedAny CW σW e
      let key := s!"pallas/{e.vk.domainLog2}/{nc}/{e.vk.publicCount}"
      unless key ∈ warmed do
        let _ ← basisFor CW "pallas" σW nc e
        warmed := key :: warmed
    for e in steps do
      let ⟨nc, _, _⟩ ← checkedAny CS σS e
      let key := s!"vesta/{e.vk.domainLog2}/{nc}/{e.vk.publicCount}"
      unless key ∈ warmed do
        let _ ← basisFor CS "vesta" σS nc e
        warmed := key :: warmed
  IO.println s!"warm-up: {warmed.length} Lagrange memos in {(← IO.monoMsNow) - t0} ms"
  (← IO.getStdout).flush
  let mut jobs : Array (IO Bool) := #[]
  let mut uncovered := 0
  for app in apps do
    let raw ← IO.FS.readFile (cacheDir / s!"{app}.json")
    let (wraps, _) ← IO.ofExcept (Cache.parseFile CW fqSide.endo pallasBase.sqrt? raw)
    let (steps, _) ← IO.ofExcept (Cache.parseFile CS fpSide.endo vestaBase.sqrt? raw)
    let mut covered : List (String × String) := []
    for tag in (← (dir / app).readDir).qsort (·.fileName < ·.fileName) do
      unless tag.path.extension == some "json" do continue
      let (js, cs) ← linkJobs ctx s!"{app}/{tag.path.fileStem.getD tag.fileName}"
        (← IO.ofExcept (Json.parse (← IO.FS.readFile tag.path))) wraps steps
      jobs := jobs ++ js
      covered := cs ++ covered
    let keys := (wraps.map fun e => (e.vkDigest, e.publicInputKey)) ++
      (steps.map fun e => (e.vkDigest, e.publicInputKey))
    for (d, pi) in keys.toList.filter (· ∉ covered) do
      uncovered := uncovered + 1
      IO.println s!"✗ {app}: the cached proof {d.take 12}…/{pi.take 12}… is in no link"
  IO.println s!"{jobs.size} run(s) on {nJobs} worker(s)"
  (← IO.getStdout).flush
  let oks ← runPool nJobs jobs
  unless uncovered = 0 && oks.all id do
    throw (IO.userError s!"links FAILED ({oks.toList.count false} run(s), {uncovered} uncovered)")
  IO.println s!"✓ {jobs.size} run(s): every compiled system holds under its prover's valuation, \
    every table satisfies its system, every public input is its cached proof's, every link \
    hypothesis holds"

/-- The apps `LINKS=all` leaves out: `Chunks4`, whose four-chunk step key needs a `2^18` Lagrange
basis and the lane's longest runs, while `Chunks2` exercises the same chunking. Named, it runs. -/
def linksAllSkips : List String := ["Chunks4"]

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
        apps.toList.filterMapM fun a => do
          pure (if (← a.path.isDir) && !linksAllSkips.contains a.fileName then some a.fileName
            else none)
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
