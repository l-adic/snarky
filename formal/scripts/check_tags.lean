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

The links (`LINKS=all`, every dumped app, or `LINKS=<app>,…`), instead: every
proof in the apps' proof caches (`PICKLES_PROOF_CACHE_DIR`) has its circuit run through the prover
at advice read off the cache — a step proof's step circuit at its rule's witness and its slots
(`stepMainAdviceOf`), a wrap proof's wrap circuit at the step proof it wrapped (`wrapMainAdviceOf`),
a base case at the cells the cache records and a slot the rule lacks at the dump's padding —
compiled as the capstones compile it (`runMain`): the capstones' hypothesis that its constraints
hold under the prover's valuation is decided (`Snarky.Kimchi.KimchiConstraint.decidableHolds`), its
table against its assembled system (the assignments reduced by `Snarky.Kimchi.reduceSolved`, the
witness laid out by `Snarky.Kimchi.makeWitness`), and its public input against the cached proof's;
and what the capstones conclude, against the cache (`stepConclusions`, `wrapConclusions`): the cells
read off the cached proofs (`Pickles.IvpProof.read_eq`, `Pickles.OldsRead.of_readPt`), the finalize
cells hold their evaluations (`Kimchi.Verifier.instDecidableEqProofEvaluations`,
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
fails the run. Chunks4's prove test dumps no tag, its links being too long to run, so its cache
is not linked. After the runs, the capstones themselves: each step run and the wrap run that wrapped
it through `Pickles.stepWrap_kimchiVerify` (`stepWrapLink`), each slot verifying a cached wrap proof
with that proof's wrap run through `Pickles.wrapStep_kimchiVerify` (`wrapStepLink`), every
hypothesis decided on the runs (their reads through `Snarky.CircuitType.decidableReads`, a slot's
key cells through `Pickles.KeyReads.of_readPt`, compared by `Pickles.instDecidableEqVkComms`) and
passed to the capstone; and every two adjacent links through the handover theorems (`stepWrapGlue`,
`wrapStepGlue`), their meeting decided on the runs.

Run from `formal/`:  PICKLES_DUMP_DIR=<dir> lake exe check-tags
(`BULLETPROOF_FIXTURES_DIR` overrides the blinding bases' fixtures.)
-/
import KimchiFixture.PS
import Pickles.StepWrap
import Pickles.WrapStep
import Pickles.Handover
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
cached proof's `pub`, and every check in `checks` holds of its cells against the cache; printed
under `tag`, with each failed check named. -/
def verdict {p : ℕ} [Fact p.Prime] {a av b bv α : Type} [CircuitType (ZMod p) a av]
    [∀ V : Valuation (ZMod p), CheckedType (ZMod p) (Builder V (KimchiConstraint (ZMod p))) a av]
    [CircuitType (ZMod p) b bv]
    {body : (V : Valuation (ZMod p)) → av →
      CircuitM (ZMod p) (Builder V (KimchiConstraint (ZMod p))) (bv × α)}
    (tag : String) (r : MainRun (a := a) (b := b) body) (pub : Array (ZMod p))
    (checks : List (String × Bool)) (ms : ℕ) : IO Bool := do
  let pubOk := decide (r.pub = pub.toList)
  let holds := @decide _ r.holds
  let failed := checks.filter (!·.2)
  let ok := holds && r.satisfies && pubOk && failed.isEmpty
  IO.println s!"{if ok then "✓" else "✗"} {tag} {ms} ms: constraints hold {holds}, table \
    satisfies {r.satisfies}, public input is the cached proof's {pubOk}, \
    {checks.length - failed.length}/{checks.length} checks against the cache"
  for (label, _) in failed do IO.println s!"    ✗ {label}"
  return ok

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
    let (cvkW, cpW) ← IO.ofExcept (W.checkedAt σW.k 1)
    let cpR : Kimchi.Verifier.KimchiProof CW 1 15 := hW ▸ cpW
    let L ← basisFor CW "pallas" σW 1 W
    let kv ← memoized ctx.memo.verify (memoKey CW "pallas" σW.k W pub) fun _ =>
      Kimchi.Verifier.kimchiVerifyWith CW σW K.cvk L cpW pub
    let (cvkS', cpS') ← IO.ofExcept (S'.checkedAt σS.k ncs)
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
  let (_, cpV) ← IO.ofExcept (S0.checkedAt σS.k nc)
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
    let (_, cpWi) ← IO.ofExcept (Wi.checkedAt σW.k 1)
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

/-- The loaded wrap SRS `σ` as the capstones' `Srs`, its round count the literal `15`, so that
constants indexed by the round count are the capstones' as they are. -/
abbrev wrapSrs (σ : Bulletproof.SRS CW.Point) (hk : σ.k = 15) (hh : σ.h ≠ 0) : Pickles.Srs CW :=
  ⟨⟨15, hk ▸ σ.g, σ.h, σ.U⟩, (by decide : Pickles.MaxProofsVerified * 15 < 2 ^ 128),
    (by decide : 0 < 15), hh⟩

/-- The loaded step SRS `σ` as the capstones' `Srs`, its round count `StepIPARounds` itself. -/
abbrev stepSrs (σ : Bulletproof.SRS CS.Point) (hk : σ.k = Pickles.StepIPARounds) (hh : σ.h ≠ 0) :
    Pickles.Srs CS :=
  ⟨⟨Pickles.StepIPARounds, hk ▸ σ.g, σ.h, σ.U⟩,
    (by decide : Pickles.MaxProofsVerified * Pickles.StepIPARounds < 2 ^ 128),
    (by decide : 0 < Pickles.StepIPARounds), hh⟩

deriving instance DecidableEq for Pickles.KnownDomain

/-- A wrap circuit's run with the constants it was compiled at, for the step runs of any tag whose
slots verify its proof. -/
structure WrapRun (σW : Bulletproof.SRS CW.Point) (hW : σW.k = 15) (hh : σW.h ≠ 0)
    (σS : Bulletproof.SRS CS.Point) where
  /-- The wrap circuit's branch count, less one. -/
  bp : ℕ
  /-- Its width. -/
  w : ℕ
  /-- Its step proofs' chunk count. -/
  nc : ℕ
  /-- Its constants at their shapes. -/
  sh : WrapMainShapes bp w nc
  /-- Its padding challenges. -/
  dummy : Vector Fq 15
  /-- The branch its proof took. -/
  b : Fin (bp + 1)
  /-- The advice it ran at. -/
  advW : Pickles.WrapMainAdvice w nc 15 Pickles.StepIPARounds (sh.slotWidths.map Fin.val).sum
  /-- The run. -/
  run : MainRun (a := Pickles.StatementPacked Pickles.StepIPARounds (Type1 Fq) Fq) (b := Unit)
    fun V => Pickles.wrapMainCircuit (c := Builder V (KimchiConstraint Fq))
      (Pickles.FopParams.of Bulletproof.IpaPallas.curve 1 (wrapSrs σW hW hh).σ.k
        Pickles.Linearization.fqTokens) sh.widths
      (Pickles.stepDomainLog2s sh.keys) (Pickles.stepKeyCells sh.keys) sh.pins
      sh.lagrange σS.h dummy sh.slotWidths advW

/-- A wrap-step link's slot with its capstone's conclusion kept: under the link's open premise
(`hlag`), it emits an accumulator and consumes the olds of the step proof its wrap circuit verifies
(`Pickles.WrapStepRun.Emits`, `Pickles.WrapStepRun.Consumes`). With the cache keys of the step
proof the link's step circuit makes and of the one its wrap proof wraps, which pair the links. -/
structure WrapStepOut where
  /-- The wrap circuit's branch count. -/
  branches : ℕ
  /-- The wrap circuit's width. -/
  w : ℕ
  /-- Its step proofs' chunk count. -/
  ncStep : ℕ
  /-- The next rule's slot count. -/
  n : ℕ
  /-- The next tag's width. -/
  wNext : ℕ
  /-- Each slot's width. -/
  ws : Fin n → ℕ
  /-- Each slot's previous statement size. -/
  ss : Fin n → ℕ
  /-- The application state's size. -/
  sa : ℕ
  /-- Each wrap slot's challenge-stack height. -/
  slotWidths : Vector (Fin (Pickles.MaxProofsVerified + 1)) w
  /-- The link's run. -/
  rk : Pickles.WrapStepRun branches w ncStep 15 Pickles.StepIPARounds n wNext ws ss sa slotWidths
  /-- The wrap circuit's padding challenges. -/
  dummy : Vector Fq 15
  /-- The slot's wrap key. -/
  cvk : Kimchi.Verifier.KimchiVK CW 1
  /-- The open premise. -/
  premise : Prop
  /-- The capstone's conclusion, as the handover reads it. -/
  concl : premise → ∃ (A : Kimchi.Verifier.Accumulator CS Pickles.StepIPARounds)
    (cp : Kimchi.Verifier.KimchiProof CS ncStep Pickles.StepIPARounds),
    rk.Emits cvk dummy A ∧ rk.Consumes cvk dummy cp.olds.toList
  /-- The cache key of the step proof the link's step circuit makes. -/
  makes : String × String
  /-- The cache key of the step proof the link's wrap proof wraps. -/
  wrapsStep : String × String
  /-- The link's slot, for the report. -/
  tag : String := ""

/-- What a wrap run's links all assume of it alone: its active branch's step key, checked, at the
wrap circuit's chunk count; its branch index; its sizes; and that key's points and Lagrange
bases finite. Decided once per wrap run (`wrapRunFacts`). -/
structure WrapRunFacts {σW : Bulletproof.SRS CW.Point} {hW : σW.k = 15} {hh : σW.h ≠ 0}
    {σS : Bulletproof.SRS CS.Point} (hS : σS.k = Pickles.StepIPARounds) (hhS : σS.h ≠ 0)
    (wr : WrapRun σW hW hh σS) where
  /-- The active branch's step key, checked. -/
  KStep : Pickles.Key CS wr.nc
  /-- It is the wrap circuit's. -/
  hkey : KStep.cvk = wr.sh.keys[wr.b]
  /-- It runs at the wrap circuit's chunk count. -/
  hnc : wr.nc = Kimchi.Verifier.chunkCount (stepSrs σS hS hhS).σ.k KStep.cvk.domainLog2
  /-- The branch index reads the active branch. -/
  hb : wr.run.result.1.2.1.whichBranch.val wr.run.V = ((wr.b : ℕ) : Fq)
  /-- The branches fit the scalar field. -/
  hbr : wr.bp + 1 ≤ PALLAS_SCALAR_CARD
  /-- The width is at most `MaxProofsVerified`. -/
  hww : wr.w ≤ Pickles.MaxProofsVerified
  /-- The key's points are finite. -/
  hnz : ∀ P ∈ wr.sh.keys[wr.b].comms.indexPoints, P ≠ 0
  /-- The key's domain's Lagrange bases are finite. -/
  hL : ∀ Ps ∈ (wr.sh.lagrange KStep.cvk.domainLog2).toList, ∀ c : Fin wr.nc, Ps[c] ≠ 0

/-- `WrapRunFacts` decided, or the first failing one named. The point checks are folds over their
lists: a bounded `∀` over points would be decided over the curve. -/
def wrapRunFacts {σW : Bulletproof.SRS CW.Point} {hW : σW.k = 15} {hh : σW.h ≠ 0}
    {σS : Bulletproof.SRS CS.Point} (hS : σS.k = Pickles.StepIPARounds) (hhS : σS.h ≠ 0)
    (wr : WrapRun σW hW hh σS) : Except String (WrapRunFacts hS hhS wr) :=
  match hK : Pickles.Key.check wr.sh.keys[wr.b] with
  | none => .error "the wrap circuit's step key is checked"
  | some KStep =>
    have hkey : KStep.cvk = wr.sh.keys[wr.b] := by
      unfold Pickles.Key.check at hK
      split at hK
      · cases hK; rfl
      · cases hK
    if hnc : wr.nc = Kimchi.Verifier.chunkCount (stepSrs σS hS hhS).σ.k KStep.cvk.domainLog2 then
    if hb : wr.run.result.1.2.1.whichBranch.val wr.run.V = ((wr.b : ℕ) : Fq) then
    if hbr : wr.bp + 1 ≤ PALLAS_SCALAR_CARD then
    if hww : wr.w ≤ Pickles.MaxProofsVerified then
    if hnz : (wr.sh.keys[wr.b].comms.indexPoints.all fun P => decide (P ≠ 0)) then
    if hL : ((wr.sh.lagrange KStep.cvk.domainLog2).toList.all fun Ps =>
        (List.finRange wr.nc).all fun c => decide (Ps[c] ≠ 0)) then
      .ok { KStep, hkey, hnc, hb, hbr, hww
            hnz := fun P hP => of_decide_eq_true (List.all_eq_true.mp hnz P hP)
            hL := fun Ps hPs c => of_decide_eq_true (List.all_eq_true.mp
              (List.all_eq_true.mp hL Ps hPs) c (List.mem_finRange c)) }
    else .error "its step key's Lagrange bases are finite"
    else .error "its step key's points are finite"
    else .error "the wrap circuit's width fits"
    else .error "the wrap circuit's branches fit the scalar field"
    else .error "the wrap circuit's branch index reads its branch"
    else .error "the step key runs at the wrap circuit's chunk count"

-- the capstone's conclusion is `let`s over compiled circuits, which the `let`-to-`have` cleanup
-- of the finished term cannot process in time; it only reshapes the term
set_option cleanup.letToHave false in
open CompElliptic.CurveForms.ShortWeierstrass in
/-- `Pickles.wrapStep_kimchiVerify` applied to one link: the run of a wrap circuit `wr` and the run
`rS` of a step circuit whose slot `i` verifies its proof, each compiled as the capstone compiles
it. Every hypothesis is decided on the runs and passed to the capstone; the label of the first
one failing is returned. The application's one open premise is the wrap circuit's table at the
active branch's domain being its step key's Lagrange points (`hlag`). -/
def wrapStepLink {σW : Bulletproof.SRS CW.Point} {hW : σW.k = 15} {hh : σW.h ≠ 0}
    {σS : Bulletproof.SRS CS.Point} (hS : σS.k = Pickles.StepIPARounds) (hhS : σS.h ≠ 0)
    (wr : WrapRun σW hW hh σS) (rule : RuleDump) (vals : Array Fp) {wNext : ℕ}
    (kb : StepMainConsts rule.prevs.size wr.nc) (hw : wNext ≤ Pickles.MaxProofsVerified)
    (adv : Pickles.StepMainAdvice rule.prevs.size wNext
      (Pickles.SlotSource.widths wNext fun i => kb.slots[i].source) 1 wr.nc 15
      Pickles.StepIPARounds (Vector Fp rule.inputSize))
    (rS : MainRun (a := Unit) (b := Pickles.StepStatement (Pickles.UnfVal 15) Fp wNext) fun V =>
      Pickles.stepMainCircuit (c := Builder V (KimchiConstraint Fp)) (ncw := 1)
        (outVal := Vector Fp rule.publicOutput.size)
        (fun i => kb.slots[i].source) (fun i => kb.slots[i].width_le hw) (wrapSrs σW hW hh).σ.h
        (fopStepParams wr.nc) kb.ownDomains.list (Pickles.constPt dummyWrapSgPt) dummyUnfN0
        (replayRule rule (some vals)) adv)
    (f : WrapRunFacts hS hhS wr) (i : Fin rule.prevs.size) (makes wrapsStep : String × String) :
    List (String × Bool × Option WrapStepOut) :=
  let SStep := stepSrs σS hS hhS
  let srcs : Fin rule.prevs.size → Pickles.SlotSource 1 Pickles.StepIPARounds :=
    fun i => kb.slots[i].source
  let m := CircuitType.size Fp (Pickles.StepStatement (Pickles.UnfVal 15) Fp wr.w)
  have eS := rS.result_eq
  have eW := wr.run.result_eq
  match rS.holds, wr.run.holds with
  | isFalse _, _ => [("the step run satisfies its compiled circuit", false, none)]
  | _, isFalse _ => [("the wrap run satisfies its compiled circuit", false, none)]
  | isTrue hstep, isTrue hwrap =>
      if hn : rule.prevs.size ≤ Pickles.MaxProofsVerified then
      if hmv : CircuitType.Reads rS.V (rS.result.1.2.prevs i).mustVerify true then
        let D := if kb.slots[i].self then kb.ownDomains else kb.slots[i].domains
        if hdi : (srcs i).domains kb.ownDomains.list = D.list then
        if hwi : Pickles.SlotSource.widths wNext srcs i = wr.w then
          let inp := Pickles.slotInput (kb.slots[i].width_le hw) (Pickles.constPt dummyWrapSgPt)
            (rS.result.1.2.prevs i) (rS.result.1.2.slots i) rS.result.1.2.unfs[i]
            rS.result.1.2.msgs[i]
          let ms := CircuitType.readVal rS.V inp.proofMask
          if hms : CircuitType.Reads rS.V inp.proofMask ms then
          if htie : CircuitType.Reads wr.run.V
              (inputVar (F := Fq)
                (a := Pickles.StatementPacked Pickles.StepIPARounds (Type1 Fq) Fq))
              (inp.packedAt kb.slots[i].key rS.V ms) then
            if hnw : rule.prevs.size ≤ wNext then
            let sa := CircuitType.size Fp (Vector Fp rule.inputSize)
              + CircuitType.size Fp (Vector Fp rule.publicOutput.size)
            let rk : Pickles.WrapStepRun (wr.bp + 1) wr.w wr.nc 15 Pickles.StepIPARounds
                rule.prevs.size wNext (Pickles.SlotSource.widths wNext srcs)
                (fun i => rule.prevs[i].1.size) sa wr.sh.slotWidths :=
              { Vw := wr.run.V, Vs := rS.V
                wrapStmt := inputVar (F := Fq)
                  (a := Pickles.StatementPacked Pickles.StepIPARounds (Type1 Fq) Fq)
                wrapFinalizeOut := wr.run.result.1.2.1, wrapVerifyOut := wr.run.result.1.2.2
                stepOut := rS.result.1.2, hn := hnw, hws := fun i => kb.slots[i].width_le hw
                dummySg := Pickles.constPt dummyWrapSgPt, i, hwi, ms }
            let out : WrapStepOut :=
              { branches := wr.bp + 1, w := wr.w, ncStep := wr.nc, n := rule.prevs.size, wNext
                ws := Pickles.SlotSource.widths wNext srcs, ss := fun i => rule.prevs[i].1.size, sa
                slotWidths := wr.sh.slotWidths, rk, dummy := wr.dummy, cvk := kb.slots[i].key, makes
                wrapsStep
                premise :=
                  wr.sh.lagrange f.KStep.cvk.domainLog2 = f.KStep.cvk.lagrangePoints SStep.σ m
                concl := fun hlag => by
                  obtain ⟨cp, oldsW, hc⟩ := Pickles.wrapStep_kimchiVerify
                    (n := rule.prevs.size) (wNext := wNext) (w := wr.w) (branches := wr.bp + 1)
                    (ncStep := wr.nc) (inVal := Vector Fp rule.inputSize)
                    (inVar := Vector (FVar Fp) rule.inputSize)
                    (outVar := Vector (FVar Fp) rule.publicOutput.size)
                    (outVal := Vector Fp rule.publicOutput.size)
                    (wrapSrs σW hW hh).σ kb.slots[i].key rfl SStep rfl wr.sh.keys wr.b f.KStep
                    f.hkey f.hnc wr.sh.lagrange hlag wr.run.V wr.sh.widths
                    (by rw [f.hkey]; exact wr.sh.layouts wr.b) wr.sh.pins wr.dummy
                    wr.sh.slotWidths wr.advW f.hbr f.hnz
                    (f.hkey ▸ (Pickles.Key.avoids_lagrangeRelations_iff Pickles.pastaShapeVesta
                      SStep.σ f.hnc m).mpr (by rw [← hlag]; exact f.hL))
                    kb.ownDomains.list D hn f.hww srcs (fun i => kb.slots[i].width_le hw)
                    (Pickles.constPt dummyWrapSgPt) dummyUnfN0 rS.V (replayRule rule (some vals))
                    adv
                    hwrap hstep (by have h := f.hb; rw [eW] at h; exact h) i
                    (by have h := hmv; rw [eS] at h; exact h) hdi hwi ms
                    (by have h := hms; simp only [inp] at h; rw [eS] at h; exact h)
                    (by have h := htie; simp only [inp] at h; rw [eS] at h; exact h)
                  obtain ⟨-, -, -, -, hcons, hkept, hhW, hhS, -⟩ := hc
                  refine ⟨_, cp, ⟨⟨htie, ?hW, ?hS⟩, rfl⟩, ⟨⟨htie, ?hW, ?hS⟩, ?hC,
                    wr.sh.widths[wr.b], Nat.le_of_lt_succ (wr.sh.widths[wr.b]).isLt, hkept⟩⟩
                  case hW => dsimp only [rk]; rw [eW]; exact hhW
                  case hS => dsimp only [rk]; rw [eS]; exact hhS
                  case hC => dsimp only [rk, inp]; rw [eS, eW]; exact hcons }
            [(s!"slot {i}: wrapStep_kimchiVerify's hypotheses hold", true, some out)]
            else [(s!"slot {i}: the rule's slots fit the next tag's width", false, none)]
          else [(s!"slot {i}: its wrap proof's statement is the one the slot rebuilds", false,
            none)]
          else [(s!"slot {i}: its proof mask reads", false, none)]
        else [(s!"slot {i}: its width is the wrap circuit's", false, none)]
        else [(s!"slot {i}: its candidate domains are its key's", false, none)]
      else [(s!"slot {i}: it must verify", false, none)]
      else [("the step rule's slots fit", false, none)]

/-- A step-wrap link's slot with its capstone's conclusion kept: under the slot's open premise
(`Fits`' table clause), the link emits an accumulator and consumes the olds of the wrap proof the
slot verifies (`Pickles.StepWrapRun.Emits`, `Pickles.StepWrapRun.Consumes`). With the cache keys
of that wrap proof and of the one the link's wrap circuit makes, which pair the links. -/
structure StepWrapOut where
  /-- The rule's slot count. -/
  n : ℕ
  /-- The tag's width. -/
  w : ℕ
  /-- Each slot's width. -/
  ws : Fin n → ℕ
  /-- Each slot's previous statement size. -/
  ss : Fin n → ℕ
  /-- The application state's size. -/
  sa : ℕ
  /-- The slots' step proofs' chunk count. -/
  ncs : ℕ
  /-- The wrap circuit's branch count. -/
  branches : ℕ
  /-- The wrap circuit's step proofs' chunk count. -/
  ncStep : ℕ
  /-- Each wrap slot's challenge-stack height. -/
  slotWidths : Vector (Fin (Pickles.MaxProofsVerified + 1)) w
  /-- The link's run. -/
  rk : Pickles.StepWrapRun n w ws ss sa ncs 15 Pickles.StepIPARounds branches ncStep slotWidths
  /-- The wrap circuit's padding challenges. -/
  dummy : Vector Fq 15
  /-- The slot's wrap key. -/
  cvk : Kimchi.Verifier.KimchiVK CW 1
  /-- The open premise. -/
  premise : Prop
  /-- The capstone's conclusion, as the handover reads it. -/
  concl : premise → ∃ (A : Kimchi.Verifier.Accumulator CW 15)
    (cp : Kimchi.Verifier.KimchiProof CW 1 15), rk.Emits dummy A ∧ rk.Consumes dummy cp.olds.toList
  /-- The cache key of the wrap proof the slot verifies. -/
  verifies : String × String
  /-- The cache key of the wrap proof the link's wrap circuit makes. -/
  makes : String × String
  /-- The link's slot, for the report. -/
  tag : String := ""

-- as for `wrapStepLink`: the capstone's conclusion defeats the `let`-to-`have` cleanup
set_option cleanup.letToHave false in
open CompElliptic.CurveForms.ShortWeierstrass in
/-- `Pickles.stepWrap_kimchiVerify` applied to one link: the run `rS` of a step circuit and the
run `rW` of the wrap circuit that wrapped its proof, each compiled as the capstone compiles it.
Each slot verifying a cached proof (`verifies`) must be must-verify, and a base case must not; per
slot that must verify, every hypothesis is decided on the runs and passed to the capstone, whose
statement thereby fixes what is decided. The label of the first one failing is returned. The
application's one open premise is the slot's dumped Lagrange table being its key's points
(`Fits`). -/
def stepWrapLink {ncs bp nc w : ℕ} (rule : RuleDump) (vals : Array Fp)
    (kb : StepMainConsts rule.prevs.size ncs) (hw : w ≤ Pickles.MaxProofsVerified)
    (σW : Bulletproof.SRS CW.Point) (hk : σW.k = 15) (hh : σW.h ≠ 0)
    (σS : Bulletproof.SRS CS.Point) (sh : WrapMainShapes bp w nc) (dummy : Vector Fq 15)
    (b : Fin (bp + 1))
    (adv : Pickles.StepMainAdvice rule.prevs.size w
      (Pickles.SlotSource.widths w fun i => kb.slots[i].source) 1 ncs 15 Pickles.StepIPARounds
      (Vector Fp rule.inputSize))
    (advW : Pickles.WrapMainAdvice w nc 15 Pickles.StepIPARounds (sh.slotWidths.map Fin.val).sum)
    (rS : MainRun (a := Unit) (b := Pickles.StepStatement (Pickles.UnfVal 15) Fp w) fun V =>
      Pickles.stepMainCircuit (c := Builder V (KimchiConstraint Fp)) (ncw := 1)
        (outVal := Vector Fp rule.publicOutput.size)
        (fun i => kb.slots[i].source) (fun i => kb.slots[i].width_le hw) (wrapSrs σW hk hh).σ.h
        (fopStepParams ncs) kb.ownDomains.list (Pickles.constPt dummyWrapSgPt) dummyUnfN0
        (replayRule rule (some vals)) adv)
    (rW : MainRun (a := Pickles.StatementPacked Pickles.StepIPARounds (Type1 Fq) Fq) (b := Unit)
      fun V => Pickles.wrapMainCircuit (c := Builder V (KimchiConstraint Fq))
        (Pickles.FopParams.of Bulletproof.IpaPallas.curve 1 (wrapSrs σW hk hh).σ.k
          Pickles.Linearization.fqTokens) sh.widths
        (Pickles.stepDomainLog2s sh.keys) (Pickles.stepKeyCells sh.keys) sh.pins
        sh.lagrange σS.h dummy sh.slotWidths advW)
    (verifies : Fin rule.prevs.size → Option (String × String)) (makes : String × String) :
    List (String × Bool × Option StepWrapOut) :=
  let S := wrapSrs σW hk hh
  let n := rule.prevs.size
  let srcs : Fin n → Pickles.SlotSource 1 Pickles.StepIPARounds := fun i => kb.slots[i].source
  have eS := rS.result_eq
  have eW := rW.result_eq
  match rS.holds, rW.holds with
  | isFalse _, _ => [("the step run satisfies its compiled circuit", false, none)]
  | _, isFalse _ => [("the wrap run satisfies its compiled circuit", false, none)]
  | isTrue hstep, isTrue hwrap =>
    if hb : rW.result.1.2.1.whichBranch.val rW.V = ((b : ℕ) : Fq) then
    if htie : CircuitType.Reads rS.V rS.result.1.2.out
        (Pickles.StepStatement.ofWrap rW.V rW.result.1.2.2.statement) then
    if hn : n ≤ w then
    if hbr : bp + 1 ≤ PALLAS_SCALAR_CARD then
    if hd : dummyWrapSgPt ≠ 0 then
      (List.finRange n).flatMap fun i =>
        match verifies i with
        | none =>
          if CircuitType.Reads rS.V (rS.result.1.2.prevs i).mustVerify true then
            [(s!"slot {i}: its base case is not must-verify", false, none)]
          else []
        | some key =>
        if hmv : CircuitType.Reads rS.V (rS.result.1.2.prevs i).mustVerify true then
          match hchecked : Pickles.Key.check kb.slots[i].key with
          | none => [(s!"slot {i}: its key is checked", false, none)]
          | some K =>
            have hlayout : Pickles.WrapKeyLayout K.cvk := by
              unfold Pickles.Key.check at hchecked
              split at hchecked
              · cases hchecked; exact kb.slots[i].layout
              · cases hchecked
            let m := CircuitType.size Fp (Pickles.PackedWrapStatement Pickles.StepIPARounds
              (Type1 Fp) Fp)
            if hK : 1 = Kimchi.Verifier.chunkCount S.σ.k K.cvk.domainLog2 then
            if hsize : m ≤ K.cvk.n then
            if hsmall : m ≤ 2 ^ S.σ.k then
            if hon : ∀ p ∈ ((srcs i).keyCells rS.result.1.2.vk.points).indexPoints,
                OnCurve CW.E.A CW.E.B (p.x.val rS.V, p.y.val rS.V) then
            if hread : ((srcs i).keyCells rS.result.1.2.vk.points).map (Pickles.readPt rS.V)
                = K.cvk.comms then
            if hsum : ∀ c : Fin 1, Pickles.corrSumPt (C := CW) zeroWrapStatement.packed.toList
                (srcs i).lagrange.toList c ≠ 0 then
            -- a fold over the list: a bounded `∀` over vectors of points would be decided over
            -- the curve (`Vector.instDecidableForallVectorSucc`)
            if hL : ((srcs i).lagrange.toList.all fun Ps => decide (Ps[0] ≠ 0)) then
              let jf := Fin.cast (Nat.sub_add_cancel hn) (Fin.natAdd (w - n) i)
              match hp : rW.result.1.2.1.slots[jf].pins[b] with
              -- an unpinned (side-loaded) slot is outside the corpus: no capstone applies to it
              | none => [(s!"slot {i}: its wrap slot is pinned on branch {b}", false, none)]
              | some j =>
                if hdom : Pickles.wrapDomainLog2s[j]? = some K.cvk.domainLog2 then
                let inp := Pickles.slotInput (kb.slots[i].width_le hw)
                  (Pickles.constPt dummyWrapSgPt) (rS.result.1.2.prevs i) (rS.result.1.2.slots i)
                  rS.result.1.2.unfs[i] rS.result.1.2.msgs[i]
                let ms := CircuitType.readVal rS.V inp.proofMask
                if hms : CircuitType.Reads rS.V inp.proofMask ms then
                  let rk : Pickles.StepWrapRun n w (Pickles.SlotSource.widths w srcs)
                      (fun i => rule.prevs[i].1.size) _ ncs 15 Pickles.StepIPARounds (bp + 1) nc
                      sh.slotWidths :=
                    { Vg := rS.V, Vs := rW.V, stepOut := rS.result.1.2
                      hws := fun i => kb.slots[i].width_le hw, dummySg := dummyWrapSgPt, i, hn, hw
                      ms, wrapStmt := inputVar (F := Fq)
                        (a := Pickles.StatementPacked Pickles.StepIPARounds (Type1 Fq) Fq)
                      wrapFinalizeOut := rW.result.1.2.1, wrapVerifyOut := rW.result.1.2.2 }
                  let out : StepWrapOut :=
                    { n := _, w := _, ws := _, ss := _, sa := _, ncs := _, branches := _
                      ncStep := _, slotWidths := _, rk, dummy, cvk := K.cvk
                      verifies := key, makes
                      premise := (srcs i).lagrange = K.cvk.lagrangePoints S.σ m
                      concl := fun hTs => by
                        obtain ⟨cp, ms', hc⟩ := Pickles.stepWrap_kimchiVerify
                          (outVal := Vector Fp rule.publicOutput.size) S rfl
                            (fopStepParams ncs) kb.ownDomains.list
                            hn hw dummyWrapSgPt hd dummyUnfN0 srcs
                            (fun i => kb.slots[i].width_le hw) rS.V (replayRule rule (some vals))
                            adv rW.V sh.widths σS sh.lagrange sh.keys
                            sh.pins
                            dummy sh.slotWidths advW hbr b hstep
                            hwrap (by have h := hb; rw [eW] at h; exact h)
                            (by have h := htie; rw [eS, eW] at h; exact h) i
                            (by have h := hmv; rw [eS] at h; exact h) K hK hlayout ⟨hsize, hTs⟩
                            (by
                              have h := Pickles.KeyReads.of_readPt hon hread
                              rw [eS] at h; exact h)
                            (fun inp' msg => (Pickles.avoids_stepRelationsAt_iff S.σ K hK
                              (inp'.statement msg) hsmall hsize).mpr
                              ⟨fun c => by
                                rw [Pickles.corrSumPt_packed_congr _ zeroWrapStatement, ← hTs]
                                exact hsum c,
                               by
                                rw [← hTs]
                                intro Ps hPs c
                                rw [Fin.fin_one_eq_zero c]
                                exact of_decide_eq_true (List.all_eq_true.mp hL Ps hPs)⟩)
                            j (by have h := hp; rw [eW] at h; exact h) hdom
                        obtain ⟨-, -, -, hcons, hhS, hhW, -⟩ := hc
                        refine ⟨_, cp, ⟨⟨htie, ?_, ?_⟩, rfl⟩, ⟨⟨htie, ?_, ?_⟩, ?_, hms⟩⟩ <;>
                          dsimp only [rk, inp] <;> (try rw [eS]) <;> (try rw [eW]) <;> assumption }
                  [(s!"slot {i}: stepWrap_kimchiVerify's hypotheses hold", true, some out)]
                else [(s!"slot {i}: its proof mask reads", false, none)]
                else [(s!"slot {i}: its wrap slot is pinned at its key's domain", false, none)]
            else [(s!"slot {i}: its Lagrange bases are finite", false, none)]
            else [(s!"slot {i}: its correction sum is finite", false, none)]
            else [(s!"slot {i}: its key cells read as its key", false, none)]
            else [(s!"slot {i}: its key cells lie on the curve", false, none)]
            else [(s!"slot {i}: its packed statement fits the SRS", false, none)]
            else [(s!"slot {i}: its packed statement fits its key's domain", false, none)]
            else [(s!"slot {i}: its key runs at one chunk", false, none)]
        else [(s!"slot {i}: it must verify", false, none)]
    else [("the dummy sg is finite", false, none)]
    else [("the wrap circuit's branches fit the scalar field", false, none)]
    else [("the rule's slots fit the tag's width", false, none)]
    else [("the step statement reads as the wrap circuit's", false, none)]
    else [("the wrap circuit's branch index reads its branch", false, none)]

/-- The handover between two adjacent step-wrap links: `l2`'s slot verifies the wrap proof `l1`'s
wrap circuit makes. `Pickles.StepWrapRun.mem_olds_or_collision` is applied to `l1`'s emission,
`l2`'s consumption and their meeting (`StepWrapRun.Hands`, decided on the two runs): under both
links' open premises, what `l1` emits is an old accumulator of the wrap proof `l2` verifies,
unless Poseidon collides. The label of the first failing hypothesis is returned. -/
def stepWrapGlue (l1 l2 : StepWrapOut) : String × Bool :=
  if hd : l2.dummy = l1.dummy then
  if hH : CircuitType.Reads l1.rk.Vs l1.rk.wrapStmt
        (l2.rk.inp.packedAt l2.cvk l2.rk.Vg l2.rk.ms) ∧
      l2.ws l2.rk.i = l1.w ∧
      (∃ k ≤ l1.w, ∀ (j : ℕ) (hj : j < l2.ws l2.rk.i), l2.rk.ms[j] = decide (l1.w - k ≤ j)) ∧
      l2.ss l2.rk.i = l1.sa then
    have _ : l1.premise → l2.premise →
        ∃ (A : Kimchi.Verifier.Accumulator CW 15) (cp : Kimchi.Verifier.KimchiProof CW 1 15),
          A ∈ cp.olds.toList ∨ l1.rk.WrapCollision l2.rk l1.dummy ∨
            l1.rk.StepCollision l2.rk l2.cvk := fun h1 h2 =>
      have ⟨A, _, he, _⟩ := l1.concl h1
      have ⟨_, cp, _, hc⟩ := l2.concl h2
      ⟨A, cp, Pickles.StepWrapRun.mem_olds_or_collision l1.rk l2.rk l2.cvk l1.dummy A cp he
        (hd ▸ hc) hH⟩
    ("the handover holds", true)
  else ("the links meet (`StepWrapRun.Hands`)", false)
  else ("the two wrap circuits pad alike", false)

/-- The handover between two adjacent wrap-step links `rk` and `rk1`: `rk1`'s wrap circuit verifies
the step proof `rk`'s step circuit makes. `Pickles.WrapStepRun.mem_olds_or_collision` is applied to
`rk`'s emission, `rk1`'s consumption and their meeting (`WrapStepRun.Hands`, decided on the two
runs): under both links' open premises, what `rk` emits is an old accumulator of the step proof
`rk1` verifies, unless Poseidon collides. The label of the first failing hypothesis is returned. -/
def wrapStepGlueAt {branches w ncStep n wNext sa : ℕ} {ws ss : Fin n → ℕ}
    {slotWidths : Vector (Fin (Pickles.MaxProofsVerified + 1)) w}
    {branches' ncStep' n' wNext' sa' : ℕ} {ws' ss' : Fin n' → ℕ}
    {slotWidths' : Vector (Fin (Pickles.MaxProofsVerified + 1)) wNext}
    (rk : Pickles.WrapStepRun branches w ncStep 15 Pickles.StepIPARounds n wNext ws ss sa
      slotWidths)
    (rk1 : Pickles.WrapStepRun branches' wNext ncStep' 15 Pickles.StepIPARounds n' wNext' ws' ss'
      sa' slotWidths')
    (cvk cvk1 : Kimchi.Verifier.KimchiVK CW 1) (dummy dummy1 : Vector Fq 15) (p p1 : Prop)
    (c : p → ∃ (A : Kimchi.Verifier.Accumulator CS Pickles.StepIPARounds)
      (cp : Kimchi.Verifier.KimchiProof CS ncStep Pickles.StepIPARounds),
      rk.Emits cvk dummy A ∧ rk.Consumes cvk dummy cp.olds.toList)
    (c1 : p1 → ∃ (A : Kimchi.Verifier.Accumulator CS Pickles.StepIPARounds)
      (cp : Kimchi.Verifier.KimchiProof CS ncStep' Pickles.StepIPARounds),
      rk1.Emits cvk1 dummy1 A ∧ rk1.Consumes cvk1 dummy1 cp.olds.toList) : String × Bool :=
  if hd : dummy1 = dummy then
  if hH : CircuitType.Reads rk.Vs rk.stepOut.out
      (Pickles.StepStatement.ofWrap rk1.Vw rk1.wrapVerifyOut.statement) ∧ ss' rk1.i = sa then
    have _ : p → p1 →
        ∃ (A : Kimchi.Verifier.Accumulator CS Pickles.StepIPARounds)
          (cp : Kimchi.Verifier.KimchiProof CS ncStep' Pickles.StepIPARounds),
          A ∈ cp.olds.toList ∨ rk.WrapCollision rk1 dummy ∨ rk.StepCollision rk1 cvk1 :=
      fun h h1 =>
        have ⟨A, _, he, _⟩ := c h
        have ⟨_, cp, _, hc⟩ := c1 h1
        ⟨A, cp, Pickles.WrapStepRun.mem_olds_or_collision rk rk1 cvk cvk1 dummy A cp he
          (hd ▸ hc) hH⟩
    ("the handover holds", true)
  else ("the links meet (`WrapStepRun.Hands`)", false)
  else ("the two wrap circuits pad alike", false)

/-- `wrapStepGlueAt` once the second link's wrap circuit is seen to be at the first's next width,
the index the handover shares between them. -/
def wrapStepGlueCast {branches w ncStep n wNext sa : ℕ} {ws ss : Fin n → ℕ}
    {slotWidths : Vector (Fin (Pickles.MaxProofsVerified + 1)) w}
    (rk : Pickles.WrapStepRun branches w ncStep 15 Pickles.StepIPARounds n wNext ws ss sa
      slotWidths)
    (cvk : Kimchi.Verifier.KimchiVK CW 1) (dummy : Vector Fq 15) (p : Prop)
    (c : p → ∃ (A : Kimchi.Verifier.Accumulator CS Pickles.StepIPARounds)
      (cp : Kimchi.Verifier.KimchiProof CS ncStep Pickles.StepIPARounds),
      rk.Emits cvk dummy A ∧ rk.Consumes cvk dummy cp.olds.toList)
    {branches' w' ncStep' n' wNext' sa' : ℕ} {ws' ss' : Fin n' → ℕ}
    {slotWidths' : Vector (Fin (Pickles.MaxProofsVerified + 1)) w'}
    (rk1 : Pickles.WrapStepRun branches' w' ncStep' 15 Pickles.StepIPARounds n' wNext' ws' ss'
      sa' slotWidths')
    (cvk1 : Kimchi.Verifier.KimchiVK CW 1) (dummy1 : Vector Fq 15) (p1 : Prop)
    (c1 : p1 → ∃ (A : Kimchi.Verifier.Accumulator CS Pickles.StepIPARounds)
      (cp : Kimchi.Verifier.KimchiProof CS ncStep' Pickles.StepIPARounds),
      rk1.Emits cvk1 dummy1 A ∧ rk1.Consumes cvk1 dummy1 cp.olds.toList)
    (hw : w' = wNext) : String × Bool := by
  subst hw
  exact wrapStepGlueAt rk rk1 cvk cvk1 dummy dummy1 p p1 c c1

/-- `wrapStepGlueAt` on two packed links. -/
def wrapStepGlue (l1 l2 : WrapStepOut) : String × Bool :=
  if hw : l2.w = l1.wNext then
    wrapStepGlueCast l1.rk l1.cvk l1.dummy l1.premise l1.concl l2.rk l2.cvk l2.dummy l2.premise
      l2.concl hw
  else ("the second link's wrap circuit is at the first's next width", false)

/-- The links of one tag: per cached step proof of each branch, the step circuit at its advice
and the wrap circuit at the wrap proof that wrapped it, as jobs, each through the prover and its
table decided against its system; per such pair, `stepWrapLink` on the two runs, to apply once
the jobs are done; and the cache keys of the proofs they cover. -/
def linkJobs (ctx : VerdictCtx) {σW : Bulletproof.SRS CW.Point} (hW : σW.k = 15)
    (hh : σW.h ≠ 0) {σS : Bulletproof.SRS CS.Point} (hS : σS.k = Pickles.StepIPARounds)
    (hhS : σS.h ≠ 0) (wrapRuns : IO.Ref (List ((String × String) × WrapRun σW hW hh σS)))
    (stepWrapOuts : IO.Ref (Array StepWrapOut)) (wrapStepOuts : IO.Ref (Array WrapStepOut))
    (name : String) (j : Json) (wraps : Array (Cache.Entry CW)) (steps : Array (Cache.Entry CS)) :
    IO (Array (IO Bool) × Array (IO Bool) × List (String × String)) := do
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
  let mut links : Array (IO Bool) := #[]
  let mut covered : List (String × String) := []
  for (bj, b) in branches.toList.zipIdx do
    let rule ← ex (RuleDump.ofJson (← ex (bj.getObjVal? "rule")))
    let n := rule.prevs.size
    let stepMainJ ← ex (bj.getObjVal? "stepMain")
    let ncs ← ex (slotChunks stepMainJ)
    let kb ← ex (stepMainOf n w ncs stepMainJ)
    let some stepKey := k.keys[b]? | throw (IO.userError s!"{name}: no step key for branch {b}")
    let some pins := k.pins[b]? | throw (IO.userError s!"{name}: no pins for branch {b}")
    let hb' : PLift (b < bp + 1) ←
      if h : b < bp + 1 then pure (PLift.up h)
      else throw (IO.userError s!"{name}: branch {b} of {bp + 1}")
    have hb := hb'.down
    let digest := toString stepKey.digest.val
    for S0 in steps.filter (·.vkDigest = digest) do
      let tag := s!"{name} branch {b} step {S0.publicInputKey.take 12}…"
      let exT {α : Type} (e : Except String α) : IO α := IO.ofExcept (e.mapError (s!"{tag}: " ++ ·))
      covered := (S0.vkDigest, S0.publicInputKey) :: covered
      let prevs ← exT (stepPrevsOf n wraps steps S0)
      let some vals := S0.rule.map (·.values) | throw (IO.userError s!"{tag}: no rule witness")
      unless vals.size = rule.allocated do
        throw (IO.userError s!"{tag}: {vals.size} witness values, the rule allocates \
          {rule.allocated}")
      let adv ← exT (stepMainAdviceOf w kb rule.inputSize wrapKey S0 prevs)
      let stepRun ← IO.mkRef none
      jobs := jobs.push do
        let t0 ← IO.monoMsNow
        let r ← runMain fpSide (b := Pickles.StepStatement (Pickles.UnfVal 15) Fp w)
          (fun V => Pickles.stepMainCircuit (c := Builder V (KimchiConstraint Fp)) (ncw := 1)
            (outVal := Vector Fp rule.publicOutput.size) (fun i => kb.slots[i].source)
            (fun i => kb.slots[i].width_le hw) (wrapSrs σW hW hh).σ.h (fopStepParams ncs)
            kb.ownDomains.list (Pickles.constPt dummyWrapSgPt) dummyUnfN0
            (replayRule rule (some vals)) adv) ()
        stepRun.set (some r)
        let concl ← stepConclusions ctx hw kb r.V r.result.1.2 S0 prevs
        verdict s!"{tag}: step circuit" r S0.publicInput concl ((← IO.monoMsNow) - t0)
      let some W0 := wraps.find? (·.step = some (S0.vkDigest, S0.publicInputKey))
        | throw (IO.userError s!"{tag}: no wrap proof wraps it")
      covered := (W0.vkDigest, W0.publicInputKey) :: covered
      let wprevs ← exT (wrapPrevsOf w pins W0 prevs)
      let advW ← exT (wrapMainAdviceOf nc b sh.slotWidths pad k.dummy S0 wprevs)
      let inp ← exT (wrapInputOf W0)
      let wrapRun ← IO.mkRef none
      jobs := jobs.push do
        let t0 ← IO.monoMsNow
        let r ← runMain fqSide (a := Pickles.StatementPacked Pickles.StepIPARounds (Type1 Fq) Fq)
          (b := Unit)
          (fun V => Pickles.wrapMainCircuit (c := Builder V (KimchiConstraint Fq))
            (Pickles.FopParams.of Bulletproof.IpaPallas.curve 1 (wrapSrs σW hW hh).σ.k
              Pickles.Linearization.fqTokens) sh.widths
            (Pickles.stepDomainLog2s sh.keys) (Pickles.stepKeyCells sh.keys) sh.pins sh.lagrange
            σS.h k.dummy sh.slotWidths advW) inp
        wrapRun.set (some r)
        wrapRuns.modify (((W0.vkDigest, W0.publicInputKey),
          { bp, w, nc, sh, dummy := k.dummy, b := ⟨b, hb⟩, advW, run := r }) :: ·)
        let concl ← wrapConclusions ctx b sh.keys kb r.V r.result.1.2.1 r.result.1.2.2 S0 W0
          prevs
        verdict s!"{tag}: wrap circuit" r W0.publicInput concl ((← IO.monoMsNow) - t0)
      links := links.push do
        let (some rS, some rW) := (← stepRun.get, ← wrapRun.get)
          | IO.println s!"✗ {tag}: stepWrap_kimchiVerify: a run failed"; return false
        let hyps := stepWrapLink rule vals kb hw σW hW hh σS sh k.dummy ⟨b, hb⟩ adv advW rS rW
          (fun i => match prevs[i] with
            | .proof W _ => some (W.vkDigest, W.publicInputKey)
            | .baseCase _ => none)
          (W0.vkDigest, W0.publicInputKey)
        let failed := hyps.filter (!·.2.1)
        stepWrapOuts.modify (· ++ (hyps.filterMap (·.2.2)).toArray.map fun o =>
          { o with tag := s!"{tag} slot {o.rk.i}" })
        IO.println s!"{if failed.isEmpty then "✓" else "✗"} {tag}: stepWrap_kimchiVerify applies \
          ({hyps.length - failed.length}/{hyps.length} slots)"
        for (label, _, _) in failed do IO.println s!"    ✗ {label}"
        return failed.isEmpty
      -- each slot verifying a cached wrap proof, with that proof's wrap run, of any tag
      for i in List.finRange n do
        let .proof W S' := prevs[i] | continue
        links := links.push do
          let some rS ← stepRun.get
            | IO.println s!"✗ {tag}: slot {i}: wrapStep_kimchiVerify: the step run failed"
              return false
          let some wr := (← wrapRuns.get).lookup (W.vkDigest, W.publicInputKey)
            | IO.println s!"✗ {tag}: slot {i}: wrapStep_kimchiVerify: no wrap run of its proof"
              return false
          let hyps : List (String × Bool × Option WrapStepOut) :=
            match wrapRunFacts hS hhS wr with
            | .error label => [(label, false, none)]
            | .ok f =>
              if h : ncs = wr.nc then
                by
                  subst h
                  exact wrapStepLink hS hhS wr rule vals kb hw adv rS f i
                    (S0.vkDigest, S0.publicInputKey) (S'.vkDigest, S'.publicInputKey)
              else [(s!"its step proofs' chunk count is the wrap circuit's", false, none)]
          let failed := hyps.filter (!·.2.1)
          wrapStepOuts.modify (· ++ (hyps.filterMap (·.2.2)).toArray.map fun o =>
            { o with tag := s!"{tag} slot {i}" })
          IO.println s!"{if failed.isEmpty then "✓" else "✗"} {tag}: slot {i}: \
            wrapStep_kimchiVerify applies ({hyps.length - failed.length}/{hyps.length})"
          for (label, _, _) in failed do IO.println s!"    ✗ {label}"
          return failed.isEmpty
  return (jobs, links, covered)

/-- Every link of the apps `apps` under `dir`, run on `nJobs` workers against the apps' proof
caches under `cacheDir`; every cached proof must be covered and every run pass its `verdict`. -/
def runLinks (dir cacheDir : System.FilePath) (apps : List String) (nJobs : ℕ) : IO Unit := do
  let ctx : VerdictCtx :=
    { pallas := ← IO.mkRef [], vesta := ← IO.mkRef [], pallasKeys := ← IO.mkRef []
      vestaKeys := ← IO.mkRef [], memo := ← Memo.new }
  -- both SRSes, and every Lagrange memo the proofs read, built before the pool, so no two
  -- workers compute one
  let ⟨σW, hW⟩ ← srsAtK CW "pallas" pallasBase.sqrt? ctx.pallas 15
  let ⟨σS, hS⟩ ← srsAtK CS "vesta" vestaBase.sqrt? ctx.vesta 16
  let hh' : PLift (σW.h ≠ 0 ∧ σS.h ≠ 0) ←
    if h : σW.h ≠ 0 ∧ σS.h ≠ 0 then pure (PLift.up h)
    else throw (IO.userError "an SRS's blinding base is the identity")
  have hh := hh'.down
  let wrapRuns ← IO.mkRef []
  let stepWrapOuts ← IO.mkRef #[]
  let wrapStepOuts ← IO.mkRef #[]
  let caches ← apps.mapM fun app => do
    let raw ← IO.FS.readFile (cacheDir / s!"{app}.json")
    let (wraps, _) ← IO.ofExcept (Cache.parseFile CW fqSide.endo pallasBase.sqrt? raw)
    let (steps, _) ← IO.ofExcept (Cache.parseFile CS fpSide.endo vestaBase.sqrt? raw)
    return (app, wraps, steps)
  let t0 ← IO.monoMsNow
  let mut warmed : List String := []
  for (_, wraps, steps) in caches do
    for e in wraps do
      let ⟨nc, _, _⟩ ← IO.ofExcept (e.checked σW.k)
      let key := s!"pallas/{e.vk.domainLog2}/{nc}/{e.vk.publicCount}"
      unless key ∈ warmed do
        let _ ← basisFor CW "pallas" σW nc e
        warmed := key :: warmed
    for e in steps do
      let ⟨nc, _, _⟩ ← IO.ofExcept (e.checked σS.k)
      let key := s!"vesta/{e.vk.domainLog2}/{nc}/{e.vk.publicCount}"
      unless key ∈ warmed do
        let _ ← basisFor CS "vesta" σS nc e
        warmed := key :: warmed
  IO.println s!"warm-up: {warmed.length} Lagrange memos in {(← IO.monoMsNow) - t0} ms"
  (← IO.getStdout).flush
  let mut jobs : Array (IO Bool) := #[]
  let mut links : Array (IO Bool) := #[]
  let mut uncovered := 0
  for (app, wraps, steps) in caches do
    let mut covered : List (String × String) := []
    for tag in (← (dir / app).readDir).qsort (·.fileName < ·.fileName) do
      unless tag.path.extension == some "json" do continue
      let (js, ls, cs) ← linkJobs ctx hW hh.1 hS hh.2 wrapRuns stepWrapOuts wrapStepOuts
        s!"{app}/{tag.path.fileStem.getD tag.fileName}"
        (← IO.ofExcept (Json.parse (← IO.FS.readFile tag.path))) wraps steps
      jobs := jobs ++ js
      links := links ++ ls
      covered := cs ++ covered
    let keys := (wraps.map fun e => (e.vkDigest, e.publicInputKey)) ++
      (steps.map fun e => (e.vkDigest, e.publicInputKey))
    for (d, pi) in keys.toList.filter (· ∉ covered) do
      uncovered := uncovered + 1
      IO.println s!"✗ {app}: the cached proof {d.take 12}…/{pi.take 12}… is in no link"
  IO.println s!"{jobs.size} run(s) on {nJobs} worker(s)"
  (← IO.getStdout).flush
  let oks ← runPool nJobs jobs
  -- each step run and the wrap run that wrapped it, through the capstone
  let mut linked : Array Bool := #[]
  for l in links do
    linked := linked.push (← try l catch e => do IO.println s!"✗ {e}"; pure false)
    (← IO.getStdout).flush
  -- the handover between adjacent step-wrap links
  let mut pairs := 0
  let outs ← stepWrapOuts.get
  for l2 in outs do
    for l1 in outs.filter (·.makes == l2.verifies) do
      let (label, ok) := stepWrapGlue l1 l2
      IO.println s!"{if ok then "✓" else "✗"} {l1.tag} → {l2.tag}: \
        StepWrapRun.mem_olds_or_collision: {label}"
      linked := linked.push ok
      pairs := pairs + 1
    (← IO.getStdout).flush
  -- the handover between adjacent wrap-step links
  let outs ← wrapStepOuts.get
  for l2 in outs do
    for l1 in outs.filter (·.makes == l2.wrapsStep) do
      let (label, ok) := wrapStepGlue l1 l2
      IO.println s!"{if ok then "✓" else "✗"} {l1.tag} → {l2.tag}: \
        WrapStepRun.mem_olds_or_collision: {label}"
      linked := linked.push ok
      pairs := pairs + 1
    (← IO.getStdout).flush
  unless uncovered = 0 && oks.all id && linked.all id do
    throw (IO.userError s!"links FAILED ({oks.toList.count false} run(s), \
      {linked.toList.count false} link(s), {uncovered} uncovered)")
  IO.println s!"✓ {jobs.size} run(s): every compiled system holds under its prover's valuation, \
    every table satisfies its system, every public input is its cached proof's, every check \
    against the cache holds; {links.size} link(s) through stepWrap_kimchiVerify and \
    wrapStep_kimchiVerify; {pairs} adjacent pair(s) through the handover theorems"

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
          pure (if ← a.path.isDir then some a.fileName else none)
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
