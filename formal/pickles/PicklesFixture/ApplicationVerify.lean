import PicklesFixture.ApplicationRun
import Pickles.Application.Handover
import PicklesFixture.Premises
import PicklesFixture.Verdicts

/-!
# Application capstones on cached executions

Typed application runs are joined using the cache's predecessor references. Each checked link
applies an application verification theorem; adjacent links apply both application handover
theorems. SRS correspondence of the dumped Lagrange tables remains an explicit premise.
-/

namespace PicklesFixture.Application

open Lean Snarky Snarky.Kimchi Pickles Pickles.Application Bulletproof
open CompElliptic.Fields.Pasta Kimchi.Fixture Kimchi.Verifier

private def require (p : Prop) [Decidable p] (label : String) : IO (PLift p) :=
  if h : p then pure ⟨h⟩ else throw (IO.userError label)

private def key {C : Ipa.KimchiCurve} (p : Cache.Entry C) :=
  (p.vkDigest, p.publicInputKey)

private def Tag.source : (t : Tag) → (b : t.shape.Branch) → t.shape.Slot b → Tag
  | .chain, _, _ => .chain
  | .child, _, i => Fin.elim0 i
  | .parent, _, i => if i.val = 0 then .child else .parent
  | .chunks, _, i => Fin.elim0 i
  | .recurse, _, _ => .chunks

private theorem Tag.source_layout (t : Tag) (b : t.shape.Branch) (i : t.shape.Slot b)
    (L : Layout t.shape) (M : Layout (t.source b i).shape) :
    t.shape.sourceLayout L b i = M.export := by
  cases t <;> fin_cases b <;> fin_cases i <;> rfl

deriving instance DecidableEq for Kimchi.Verifier.KimchiVK
deriving instance DecidableEq for Kimchi.Verifier.Accumulator
deriving instance DecidableEq for MessagesForNextStepProof
deriving instance DecidableEq for MessagesForNextWrapProof
deriving instance DecidableEq for Key
deriving instance DecidableEq for KnownDomains
deriving instance DecidableEq for CircuitInterface

-- Cross-library deriving appends the owning library name to these identifiers.
attribute [nolint defsWithUnderscore] instDecidableEqKimchiVK_picklesFixture
  instDecidableEqKimchiVK_picklesFixture.decEq
attribute [nolint defsWithUnderscore] instDecidableEqAccumulator_picklesFixture
  instDecidableEqAccumulator_picklesFixture.decEq
attribute [nolint defsWithUnderscore] instDecidableEqMessagesForNextStepProof_picklesFixture
  instDecidableEqMessagesForNextStepProof_picklesFixture.decEq
attribute [nolint defsWithUnderscore] instDecidableEqMessagesForNextWrapProof_picklesFixture
  instDecidableEqMessagesForNextWrapProof_picklesFixture.decEq
attribute [nolint defsWithUnderscore] instDecidableEqKey_picklesFixture
  instDecidableEqKey_picklesFixture.decEq
attribute [nolint defsWithUnderscore] instDecidableEqKnownDomains_picklesFixture
  instDecidableEqKnownDomains_picklesFixture.decEq
attribute [nolint defsWithUnderscore] instDecidableEqCircuitInterface_picklesFixture
  instDecidableEqCircuitInterface_picklesFixture.decEq

private def sourceFor {S : Setup} {t : Tag} (consumer : Context S t)
    (branch : t.shape.Branch) (slot : t.shape.Slot branch)
    (producer : Context S (t.source branch slot)) :
    IO (PLift (SourceFor (producer.assembled.circuits S (fun _ => none))
      (consumer.assembled.circuits S (fun _ => none)) branch slot)) := do
  let ⟨hd⟩ ← require (producer.assembled.dummy = consumer.assembled.dummy)
    "application padding differs"
  have hl := t.source_layout branch slot consumer.assembled.layout producer.assembled.layout
  let ⟨hi⟩ ← require
    (hl ▸ consumer.assembled.wiring.source branch slot = producer.assembled.wiring.export)
    "slot interface differs from its declared producer"
  return ⟨⟨by simp only [Assembled.circuits, hd], by
    exact (Sigma.mk.inj_iff.mpr ⟨hl, (eqRec_heq hl _).symm.trans (heq_of_eq hi)⟩)⟩⟩

private def findContext {S : Setup} (contexts : List ((t : Tag) × Context S t)) (t : Tag) :
    IO (Context S t) := do
  for ⟨u, c⟩ in contexts do
    if h : u = t then return h ▸ c
  throw (IO.userError "missing declared source application")

private structure Pair {D : Shape} {L : Layout D} (C : Circuits D L) where
  branch : D.Branch
  link : StepWrapLink C branch
  step : Cache.Entry CS
  wrap : Cache.Entry CW
  previous : Vector StepPrev (D.slots branch)

private def pairs {S : Setup} {t : Tag} (A : Context S t) :
    IO (List (Pair (A.assembled.circuits S (fun _ => none)))) := do
  let mut result := []
  for w in ← A.wraps.get do
    let some s := (← A.steps.get).find? (fun s => key s.proof == key w.step)
      | throw (IO.userError "wrap has no application step run")
    let ⟨_⟩ ← require (w.branch = s.branch) "paired application branches differ"
    let ⟨hbranch⟩ ← require (w.run.cells.1.whichBranch.val w.run.V = (s.branch : Fq))
      "wrap execution selects another branch"
    let ⟨hpub⟩ ← require (CircuitType.Reads s.run.V s.run.cells.out
      (StepStatement.ofWrap w.run.V w.run.cells.2.statement)) "step/wrap public inputs differ"
    result := result ++ [⟨s.branch, ⟨s.run, w.run, hbranch, hpub⟩, s.proof, w.proof, s.previous⟩]
  return result

private def wrapTable {D : Shape} {L : Layout D} (C : Circuits D L) (b : D.Branch) : Prop :=
  C.stepLagrange C.wiring.backend.stepKeys[b].cvk.domainLog2 =
    C.wiring.backend.stepKeys[b].cvk.lagrangePoints C.setup.stepSrs.σ
      (CircuitType.size Fp (StepStatement (UnfVal WrapIPARounds) Fp D.width))

private def stepTable {D : Shape} {L : Layout D} (C : Circuits D L)
    (b : D.Branch) (i : D.Slot b) : Prop :=
  (C.wiring.sources b i).lagrange = (C.wiring.source b i).wrapKey.cvk.lagrangePoints
    C.setup.wrapSrs.σ (CircuitType.size Fp (PackedWrapStatement StepIPARounds (Type1 Fp) Fp))

private def wrapAssumptions {D : Shape} {L : Layout D} (C : Circuits D L) (b : D.Branch) :
    IO (PLift (wrapTable C b → WrapStepAssumptions C b)) := do
  let K := C.wiring.backend.stepKeys[b]
  let ⟨hn⟩ ← require (K.cvk.comms.indexPoints.all (fun P => decide (P ≠ 0)) = true)
    "step key has an infinite commitment"
  let ⟨hL⟩ ← require ((C.stepLagrange K.cvk.domainLog2).toList.all fun Ps =>
    (List.finRange C.wiring.backend.stepChunks).all fun c => decide (Ps[c] ≠ 0))
    "step table has an infinite commitment"
  return ⟨fun ht => ⟨ht,
    fun P hP => of_decide_eq_true (List.all_eq_true.mp hn P hP), by
      apply (Key.avoids_lagrangeRelations_iff pastaShapeVesta C.setup.stepSrs.σ
        (C.wiring.valid.stepChunks b) _).mpr
      rw [← ht]
      exact fun Ps hPs c => of_decide_eq_true (List.all_eq_true.mp
        (List.all_eq_true.mp hL Ps hPs) c (List.mem_finRange c))⟩⟩

private def stepAssumptions {D : Shape} {L : Layout D} (C : Circuits D L)
    (b : D.Branch) (i : D.Slot b) :
    IO (PLift (stepTable C b i → StepWrapAssumptions C b i)) := do
  let source := C.wiring.source b i
  let K := source.wrapKey
  let m := CircuitType.size Fp (PackedWrapStatement StepIPARounds (Type1 Fp) Fp)
  let ⟨hd⟩ ← require (C.setup.dummySg ≠ 0) "padding commitment is infinite"
  let ⟨hs⟩ ← require (m ≤ 2 ^ WrapIPARounds ∧ m ≤ K.cvk.n) "wrap statement size"
  let ⟨hL⟩ ← require ((C.wiring.sources b i).lagrange.toList.all
    fun Ps => decide (Ps[0] ≠ 0)) "wrap table has an infinite commitment"
  let ⟨hc⟩ ← require (∀ c : Fin 1, corrSumPt (C := CW) zeroWrapStatement.packed.toList
    (C.wiring.sources b i).lagrange.toList c ≠ 0) "wrap correction sum is infinite"
  return ⟨fun ht => ⟨hd, ht, fun inp msg =>
    (avoids_stepRelationsAt_iff C.setup.wrapSrs.σ K source.wrapChunks
      (inp.statement msg) hs.1 hs.2).mpr ⟨fun c => by
        rw [corrSumPt_packed_congr _ zeroWrapStatement, ← ht]
        exact hc c,
      by
        rw [← ht]
        intro Ps hPs c
        rw [Fin.fin_one_eq_zero c]
        exact of_decide_eq_true (List.all_eq_true.mp hL Ps hPs)⟩⟩⟩

private def compareProof {C : Ipa.KimchiCurve} {nc : Nat} (name : String)
    (σ : SRS C.Point) (vk : Kimchi.Verifier.KimchiVK C nc)
    (q : Kimchi.Verifier.KimchiProof C nc σ.k) (pub : Array C.ScalarField)
    (cached : Cache.Entry C) : IO Unit := do
  let (key, p) ← IO.ofExcept (cached.checkedAt σ.k nc)
  let _ ← require (vk = key ∧ pub = cached.publicInput) "application proof key/public input"
  let _ ← require (q.wComm = p.wComm ∧ q.zComm = p.zComm ∧ q.tComm = p.tComm ∧
    q.opening.lr = p.opening.lr ∧ q.opening.delta = p.opening.delta ∧
    q.opening.z1 = p.opening.z1 ∧ q.opening.z2 = p.opening.z2 ∧
    q.opening.sg = p.opening.sg ∧ q.evals = p.evals ∧ q.ftEval1 = p.ftEval1 ∧
    q.olds = p.olds) "application proof differs from cache (including ordered olds)"
  let L ← basisFor C name σ nc cached
  let .carried pe := q.pubEvals | throw (IO.userError "application reader lost public evaluations")
  let _ ← require (pe = pubEvalsWith σ vk L p pub) "application public evaluations differ"

private def keyBound {D : Shape} {L : Layout D} {C : Circuits D L} {b : D.Branch}
    (r : Pickles.Application.StepRun C b) (i : D.Slot b) : IO (PLift (r.KeyBound i)) := do
  let pts := (C.wiring.sources b i).keyCells r.cells.vk.points
  let ⟨hon⟩ ← require (∀ p ∈ pts.indexPoints,
    CompElliptic.CurveForms.ShortWeierstrass.OnCurve CW.E.A CW.E.B
      (p.x.val r.V, p.y.val r.V)) "key cells are off curve"
  let ⟨hread⟩ ← require (pts.map (readPt r.V) = (C.wiring.source b i).wrapKey.cvk.comms)
    "key cells differ from the application interface"
  return ⟨KeyReads.of_readPt hon hread⟩

private structure StepFacts {D : Shape} {L : Layout D} {C : Circuits D L} {b : D.Branch}
    (e : StepWrapLink C b) (i : D.Slot b) : Prop where
  mustVerify : CircuitType.Reads e.step.V (e.step.cells.prevs i).mustVerify true
  keyBound : e.step.KeyBound i
  assumptions : stepTable C b i → StepWrapAssumptions C b i
  accepts : stepTable C b i → kimchiVerify CW C.setup.wrapSrs.σ
    (C.wiring.source b i).wrapKey.cvk (e.proof i) (e.proofPublicInput i) = true

set_option cleanup.letToHave false in
private def checkStep {D : Shape} {L : Layout D} {C : Circuits D L} {b : D.Branch}
    (e : StepWrapLink C b) (i : D.Slot b) (cached : Cache.Entry CW) :
    IO (PLift (StepFacts e i)) := do
  let ⟨hp⟩ ← stepAssumptions C b i
  let ⟨hmv⟩ ← require (CircuitType.Reads e.step.V (e.step.cells.prevs i).mustVerify true)
    "verified application slot is not mustVerify"
  let ⟨hkey⟩ ← keyBound e.step i
  let r := e.run i (e.mask i)
  let ⟨ha⟩ ← require (accOk C.setup.wrapSrs.σ (StepWrap.emittedAccumulator r.Vg r.Vs
    r.i r.jf r.stepOut r.wrapVerifyOut r.wrapFinalizeOut) = true)
    "application wrap-proof accumulator is invalid"
  compareProof "pallas" C.setup.wrapSrs.σ (C.wiring.source b i).wrapKey.cvk
    (e.proof i) (e.proofPublicInput i) cached
  return ⟨⟨hmv, hkey, hp, fun ht => by
    obtain ⟨he, _, hv⟩ := e.verifies_proof i (hp ht) hmv hkey
    apply hv
    have hz := (congrArg (accOk C.setup.wrapSrs.σ) he.2).symm.trans ha
    simp only [accOk, decide_eq_true_eq] at hz
    exact hz⟩⟩

private structure Connection {D E : Shape} {L : Layout D} {M : Layout E}
    {A : Circuits D L} {B : Circuits E M} (a : Pair A) (b : Pair B)
    (i : E.Slot b.branch) : Prop where
  mustVerify : CircuitType.Reads b.link.step.V (b.link.step.cells.prevs i).mustVerify true
  maskReads : CircuitType.Reads b.link.step.V (b.link.step.inp i).proofMask (b.link.mask i)
  publicInput : CircuitType.Reads a.link.wrap.V wrapStatement
    ((b.link.step.inp i).packedAt A.wiring.backend.wrapKey.cvk b.link.step.V (b.link.mask i))

private def Connection.link {D E : Shape} {L : Layout D} {M : Layout E}
    {A : Circuits D L} {B : Circuits E M} {a : Pair A} {b : Pair B} {i : E.Slot b.branch}
    (c : Connection a b i) (h : SourceFor A B b.branch i) :
    WrapStepLink A B a.branch b.branch i :=
  ⟨h, a.link.wrap, b.link.step, a.link.branch, c.mustVerify, b.link.mask i,
    c.maskReads, c.publicInput⟩

private def connect {D E : Shape} {L : Layout D} {M : Layout E}
    {A : Circuits D L} {B : Circuits E M} (a : Pair A) (b : Pair B) (i : E.Slot b.branch)
    : IO (PLift (Connection a b i)) := do
  let ⟨hmv⟩ ← require (CircuitType.Reads b.link.step.V
    (b.link.step.cells.prevs i).mustVerify true) "consumer slot is not mustVerify"
  let mask := b.link.mask i
  let ⟨hm⟩ ← require (CircuitType.Reads b.link.step.V (b.link.step.inp i).proofMask mask)
    "application proof mask does not read"
  let ⟨ht⟩ ← require (CircuitType.Reads a.link.wrap.V wrapStatement
    ((b.link.step.inp i).packedAt A.wiring.backend.wrapKey.cvk b.link.step.V mask))
    "application wrap/step public inputs differ"
  return ⟨⟨hmv, hm, ht⟩⟩

private structure WrapFacts {D E : Shape} {L : Layout D} {M : Layout E}
    {A : Circuits D L} {B : Circuits E M} {a : D.Branch} {b : E.Branch} {i : E.Slot b}
    (e : WrapStepLink A B a b i) : Prop where
  assumptions : wrapTable A a → WrapStepAssumptions A a
  accepts : wrapTable A a → kimchiVerify CS A.setup.stepSrs.σ
    A.wiring.backend.stepKeys[a].cvk e.proof e.proofPublicInput = true

set_option cleanup.letToHave false in
private def checkWrap {D E : Shape} {L : Layout D} {M : Layout E}
    {A : Circuits D L} {B : Circuits E M} {a : D.Branch} {b : E.Branch} {i : E.Slot b}
    (e : WrapStepLink A B a b i) (cached : Cache.Entry CS) : IO (PLift (WrapFacts e)) := do
  let ⟨hp⟩ ← wrapAssumptions A a
  let r := e.run
  let ⟨ha⟩ ← require (accOk A.setup.stepSrs.σ (WrapStep.emittedAccumulator r.Vw r.Vs
    r.i r.wrapVerifyOut r.wrapFinalizeOut r.stepOut) = true)
    "application step-proof accumulator is invalid"
  compareProof "vesta" A.setup.stepSrs.σ A.wiring.backend.stepKeys[a].cvk
    e.proof e.proofPublicInput cached
  return ⟨⟨hp, fun ht => by
    obtain ⟨he, _, _, hv⟩ := e.verifies_proof (hp ht)
    apply hv
    have hz := (congrArg (accOk A.setup.stepSrs.σ) he.2).symm.trans ha
    simp only [accOk, decide_eq_true_eq] at hz
    exact hz⟩⟩

set_option cleanup.letToHave false in
private def checkStepHandover {D E G : Shape} {L : Layout D} {M : Layout E} {N : Layout G}
    {A : Circuits D L} {B : Circuits E M} {C : Circuits G N}
    {a : D.Branch} {b : E.Branch} {c : G.Branch} {i : E.Slot b} {j : G.Slot c}
    (e : StepProofHandover A B C a b c i j)
    (f : WrapFacts e.producer) (g : WrapFacts e.consumer) : IO Unit := do
  have _ : wrapTable A a → wrapTable B b →
      (e.sentStep = e.receivedStep ∧ e.sentWrap = e.receivedWrap ∧
        (kimchiVerify CS A.setup.stepSrs.σ A.wiring.backend.stepKeys[a].cvk
          e.producer.proof e.producer.proofPublicInput = true ∨
         AccumulatorFailure A.setup.stepSrs.σ B.wiring.backend.stepKeys[b].cvk
          e.consumer.proof e.consumer.proofPublicInput)) ∨
      e.producer.run.WrapCollision e.consumer.run A.setup.dummy ∨
      e.producer.run.StepCollision e.consumer.run B.wiring.backend.wrapKey.cvk := by
    intro hA hB
    exact e.handover_or_collision (f.assumptions hA) (g.assumptions hB)
      (by rw [e.producer.sourceFor.setup]; exact g.accepts hB)
  let _ ← require (e.sentStep = e.receivedStep ∧ e.sentWrap = e.receivedWrap)
    "application step-proof handover messages differ"

set_option cleanup.letToHave false in
private def checkWrapHandover {D E : Shape} {L : Layout D} {M : Layout E}
    {A : Circuits D L} {B : Circuits E M} {a : D.Branch} {b : E.Branch}
    {i : D.Slot a} {j : E.Slot b} (e : WrapProofHandover A B a b i j)
    (f : StepFacts e.producer i) (g : StepFacts e.consumer j) : IO Unit := do
  have _ : stepTable A a i → stepTable B b j →
      (e.sentStep = e.receivedStep ∧ e.sentWrap = e.receivedWrap ∧
        (kimchiVerify CW A.setup.wrapSrs.σ (A.wiring.source a i).wrapKey.cvk
          (e.producer.proof i) (e.producer.proofPublicInput i) = true ∨
         AccumulatorFailure A.setup.wrapSrs.σ (B.wiring.source b j).wrapKey.cvk
          (e.consumer.proof j) (e.consumer.proofPublicInput j))) ∨
      (e.producer.run i (e.producer.mask i)).WrapCollision
        (e.consumer.run j (e.consumer.mask j)) A.setup.dummy ∨
      (e.producer.run i (e.producer.mask i)).StepCollision
        (e.consumer.run j (e.consumer.mask j)) (B.wiring.source b j).wrapKey.cvk := by
    intro hA hB
    exact e.handover_or_collision (f.assumptions hA) (g.assumptions hB)
      (by rw [e.sourceFor.setup]; exact g.accepts hB)
  have _ : stepTable A a i → stepTable B b j →
      (e.producer.step.cells.messagesForNextStepProof.appState.map
          (·.val e.producer.step.V) =
        ((e.consumer.step.cells.prevs j).appState.map
          (·.val e.consumer.step.V)).cast e.sourceFor.prevSize) ∨
      (e.producer.run i (e.producer.mask i)).WrapCollision
        (e.consumer.run j (e.consumer.mask j)) A.setup.dummy ∨
      (e.producer.run i (e.producer.mask i)).StepCollision
        (e.consumer.run j (e.consumer.mask j)) (B.wiring.source b j).wrapKey.cvk := by
    intro hA hB
    exact e.appState_eq_or_collision (f.assumptions hA) (g.assumptions hB)
      (by rw [e.sourceFor.setup]; exact g.accepts hB)
  let _ ← require (e.sentStep = e.receivedStep ∧ e.sentWrap = e.receivedWrap)
    "application wrap-proof handover messages differ"

private def findPair {D : Shape} {L : Layout D} {C : Circuits D L} (ps : List (Pair C))
    (cached : Cache.Entry CW) : IO (Pair C) :=
  match ps.find? (fun p => key p.wrap == key cached) with
  | some p => pure p
  | none => throw (IO.userError "cached predecessor has no typed application run")

/-- Apply the application capstones and handovers to every selected verified slot and pair.
The only unchecked premises are the two families of SRS Lagrange-table equalities. -/
def validate {S : Setup} (contexts : List ((t : Tag) × Context S t)) : IO Unit := do
  IO.println s!"application capstones: checking {contexts.length} selected tags"
  (← IO.getStdout).flush
  let mut links := 0
  let mut stepPairs := 0
  let mut wrapPairs := 0
  let mut negatives := 0
  for ⟨t, B⟩ in contexts do
    let bs ← pairs B
    unless !bs.isEmpty do throw (IO.userError s!"{B.name}: no typed application runs")
    -- Distinct statements must not pass the public-input connection used by a link.
    for b in bs do
      for b' in bs do
        if b.step.publicInput != b'.step.publicInput then
          let _ ← require (¬ CircuitType.Reads b.link.step.V b.link.step.cells.out
            (StepStatement.ofWrap b'.link.wrap.V b'.link.wrap.cells.2.statement))
            "mismatched application statements passed the connection check"
          negatives := negatives + 1
    for b in bs do
      for i in List.finRange (t.shape.slots b.branch) do
        let .proof cached _ := b.previous[i] | continue
        let A ← findContext contexts (t.source b.branch i)
        let a ← findPair (← pairs A) cached
        let ⟨h⟩ ← sourceFor B b.branch i A
        let ⟨connection⟩ ← connect a b i
        let ab := connection.link h
        let ⟨fb⟩ ← checkStep b.link i cached
        let ⟨fab⟩ ← checkWrap ab a.step
        links := links + 2
        IO.println s!"✓ {B.name}/{b.branch.val}/{i.val}: application verification capstones; \
          reconstructed proofs match cache"
        (← IO.getStdout).flush
        for j in List.finRange ((t.source b.branch i).shape.slots a.branch) do
          let .proof older _ := a.previous[j] | continue
          let ⟨fa⟩ ← checkStep a.link j older
          let w : WrapProofHandover _ _ a.branch b.branch j i :=
            { producer := a.link, consumer := b.link, sourceFor := h
              mustVerifyProducer := fa.mustVerify, keyProducer := fa.keyBound
              mustVerifyConsumer := fb.mustVerify, keyConsumer := fb.keyBound
              middlePublicInput := ab.publicInput }
          checkWrapHandover w fa fb
          wrapPairs := wrapPairs + 1
          let P ← findContext contexts ((t.source b.branch i).source a.branch j)
          let p ← findPair (← pairs P) older
          let ⟨hp⟩ ← sourceFor A a.branch j P
          let ⟨previousConnection⟩ ← connect p a j
          let pa := previousConnection.link hp
          let ⟨fpa⟩ ← checkWrap pa p.step
          let s : StepProofHandover _ _ _ p.branch a.branch b.branch j i :=
            { producer := pa, consumer := ab, middlePublicInput := a.link.publicInput }
          checkStepHandover s fpa fab
          stepPairs := stepPairs + 1
          IO.println s!"✓ {A.name}/{a.branch.val}/{j.val} → {B.name}/{b.branch.val}/{i.val}: \
            both application handovers; both complete messages agree"
          (← IO.getStdout).flush
  let expectedLinks := 2 * (contexts.map fun c => match c.1 with
    | .chain => 3 | .parent => 4 | .recurse => 1 | .child | .chunks => 0).sum
  unless links = expectedLinks do
    throw (IO.userError s!"application verification coverage: {links}, expected {expectedLinks}")
  let expected := 2 * (contexts.countP (fun c => c.1 == .chain || c.1 == .parent))
  unless stepPairs = expected && wrapPairs = expected do
    throw (IO.userError s!"application handover coverage: {stepPairs}/{wrapPairs}, \
      expected {expected} in each direction")
  unless contexts.isEmpty || (links > 0 && (expected = 0 || negatives > 0)) do
    throw (IO.userError "application verification or negative connection coverage is empty")
  IO.println s!"✓ application capstones: {links} links, {stepPairs} step-proof and \
    {wrapPairs} wrap-proof handovers, {negatives} rejected statement mismatches; \
    conditional only on Lagrange correspondence"

end PicklesFixture.Application
