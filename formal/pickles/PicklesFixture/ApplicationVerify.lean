import PicklesFixture.ApplicationRun
import Pickles.Application.Handover
import PicklesFixture.Premises
import PicklesFixture.Verdicts

/-!
# Application capstones on cached executions

Typed application runs are joined using the cache's predecessor references. Each checked link
applies an application verification theorem; adjacent links apply both application handover
theorems. Lagrange correspondence is checked against the shared SRS before applying them.
-/

namespace PicklesFixture.Application

open Lean Snarky Snarky.Kimchi Pickles Pickles.Application Bulletproof
open CompElliptic.Fields.Pasta Kimchi.Fixture Kimchi.Verifier

private def key {C : Ipa.KimchiCurve} (p : Cache.Entry C) :=
  (p.vkDigest, p.publicInputKey)

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

private def FieldSchemas.source {D : Shape} (F : FieldSchemas D)
    (b : D.Branch) (i : D.Slot b) : FieldLayoutDump :=
  match D.source b i with
  | .self => F.own
  | .external t => F.imports t

private theorem FieldSchemas.source_eq {D : Shape} (F : FieldSchemas D) (L : Layout D)
    (b : D.Branch) (i : D.Slot b) :
    (D.sourceLayout L b i).schema = fieldSchema (F.source b i) := by
  cases h : D.source b i with
  | self => simpa [Shape.sourceLayout, FieldSchemas.source, h, Layout.export] using F.own_eq
  | external t => simpa [Shape.sourceLayout, FieldSchemas.source, h] using F.imports_eq t

private theorem interface_eq {I J : LayoutInterface}
    (hs : I.schema = J.schema) (hw : I.width = J.width) : I = J := by
  cases I
  cases J
  cases hs
  cases hw
  rfl

private def sourceFor {S : Setup} {D E : Shape} (consumer : Context S E)
    (branch : E.Branch) (slot : E.Slot branch) (producer : Context S D) :
    IO (PLift (SourceFor (producer.assembled.circuits S (fun _ => none))
      (consumer.assembled.circuits S (fun _ => none)) branch slot)) := do
  let ⟨hs⟩ ← requireProof (consumer.schemas.source branch slot = producer.schemas.own)
    (IO.userError "slot statement encoding differs from its producer")
  let ⟨hw⟩ ← requireProof
    ((E.sourceLayout consumer.assembled.layout branch slot).width =
      producer.assembled.layout.export.width)
    (IO.userError "slot width differs from its producer")
  have hl : E.sourceLayout consumer.assembled.layout branch slot =
      producer.assembled.layout.export := by
    have he := (consumer.schemas.source_eq consumer.assembled.layout branch slot).trans
      ((congrArg fieldSchema hs).trans producer.schemas.own_eq.symm)
    exact interface_eq he hw
  let ⟨hi⟩ ← requireProof
    (hl ▸ consumer.assembled.wiring.source branch slot = producer.assembled.wiring.export)
    (IO.userError "slot interface differs from its declared producer")
  return ⟨⟨rfl, by
    exact (Sigma.mk.inj_iff.mpr ⟨hl, (eqRec_heq hl _).symm.trans (heq_of_eq hi)⟩)⟩⟩

private structure Pair {D : Shape} {L : Layout D} (C : Circuits D L) where
  branch : D.Branch
  link : StepWrapLink C branch
  step : Cache.Entry CS
  wrap : Cache.Entry CW
  previous : Vector StepPrev (D.slots branch)

private def pairs {S : Setup} {D : Shape} (A : Context S D) :
    IO (List (Pair (A.assembled.circuits S (fun _ => none)))) := do
  let mut result := []
  for w in ← A.wraps.get do
    let some s := (← A.steps.get).find? (fun s => key s.proof == key w.step)
      | throw (IO.userError "wrap has no application step run")
    let ⟨_⟩ ← requireProof (w.branch = s.branch)
      (IO.userError "paired application branches differ")
    let ⟨hbranch⟩ ← requireProof (w.run.cells.1.whichBranch.val w.run.V = (s.branch : Fq))
      (IO.userError "wrap execution selects another branch")
    let ⟨hpub⟩ ← requireProof (CircuitType.Reads s.run.V s.run.cells.out
      (StepStatement.ofWrap w.run.V w.run.cells.2.statement))
      (IO.userError "step/wrap public inputs differ")
    result := result ++ [⟨s.branch, ⟨s.run, w.run, hbranch, hpub⟩, s.proof, w.proof, s.previous⟩]
  return result

private abbrev wrapTable {D : Shape} {L : Layout D} (C : Circuits D L) (b : D.Branch) : Prop :=
  C.stepLagrange C.wiring.backend.stepKeys[b].cvk.domainLog2 =
    C.wiring.backend.stepKeys[b].cvk.lagrangePoints C.setup.stepSrs.σ
      (CircuitType.size Fp (StepStatement (UnfVal WrapIPARounds) Fp D.width))

private abbrev stepTable {D : Shape} {L : Layout D} (C : Circuits D L)
    (b : D.Branch) (i : D.Slot b) : Prop :=
  (C.wiring.sources b i).lagrange = (C.wiring.source b i).wrapKey.cvk.lagrangePoints
    C.setup.wrapSrs.σ (CircuitType.size Fp (PackedWrapStatement StepIPARounds (Type1 Fp) Fp))

private def wrapAssumptions {D : Shape} {L : Layout D} (C : Circuits D L) (b : D.Branch) :
    IO (PLift (WrapStepAssumptions C b)) := do
  let ⟨ht⟩ ← requireProof (wrapTable C b)
    (IO.userError "step Lagrange basis differs from the SRS")
  let K := C.wiring.backend.stepKeys[b]
  let ⟨hn⟩ ← requireProof (K.cvk.comms.indexPoints.all (fun P => decide (P ≠ 0)) = true)
    (IO.userError "step key has an infinite commitment")
  let ⟨hL⟩ ← requireProof ((C.stepLagrange K.cvk.domainLog2).toList.all fun Ps =>
    (List.finRange C.wiring.backend.stepChunks).all fun c => decide (Ps[c] ≠ 0))
    (IO.userError "step table has an infinite commitment")
  return ⟨⟨ht,
    fun P hP => of_decide_eq_true (List.all_eq_true.mp hn P hP), by
      apply (Key.avoids_lagrangeRelations_iff pastaShapeVesta C.setup.stepSrs.σ
        (C.wiring.valid.stepChunks b) _).mpr
      rw [← ht]
      exact fun Ps hPs c => of_decide_eq_true (List.all_eq_true.mp
        (List.all_eq_true.mp hL Ps hPs) c (List.mem_finRange c))⟩⟩

private def stepAssumptions {D : Shape} {L : Layout D} (C : Circuits D L)
    (b : D.Branch) (i : D.Slot b) :
    IO (PLift (StepWrapAssumptions C b i)) := do
  let ⟨ht⟩ ← requireProof (stepTable C b i)
    (IO.userError "wrap Lagrange basis differs from the SRS")
  let source := C.wiring.source b i
  let K := source.wrapKey
  let m := CircuitType.size Fp (PackedWrapStatement StepIPARounds (Type1 Fp) Fp)
  let ⟨hd⟩ ← requireProof (C.setup.dummySg ≠ 0)
    (IO.userError "padding commitment is infinite")
  let ⟨hs⟩ ← requireProof (m ≤ 2 ^ WrapIPARounds ∧ m ≤ K.cvk.n)
    (IO.userError "wrap statement size")
  let ⟨hL⟩ ← requireProof ((C.wiring.sources b i).lagrange.toList.all
    fun Ps => decide (Ps[0] ≠ 0)) (IO.userError "wrap table has an infinite commitment")
  let ⟨hc⟩ ← requireProof (∀ c : Fin 1, corrSumPt (C := CW) zeroWrapStatement.packed.toList
    (C.wiring.sources b i).lagrange.toList c ≠ 0) (IO.userError "wrap correction sum is infinite")
  return ⟨⟨hd, ht, fun inp msg =>
    (avoids_stepRelationsAt_iff C.setup.wrapSrs.σ K source.wrapChunks
      (inp.statement msg) hs.1 hs.2).mpr ⟨fun c => by
        rw [corrSumPt_packed_congr _ zeroWrapStatement, ← ht]
        exact hc c,
      by
        rw [← ht]
        intro Ps hPs c
        rw [Fin.fin_one_eq_zero c]
        exact of_decide_eq_true (List.all_eq_true.mp hL Ps hPs)⟩⟩⟩

private def Context.stepParametersAt {S : Setup} {D : Shape}
    (A : Context S D) (b : D.Branch) (i : D.Slot b) :
    IO (PLift (StepWrapAssumptions (A.assembled.circuits S (fun _ => none)) b i)) := do
  for ⟨b', i', p⟩ in ← A.stepParameters.get do
    if hb : b' = b then
      let j : D.Slot b := hb ▸ i'
      let q : PLift (StepWrapAssumptions (A.assembled.circuits S (fun _ => none)) b j) := by
        subst b'
        exact p
      if hi : j = i then return hi ▸ q
  let p ← stepAssumptions (A.assembled.circuits S (fun _ => none)) b i
  A.stepParameters.modify (⟨b, i, p⟩ :: ·)
  return p

private def Context.wrapParametersAt {S : Setup} {D : Shape}
    (A : Context S D) (b : D.Branch) :
    IO (PLift (WrapStepAssumptions (A.assembled.circuits S (fun _ => none)) b)) := do
  for ⟨b', p⟩ in ← A.wrapParameters.get do
    if hb : b' = b then return hb ▸ p
  let p ← wrapAssumptions (A.assembled.circuits S (fun _ => none)) b
  A.wrapParameters.modify (⟨b, p⟩ :: ·)
  return p

private def compareProof {C : Ipa.KimchiCurve} {nc : Nat} (name : String)
    (σ : SRS C.Point) (vk : Kimchi.Verifier.KimchiVK C nc)
    (q : Kimchi.Verifier.KimchiProof C nc σ.k) (pub : Array C.ScalarField)
    (cached : Cache.Entry C) : IO Unit := do
  let (key, p) ← IO.ofExcept (cached.checkedAt σ.k nc)
  let _ ← requireProof (vk = key ∧ pub = cached.publicInput)
    (IO.userError "application proof key/public input")
  let _ ← requireProof (q.wComm = p.wComm ∧ q.zComm = p.zComm ∧ q.tComm = p.tComm ∧
    q.opening.lr = p.opening.lr ∧ q.opening.delta = p.opening.delta ∧
    q.opening.z1 = p.opening.z1 ∧ q.opening.z2 = p.opening.z2 ∧
    q.opening.sg = p.opening.sg ∧ q.evals = p.evals ∧ q.ftEval1 = p.ftEval1 ∧
    q.olds = p.olds) (IO.userError "application proof differs from cache (including ordered olds)")
  let L ← basisFor C name σ nc cached
  let .carried pe := q.pubEvals | throw (IO.userError "application reader lost public evaluations")
  let _ ← requireProof (pe = pubEvalsWith σ vk L p pub)
    (IO.userError "application public evaluations differ")

private def keyBound {D : Shape} {L : Layout D} {C : Circuits D L} {b : D.Branch}
    (r : Pickles.Application.StepRun C b) (i : D.Slot b) : IO (PLift (r.KeyBound i)) := do
  let pts := (C.wiring.sources b i).keyCells r.cells.vk.points
  let ⟨hon⟩ ← requireProof (∀ p ∈ pts.indexPoints,
    CompElliptic.CurveForms.ShortWeierstrass.OnCurve CW.E.A CW.E.B
      (p.x.val r.V, p.y.val r.V)) (IO.userError "key cells are off curve")
  let ⟨hread⟩ ← requireProof (pts.map (readPt r.V) = (C.wiring.source b i).wrapKey.cvk.comms)
    (IO.userError "key cells differ from the application interface")
  return ⟨KeyReads.of_readPt hon hread⟩

private structure StepFacts {D : Shape} {L : Layout D} {C : Circuits D L} {b : D.Branch}
    (e : StepWrapLink C b) (i : D.Slot b) : Prop where
  mustVerify : CircuitType.Reads e.step.V (e.step.cells.prevs i).mustVerify true
  keyBound : e.step.KeyBound i
  assumptions : StepWrapAssumptions C b i
  accepts : kimchiVerify CW C.setup.wrapSrs.σ
    (C.wiring.source b i).wrapKey.cvk (e.proof i) (e.proofPublicInput i) = true

set_option cleanup.letToHave false in
private def checkStep {D : Shape} {L : Layout D} {C : Circuits D L} {b : D.Branch}
    (e : StepWrapLink C b) (i : D.Slot b) (hp : StepWrapAssumptions C b i)
    (cached : Cache.Entry CW) :
    IO (PLift (StepFacts e i)) := do
  let ⟨hmv⟩ ← requireProof (CircuitType.Reads e.step.V (e.step.cells.prevs i).mustVerify true)
    (IO.userError "verified application slot is not mustVerify")
  let ⟨hkey⟩ ← keyBound e.step i
  let r := e.run i (e.mask i)
  let ⟨ha⟩ ← requireProof (accOk C.setup.wrapSrs.σ (StepWrap.emittedAccumulator r.Vg r.Vs
    r.i r.jf r.stepOut r.wrapVerifyOut r.wrapFinalizeOut) = true)
    (IO.userError "application wrap-proof accumulator is invalid")
  compareProof "pallas" C.setup.wrapSrs.σ (C.wiring.source b i).wrapKey.cvk
    (e.proof i) (e.proofPublicInput i) cached
  return ⟨⟨hmv, hkey, hp, by
    obtain ⟨he, _, hv⟩ := e.verifies_proof i hp hmv hkey
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
  let ⟨hmv⟩ ← requireProof (CircuitType.Reads b.link.step.V
    (b.link.step.cells.prevs i).mustVerify true) (IO.userError "consumer slot is not mustVerify")
  let mask := b.link.mask i
  let ⟨hm⟩ ← requireProof (CircuitType.Reads b.link.step.V (b.link.step.inp i).proofMask mask)
    (IO.userError "application proof mask does not read")
  let ⟨ht⟩ ← requireProof (CircuitType.Reads a.link.wrap.V wrapStatement
    ((b.link.step.inp i).packedAt A.wiring.backend.wrapKey.cvk b.link.step.V mask))
    (IO.userError "application wrap/step public inputs differ")
  return ⟨⟨hmv, hm, ht⟩⟩

private structure WrapFacts {D E : Shape} {L : Layout D} {M : Layout E}
    {A : Circuits D L} {B : Circuits E M} {a : D.Branch} {b : E.Branch} {i : E.Slot b}
    (e : WrapStepLink A B a b i) : Prop where
  assumptions : WrapStepAssumptions A a
  accepts : kimchiVerify CS A.setup.stepSrs.σ
    A.wiring.backend.stepKeys[a].cvk e.proof e.proofPublicInput = true

set_option cleanup.letToHave false in
private def checkWrap {D E : Shape} {L : Layout D} {M : Layout E}
    {A : Circuits D L} {B : Circuits E M} {a : D.Branch} {b : E.Branch} {i : E.Slot b}
    (e : WrapStepLink A B a b i) (hp : WrapStepAssumptions A a)
    (cached : Cache.Entry CS) : IO (PLift (WrapFacts e)) := do
  let r := e.run
  let ⟨ha⟩ ← requireProof (accOk A.setup.stepSrs.σ (WrapStep.emittedAccumulator r.Vw r.Vs
    r.i r.wrapVerifyOut r.wrapFinalizeOut r.stepOut) = true)
    (IO.userError "application step-proof accumulator is invalid")
  compareProof "vesta" A.setup.stepSrs.σ A.wiring.backend.stepKeys[a].cvk
    e.proof e.proofPublicInput cached
  return ⟨⟨hp, by
    obtain ⟨he, _, _, hv⟩ := e.verifies_proof hp
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
  have _ :
      (e.sentStep = e.receivedStep ∧ e.sentWrap = e.receivedWrap ∧
        (kimchiVerify CS A.setup.stepSrs.σ A.wiring.backend.stepKeys[a].cvk
          e.producer.proof e.producer.proofPublicInput = true ∨
         AccumulatorFailure A.setup.stepSrs.σ B.wiring.backend.stepKeys[b].cvk
          e.consumer.proof e.consumer.proofPublicInput)) ∨
      e.producer.run.WrapCollision e.consumer.run A.setup.dummy ∨
      e.producer.run.StepCollision e.consumer.run B.wiring.backend.wrapKey.cvk := by
    exact e.handover_or_collision f.assumptions g.assumptions
      (by rw [e.producer.sourceFor.setup]; exact g.accepts)
  let _ ← requireProof (e.sentStep = e.receivedStep ∧ e.sentWrap = e.receivedWrap)
    (IO.userError "application step-proof handover messages differ")

set_option cleanup.letToHave false in
private def checkWrapHandover {D E : Shape} {L : Layout D} {M : Layout E}
    {A : Circuits D L} {B : Circuits E M} {a : D.Branch} {b : E.Branch}
    {i : D.Slot a} {j : E.Slot b} (e : WrapProofHandover A B a b i j)
    (f : StepFacts e.producer i) (g : StepFacts e.consumer j) : IO Unit := do
  have _ :
      (e.sentStep = e.receivedStep ∧ e.sentWrap = e.receivedWrap ∧
        (kimchiVerify CW A.setup.wrapSrs.σ (A.wiring.source a i).wrapKey.cvk
          (e.producer.proof i) (e.producer.proofPublicInput i) = true ∨
         AccumulatorFailure A.setup.wrapSrs.σ (B.wiring.source b j).wrapKey.cvk
          (e.consumer.proof j) (e.consumer.proofPublicInput j))) ∨
      (e.producer.run i (e.producer.mask i)).WrapCollision
        (e.consumer.run j (e.consumer.mask j)) A.setup.dummy ∨
      (e.producer.run i (e.producer.mask i)).StepCollision
        (e.consumer.run j (e.consumer.mask j)) (B.wiring.source b j).wrapKey.cvk := by
    exact e.handover_or_collision f.assumptions g.assumptions
      (by rw [e.sourceFor.setup]; exact g.accepts)
  have _ :
      (e.producer.step.cells.messagesForNextStepProof.appState.map
          (·.val e.producer.step.V) =
        ((e.consumer.step.cells.prevs j).appState.map
          (·.val e.consumer.step.V)).cast e.sourceFor.prevSize) ∨
      (e.producer.run i (e.producer.mask i)).WrapCollision
        (e.consumer.run j (e.consumer.mask j)) A.setup.dummy ∨
      (e.producer.run i (e.producer.mask i)).StepCollision
        (e.consumer.run j (e.consumer.mask j)) (B.wiring.source b j).wrapKey.cvk := by
    exact e.appState_eq_or_collision f.assumptions g.assumptions
      (by rw [e.sourceFor.setup]; exact g.accepts)
  let _ ← requireProof (e.sentStep = e.receivedStep ∧ e.sentWrap = e.receivedWrap)
    (IO.userError "application wrap-proof handover messages differ")

private def findPair {D : Shape} {L : Layout D} {C : Circuits D L} (ps : List (Pair C))
    (cached : Cache.Entry CW) : IO (Pair C) :=
  match ps.find? (fun p => key p.wrap == key cached) with
  | some p => pure p
  | none => throw (IO.userError "cached predecessor has no typed application run")

/-- What a verified slot established: the producing application, the run whose wrap proof the
slot verifies, the connection to that run, and the decided facts of both links. -/
private structure SlotFacts {S : Setup} (contexts : List ((D : Shape) × Context S D))
    {D : Shape} {B : Context S D} (b : Pair (B.assembled.circuits S fun _ => none))
    (i : D.Slot b.branch) where
  producer : Fin contexts.length
  run : Pair (contexts[producer].2.assembled.circuits S fun _ => none)
  source : SourceFor (contexts[producer].2.assembled.circuits S fun _ => none)
    (B.assembled.circuits S fun _ => none) b.branch i
  connection : Connection run b i
  step : StepFacts b.link i
  wrap : WrapFacts (connection.link source)

/-- A typed run with what each of its verified slots established. -/
private structure Node {S : Setup} (contexts : List ((D : Shape) × Context S D))
    {D : Shape} (B : Context S D) where
  pair : Pair (B.assembled.circuits S fun _ => none)
  slots : (i : D.Slot pair.branch) → Option (SlotFacts contexts pair i)

/-- A selected application's typed runs, joined once, the runs checked so far, and the counts
of its verified slots, of their adjacent pairs, of its disabled slots and of the foreign
producer interfaces its slots rejected. -/
private structure Store {S : Setup} (contexts : List ((D : Shape) × Context S D))
    {D : Shape} (B : Context S D) where
  pairs : List (Pair (B.assembled.circuits S fun _ => none))
  nodes : IO.Ref (List (Node contexts B))
  verified : IO.Ref Nat
  handovers : IO.Ref Nat
  disabled : IO.Ref Nat
  negatives : IO.Ref Nat

/-- The consumer's fixture's application whose wrap key produced `cached`: a cache holds one
fixture's runs, so a cached predecessor's producer is a tag of the same fixture. -/
private def findProducer {S : Setup} (contexts : List ((D : Shape) × Context S D))
    (fixture : String) (cached : Cache.Entry CW) : Option (Fin contexts.length) :=
  (List.finRange contexts.length).find? fun k =>
    contexts[k].2.fixture == fixture &&
      toString contexts[k].2.assembled.wiring.backend.wrapKey.cvk.digest.val == cached.vkDigest

/-- The run whose wrap proof is `cached`, each of its verified slots checked once: both
verification capstones against the cache, and both handovers against each verified slot of the
producing run, itself checked first. `fuel` bounds the chain of predecessors. -/
private def nodeOf {S : Setup} {contexts : List ((D : Shape) × Context S D)}
    (stores : (k : Fin contexts.length) → Store contexts contexts[k].2) (fuel : Nat)
    {D : Shape} {B : Context S D} (store : Store contexts B) (cached : Cache.Entry CW) :
    IO (Node contexts B) :=
  match fuel with
  | 0 => throw (IO.userError
      s!"{B.name}: a chain of cached predecessors is longer than the typed runs")
  | fuel + 1 => do
    if let some n := (← store.nodes.get).find? (fun n => key n.pair.wrap == key cached) then
      return n
    let b ← findPair store.pairs cached
    let slots ← finSequence (β := fun i => Option (SlotFacts contexts b i))
      fun i : Fin (D.slots b.branch) => do
        let .proof older _ := b.previous[i] | do
          let _ ← requireProof (CircuitType.Reads b.link.step.V
            (b.link.step.cells.prevs i).mustVerify false)
            (IO.userError "base-case slot must disable verification")
          store.disabled.modify (· + 1)
          return none
        let some k := findProducer contexts B.fixture older
          | throw (IO.userError "cached proof has no reconstructed producer")
        let A := contexts[k].2
        let n ← nodeOf stores fuel (stores k) older
        let a := n.pair
        for ⟨_, wrong⟩ in contexts do
          unless sameKey wrong.assembled.wiring.backend.wrapKey
              A.assembled.wiring.backend.wrapKey do
            let accepted ← try
              let _ ← sourceFor B b.branch i wrong
              pure true
            catch _ => pure false
            if accepted then throw (IO.userError "a slot accepted another producer interface")
            store.negatives.modify (· + 1)
        let ⟨h⟩ ← sourceFor B b.branch i A
        let ⟨connection⟩ ← connect a b i
        let ab := connection.link h
        let ⟨pb⟩ ← B.stepParametersAt b.branch i
        let ⟨fb⟩ ← checkStep b.link i pb older
        let ⟨pab⟩ ← A.wrapParametersAt a.branch
        let ⟨fab⟩ ← checkWrap ab pab a.step
        store.verified.modify (· + 1)
        IO.println s!"✓ {B.name}/{b.branch.val}/{i.val}: application verification capstones; \
          reconstructed proofs match cache"
        (← IO.getStdout).flush
        for j in List.finRange (contexts[k].1.slots a.branch) do
          let some g := n.slots j | continue
          let w : WrapProofHandover _ _ a.branch b.branch j i :=
            { producer := a.link, consumer := b.link, sourceFor := h
              mustVerifyProducer := g.step.mustVerify, keyProducer := g.step.keyBound
              mustVerifyConsumer := fb.mustVerify, keyConsumer := fb.keyBound
              middlePublicInput := ab.publicInput }
          checkWrapHandover w g.step fb
          let s : StepProofHandover _ _ _ g.run.branch a.branch b.branch j i :=
            { producer := g.connection.link g.source, consumer := ab
              middlePublicInput := a.link.publicInput }
          checkStepHandover s g.wrap fab
          store.handovers.modify (· + 1)
          IO.println s!"✓ {A.name}/{a.branch.val}/{j.val} → {B.name}/{b.branch.val}/{i.val}: \
            both application handovers; both complete messages agree"
          (← IO.getStdout).flush
        return some ⟨k, a, h, connection, fb, fab⟩
    let n : Node contexts B := ⟨b, slots⟩
    store.nodes.modify (n :: ·)
    return n

/-- Apply the application capstones and handovers to every selected verified slot and pair.
Lagrange correspondence is decided against the shared SRS. -/
def validate {S : Setup} (contexts : List ((D : Shape) × Context S D)) : IO Unit := do
  IO.println s!"application capstones: checking {contexts.length} selected tags"
  (← IO.getStdout).flush
  let mut expectedLinks := 0
  let mut expectedPairs := 0
  for ⟨_, B⟩ in contexts do
    for s in ← B.steps.get do
      expectedLinks := expectedLinks + 2 * s.proof.prevs.countP Option.isSome
      for prev in s.previous do
        if let .proof _ older := prev then
          expectedPairs := expectedPairs + older.prevs.countP Option.isSome
  let stores ← finSequence (β := fun k => Store contexts contexts[k].2) fun k => do
    let B := contexts[k].2
    let ps ← pairs B
    unless !ps.isEmpty do throw (IO.userError s!"{B.name}: no typed application runs")
    let nodes ← IO.mkRef ([] : List (Node contexts B))
    return ⟨ps, nodes, ← IO.mkRef 0, ← IO.mkRef 0, ← IO.mkRef 0, ← IO.mkRef 0⟩
  let mut negatives := 0
  for k in List.finRange contexts.length do
    -- Distinct statements must not pass the public-input connection used by a link.
    for b in (stores k).pairs do
      for b' in (stores k).pairs do
        if b.step.publicInput != b'.step.publicInput then
          let _ ← requireProof (¬ CircuitType.Reads b.link.step.V b.link.step.cells.out
            (StepStatement.ofWrap b'.link.wrap.V b'.link.wrap.cells.2.statement))
            (IO.userError "mismatched application statements passed the connection check")
          negatives := negatives + 1
  -- A chain of predecessors visits each run at most once.
  let fuel := ((List.finRange contexts.length).map fun k => (stores k).pairs.length).sum
  for k in List.finRange contexts.length do
    for b in (stores k).pairs do
      let _ ← nodeOf stores fuel (stores k) b.wrap
  let mut links := 0
  let mut handovers := 0
  let mut disabled := 0
  for k in List.finRange contexts.length do
    links := links + 2 * (← (stores k).verified.get)
    handovers := handovers + (← (stores k).handovers.get)
    disabled := disabled + (← (stores k).disabled.get)
    negatives := negatives + (← (stores k).negatives.get)
  unless links == expectedLinks && handovers == expectedPairs do
    throw (IO.userError s!"capstone coverage: {links} links and {handovers} handovers; \
      the cache requires {expectedLinks} and {expectedPairs}")
  IO.println s!"✓ application capstones: {links} links, {handovers} step-proof and \
    {handovers} wrap-proof handovers, {disabled} disabled slots, {negatives} rejected mismatches; \
    SRS Lagrange correspondence checked"

end PicklesFixture.Application
