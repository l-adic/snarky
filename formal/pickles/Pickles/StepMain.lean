import Pickles.StepSlot
import Pickles.VerifyOne

/-!
# The step circuit

Transcribed from `Pickles/Step/Main.purs`: the step circuit of a rule with `n` previous proofs,
slot `i`'s from its source (`SlotSource`): a proof of this system, verified against the witnessed
wrap key, or of another compiled system, against that system's key as constants. It allocates
the public input, runs the rule, allocates this system's wrap key, every slot's witness at its
own width, the unfinalized proofs and the wrap-side messages, verifies each slot
(`verifyOneBy`), asserts every verdict, and hashes the step-side messages. Its output is the
step statement: the unfinalized proofs, the digest, the wrap-side messages, the first and last
padded in front to the tag's width `w` when the rule verifies fewer proofs.

The rule is an arbitrary circuit: it receives the public input and returns, per slot, the
previous proof's statement and whether it must verify, with its own public output.

## Main definitions

* `SlotSource`: where a slot's wrap key comes from, and what follows from it: the slot's width,
  Lagrange points, candidate step domains and key cells;
* `PrevStatement`: what the rule returns for one slot;
* `StepMainAdvice`: the prover's values for every allocation;
* `slotInput`: one slot's `verifyOneBy` input, assembled from its allocated cells;
* `stepMain`: the circuit;
* `stepMainCircuit`: the circuit as a circuit of its statement, what `Snarky.compile` takes.
-/

namespace Pickles

open Snarky Snarky.Kimchi Kimchi.Verifier Bulletproof Bulletproof.Ipa
open CompElliptic.Fields.Pasta
open scoped Kimchi

/-- One slot's witness cells: `w` accumulators, the wrap proof at `ncw` chunks with its opening
at `k` rounds, the previous step proof at `ncs` chunks with its challenges at `ks`. -/
abbrev SlotVar (w ncw ncs k ks : ℕ) : Type :=
  SlotWitness w ncw ncs k ks (FVar Fp) (BoolVar Fp) (Type2 (SplitField (FVar Fp) (BoolVar Fp)))
      (PallasPt (FVar Fp))

/-- One slot's witness values. -/
abbrev SlotVal (w ncw ncs k ks : ℕ) : Type :=
  SlotWitness w ncw ncs k ks Fp Bool (Type2 (SplitField Fp Bool)) (PallasPt Fp)

/-- The Lagrange points a slot's public-input commitment reads: one per cell of the packed wrap
statement at `ks` rounds (`PackedWrapStatement`), `ncw` chunks each. -/
abbrev SlotLagrange (ncw ks : ℕ) : Type :=
  Vector (Vector IpaPallas.curve.Point ncw)
    (CircuitType.size Fp (PackedWrapStatement ks (Type1 Fp) Fp))

/-- Where a slot's wrap key comes from: this system's, which the circuit witnesses, or another
compiled system's, which it bakes in. Either way the circuit bakes in the key's Lagrange
points. -/
inductive SlotSource (ncw ks : ℕ) where
  /-- A proof of this system: the witnessed key, whose Lagrange points are `lagrange`, at the
  tag's width and step domains. -/
  | self (lagrange : SlotLagrange ncw ks)
  /-- A proof of another compiled system: its wrap key's commitments, as constants, with its
  Lagrange points, at its width and its step domains. -/
  | external (comms : VkComms ncw IpaPallas.curve.Point) (lagrange : SlotLagrange ncw ks)
      (width : ℕ) (domains : List (KnownDomain Fp))

namespace SlotSource

variable {ncw ks : ℕ}

/-- The slot's width: the tag's `w` for a self slot. -/
@[reducible] def width (w : ℕ) : SlotSource ncw ks → ℕ
  | .self _ => w
  | .external _ _ d _ => d

/-- Every slot's width, slot `i`'s from its source. -/
abbrev widths {n : ℕ} (w : ℕ) (srcs : Fin n → SlotSource ncw ks) (i : Fin n) : ℕ :=
  (srcs i).width w

/-- The Lagrange points the slot's public-input commitment reads. -/
def lagrange : SlotSource ncw ks → SlotLagrange ncw ks
  | .self l => l
  | .external _ l _ _ => l

/-- The finalize's candidate step domains: this compile's `own` for a self slot. -/
def domains (own : List (KnownDomain Fp)) : SlotSource ncw ks → List (KnownDomain Fp)
  | .self _ => own
  | .external _ _ _ ds => ds

/-- The slot's key cells: the witnessed `vk` for a self slot, the imported commitments as
constant cells for an external one. -/
def keyCells (vk : VkComms ncw (AffinePoint (FVar Fp))) :
    SlotSource ncw ks → VkComms ncw (AffinePoint (FVar Fp))
  | .self _ => vk
  | .external comms _ _ _ => comms.map constPt

/-- A slot source fits `K`, the wrap key the slot verifies against, over the SRS `σ`: its
Lagrange points are the SRS's first on `K`'s domain, and they fit in the domain. -/
def Fits (σ : SRS IpaPallas.curve.Point) (K : KimchiVK IpaPallas.curve ncw)
    (s : SlotSource ncw ks) : Prop :=
  CircuitType.size Fp (PackedWrapStatement ks (Type1 Fp) Fp) ≤ K.n ∧
    s.lagrange = K.lagrangePoints σ _

end SlotSource

/-- What the rule returns for one slot: the previous proof's statement, as field cells, and
whether it must verify. -/
structure PrevStatement where
  /-- The previous proof's statement. -/
  appState : List (FVar Fp)
  /-- Whether the slot must verify. -/
  mustVerify : BoolVar Fp

/-- The prover's values for every allocation of the step circuit, slot `i`'s witness at width
`ws i`. -/
structure StepMainAdvice (n w : ℕ) (ws : Fin n → ℕ) (ncw ncs k ks : ℕ) (inVal : Type) where
  /-- The public input. -/
  publicInput : AsProver Fp inVal
  /-- This system's wrap key. -/
  vk : AsProver Fp (VkComms ncw (PallasPt Fp))
  /-- Every slot's witness, each at its width. -/
  slots : AsProver Fp ((i : Fin n) → SlotVal (ws i) ncw ncs k ks)
  /-- The unfinalized proofs. -/
  unfinalized : AsProver Fp (Vector (UnfVal k) n)
  /-- The wrap-side messages. -/
  msgs : AsProver Fp (Vector Fp n)
  /-- The wrap-side messages padding the statement to the tag's `w` slots. -/
  msgsPad : AsProver Fp (Vector Fp (w - n))

/-- One slot's `verifyOneBy` input from its cells: the previous statement, the witness, the
unfinalized entry and the wrap-side message; the accumulator points widened to
`MaxProofsVerified` with `dummySg` at the front, the mask trimmed to the slot's `w`. -/
def slotInput {w ncw ncs k ks : ℕ} (hw : w ≤ MaxProofsVerified) (dummySg : AffinePoint (FVar Fp))
    (prev : PrevStatement) (s : SlotVar w ncw ncs k ks) (u : UnfVar k) (msg : FVar Fp) :
    VerifyOneInput ks k ncw ncs w where
  appState := prev.appState
  deferred := ⟨⟨⟨s.alpha⟩, ⟨s.beta⟩, ⟨s.gamma⟩, ⟨s.zeta⟩, ⟨s.perm⟩, ⟨s.zetaToSrsLength⟩,
      ⟨s.zetaToDomainSize⟩⟩, ⟨s.cip⟩, ⟨s.xi⟩, s.bulletproofChallenges.map SizedF.mk, ⟨s.b⟩⟩
  spongeDigest := s.spongeDigest
  branchData := ⟨s.branch.domainLog2, s.branch.mask⟩
  messagesForNextWrapProof := msg
  evals := s.evals.toChunked
  proofMask := (s.branch.mask.drop (MaxProofsVerified - w)).cast (by omega)
  prevChallenges := s.prevChallenges
  prevSgs := s.prevSgs.map CheckedPoint.pt
  sgOld := (Vector.replicate (MaxProofsVerified - w) dummySg ++ s.prevSgs.map CheckedPoint.pt).cast
    (by omega)
  unfinalized := u.toUnfinalized
  proof := ⟨s.wComm.map (·.map CheckedPoint.pt), s.zComm.map CheckedPoint.pt,
    (s.tComm.map (·.map CheckedPoint.pt)).flatten,
    ⟨s.lr.map fun q => (q.1.pt, q.2.pt), s.z1, s.z2, s.delta.pt, s.sg.pt⟩⟩
  mustVerify := prev.mustVerify

/-- What the step circuit allocated and returns: the step statement's cells, and the cells it
read them from, so a statement about the circuit can name them. -/
structure StepMainOut (n w : ℕ) (ws : Fin n → ℕ) (ncw ncs k ks : ℕ) where
  /-- The step statement: the unfinalized entries, the digest, the wrap-side messages. -/
  out : StepStatement (UnfVar k) (FVar Fp) w
  /-- What the rule returned for each slot. -/
  prevs : Vector PrevStatement n
  /-- This system's wrap key. -/
  vk : VkComms ncw (PallasPt (FVar Fp))
  /-- Each slot's witness, at its width. -/
  slots : (i : Fin n) → SlotVar (ws i) ncw ncs k ks
  /-- The unfinalized proofs. -/
  unfs : Vector (UnfVar k) n
  /-- The wrap-side messages. -/
  msgs : Vector (FVar Fp) n
  /-- The message the statement's step-message digest hashes. -/
  messagesForNextStepProof : MessagesForNextStepProof (VkComms ncw (AffinePoint (FVar Fp)))
    (List (FVar Fp)) (Vector (AffinePoint (FVar Fp)) n) (Vector (Vector (FVar Fp) ks) n)

variable {c : Type} [BasicSystem Fp c] [KimchiSystem Fp c]

/-- The step circuit of a rule with `n` slots, slot `i` from source `srcs i`, over wrap proofs at
`ncw` chunks and the step proofs they verified at `ncs`. Slot `i`'s wrap proof is checked by
`verifyProofWith` at the blinding base `h` and its source's Lagrange points and key cells; `P` are
the finalize's parameters, `domains` this compile's candidate step domains. The statement is the
unfinalized proofs' cells, the step-message digest, the wrap-side messages, each front-padded to
the tag's `w` slots: `w − n`
constant `dummyUnf` entries and `w − n` fresh message cells. The cells it was read from are
returned beside it. -/
def stepMain [ConstraintHolds Fp c] [LawfulBasicSystem Fp c] {n w ncw ncs k ks : ℕ}
    {inVal inVar : Type} [CircuitType Fp inVal inVar] [CheckedType Fp c inVal inVar]
    [CheckedType Fp c (AllocBranchData Fp Bool) (AllocBranchData (FVar Fp) (BoolVar Fp))]
    (srcs : Fin n → SlotSource ncw ks)
    (hws : ∀ i, SlotSource.widths w srcs i ≤ MaxProofsVerified) (h : IpaPallas.curve.Point)
    (P : FopParams Fp) (domains : List (KnownDomain Fp)) (dummySg : AffinePoint (FVar Fp))
    (dummyUnf : UnfVal k)
    (rule : inVar → CircuitM Fp c (Vector PrevStatement n × List (FVar Fp)))
    (adv : StepMainAdvice n w (SlotSource.widths w srcs) ncw ncs k ks inVal) :
    CircuitM Fp c (StepMainOut n w (SlotSource.widths w srcs) ncw ncs k ks) := do
  let publicInput ← witness (val := inVal) adv.publicInput
  let (prevs, publicOutput) ← rule publicInput
  let vk ← witness (val := VkComms ncw (PallasPt Fp)) adv.vk
  let slots ← witness (val := (i : Fin n) → SlotVal (SlotSource.widths w srcs i) ncw ncs k ks)
    adv.slots
  let unfs ← witness (val := Vector (UnfVal k) n) adv.unfinalized
  let msgs ← witness (val := Vector Fp n) adv.msgs
  let msgsPad ← witness (val := Vector Fp (w - n)) adv.msgsPad
  let results ← (Vector.finRange n).mapM fun i =>
    verifyOneBy (verifyProofWith h (srcs i).lagrange) P ((srcs i).domains domains)
      ((srcs i).keyCells vk.points) (slotInput (hws i) dummySg prevs[i] (slots i) unfs[i] msgs[i])
  assertAll (results.toList.map (·.2))
  let appFields := (CircuitType.varToFields (F := Fp) (val := inVal) publicInput).toList ++
    publicOutput
  let msgNext : MessagesForNextStepProof (VkComms ncw (AffinePoint (FVar Fp))) (List (FVar Fp))
      (Vector (AffinePoint (FVar Fp)) n) (Vector (Vector (FVar Fp) ks) n) :=
    ⟨appFields, vk.points, Vector.ofFn fun i => (slots i).sg.pt,
      results.map (·.1.expandedChallenges)⟩
  let digest ← hashMessagesForNextStepProof IpaPallas.curve.sponge.params msgNext
  -- the first `w − n` slots are padding
  let unfsW := Vector.ofFn fun j : Fin w => if h : j.val < w - n
    then CircuitType.constVar (F := Fp) (var := UnfVar k) dummyUnf
    else unfs[j.val - (w - n)]'(by omega)
  let msgsW := Vector.ofFn fun j : Fin w =>
    if h : j.val < w - n then msgsPad[j.val] else msgs[j.val - (w - n)]'(by omega)
  pure ⟨⟨⟨unfsW, digest⟩, msgsW⟩, prevs, vk, slots, unfs, msgs, msgNext⟩

/-- The step circuit as a circuit of its statement: no input cells (the `Unit` argument is
`Snarky.compileWith`'s empty input), the output `stepMain`'s statement, and `stepMain`'s cells
kept beside it. -/
@[nolint unusedArguments]
def stepMainCircuit [ConstraintHolds Fp c] [LawfulBasicSystem Fp c] {n w ncw ncs k ks : ℕ}
    {inVal inVar : Type} [CircuitType Fp inVal inVar] [CheckedType Fp c inVal inVar]
    [CheckedType Fp c (AllocBranchData Fp Bool) (AllocBranchData (FVar Fp) (BoolVar Fp))]
    (srcs : Fin n → SlotSource ncw ks)
    (hws : ∀ i, SlotSource.widths w srcs i ≤ MaxProofsVerified) (h : IpaPallas.curve.Point)
    (P : FopParams Fp) (domains : List (KnownDomain Fp)) (dummySg : AffinePoint (FVar Fp))
    (dummyUnf : UnfVal k)
    (rule : inVar → CircuitM Fp c (Vector PrevStatement n × List (FVar Fp)))
    (adv : StepMainAdvice n w (SlotSource.widths w srcs) ncw ncs k ks inVal) (_ : Unit) :
    CircuitM Fp c (StepStatement (UnfVar k) (FVar Fp) w × StepMainOut n w
        (SlotSource.widths w srcs) ncw ncs k ks) :=
  (fun r => (r.out, r)) <$> stepMain srcs hws h P domains dummySg dummyUnf rule adv

/-- The compiled step circuit's rows contain `stepMain`'s, built from the first variable: the
statement has no input cells, so the body starts there. -/
theorem mem_compileWith_stepMainCircuit {n w ncw ncs k ks : ℕ} {inVal inVar : Type}
    [CircuitType Fp inVal inVar] {V : Valuation Fp}
    [CheckedType Fp (Builder V (KimchiConstraint Fp)) inVal inVar]
    (srcs : Fin n → SlotSource ncw ks)
    (hws : ∀ i, SlotSource.widths w srcs i ≤ MaxProofsVerified) (h : IpaPallas.curve.Point)
    (P : FopParams Fp) (domains : List (KnownDomain Fp)) (dummySg : AffinePoint (FVar Fp))
    (dummyUnf : UnfVal k)
    (rule : inVar →
      CircuitM Fp (Builder V (KimchiConstraint Fp)) (Vector PrevStatement n × List (FVar Fp)))
    (adv : StepMainAdvice n w (SlotSource.widths w srcs) ncw ncs k ks inVal)
    {con : KimchiConstraint Fp}
    (hc : con ∈ (build (stepMain srcs hws h P domains dummySg dummyUnf rule adv) 0).constraints) :
    con ∈ (compileWith (a := Unit) (b := StepStatement (UnfVal k) Fp w)
      (stepMainCircuit srcs hws h P domains dummySg dummyUnf rule adv)).constraints := by
  refine mem_compileWith_of_mem_body ?_
  unfold stepMainCircuit
  erw [map_eq_pure_bind, build_bind]
  exact List.mem_append_left _ hc

/-- The compiled step circuit's cells are `stepMain`'s run, built from the first variable. -/
theorem compileWith_stepMainCircuit_cells {n w ncw ncs k ks : ℕ} {inVal inVar : Type}
    [CircuitType Fp inVal inVar] {V : Valuation Fp}
    [CheckedType Fp (Builder V (KimchiConstraint Fp)) inVal inVar]
    (srcs : Fin n → SlotSource ncw ks)
    (hws : ∀ i, SlotSource.widths w srcs i ≤ MaxProofsVerified) (h : IpaPallas.curve.Point)
    (P : FopParams Fp) (domains : List (KnownDomain Fp)) (dummySg : AffinePoint (FVar Fp))
    (dummyUnf : UnfVal k)
    (rule : inVar →
      CircuitM Fp (Builder V (KimchiConstraint Fp)) (Vector PrevStatement n × List (FVar Fp)))
    (adv : StepMainAdvice n w (SlotSource.widths w srcs) ncw ncs k ks inVal) :
    (compileWith (a := Unit) (b := StepStatement (UnfVal k) Fp w)
      (stepMainCircuit srcs hws h P domains dummySg dummyUnf rule adv)).result.1.2
      = (build (stepMain srcs hws h P domains dummySg dummyUnf rule adv) 0).result := by
  rw [compileWith_result]
  unfold stepMainCircuit
  erw [map_eq_pure_bind, build_bind]
  rfl

/-! ## The read -/

section Reads

open Std.Do

variable {V : Valuation Fp}

/-- The step statement's unfinalized entries are the circuit's, front-padded to `w` with the
constant `dummyUnf`. -/
theorem stepMain_out {n w ncw ncs k ks : ℕ} {inVal inVar : Type} [CircuitType Fp inVal inVar]
    [CheckedType Fp (Builder V (KimchiConstraint Fp)) inVal inVar]
    (srcs : Fin n → SlotSource ncw ks)
    (hws : ∀ i, SlotSource.widths w srcs i ≤ MaxProofsVerified) (h : IpaPallas.curve.Point)
    (P : FopParams Fp) (domains : List (KnownDomain Fp)) (dummySg : AffinePoint (FVar Fp))
    (dummyUnf : UnfVal k)
    (rule : inVar →
      CircuitM Fp (Builder V (KimchiConstraint Fp)) (Vector PrevStatement n × List (FVar Fp)))
    (adv : StepMainAdvice n w (SlotSource.widths w srcs) ncw ncs k ks inVal) :
    ⦃⌜True⌝⦄
    stepMain srcs hws h P domains dummySg dummyUnf rule adv
    ⦃⇓ r _ => ⌜r.out.proofState.unfinalizedProofs = Vector.ofFn fun j : Fin w =>
      if h : j.val < w - n
      then CircuitType.constVar (F := Fp) (var := UnfVar k) dummyUnf
      else r.unfs[j.val - (w - n)]'(by omega)⌝⦄ := by
  have hrule := fun x => builder_spec_true (rule x)
  have hmap := fun (f : Fin n → CircuitM Fp (Builder V (KimchiConstraint Fp))
      (FopOutput Fp ks × BoolVar Fp)) => builder_spec_true ((Vector.finRange n).mapM f)
  have hall := fun bs => builder_spec_true
    (assertAll (c := Builder V (KimchiConstraint Fp)) bs)
  have hhash := fun (p : Poseidon.Params Fp) m =>
    builder_spec_true (hashMessagesForNextStepProof (c := Builder V (KimchiConstraint Fp))
      (nc := ncw) (n := n) (k := ks) p m)
  simp only [stepMain]
  mvcgen [hrule, hmap, hall, hhash, -Snarky.assertAll_spec]

/-- A slot's kept mask cells are its branch data's mask cells: when those read as bits, the
kept ones read as some mask. -/
private theorem slotInput_mask_reads {w ncw ncs k ks : ℕ} (hw : w ≤ MaxProofsVerified)
    (dummySg : AffinePoint (FVar Fp)) (prev : PrevStatement) {s : SlotVar w ncw ncs k ks}
    (u : UnfVar k) (msg : FVar Fp)
    (hm : ∀ m ∈ s.branch.mask.toList, ∃ b : Bool, (↑m : CVar Fp).val V = bit b) :
    ∃ ms : Vector Bool w,
      CircuitType.Reads V (slotInput hw dummySg prev s u msg).proofMask ms := by
  refine CircuitType.exists_reads_vector fun j hj => ?_
  have hb : (slotInput hw dummySg prev s u msg).proofMask[j]
      ∈ (slotInput hw dummySg prev s u msg).proofMask.toList := by simp
  generalize (slotInput hw dummySg prev s u msg).proofMask[j] = b at hb ⊢
  simp only [slotInput, Vector.toList_cast, Vector.toList_drop] at hb
  obtain ⟨bb, h⟩ := hm b (List.mem_of_mem_drop hb)
  exact ⟨bb, CircuitType.reads_boolVar.mpr h⟩

/-- **The step circuit's slots read as their proofs' halves.** For any rule, under a valuation
satisfying the emitted constraints, every slot the rule marks must-verify has its unfinalized
entry's `shouldFinalize` set, satisfies `Q`, any property the slot's `verifyOneBy` establishes
of an accepted slot (`ScalarReads` at a step key whose finalize constants are `P`, `domains`),
and, over the shared SRS `σ` once checked, `SlotReads` at any checked wrap key `K` that its
source fits (the group half accepts any wrap proof its cells read as, at the slot's statement
carrying the step-message digest). The rule is opaque; the slots' parity bits, mask bits and
verdicts are bits by their allocation checks. -/
theorem stepMain_reads {n w ncw ncs ks : ℕ} {inVal inVar : Type} [CircuitType Fp inVal inVar]
    [CheckedType Fp (Builder V (KimchiConstraint Fp)) inVal inVar]
    (σ : SRS IpaPallas.curve.Point) (P : FopParams Fp) (domains : List (KnownDomain Fp))
    (hks : MaxProofsVerified * ks < 2 ^ 128)
    -- each slot's source
    (srcs : Fin n → SlotSource ncw ks)
    -- what the slot's finalize establishes of an accepted slot, at its expanded challenges
    (Q : (i : Fin n) → VerifyOneInput ks σ.k ncw ncs (SlotSource.widths w srcs i) →
      Vector (FVar Fp) ks → Prop)
    (hQ : ∀ (i : Fin n) (vk : VkComms ncw (AffinePoint (FVar Fp)))
        (inp : VerifyOneInput ks σ.k ncw ncs (SlotSource.widths w srcs i)),
      ⦃⌜True⌝⦄ verifyOneBy (c := Builder V (KimchiConstraint Fp))
        (verifyProofWith σ.h (srcs i).lagrange) P ((srcs i).domains domains) vk inp
      ⦃⇓ o _ => ⌜(∃ ms : Vector Bool (SlotSource.widths w srcs i),
          CircuitType.Reads V inp.proofMask ms) →
        CircuitType.Reads V inp.mustVerify true → (↑o.2 : CVar Fp).val V = 1 →
        Q i inp o.1.expandedChallenges⌝⦄)
    (hn : n ≤ MaxProofsVerified) (hws : ∀ i, SlotSource.widths w srcs i ≤ MaxProofsVerified)
    (dummySg : AffinePoint (FVar Fp)) (dummyUnf : UnfVal σ.k)
    (rule : inVar →
      CircuitM Fp (Builder V (KimchiConstraint Fp)) (Vector PrevStatement n × List (FVar Fp)))
    (adv : StepMainAdvice n w (SlotSource.widths w srcs) ncw ncs σ.k ks inVal)
    -- the statement's shape against the SRS
    (hsmall : CircuitType.size Fp (PackedWrapStatement ks (Type1 Fp) Fp) ≤ 2 ^ σ.k) :
    ⦃⌜True⌝⦄
    stepMain (c := Builder V (KimchiConstraint Fp)) srcs hws σ.h
      P domains dummySg dummyUnf rule adv
    ⦃⇓ r _ => ⌜∀ i : Fin n, CircuitType.Reads V r.prevs[i].mustVerify true →
      CircuitType.Reads V r.unfs[i].shouldFinalize true ∧
      -- over the SRS once checked, at any key its source fits, whose statements' relations the
      -- SRS avoids
      (∀ S : Srs IpaPallas.curve, S.σ = σ →
        ∀ K : Key IpaPallas.curve ncw, ncw = chunkCount σ.k K.cvk.domainLog2 →
        (srcs i).Fits σ K.cvk →
        (∀ (inp : VerifyOneInput ks σ.k ncw ncs (SlotSource.widths w srcs i)) msg,
          σ.Avoids (stepRelationsAt σ K.cvk (inp.statement msg))) →
        (slotInput (hws i) dummySg r.prevs[i] (r.slots i) r.unfs[i] r.msgs[i]).SlotReads
          σ K.cvk V ((srcs i).keyCells r.vk.points)) ∧
      Q i (slotInput (hws i) dummySg r.prevs[i] (r.slots i) r.unfs[i] r.msgs[i])
        r.messagesForNextStepProof.oldBulletproofChallenges[i] ∧
      SlotWitness.PointsOnCurve V (r.slots i) ∧
      (∃ ms : Vector Bool (SlotSource.widths w srcs i), CircuitType.Reads V
        (slotInput (hws i) dummySg r.prevs[i] (r.slots i) r.unfs[i] r.msgs[i]).proofMask ms) ∧
      ∃ (d : ℕ) (ms : Vector Bool MaxProofsVerified), d < 2 ^ 16 ∧
        (slotInput (hws i) dummySg r.prevs[i] (r.slots i) r.unfs[i]
          r.msgs[i]).branchData.domainLog2.val V = (d : Fp) ∧
        CircuitType.Reads V
          (slotInput (hws i) dummySg r.prevs[i] (r.slots i) r.unfs[i]
            r.msgs[i]).branchData.proofsVerifiedMask
          ms⌝⦄ := by
  have hinj := castInj128_of_lt PALLAS_BASE_CARD (by decide)
  have hrule := fun x => builder_spec_true (rule x)
  -- at a key slot `i`'s source fits, its verifier is `verifyProofAt` over `σ`
  have hv : ∀ (i : Fin n) (K : KimchiVK IpaPallas.curve ncw), (srcs i).Fits σ K →
      verifyProofWith (c := Builder V (KimchiConstraint Fp)) (ks := ks) (k := σ.k)
        (np := MaxProofsVerified) σ.h
        (srcs i).lagrange = verifyProofAt σ K := by
    intro i K hfit
    funext sv b st u cells
    unfold verifyProofAt
    rw [hfit.2]
  have hmap := fun (vk : VkComms ncw (PallasPt (FVar Fp)))
      (slots : (i : Fin n) → SlotVar (SlotSource.widths w srcs i) ncw ncs σ.k ks)
      (unfs : Vector (UnfVar σ.k) n) (msgs : Vector (FVar Fp) n)
      (prevs : Vector PrevStatement n) =>
    builder_spec_vector_mapM_get (V := V) (c := KimchiConstraint Fp)
      (fun i : Fin n => verifyOneBy (verifyProofWith σ.h (srcs i).lagrange) P
        ((srcs i).domains domains) ((srcs i).keyCells vk.points)
        (slotInput (hws i) dummySg prevs[i] (slots i) unfs[i] msgs[i]))
      (fun (i : Fin n) o =>
        let inp := slotInput (hws i) dummySg prevs[i] (slots i) unfs[i] msgs[i]
        ((∃ bb : Bool, (↑inp.unfinalized.shouldFinalize : CVar Fp).val V = bit bb) →
          ∃ bb : Bool, (↑o.2 : CVar Fp).val V = bit bb) ∧
        (∀ SK : {SK : Srs IpaPallas.curve × Key IpaPallas.curve ncw //
            SK.1.σ = σ ∧ ncw = chunkCount σ.k SK.2.cvk.domainLog2},
          ((srcs i).Fits σ SK.1.2.cvk ∧
            ∀ msg, σ.Avoids (stepRelationsAt σ SK.1.2.cvk (inp.statement msg))) →
          CircuitType.Reads V inp.mustVerify true → (↑o.2 : CVar Fp).val V = 1 →
          (∀ x ∈ (ivpInputOf inp.unfinalized.deferredValues (inp.sgOld.map (none, ·))
            ((srcs i).keyCells vk.points) inp.proof).shifted, (stepSide V).ClaimOk x) →
          inp.SlotReads σ SK.1.2.cvk V ((srcs i).keyCells vk.points)) ∧
        ((∃ ms : Vector Bool (SlotSource.widths w srcs i), CircuitType.Reads V inp.proofMask ms) →
          CircuitType.Reads V inp.mustVerify true → (↑o.2 : CVar Fp).val V = 1 →
          Q i inp o.1.expandedChallenges) ∧
        (↑inp.unfinalized.shouldFinalize : CVar Fp).val V = (↑inp.mustVerify : CVar Fp).val V)
      (fun i => by
        beta_reduce
        exact builder_spec_and _ _ _
          (verifyOneBy_verdict_bit (verifyProofWith σ.h (srcs i).lagrange)
            (fun sv b st u cells =>
              verifyProofWith_success_bit σ.h (srcs i).lagrange sv b st u cells) _ _ _ _)
          (builder_spec_and _ _ _
            (builder_spec_forall _ _ _ fun SK hK => by
              obtain ⟨⟨S, K⟩, hS, hnc⟩ := SK
              subst hS
              rw [hv i K.cvk hK.1]
              exact verifyOne_slotReads S K hnc P ((srcs i).domains domains)
                hks (hws i) ((srcs i).keyCells vk.points) _ hsmall hK.1.1 hK.2)
            (builder_spec_and _ _ _
              (hQ i ((srcs i).keyCells vk.points) _)
              (verifyOneBy_shouldFinalize (verifyProofWith σ.h (srcs i).lagrange)
                _ _ _ _))))
      (Vector.finRange n)
  have hhash := fun (p : Poseidon.Params Fp) m =>
    builder_spec_true (hashMessagesForNextStepProof (c := Builder V (KimchiConstraint Fp))
      (nc := ncw) (n := n) (k := ks) p m)
  have hall : ∀ bs : List (BoolVar Fp), ⦃⌜True⌝⦄ assertAll (c := Builder V (KimchiConstraint Fp)) bs
      ⦃⇓ _ _ => ⌜bs.length ≤ MaxProofsVerified →
        (∀ b ∈ bs, (↑b : CVar Fp).val V = 0 ∨ (↑b : CVar Fp).val V = 1) →
        ∀ b ∈ bs, (↑b : CVar Fp).val V = 1⌝⦄ := fun bs => by
    rw [builder_spec_iff]
    intro nv hsat hl
    exact (builder_spec_iff _ _).mp (assertAll_spec (V := V) (c := KimchiConstraint Fp) bs
      (fun j k' hj hk h => hinj j k' (by simp only [MaxProofsVerified] at hl; omega)
        (by simp only [MaxProofsVerified] at hl; omega) h)) nv hsat
  simp only [stepMain]
  mvcgen [hrule, hmap, hhash, hall, -Snarky.assertAll_spec]
  rename_i _ _ _ _ rout _ vk _ _ slots _ hcheck unfs _ hunf msgs _ _ _ _ _ results _ _ _
    hassert _ _ hres
  intro i hmv
  have hget := fun j : Fin n => by
    have h := hres j
    rw [show (Vector.finRange n)[j] = j by simp] at h
    exact h
  -- every unfinalized entry's check: its parity bits and its finalize flag are boolean
  have hunfPost : ∀ j : Fin n, CheckedType.post (F := Fp) (c := Builder V (KimchiConstraint Fp))
      (val := UnfVal σ.k) V unfs[j] := fun j => hunf _ (by simp)
  -- every verdict is a bit, so the asserted sum pins each to `1`
  have hbits : ∀ b ∈ results.toList.map (fun x => x.2),
      b.toCVar.val V = 0 ∨ b.toCVar.val V = 1 := by
    intro b hb
    obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hb
    obtain ⟨jj, hjj, rfl⟩ := List.getElem_of_mem hm
    have hjn : jj < n := by simpa using hjj
    obtain ⟨hbit, -⟩ := hget ⟨jj, hjn⟩
    obtain ⟨bb, hbb⟩ := hbit (hunfPost ⟨jj, hjn⟩).2.2.2.2.2.2.2.2.2.2.2.2
    simp only [Vector.getElem_toList, Fin.getElem_fin] at hbb ⊢
    rw [hbb]; cases bb <;> simp [bit]
  obtain ⟨-, hacc, hsc, hsf⟩ := hget i
  have h1 := hassert (by simpa using hn) hbits results[i].2
    (List.mem_map.mpr ⟨_, Vector.mem_toList_iff.mpr (Vector.getElem_mem i.isLt), rfl⟩)
  have hz := SlotWitness.of_post ((CheckedType.post_finFamily V slots).mp hcheck i)
  have hmask := slotInput_mask_reads (hws i) dummySg rout.1[i] unfs[i] msgs[i] hz.2.2.1
  refine ⟨CircuitType.reads_boolVar.mpr (hsf.trans (CircuitType.reads_boolVar.mp hmv)),
    fun S hS K hK hfit hav => hacc ⟨(S, K), hS, hK⟩ hfit (hav _) hmv h1 fun x hx => ?_,
    by simpa only [Fin.getElem_fin, Vector.getElem_map] using hsc hmask hmv h1, hz.2.2.2.2,
    hmask, ?_⟩
  rotate_left
  · obtain ⟨-, -, hmb, ⟨m, hm, hdv⟩, -⟩ := hz
    obtain ⟨bs, hbs⟩ := CircuitType.exists_reads_vector (vs := (slots i).branch.mask) fun j hj =>
      (hmb _ (by simp)).imp fun _ h => CircuitType.reads_boolVar.mpr h
    simp only [slotInput]
    exact ⟨m, bs, hm, hdv, hbs⟩
  have hu := hunfPost i
  simp only [IvpInput.shifted, ivpInputOf, slotInput, AllocUnfinalized.toUnfinalized,
    List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact stepSide_claimOk_of_bit _ hu.2.2.2.2.1.2
  · exact stepSide_claimOk_of_bit _ hu.2.2.1.2
  · exact stepSide_claimOk_of_bit _ hu.2.2.2.1.2
  · exact stepSide_claimOk_of_bit _ hu.1.2
  · exact stepSide_claimOk_of_bit _ hu.2.1.2
  · exact stepSide_claimOk_of_bit _ hz.1
  · exact stepSide_claimOk_of_bit _ hz.2.1

end Reads

end Pickles
