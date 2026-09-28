import Pickles.StepSlot
import Pickles.VerifyOne

/-!
# The step circuit

Transcribed from `Pickles/Step/Main.purs`: the step circuit of a rule whose `n` previous proofs
are all proofs of the same system (self slots), each verifying `w` accumulators. It allocates the
public input, runs the rule, allocates this system's wrap key, every slot's witness, the
unfinalized proofs and the wrap-side messages, verifies each slot (`verifyOneBy`), asserts every
verdict, and hashes the step-side messages. Its output is the step statement: the unfinalized
proofs, the digest, the wrap-side messages, the first and last padded in front to the tag's
width `w` when the rule verifies fewer proofs.

The rule is an arbitrary circuit: it receives the public input and returns, per slot, the
previous proof's statement and whether it must verify, with its own public output.

## Main definitions

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

/-- The step statement's shifted claims, at the step field. -/
abbrev StepSf : Type := Type2 (SplitField (FVar Fp) (BoolVar Fp))

/-- One slot's witness cells: `w` accumulators, the wrap proof at `ncw` chunks with its opening
at `k` rounds, the previous step proof at `ncs` chunks with its challenges at `ks`. -/
abbrev SlotVar (w ncw ncs k ks : ℕ) : Type :=
  SlotWitness w ncw ncs k ks (FVar Fp) (BoolVar Fp) StepSf (PallasPt (FVar Fp))

/-- One slot's witness values. -/
abbrev SlotVal (w ncw ncs k ks : ℕ) : Type :=
  SlotWitness w ncw ncs k ks Fp Bool (Type2 (SplitField Fp Bool)) (PallasPt Fp)

/-- One unfinalized entry's cells, at `k` rounds. -/
abbrev UnfVar (k : ℕ) : Type := AllocUnfinalized k (FVar Fp) (BoolVar Fp) StepSf

/-- One unfinalized entry's values. -/
abbrev UnfVal (k : ℕ) : Type := AllocUnfinalized k Fp Bool (Type2 (SplitField Fp Bool))

/-- The step statement's cells at the tag's `w` slots, in wire order: the unfinalized entries,
the step-message digest, the wrap-side messages. -/
abbrev StmtVar (k w : ℕ) : Type := Vector (UnfVar k) w × FVar Fp × Vector (FVar Fp) w

/-- The step statement's values, in wire order. -/
abbrev StmtVal (k w : ℕ) : Type := Vector (UnfVal k) w × Fp × Vector Fp w

/-- What the rule returns for one slot: the previous proof's statement, as field cells, and
whether it must verify. -/
structure PrevStatement where
  /-- The previous proof's statement. -/
  appState : List (FVar Fp)
  /-- Whether the slot must verify. -/
  mustVerify : BoolVar Fp

/-- The prover's values for every allocation of the step circuit. -/
structure StepMainAdvice (n w ncw ncs k ks : ℕ) (inVal : Type) where
  /-- The public input. -/
  publicInput : AsProver Fp inVal
  /-- This system's wrap key. -/
  vk : AsProver Fp (VkComms ncw (PallasPt Fp))
  /-- Every slot's witness. -/
  slots : AsProver Fp (Vector (SlotVal w ncw ncs k ks) n)
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
  branchData := ⟨s.branch.domainLog2, #v[s.branch.mask0, s.branch.mask1]⟩
  messagesForNextWrapProof := msg
  evals := s.evals.toChunked
  proofMask := (#v[s.branch.mask0, s.branch.mask1].drop (2 - w)).cast
    (by simp only [MaxProofsVerified] at hw; omega)
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
structure StepMainOut (n w ncw ncs k ks : ℕ) where
  /-- The step statement: the unfinalized entries, the digest, the wrap-side messages. -/
  out : StmtVar k w
  /-- What the rule returned for each slot. -/
  prevs : Vector PrevStatement n
  /-- This system's wrap key. -/
  vk : VkComms ncw (PallasPt (FVar Fp))
  /-- Every slot's witness. -/
  slots : Vector (SlotVar w ncw ncs k ks) n
  /-- The unfinalized proofs. -/
  unfs : Vector (UnfVar k) n
  /-- The wrap-side messages. -/
  msgs : Vector (FVar Fp) n

variable {c : Type} [BasicSystem Fp c] [KimchiSystem Fp c]

/-- The step circuit of a rule with `n` self slots, each verifying `w` accumulators, over wrap
proofs at `ncw` chunks and the step proofs they verified at `ncs`. `verify` checks one wrap
proof (`verifyProofWith` at this system's wrap key); `P`, `domains` are the finalize's
parameters and candidate domains. The statement is the unfinalized proofs' cells, the
step-message digest, the wrap-side messages, each front-padded to the tag's `w` slots: `w − n`
constant `dummyUnf` entries and `w − n` fresh message cells. The cells it was read from are
returned beside it. -/
def stepMain {n w ncw ncs k ks : ℕ} {inVal inVar : Type} [CircuitType Fp inVal inVar]
    [CheckedType Fp c inVal inVar] (hw : w ≤ MaxProofsVerified)
    (verify : SpongeVar Fp → BoolVar Fp →
      WrapStatement ks (FVar Fp) (BoolVar Fp) (Type1 (FVar Fp)) →
      UnfinalizedProof k (FVar Fp) (BoolVar Fp) StepSf →
      IvpInput k ncw (FVar Fp) (BoolVar Fp) StepSf → CircuitM Fp c (BoolVar Fp))
    (P : FopParams Fp) (domains : List (KnownDomain Fp)) (dummySg : AffinePoint (FVar Fp))
    (dummyUnf : UnfVal k)
    (rule : inVar → CircuitM Fp c (Vector PrevStatement n × List (FVar Fp)))
    (adv : StepMainAdvice n w ncw ncs k ks inVal) :
    CircuitM Fp c (StepMainOut n w ncw ncs k ks) := do
  let publicInput ← witness (val := inVal) adv.publicInput
  let (prevs, publicOutput) ← rule publicInput
  let vk ← witness (val := VkComms ncw (PallasPt Fp)) adv.vk
  let slots ← witness (val := UnChecked (Vector (SlotVal w ncw ncs k ks) n))
    (UnChecked.mk <$> adv.slots)
  slots.val.toList.forM SlotWitness.check
  let unfs ← witness (val := Vector (UnfVal k) n) adv.unfinalized
  let msgs ← witness (val := Vector Fp n) adv.msgs
  let msgsPad ← witness (val := Vector Fp (w - n)) adv.msgsPad
  let results ← (List.finRange n).mapM fun i =>
    verifyOneBy verify P domains vk.points
      (slotInput hw dummySg prevs[i] slots.val[i] unfs[i] msgs[i])
  assertAll (results.map (·.2))
  let appFields := (CircuitType.varToFields (F := Fp) (val := inVal) publicInput).toList ++
    publicOutput
  let proofs := (List.finRange n).zip results |>.map fun (i, r) =>
    (slots.val[i].sg.pt, r.1.expandedChallenges)
  let digest ← hashMessagesForNextStepProof IpaPallas.curve.sponge.params vk.points appFields
    proofs
  -- the first `w − n` slots are padding
  let unfsW := Vector.ofFn fun j : Fin w => if h : j.val < w - n
    then CircuitType.constVar (F := Fp) (var := UnfVar k) dummyUnf
    else unfs[j.val - (w - n)]'(by omega)
  let msgsW := Vector.ofFn fun j : Fin w =>
    if h : j.val < w - n then msgsPad[j.val] else msgs[j.val - (w - n)]'(by omega)
  pure ⟨(unfsW, digest, msgsW), prevs, vk, slots.val, unfs, msgs⟩

/-- The step circuit as a circuit of its statement: no input cells (the `Unit` argument is
`Snarky.compile`'s empty input), the output `stepMain`'s statement. -/
@[nolint unusedArguments]
def stepMainCircuit {n w ncw ncs k ks : ℕ} {inVal inVar : Type} [CircuitType Fp inVal inVar]
    [CheckedType Fp c inVal inVar] (hw : w ≤ MaxProofsVerified)
    (verify : SpongeVar Fp → BoolVar Fp →
      WrapStatement ks (FVar Fp) (BoolVar Fp) (Type1 (FVar Fp)) →
      UnfinalizedProof k (FVar Fp) (BoolVar Fp) StepSf →
      IvpInput k ncw (FVar Fp) (BoolVar Fp) StepSf → CircuitM Fp c (BoolVar Fp))
    (P : FopParams Fp) (domains : List (KnownDomain Fp)) (dummySg : AffinePoint (FVar Fp))
    (dummyUnf : UnfVal k)
    (rule : inVar → CircuitM Fp c (Vector PrevStatement n × List (FVar Fp)))
    (adv : StepMainAdvice n w ncw ncs k ks inVal) (_ : Unit) :
    CircuitM Fp c (StmtVar k w) :=
  StepMainOut.out <$> stepMain hw verify P domains dummySg dummyUnf rule adv

/-- The compiled step circuit's rows contain `stepMain`'s, built from the first variable: the
statement has no input cells, so the body starts there. -/
theorem mem_compile_stepMainCircuit {n w ncw ncs k ks : ℕ} {inVal inVar : Type}
    [CircuitType Fp inVal inVar] {V : Valuation Fp}
    [CheckedType Fp (Builder V (KimchiConstraint Fp)) inVal inVar] (hw : w ≤ MaxProofsVerified)
    (verify : SpongeVar Fp → BoolVar Fp →
      WrapStatement ks (FVar Fp) (BoolVar Fp) (Type1 (FVar Fp)) →
      UnfinalizedProof k (FVar Fp) (BoolVar Fp) StepSf →
      IvpInput k ncw (FVar Fp) (BoolVar Fp) StepSf →
      CircuitM Fp (Builder V (KimchiConstraint Fp)) (BoolVar Fp))
    (P : FopParams Fp) (domains : List (KnownDomain Fp)) (dummySg : AffinePoint (FVar Fp))
    (dummyUnf : UnfVal k)
    (rule : inVar →
      CircuitM Fp (Builder V (KimchiConstraint Fp)) (Vector PrevStatement n × List (FVar Fp)))
    (adv : StepMainAdvice n w ncw ncs k ks inVal) {con : KimchiConstraint Fp}
    (h : con ∈ (build (stepMain hw verify P domains dummySg dummyUnf rule adv) 0).constraints) :
    con ∈ (compile (a := Unit) (b := StmtVal k w)
      (stepMainCircuit hw verify P domains dummySg dummyUnf rule adv)).constraints := by
  refine mem_compile_of_mem_body ?_
  unfold stepMainCircuit
  erw [build_bind]
  exact List.mem_append_left _ h

/-! ## The read -/

section Reads

open Std.Do

variable {V : Valuation Fp}

/-- The step statement has `w · (k + 17) + 1 + w` cells: `k + 17` per entry, the digest, one
message per slot. -/
theorem StmtVal.size (k w : ℕ) : CircuitType.size Fp (StmtVal k w) = w * (k + 17) + 1 + w := by
  have h1 : CircuitType.size Fp Fp = 1 := rfl
  have h2 : CircuitType.size Fp (Type2 (SplitField Fp Bool)) = 2 := rfl
  have hb : CircuitType.size Fp Bool = 1 := rfl
  have hu : CircuitType.size Fp (UnfVal k) = k + 17 := by
    unfold CircuitType.size
    dsimp only [instAllocUnfinalizedCircuitType, CircuitType.ofEquiv]
    simp [h1, h2, hb]
    omega
  simp [hu, h1]
  ring

/-- The step statement's unfinalized entries are the circuit's, front-padded to `w` with the
constant `dummyUnf`. -/
theorem stepMain_out {n w ncw ncs k ks : ℕ} {inVal inVar : Type} [CircuitType Fp inVal inVar]
    [CheckedType Fp (Builder V (KimchiConstraint Fp)) inVal inVar] (hw : w ≤ MaxProofsVerified)
    (verify : SpongeVar Fp → BoolVar Fp →
      WrapStatement ks (FVar Fp) (BoolVar Fp) (Type1 (FVar Fp)) →
      UnfinalizedProof k (FVar Fp) (BoolVar Fp) StepSf →
      IvpInput k ncw (FVar Fp) (BoolVar Fp) StepSf →
      CircuitM Fp (Builder V (KimchiConstraint Fp)) (BoolVar Fp))
    (P : FopParams Fp) (domains : List (KnownDomain Fp)) (dummySg : AffinePoint (FVar Fp))
    (dummyUnf : UnfVal k)
    (rule : inVar →
      CircuitM Fp (Builder V (KimchiConstraint Fp)) (Vector PrevStatement n × List (FVar Fp)))
    (adv : StepMainAdvice n w ncw ncs k ks inVal) :
    ⦃⌜True⌝⦄
    stepMain hw verify P domains dummySg dummyUnf rule adv
    ⦃⇓ r _ => ⌜r.out.1 = Vector.ofFn fun j : Fin w => if h : j.val < w - n
      then CircuitType.constVar (F := Fp) (var := UnfVar k) dummyUnf
      else r.unfs[j.val - (w - n)]'(by omega)⌝⦄ := by
  have hrule := fun x => builder_spec_true (rule x)
  have hfm := fun (l : List (SlotVar w ncw ncs k ks)) => builder_spec_true
    (l.forM (SlotWitness.check (c := Builder V (KimchiConstraint Fp))))
  have hmap := fun (f : Fin n → CircuitM Fp (Builder V (KimchiConstraint Fp))
      (FopOutput Fp × BoolVar Fp)) => builder_spec_true ((List.finRange n).mapM f)
  have hall := fun bs => builder_spec_true
    (assertAll (c := Builder V (KimchiConstraint Fp)) bs)
  have hhash := fun (p : Poseidon.Params Fp) (vk : VkComms ncw (AffinePoint (FVar Fp))) a pr =>
    builder_spec_true
      (hashMessagesForNextStepProof (c := Builder V (KimchiConstraint Fp)) p vk a pr)
  simp only [stepMain]
  mvcgen [hrule, hfm, hmap, hall, hhash, -Snarky.assertAll_spec]

/-- A list related entrywise to `finRange n` has length `n`, and its entry at `j` is related
to `j`. -/
private theorem forall₂_finRange {α : Type} {R : α → Fin n → Prop} {l : List α}
    (h : List.Forall₂ R l ((List.finRange n).map id)) :
    ∃ hlen : l.length = n, ∀ j : Fin n, R (l[j.val]'(hlen ▸ j.isLt)) j := by
  have hlen : l.length = n := by simpa using h.length_eq
  refine ⟨hlen, fun j => ?_⟩
  have := (List.forall₂_iff_get.mp h).2 j.val (hlen ▸ j.isLt) (by simp)
  simpa using this

/-- A slot's kept mask cells are its branch data's mask cells: when those read as bits, the
kept ones read as some mask. -/
private theorem slotInput_mask_reads {w ncw ncs k ks : ℕ} (hw : w ≤ MaxProofsVerified)
    (dummySg : AffinePoint (FVar Fp)) (prev : PrevStatement) {s : SlotVar w ncw ncs k ks}
    (u : UnfVar k) (msg : FVar Fp)
    (h0 : ∃ b : Bool, (↑s.branch.mask0 : CVar Fp).val V = bit b)
    (h1 : ∃ b : Bool, (↑s.branch.mask1 : CVar Fp).val V = bit b) :
    ∃ ms : Vector Bool w,
      CircuitType.Reads V (slotInput hw dummySg prev s u msg).proofMask ms := by
  refine CircuitType.exists_reads_vector fun j hj => ?_
  have hb : (slotInput hw dummySg prev s u msg).proofMask[j]
      ∈ (slotInput hw dummySg prev s u msg).proofMask.toList := by simp
  generalize (slotInput hw dummySg prev s u msg).proofMask[j] = b at hb ⊢
  simp only [slotInput, Vector.toList_cast, Vector.toList_drop] at hb
  have hb' : b = s.branch.mask0 ∨ b = s.branch.mask1 := by
    simpa using List.mem_of_mem_drop hb
  rcases hb' with rfl | rfl
  · obtain ⟨bb, h⟩ := h0
    exact ⟨bb, CircuitType.reads_boolVar.mpr h⟩
  · obtain ⟨bb, h⟩ := h1
    exact ⟨bb, CircuitType.reads_boolVar.mpr h⟩

/-- **The step circuit's slots read as their proofs' halves.** For any rule, under a valuation
satisfying the emitted constraints, every slot the rule marks must-verify has its unfinalized
entry's `shouldFinalize` set, satisfies `SlotReads` (the group half accepts any wrap proof its
cells read as, at the slot's statement carrying the step-message digest) and `S`, any property
the slot's `verifyOneBy` establishes of an accepted slot (`ScalarReads` at a step key whose
finalize constants are `P`, `domains`). The rule is opaque; the slots' parity bits, mask bits
and verdicts are bits by their allocation checks. -/
theorem stepMain_reads {n w ncw ncs ks : ℕ} {inVal inVar : Type} [CircuitType Fp inVal inVar]
    [CheckedType Fp (Builder V (KimchiConstraint Fp)) inVal inVar]
    (E : Env IpaPallas.curve ncw) (P : FopParams Fp) (domains : List (KnownDomain Fp))
    (hks : MaxProofsVerified * ks < 2 ^ 128)
    -- what the slot's finalize establishes of an accepted slot
    (S : VerifyOneInput ks E.σ.k ncw ncs w → Prop)
    (hS : ∀ (vk : VkComms ncw (AffinePoint (FVar Fp))) (inp : VerifyOneInput ks E.σ.k ncw ncs w),
      ⦃⌜True⌝⦄ verifyOneBy (c := Builder V (KimchiConstraint Fp)) (verifyProofAt E) P domains vk
        inp
      ⦃⇓ o _ => ⌜(∃ ms : Vector Bool w, CircuitType.Reads V inp.proofMask ms) →
        CircuitType.Reads V inp.mustVerify true → (↑o.2 : CVar Fp).val V = 1 → S inp⌝⦄)
    (hn : n ≤ MaxProofsVerified) (hw : w ≤ MaxProofsVerified) (dummySg : AffinePoint (FVar Fp))
    (dummyUnf : UnfVal E.σ.k)
    (rule : inVar →
      CircuitM Fp (Builder V (KimchiConstraint Fp)) (Vector PrevStatement n × List (FVar Fp)))
    (adv : StepMainAdvice n w ncw ncs E.σ.k ks inVal)
    -- the statement's shape against the SRS
    (hsmall : ∀ (inp : VerifyOneInput ks E.σ.k ncw ncs w) msg,
      (inp.statement msg).packed.length ≤ 2 ^ E.σ.k)
    (havoid : ∀ (inp : VerifyOneInput ks E.σ.k ncw ncs w) msg,
      E.σ.Avoids (stepRelationsAt E (inp.statement msg))) :
    ⦃⌜True⌝⦄
    stepMain (c := Builder V (KimchiConstraint Fp)) hw (verifyProofAt E)
      P domains dummySg dummyUnf rule adv
    ⦃⇓ r _ => ⌜∀ i : Fin n, CircuitType.Reads V r.prevs[i].mustVerify true →
      CircuitType.Reads V r.unfs[i].shouldFinalize true ∧
      (slotInput hw dummySg r.prevs[i] r.slots[i] r.unfs[i] r.msgs[i]).SlotReads E V
        r.vk.points ∧
      S (slotInput hw dummySg r.prevs[i] r.slots[i] r.unfs[i] r.msgs[i]) ∧
      SlotWitness.PointsOnCurve V r.slots[i] ∧
      (∃ ms : Vector Bool w, CircuitType.Reads V
        (slotInput hw dummySg r.prevs[i] r.slots[i] r.unfs[i] r.msgs[i]).proofMask ms) ∧
      ∃ (d : ℕ) (ms : Vector Bool MaxProofsVerified), d < 2 ^ 16 ∧
        (slotInput hw dummySg r.prevs[i] r.slots[i] r.unfs[i] r.msgs[i]).branchData.domainLog2.val V
          = (d : Fp) ∧
        CircuitType.Reads V
          (slotInput hw dummySg r.prevs[i] r.slots[i] r.unfs[i]
            r.msgs[i]).branchData.proofsVerifiedMask
          ms⌝⦄ := by
  have hinj := castInj128_of_lt PALLAS_BASE_CARD (by decide)
  have hrule := fun x => builder_spec_true (rule x)
  have hfm := forM_spec (V := V) (c := KimchiConstraint Fp)
    (SlotWitness.check (c := Builder V (KimchiConstraint Fp)) (w := w) (ncw := ncw) (ncs := ncs)
      (k := E.σ.k) (ks := ks))
    (fun s => (∃ b : Bool, (↑s.z1.val.sOdd : CVar Fp).val V = bit b) ∧
      (∃ b : Bool, (↑s.z2.val.sOdd : CVar Fp).val V = bit b) ∧
      (∃ b : Bool, (↑s.branch.mask0 : CVar Fp).val V = bit b) ∧
      (∃ b : Bool, (↑s.branch.mask1 : CVar Fp).val V = bit b) ∧
      (∃ n : ℕ, n < 2 ^ 16 ∧ s.branch.domainLog2.val V = (n : Fp)) ∧
      SlotWitness.PointsOnCurve V s)
    (fun s => SlotWitness.check_spec s)
  have hmap := fun (vk : VkComms ncw (PallasPt (FVar Fp)))
      (slots : UnChecked (Vector (SlotVar w ncw ncs E.σ.k ks) n))
      (unfs : Vector (UnfVar E.σ.k) n) (msgs : Vector (FVar Fp) n)
      (prevs : Vector PrevStatement n) =>
    builder_spec_mapM (V := V) (c := KimchiConstraint Fp)
      (fun i : Fin n => verifyOneBy (verifyProofAt E) P domains vk.points
        (slotInput hw dummySg prevs[i] slots.val[i] unfs[i] msgs[i]))
      (fun o (i : Fin n) =>
        let inp := slotInput hw dummySg prevs[i] slots.val[i] unfs[i] msgs[i]
        ((∃ bb : Bool, (↑inp.unfinalized.shouldFinalize : CVar Fp).val V = bit bb) →
          ∃ bb : Bool, (↑o.2 : CVar Fp).val V = bit bb) ∧
        (CircuitType.Reads V inp.mustVerify true → (↑o.2 : CVar Fp).val V = 1 →
          (∀ x ∈ (ivpInputOf inp.unfinalized.deferredValues (inp.sgOld.toList.map (none, ·))
            vk.points inp.proof).shifted, (stepSide V).ClaimOk x) →
          inp.SlotReads E V vk.points) ∧
        ((∃ ms : Vector Bool w, CircuitType.Reads V inp.proofMask ms) →
          CircuitType.Reads V inp.mustVerify true → (↑o.2 : CVar Fp).val V = 1 →
          S inp) ∧
        (↑inp.unfinalized.shouldFinalize : CVar Fp).val V = (↑inp.mustVerify : CVar Fp).val V)
      id
      (fun i => builder_spec_and _ _ _
        (verifyOneBy_verdict_bit (verifyProofAt E) (fun sv b st u cells =>
          verifyProofAt_success_bit E sv b st u cells) _ _ _ _)
        (builder_spec_and _ _ _
          (verifyOne_slotReads E P domains hks hw vk.points _ (hsmall _) (havoid _))
          (builder_spec_and _ _ _
            (hS vk.points _)
            (verifyOneBy_shouldFinalize (verifyProofAt E) _ _ _ _))))
      (List.finRange n)
  have hhash := fun (p : Poseidon.Params Fp) (vk : VkComms ncw (AffinePoint (FVar Fp))) a pr =>
    builder_spec_true
      (hashMessagesForNextStepProof (c := Builder V (KimchiConstraint Fp)) p vk a pr)
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
  mvcgen [hrule, hfm, hmap, hhash, hall, -Snarky.assertAll_spec]
  rename_i _ _ _ _ rout _ vk _ _ slots _ _ _ _ hcheck unfs _ hunf msgs _ _ _ _ _ results _ hres
    _ _ hassert _ _
  intro i hmv
  obtain ⟨hlen, hget⟩ := forall₂_finRange hres
  -- every unfinalized entry's check: its parity bits and its finalize flag are boolean
  have hunfPost : ∀ j : Fin n, CheckedType.post (F := Fp) (c := Builder V (KimchiConstraint Fp))
      (val := UnfVal E.σ.k) V unfs[j] := fun j => hunf _ (by simp)
  -- every verdict is a bit, so the asserted sum pins each to `1`
  have hbits : ∀ b ∈ results.map (fun x => x.2), b.toCVar.val V = 0 ∨ b.toCVar.val V = 1 := by
    intro b hb
    obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hb
    obtain ⟨jj, hjj, rfl⟩ := List.getElem_of_mem hm
    obtain ⟨hbit, -⟩ := hget ⟨jj, hlen ▸ hjj⟩
    obtain ⟨bb, hbb⟩ := hbit (hunfPost ⟨jj, hlen ▸ hjj⟩).2.2.2.2.2.2.2.2.2.2.2.2
    rw [hbb]; cases bb <;> simp [bit]
  obtain ⟨-, hacc, hsc, hsf⟩ := hget i
  have hi : i.val < results.length := by rw [hlen]; exact i.isLt
  have h1 := hassert (by simpa [hlen] using hn) hbits (results[i.val]'hi).2
    (List.mem_map.mpr ⟨_, List.getElem_mem hi, rfl⟩)
  have hz := hcheck slots.val[i] (by simp)
  have hmask := slotInput_mask_reads hw dummySg rout.1[i] unfs[i] msgs[i] hz.2.2.1 hz.2.2.2.1
  refine ⟨CircuitType.reads_boolVar.mpr (hsf.trans (CircuitType.reads_boolVar.mp hmv)),
    hacc hmv h1 fun x hx => ?_, hsc hmask hmv h1, hz.2.2.2.2.2, hmask, ?_⟩
  rotate_left
  · obtain ⟨-, -, h0, h1, hd, -⟩ := hz
    obtain ⟨m, hm, hdv⟩ := hd
    obtain ⟨b0, hb0⟩ := h0
    obtain ⟨b1, hb1⟩ := h1
    simp only [slotInput]
    refine ⟨m, #v[b0, b1], hm, hdv, CircuitType.reads_vector.mpr fun j hj => ?_⟩
    rw [CircuitType.reads_boolVar]
    match j, hj with
    | 0, _ => exact hb0
    | 1, _ => exact hb1
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
