import Pickles.StepSlot
import Pickles.VerifyOne

/-!
# The step circuit

Transcribed from `Pickles/Step/Main.purs`: the step circuit of a rule whose `n` previous proofs
are all proofs of the same system (self slots), each verifying `w` accumulators. It allocates the
public input, runs the rule, allocates this system's wrap key, every slot's witness, the
unfinalized proofs and the wrap-side messages, verifies each slot (`verifyOneBy`), asserts every
verdict, and hashes the step-side messages. Its output is the step statement: the unfinalized
proofs, the digest, the wrap-side messages.

The rule is an arbitrary circuit: it receives the public input and returns, per slot, the
previous proof's statement and whether it must verify, with its own public output.

## Main definitions

* `PrevStatement`: what the rule returns for one slot;
* `StepMainAdvice`: the prover's values for every allocation;
* `slotInput`: one slot's `verifyOne` input, assembled from its allocated cells;
* `stepMain`: the circuit.
-/

namespace Pickles

open Snarky Snarky.Kimchi Kimchi.Verifier Bulletproof Bulletproof.Ipa
open CompElliptic.Fields.Pasta
open scoped Kimchi

/-- The step statement's shifted claims, at the step field. -/
abbrev StepSf : Type := Type2 (SplitField (FVar Fp) (BoolVar Fp))

/-- One slot's witness cells: `w` accumulators, the previous step proof at `nc` chunks, the
wrap proof's opening at `k` rounds, the step proof's challenges at `ks`. -/
abbrev SlotVar (w nc k ks : ℕ) : Type :=
  SlotWitness w nc k ks (FVar Fp) (BoolVar Fp) StepSf (PallasPt (FVar Fp))

/-- One slot's witness values. -/
abbrev SlotVal (w nc k ks : ℕ) : Type :=
  SlotWitness w nc k ks Fp Bool (Type2 (SplitField Fp Bool)) (PallasPt Fp)

/-- One unfinalized entry's cells, at `k` rounds. -/
abbrev UnfVar (k : ℕ) : Type := AllocUnfinalized k (FVar Fp) (BoolVar Fp) StepSf

/-- One unfinalized entry's values. -/
abbrev UnfVal (k : ℕ) : Type := AllocUnfinalized k Fp Bool (Type2 (SplitField Fp Bool))

/-- What the rule returns for one slot: the previous proof's statement, as field cells, and
whether it must verify. -/
structure PrevStatement where
  /-- The previous proof's statement. -/
  appState : List (FVar Fp)
  /-- Whether the slot must verify. -/
  mustVerify : BoolVar Fp

/-- The prover's values for every allocation of the step circuit. -/
structure StepMainAdvice (n w nc k ks : ℕ) (inVal : Type) where
  /-- The public input. -/
  publicInput : AsProver Fp inVal
  /-- This system's wrap key. -/
  vk : AsProver Fp (VkComms nc (PallasPt Fp))
  /-- Every slot's witness. -/
  slots : AsProver Fp (Vector (SlotVal w nc k ks) n)
  /-- The unfinalized proofs. -/
  unfinalized : AsProver Fp (Vector (UnfVal k) n)
  /-- The wrap-side messages. -/
  msgs : AsProver Fp (Vector Fp n)

/-- One slot's `verifyOne` input from its cells: the previous statement, the witness, the
unfinalized entry and the wrap-side message; the accumulator points widened to
`MaxProofsVerified` with `dummySg` at the front, the mask trimmed to the slot's `w`. -/
def slotInput {w nc k ks : ℕ} (hw : w ≤ MaxProofsVerified) (dummySg : AffinePoint (FVar Fp))
    (prev : PrevStatement) (s : SlotVar w nc k ks) (u : UnfVar k) (msg : FVar Fp) :
    VerifyOneInput ks k nc w where
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
structure StepMainOut (n w nc k ks : ℕ) where
  /-- The step statement: the unfinalized proofs' cells, the digest, the wrap-side messages. -/
  out : List (FVar Fp)
  /-- What the rule returned for each slot. -/
  prevs : Vector PrevStatement n
  /-- This system's wrap key. -/
  vk : VkComms nc (PallasPt (FVar Fp))
  /-- Every slot's witness. -/
  slots : Vector (SlotVar w nc k ks) n
  /-- The unfinalized proofs. -/
  unfs : Vector (UnfVar k) n
  /-- The wrap-side messages. -/
  msgs : Vector (FVar Fp) n

variable {c : Type} [BasicSystem Fp c] [KimchiSystem Fp c]

/-- The step circuit of a rule with `n` self slots, each verifying `w` accumulators, over a
previous step proof at `nc` chunks. `verify` checks one wrap proof (`verifyProofWith` at this
system's wrap key); `P`, `domains` are the finalize's parameters and candidate domains. The
statement is the unfinalized proofs' cells, the step-message digest, the wrap-side messages;
the cells it was read from are returned beside it. -/
def stepMain {n w nc k ks : ℕ} {inVal inVar : Type} [CircuitType Fp inVal inVar]
    [CheckedType Fp c inVal inVar] (hw : w ≤ MaxProofsVerified)
    (verify : SpongeVar Fp → BoolVar Fp →
      WrapStatement ks (FVar Fp) (BoolVar Fp) (Type1 (FVar Fp)) →
      UnfinalizedProof k (FVar Fp) (BoolVar Fp) StepSf →
      IvpInput k nc (FVar Fp) (BoolVar Fp) StepSf → CircuitM Fp c (BoolVar Fp))
    (P : FopParams Fp) (domains : List (KnownDomain Fp)) (dummySg : AffinePoint (FVar Fp))
    (rule : inVar → CircuitM Fp c (Vector PrevStatement n × List (FVar Fp)))
    (adv : StepMainAdvice n w nc k ks inVal) : CircuitM Fp c (StepMainOut n w nc k ks) := do
  let publicInput ← witness (val := inVal) adv.publicInput
  let (prevs, publicOutput) ← rule publicInput
  let vk ← witness (val := VkComms nc (PallasPt Fp)) adv.vk
  let slots ← witness (val := UnChecked (Vector (SlotVal w nc k ks) n))
    (UnChecked.mk <$> adv.slots)
  slots.val.toList.forM SlotWitness.check
  let unfs ← witness (val := Vector (UnfVal k) n) adv.unfinalized
  let msgs ← witness (val := Vector Fp n) adv.msgs
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
  pure ⟨unfs.toList.flatMap
      (fun u => (CircuitType.varToFields (F := Fp) (val := UnfVal k) u).toList)
    ++ [digest] ++ msgs.toList, prevs, vk, slots.val, unfs, msgs⟩

/-! ## The read -/

section Reads

open Std.Do

variable {V : Valuation Fp}

/-- A list related entrywise to `finRange n` has length `n`, and its entry at `j` is related
to `j`. -/
private theorem forall₂_finRange {α : Type} {R : α → Fin n → Prop} {l : List α}
    (h : List.Forall₂ R l ((List.finRange n).map id)) :
    ∃ hlen : l.length = n, ∀ j : Fin n, R (l[j.val]'(hlen ▸ j.isLt)) j := by
  have hlen : l.length = n := by simpa using h.length_eq
  refine ⟨hlen, fun j => ?_⟩
  have := (List.forall₂_iff_get.mp h).2 j.val (hlen ▸ j.isLt) (by simp)
  simpa using this

/-- **The step circuit's slots read as their wrap proofs' group halves.** For any rule, under a
valuation satisfying the emitted constraints, every slot the rule marks must-verify satisfies
`SlotReads`: for any wrap proof its cells read as, the group half accepts it at the slot's
statement, carrying the step-message digest of this step's key, application state and kept
proofs. The rule is opaque; the slots' parity bits and verdicts are bits by their allocation
checks. -/
theorem stepMain_reads {n w nc : ℕ} {inVal inVar : Type} [CircuitType Fp inVal inVar]
    [CheckedType Fp (Builder V (KimchiConstraint Fp)) inVal inVar]
    (E : Env IpaPallas.curve nc) (Es : Env IpaVesta.curve nc) (D : KnownDomains Es)
    (hn : n ≤ MaxProofsVerified) (hw : w ≤ MaxProofsVerified) (dummySg : AffinePoint (FVar Fp))
    (rule : inVar →
      CircuitM Fp (Builder V (KimchiConstraint Fp)) (Vector PrevStatement n × List (FVar Fp)))
    (adv : StepMainAdvice n w nc E.σ.k Es.σ.k inVal)
    -- the statement's shape against the SRS
    (hsmall : ∀ (inp : VerifyOneInput Es.σ.k E.σ.k nc w) msg,
      (inp.statement msg).packed.length ≤ 2 ^ E.σ.k)
    (havoid : ∀ (inp : VerifyOneInput Es.σ.k E.σ.k nc w) msg,
      E.σ.Avoids (stepRelationsAt E (inp.statement msg))) :
    ⦃⌜True⌝⦄
    stepMain (c := Builder V (KimchiConstraint Fp)) hw (verifyProofAt E)
      (FopParams.ofEnv Es Linearization.fpTokens) D.list dummySg rule adv
    ⦃⇓ r _ => ⌜∀ i : Fin n, CircuitType.Reads V r.prevs[i].mustVerify true →
      (slotInput hw dummySg r.prevs[i] r.slots[i] r.unfs[i] r.msgs[i]).SlotReads E V
        r.vk.points⌝⦄ := by
  have hinj := castInj128_of_lt PALLAS_BASE_CARD (by decide)
  have hrule := fun x => builder_spec_true (rule x)
  have hfm := forM_spec (V := V) (c := KimchiConstraint Fp)
    (SlotWitness.check (c := Builder V (KimchiConstraint Fp)) (w := w) (nc := nc) (k := E.σ.k)
      (ks := Es.σ.k))
    (fun s => (∃ b : Bool, (↑s.z1.val.sOdd : CVar Fp).val V = bit b) ∧
      ∃ b : Bool, (↑s.z2.val.sOdd : CVar Fp).val V = bit b)
    (fun s => SlotWitness.check_spec s)
  have hmap := fun (vk : VkComms nc (PallasPt (FVar Fp)))
      (slots : UnChecked (Vector (SlotVar w nc E.σ.k Es.σ.k) n)) (unfs : Vector (UnfVar E.σ.k) n)
      (msgs : Vector (FVar Fp) n) (prevs : Vector PrevStatement n) =>
    builder_spec_mapM (V := V) (c := KimchiConstraint Fp)
      (fun i : Fin n => verifyOneBy (verifyProofAt E) (FopParams.ofEnv Es Linearization.fpTokens)
        D.list vk.points (slotInput hw dummySg prevs[i] slots.val[i] unfs[i] msgs[i]))
      (fun o (i : Fin n) =>
        let inp := slotInput hw dummySg prevs[i] slots.val[i] unfs[i] msgs[i]
        ((∃ bb : Bool, (↑inp.unfinalized.shouldFinalize : CVar Fp).val V = bit bb) →
          ∃ bb : Bool, (↑o.2 : CVar Fp).val V = bit bb) ∧
        (CircuitType.Reads V inp.mustVerify true → (↑o.2 : CVar Fp).val V = 1 →
          (∀ x ∈ (ivpInputOf inp.unfinalized.deferredValues (inp.sgOld.toList.map (none, ·))
            vk.points inp.proof).shifted, (stepSide V).ClaimOk x) →
          inp.SlotReads E V vk.points))
      id
      (fun i => builder_spec_and _ _ _
        (verifyOneBy_verdict_bit (verifyProofAt E) (fun sv b st u cells =>
          verifyProofAt_success_bit E sv b st u cells) _ _ _ _)
        (verifyOne_slotReads E Es D hw vk.points _ (hsmall _) (havoid _)))
      (List.finRange n)
  have hhash := fun (p : Poseidon.Params Fp) (vk : VkComms nc (AffinePoint (FVar Fp))) a pr =>
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
  rename_i _ _ _ _ rout _ vk _ _ slots _ _ _ _ hcheck unfs _ hunf msgs _ _ results _ hres _ _
    hassert _ _
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
  obtain ⟨-, hacc⟩ := hget i
  have hi : i.val < results.length := by rw [hlen]; exact i.isLt
  have h1 := hassert (by simpa [hlen] using hn) hbits (results[i.val]'hi).2
    (List.mem_map.mpr ⟨_, List.getElem_mem hi, rfl⟩)
  refine hacc hmv h1 fun x hx => ?_
  have hu := hunfPost i
  have hz := hcheck slots.val[i] (by simp)
  simp only [IvpInput.shifted, ivpInputOf, slotInput, AllocUnfinalized.toUnfinalized,
    List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact stepSide_claimOk_of_bit _ hu.2.2.2.2.1.2
  · exact stepSide_claimOk_of_bit _ hu.2.2.1.2
  · exact stepSide_claimOk_of_bit _ hu.2.2.2.1.2
  · exact stepSide_claimOk_of_bit _ hu.1.2
  · exact stepSide_claimOk_of_bit _ hu.2.1.2
  · exact stepSide_claimOk_of_bit _ hz.1
  · exact stepSide_claimOk_of_bit _ hz.2

end Reads

end Pickles
