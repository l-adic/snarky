import Pickles.MessageHash
import Pickles.StepGroupHalf
import Pickles.StepScalarHalf
import Pickles.WrapProof

/-!
# One previous proof inside the step circuit

Transcribed from `Pickles/Step/VerifyOne.purs`. For one previous wrap proof the step circuit
finalizes the deferred values that proof carries (`finalizeOtherProofStep`), recomputes its
`messagesForNextStepProof` digest (`hashMessagesForNextStepProofOpt`), checks the wrap proof's
group half against the statement those rebuild (`verifyProofAt`, resumed from the digest's
sponge after the key), and combines the two verdicts under the slot's `mustVerify` bit.

## Main definitions

* `VerifyOneInput`: the cells `verifyOneBy` reads for one previous proof;
* `verifyOneBy`: the gadget, returning the finalized proof's round challenges and the verdict.

## Main results

* `verifyOne_reads`: when the slot must verify and the verdict reads `1`, the step-message
  digest is the hash of the key, the application state and the kept proofs' advice, the wrap
  proof's group half accepts at the statement carrying it, and the carried values finalize.
-/

namespace Pickles

open Snarky Snarky.Kimchi Kimchi.Verifier Bulletproof Bulletproof.Ipa
open CompElliptic.Fields.Pasta

/-- The cells `verifyOneBy` reads for one previous wrap proof: that proof's own deferred values
and digest (the step proof it verified, finalized here), its application state, evaluations
and the accumulator advice it carries, the unfinalized proof the step circuit holds for it,
its proof cells, and the slot's bits. The wrap proof is at `ncw` chunks, the step proof it
verified at `ncs`. -/
structure VerifyOneInput (ks k ncw ncs w : ℕ) where
  /-- The previous proof's statement, as field elements. -/
  appState : List (FVar Fp)
  /-- The deferred values the previous wrap proof carries. -/
  deferred : DeferredValues ks (FVar Fp) (Type1 (FVar Fp))
  /-- Their fq-sponge digest before evaluations. -/
  spongeDigest : FVar Fp
  /-- The branch data the previous wrap proof carries. -/
  branchData : BranchData (FVar Fp) (BoolVar Fp)
  /-- The previous wrap proof's `messagesForNextWrapProof` digest. -/
  messagesForNextWrapProof : FVar Fp
  /-- The evaluations the deferred values are finalized against. -/
  evals : ChunkedEvals ncs (FVar Fp)
  /-- The proofs-verified mask, trimmed to the slot's width. -/
  proofMask : Vector (BoolVar Fp) w
  /-- The round challenges carried from the proofs the previous proof verified. -/
  prevChallenges : Vector (Vector (FVar Fp) ks) w
  /-- Their `sg` points, unpadded. -/
  prevSgs : Vector (AffinePoint (FVar Fp)) w
  /-- The `sg` points widened to the padded length, dummies first. -/
  sgOld : Vector (AffinePoint (FVar Fp)) MaxProofsVerified
  /-- The unfinalized proof the step circuit carries for this slot. -/
  unfinalized :
    UnfinalizedProof k (FVar Fp) (BoolVar Fp) (Type2 (SplitField (FVar Fp) (BoolVar Fp)))
  /-- The wrap proof's commitments and opening. -/
  proof : IvpProof k ncw (FVar Fp) (Type2 (SplitField (FVar Fp) (BoolVar Fp)))
  /-- Whether this slot must verify. -/
  mustVerify : BoolVar Fp

/-- The wrap statement a slot's proof is verified against: the carried deferred values, branch
data and digests, with the step-message digest `msg`. -/
def VerifyOneInput.statement {ks k ncw ncs w : ℕ} (inp : VerifyOneInput ks k ncw ncs w)
    (msg : FVar Fp) : WrapStatement ks (FVar Fp) (BoolVar Fp) (Type1 (FVar Fp)) :=
  ⟨⟨⟨inp.deferred, inp.branchData⟩, inp.spongeDigest, inp.messagesForNextWrapProof⟩, msg⟩

/-- The previous proofs the step-message digest absorbs: each one's mask, `sg` and challenges. -/
def VerifyOneInput.hashed {ks k ncw ncs w : ℕ} (inp : VerifyOneInput ks k ncw ncs w) :
    List (BoolVar Fp × AffinePoint (FVar Fp) × List (FVar Fp)) :=
  inp.proofMask.toList.zip (inp.prevSgs.toList.zip (inp.prevChallenges.toList.map Vector.toList))

/-- The step-message digest a slot's statement carries, as a value: the fq-sponge after the
key, then the application state and the kept proofs' `sg` and challenges, squeezed. -/
def VerifyOneInput.stepMsgDigest {ks k ncw ncs w : ℕ} (E : Env IpaPallas.curve ncw)
    (V : Valuation Fp) (ms : List Bool) (inp : VerifyOneInput ks k ncw ncs w) : Fp :=
  (Poseidon.squeeze IpaPallas.curve.sponge.params
    (Poseidon.absorb IpaPallas.curve.sponge.params E.cvk.indexState
      (inp.appState.map (·.val V) ++ keptValues V ms inp.hashed))).1

/-- The public input a slot's wrap proof is verified at: its statement read at `V`, carrying
the step-message digest `stepMsgDigest`. -/
def VerifyOneInput.publicInputAt {ks k ncw ncs w : ℕ} (E : Env IpaPallas.curve ncw)
    (V : Valuation Fp) (ms : List Bool) (inp : VerifyOneInput ks k ncw ncs w) : Array Fq :=
  stepPublicInput E V (inp.statement (.const (inp.stepMsgDigest E V ms)))

variable {c : Type} [BasicSystem Fp c] [KimchiSystem Fp c] {ks k ncw ncs w : ℕ}

/-- One previous proof: assert the unfinalized proof's `shouldFinalize` is `mustVerify`,
finalize the carried deferred values, hash the step-side messages, run the group half at the
rebuilt wrap statement from the hash's sponge after the key, and return the finalized round
challenges with the verdict `(verified ∧ finalized) ∨ ¬mustVerify`. -/
def verifyOneBy
    (verify : SpongeVar Fp → BoolVar Fp →
      WrapStatement ks (FVar Fp) (BoolVar Fp) (Type1 (FVar Fp)) →
      UnfinalizedProof k (FVar Fp) (BoolVar Fp) (Type2 (SplitField (FVar Fp) (BoolVar Fp))) →
      IvpInput k ncw (FVar Fp) (BoolVar Fp) (Type2 (SplitField (FVar Fp) (BoolVar Fp))) →
      CircuitM Fp c (BoolVar Fp))
    (P : FopParams Fp) (domains : List (KnownDomain Fp))
    (vk : VkComms ncw (AffinePoint (FVar Fp))) (inp : VerifyOneInput ks k ncw ncs w) :
    CircuitM Fp c (FopOutput Fp × BoolVar Fp) := do
  assertEqual (inp.unfinalized.shouldFinalize : FVar Fp) (inp.mustVerify : FVar Fp)
  let fop ← finalizeOtherProofStep P domains ⟨inp.deferred, true_, inp.spongeDigest⟩ inp.evals
    inp.proofMask.toList (inp.prevChallenges.toList.map Vector.toList) inp.branchData.domainLog2
  let (msgStep, afterIndex) ← hashMessagesForNextStepProofOpt IpaPallas.curve.sponge.params vk
    inp.appState inp.hashed
  let success ← verify afterIndex (Snarky.not inp.mustVerify) (inp.statement msgStep)
    inp.unfinalized
    (ivpInputOf inp.unfinalized.deferredValues (inp.sgOld.toList.map (none, ·)) vk inp.proof)
  let verified ← Snarky.and success fop.finalized
  let result ← Snarky.or verified (Snarky.not inp.mustVerify)
  pure (fop, result)

/-! ## The read -/

section Reads

open Std.Do

variable {V : Valuation Fp}

/-- `and` reads as the product of its operands. -/
private theorem and_val (a b : BoolVar Fp) :
    ⦃⌜True⌝⦄ Snarky.and (c := Builder V (KimchiConstraint Fp)) a b
    ⦃⇓ r _ => ⌜(↑r : CVar Fp).val V = (↑a : CVar Fp).val V * (↑b : CVar Fp).val V⌝⦄ := by
  simp only [Snarky.and]
  mvcgen

/-- `or` reads as `1 − (1 − a)(1 − b)`. -/
private theorem or_val (a b : BoolVar Fp) :
    ⦃⌜True⌝⦄ Snarky.or (c := Builder V (KimchiConstraint Fp)) a b
    ⦃⇓ r _ => ⌜(↑r : CVar Fp).val V
      = 1 - (1 - (↑a : CVar Fp).val V) * (1 - (↑b : CVar Fp).val V)⌝⦄ := by
  simp only [Snarky.or]
  have h := and_val (V := V) (Snarky.not a) (Snarky.not b)
  mvcgen [h, -Snarky.and_spec]
  rename_i r _ hr
  simp only [Snarky.not, BoolVar.coe_unchecked, CVar.val_sub_] at hr ⊢
  rw [hr]
  simp

/-- Under any valuation satisfying the emitted constraints, with `verify`'s returned bit a bit,
the verdict reads as a bit once the unfinalized proof's `shouldFinalize` does: `mustVerify` is
pinned to it, `finalized` is a bit (`finalizeOtherProofStep_finalized_bit`), and `and`, `or`
keep bits. -/
theorem verifyOneBy_verdict_bit
    (verify : SpongeVar Fp → BoolVar Fp →
      WrapStatement ks (FVar Fp) (BoolVar Fp) (Type1 (FVar Fp)) →
      UnfinalizedProof k (FVar Fp) (BoolVar Fp) (Type2 (SplitField (FVar Fp) (BoolVar Fp))) →
      IvpInput k ncw (FVar Fp) (BoolVar Fp) (Type2 (SplitField (FVar Fp) (BoolVar Fp))) →
      CircuitM Fp (Builder V (KimchiConstraint Fp)) (BoolVar Fp))
    (hverify : ∀ sv b st u cells, ⦃⌜True⌝⦄ verify sv b st u cells
      ⦃⇓ v _ => ⌜∃ bb : Bool, (↑v : CVar Fp).val V = bit bb⌝⦄)
    (P : FopParams Fp) (domains : List (KnownDomain Fp))
    (vk : VkComms ncw (AffinePoint (FVar Fp))) (inp : VerifyOneInput ks k ncw ncs w) :
    ⦃⌜True⌝⦄ verifyOneBy verify P domains vk inp
    ⦃⇓ o _ => ⌜(∃ bb : Bool, (↑inp.unfinalized.shouldFinalize : CVar Fp).val V = bit bb) →
      ∃ bb : Bool, (↑o.2 : CVar Fp).val V = bit bb⌝⦄ := by
  have hfop := fun u (e : ChunkedEvals ncs (FVar Fp)) m pr d =>
    finalizeOtherProofStep_finalized_bit (V := V) (k := ks) P domains u e m pr d
  have hh := fun p vk' a pr => builder_spec_true
    (hashMessagesForNextStepProofOpt (c := Builder V (KimchiConstraint Fp)) (nc := ncw) p vk' a pr)
  simp only [verifyOneBy]
  mvcgen [hfop, hh, hverify]
  rename_i _ _ hpin _ _ hfin _ _ _ _ hsucc _ _ hand _ _ hor
  rintro ⟨bm, hbm⟩
  obtain ⟨bf, hbf⟩ := hfin
  obtain ⟨bs, hbs⟩ := hsucc
  exact ⟨_, hor _ _ (hand _ _ hbs hbf) (not_val (hpin ▸ hbm))⟩

/-- Under any valuation satisfying the emitted constraints, the unfinalized proof's
`shouldFinalize` reads as `mustVerify`, for any `verify`. -/
theorem verifyOneBy_shouldFinalize
    (verify : SpongeVar Fp → BoolVar Fp →
      WrapStatement ks (FVar Fp) (BoolVar Fp) (Type1 (FVar Fp)) →
      UnfinalizedProof k (FVar Fp) (BoolVar Fp) (Type2 (SplitField (FVar Fp) (BoolVar Fp))) →
      IvpInput k ncw (FVar Fp) (BoolVar Fp) (Type2 (SplitField (FVar Fp) (BoolVar Fp))) →
      CircuitM Fp (Builder V (KimchiConstraint Fp)) (BoolVar Fp))
    (P : FopParams Fp) (domains : List (KnownDomain Fp))
    (vk : VkComms ncw (AffinePoint (FVar Fp))) (inp : VerifyOneInput ks k ncw ncs w) :
    ⦃⌜True⌝⦄ verifyOneBy verify P domains vk inp
    ⦃⇓ _ _ => ⌜(↑inp.unfinalized.shouldFinalize : CVar Fp).val V
      = (↑inp.mustVerify : CVar Fp).val V⌝⦄ := by
  have hfop := fun u (e : ChunkedEvals ncs (FVar Fp)) m pr d => builder_spec_true
    (finalizeOtherProofStep (c := Builder V (KimchiConstraint Fp)) (k := ks) P domains u e m pr d)
  have hh := fun p vk' a pr => builder_spec_true
    (hashMessagesForNextStepProofOpt (c := Builder V (KimchiConstraint Fp)) (nc := ncw) p vk' a pr)
  have hv := fun sv b st u cells => builder_spec_true (verify sv b st u cells)
  simp only [verifyOneBy]
  mvcgen [hfop, hh, hv]

/-- A relation on a list's entries carries to its zip with an equally long list. -/
private theorem forall₂_zip_fst {α β γ : Type} {R : α → γ → Prop} :
    ∀ (as : List α) (bs : List β) (cs : List γ), List.Forall₂ R as cs →
      bs.length = as.length → List.Forall₂ (fun q c => R q.1 c) (as.zip bs) cs
  | [], _, [], .nil, _ => by simp
  | a :: as, b :: bs, c :: cs, .cons h hs, hl => by
    simp only [List.zip_cons_cons]
    exact .cons h (forall₂_zip_fst as bs cs hs (by simpa using hl))
  | _ :: _, [], _, _, hl => by simp at hl

/-- The digest's absorb count is at most two per proof plus its challenges. -/
private theorem hashed_count_le {α : Type} :
    ∀ (ms : List α) (sgs : List (AffinePoint (FVar Fp))) (chs : List (List (FVar Fp))),
      (((ms.zip (sgs.zip chs)).map fun q => q.2.2.length + 2).sum
        ≤ 2 * ms.length + chs.flatten.length)
  | [], _, _ => by simp
  | _ :: _, [], _ => by simp
  | _ :: _, _ :: _, [] => by simp
  | _ :: ms, _ :: sgs, ch :: chs => by
    have := hashed_count_le ms sgs chs
    simp only [List.zip_cons_cons, List.map_cons, List.sum_cons, List.length_cons,
      List.flatten_cons, List.length_append]
    omega

/-- **One slot reads as its wrap proof's group half.** Under a valuation satisfying the emitted
constraints, with the slot's proof cells reading as `cp`'s, its `sg` cells as `cp`'s old
accumulators, the key cells as the key, and
the masks as `ms`: when the slot must verify and the verdict
reads `1`, the step-message digest cell reads as the hash of the key, the application state
and the kept proofs' `sg` and challenges, the group half accepts `cp` at the statement carrying
that digest, and the carried deferred values finalize. -/
theorem verifyOne_reads (E : Env IpaPallas.curve ncw) (Es : Env IpaVesta.curve ncs)
    (D : KnownDomains Es) (hw : w ≤ MaxProofsVerified)
    (vk : VkComms ncw (AffinePoint (FVar Fp))) (inp : VerifyOneInput Es.σ.k E.σ.k ncw ncs w)
    (cp : KimchiProof IpaPallas.curve ncw E.σ.k)
    -- the masks
    (ms : List Bool) (hm : List.Forall₂ (CircuitType.Reads V) inp.proofMask.toList ms)
    -- the key
    (hkey : KeyReads IpaPallas.curve V vk E.cvk)
    -- the proof
    (hproof : ProofReads (stepSide V) (inp.proof.wComm.toList.map (·.toList))
      inp.proof.zComm.toList inp.proof.tComm.toList inp.proof.opening cp)
    (holds : CommReads IpaPallas.curve V inp.sgOld.toList (cp.olds.map (·.sg)).toList)
    (hclaimOk : ∀ x ∈ (ivpInputOf inp.unfinalized.deferredValues (inp.sgOld.toList.map (none, ·))
      vk inp.proof).shifted, (stepSide V).ClaimOk x)
    -- the statement's shape against the SRS
    (hsmall : ∀ msg, (inp.statement msg).packed.length ≤ 2 ^ E.σ.k)
    (havoid : ∀ msg, E.σ.Avoids (stepRelationsAt E (inp.statement msg))) :
    ⦃⌜True⌝⦄ verifyOneBy (c := Builder V (KimchiConstraint Fp)) (verifyProofAt E)
      (FopParams.ofEnv Es Linearization.fpTokens) D.list vk inp
    ⦃⇓ o _ => ⌜CircuitType.Reads V inp.mustVerify true → (↑o.2 : CVar Fp).val V = 1 →
      ∃ (msg : FVar Fp) (v : BoolVar Fp),
        msg.val V = inp.stepMsgDigest E V ms ∧
        VerifyReads (stepSide V) E.σ E.cvk cp (stepPublicInput E V (inp.statement msg))
          inp.unfinalized false v ∧
        (↑v : CVar Fp).val V = 1 ∧ (↑o.1.finalized : CVar Fp).val V = 1⌝⦄ := by
  have hinj := castInj128_of_lt PALLAS_BASE_CARD (by decide)
  have hall : ∀ j k : ℕ, j ≤ 3 → k ≤ 3 → (j : Fp) = k → j = k := fun j k hj hk h =>
    hinj j k (by omega) (by omega) h
  have hms := forall₂_zip_fst inp.proofMask.toList
    (inp.prevSgs.toList.zip (inp.prevChallenges.toList.map Vector.toList)) ms hm (by simp)
  have hprevlen : (inp.prevChallenges.toList.map Vector.toList).flatten.length < 2 ^ 128 := by
    have : (inp.prevChallenges.toList.map Vector.toList).flatten.length = w * Es.σ.k := by
      rw [List.length_flatten, List.map_map]
      simp [Function.comp_def]
    have := Es.rounds_small
    have : w * Es.σ.k ≤ MaxProofsVerified * Es.σ.k := Nat.mul_le_mul_right _ hw
    simp only [MaxProofsVerified] at *
    omega
  have hchar : ∀ k : ℕ, k ≤ (inp.hashed.map fun q => q.2.2.length + 2).sum →
      (k : Fp) = 0 → k = 0 := by
    intro k hk h0
    have hb := hashed_count_le inp.proofMask.toList inp.prevSgs.toList
      (inp.prevChallenges.toList.map Vector.toList)
    have hd : PALLAS_BASE_CARD ∣ k := (ZMod.natCast_eq_zero_iff k PALLAS_BASE_CARD).mp h0
    refine Nat.eq_zero_of_dvd_of_lt hd (lt_of_le_of_lt (le_trans hk hb) ?_)
    have : (2 : ℕ) ^ 128 + 4 < PALLAS_BASE_CARD := by norm_num [PALLAS_BASE_CARD]
    have : inp.proofMask.toList.length ≤ 2 := by
      simpa [MaxProofsVerified] using hw
    unfold VerifyOneInput.hashed at *
    omega
  have hfop := fun u (e : ChunkedEvals ncs (FVar Fp)) m pr d =>
    finalizeOtherProofStep_finalized_bit (V := V) (k := Es.σ.k)
      (FopParams.ofEnv Es Linearization.fpTokens) D.list u e m pr d
  have hh := hashMessagesForNextStepProofOpt_spec (V := V) IpaPallas.curve.sponge.params
    IpaPallas.curve.sponge.hsize hall vk inp.appState inp.hashed ms hms hchar
  have hvp : ∀ (sv : SpongeVar Fp) (msg : FVar Fp),
      ⦃⌜True⌝⦄ verifyProofAt (c := Builder V (KimchiConstraint Fp)) E sv
        (Snarky.not inp.mustVerify) (inp.statement msg) inp.unfinalized
        (ivpInputOf inp.unfinalized.deferredValues (inp.sgOld.toList.map (none, ·)) vk
          inp.proof)
      ⦃⇓ v _ => ⌜CircuitType.Reads V inp.mustVerify true →
        SpongeVar.ReadsAt V sv (Poseidon.absorb IpaPallas.curve.sponge.params Poseidon.init
          (vk.indexPoints.flatMap fun P => [P.x.val V, P.y.val V])) →
        VerifyReads (stepSide V) E.σ E.cvk cp (stepPublicInput E V (inp.statement msg))
          inp.unfinalized false v⌝⦄ := by
    intro sv msg
    rw [builder_spec_iff]
    intro nv hsat hmv hsv
    rw [hkey.indexCoords] at hsv
    have hbase : CircuitType.Reads V (Snarky.not inp.mustVerify) false :=
      CircuitType.reads_boolVar.mpr (not_val (CircuitType.reads_boolVar.mp hmv))
    obtain ⟨oldsW, hivp⟩ := ivpHyps_of_reads (pub := stepPublicInput E V (inp.statement msg))
      inp.unfinalized inp.sgOld.toList inp.proof (by simp [MaxProofsVerified]) hproof holds
      ⟨⟨_, hsv, E.digest_eq.symm⟩, hkey⟩ hclaimOk
    exact (builder_spec_iff _ _).mp (verifyProofAt_reads E cp sv _ (inp.statement msg)
      inp.unfinalized _ oldsW hbase (hsmall msg) (havoid msg) hivp) nv hsat
  simp only [verifyOneBy]
  mvcgen [hfop, hh, hvp, and_val, or_val, -Snarky.and_spec, -Snarky.or_spec]
  rename_i _ _ _ _ fop _ hF hr _ hH succ _ hVp ver _ hVer res _ hRes
  intro hmv hres
  have hnot : (↑(Snarky.not inp.mustVerify) : CVar Fp).val V = 0 := by
    rw [not_val (CircuitType.reads_boolVar.mp hmv)]
    simp [bit]
  rw [hres, hnot] at hRes
  have hver : (↑ver : CVar Fp).val V = 1 := by linear_combination -hRes
  rw [hVer] at hver
  obtain ⟨bf, hbf⟩ := hF
  cases bf
  · rw [hbf, bit, if_neg (by decide), mul_zero] at hver
    exact absurd hver zero_ne_one
  · have h1 : (↑fop.finalized : CVar Fp).val V = 1 := by simpa [bit] using hbf
    rw [h1, mul_one] at hver
    refine ⟨hr.1, succ, ?_, hVp hmv hH.1, hver, h1⟩
    rw [hH.2, hkey.indexCoords, VerifyOneInput.stepMsgDigest, KimchiVK.indexState,
      List.append_assoc]
    simp only [Poseidon.absorb, List.foldl_append]

/-- A slot's cells hold the wire proof `cp`: its mask cells read as `ms`, the key cells as the
key, its proof cells as `cp`'s commitments and opening, and its `sg` cells as `cp`'s old
accumulators. -/
def VerifyOneInput.WireReads (E : Env IpaPallas.curve ncw) (V : Valuation Fp)
    (vk : VkComms ncw (AffinePoint (FVar Fp))) (inp : VerifyOneInput ks E.σ.k ncw ncs w)
    (cp : KimchiProof IpaPallas.curve ncw E.σ.k) (ms : List Bool) : Prop :=
  List.Forall₂ (CircuitType.Reads V) inp.proofMask.toList ms ∧
    KeyReads IpaPallas.curve V vk E.cvk ∧
    ProofReads (stepSide V) (inp.proof.wComm.toList.map (·.toList))
      inp.proof.zComm.toList inp.proof.tComm.toList inp.proof.opening cp ∧
    CommReads IpaPallas.curve V inp.sgOld.toList (cp.olds.map (·.sg)).toList

/-- What a verified slot certifies: for any wire proof `cp` the slot's cells hold, the group
half accepts `cp` at the slot's public input. -/
def VerifyOneInput.SlotReads (E : Env IpaPallas.curve ncw) (V : Valuation Fp)
    (vk : VkComms ncw (AffinePoint (FVar Fp))) (inp : VerifyOneInput ks E.σ.k ncw ncs w) : Prop :=
    ∀ (cp : KimchiProof IpaPallas.curve ncw E.σ.k) (ms : List Bool),
      inp.WireReads E V vk cp ms →
      ∃ v : BoolVar Fp,
        (GroupHalf.step V inp.unfinalized).Reads E cp (inp.publicInputAt E V ms) v ∧
          (↑v : CVar Fp).val V = 1

/-- `verifyOne_reads` as the slot's `SlotReads`: when the slot must verify, the verdict reads `1`
and the shifted claims are in the ladder's regime, the readings become premises of the
conclusion, and the digest cell is replaced by its value in the public input — the form a
circuit that allocates the slot's cells before running it consumes. -/
theorem verifyOne_slotReads (E : Env IpaPallas.curve ncw) (Es : Env IpaVesta.curve ncs)
    (D : KnownDomains Es) (hw : w ≤ MaxProofsVerified)
    (vk : VkComms ncw (AffinePoint (FVar Fp))) (inp : VerifyOneInput Es.σ.k E.σ.k ncw ncs w)
    (hsmall : ∀ msg, (inp.statement msg).packed.length ≤ 2 ^ E.σ.k)
    (havoid : ∀ msg, E.σ.Avoids (stepRelationsAt E (inp.statement msg))) :
    ⦃⌜True⌝⦄ verifyOneBy (c := Builder V (KimchiConstraint Fp)) (verifyProofAt E)
      (FopParams.ofEnv Es Linearization.fpTokens) D.list vk inp
    ⦃⇓ o _ => ⌜CircuitType.Reads V inp.mustVerify true → (↑o.2 : CVar Fp).val V = 1 →
      (∀ x ∈ (ivpInputOf inp.unfinalized.deferredValues (inp.sgOld.toList.map (none, ·)) vk
        inp.proof).shifted, (stepSide V).ClaimOk x) →
      inp.SlotReads E V vk⌝⦄ := by
  rw [builder_spec_iff]
  intro nv hsat hmv h1 hclaimOk cp ms ⟨hm, hkey, hproof, holds⟩
  obtain ⟨msg, v, hmsg, hvr, hv1, -⟩ := (builder_spec_iff _ _).mp
    (verifyOne_reads E Es D hw vk inp cp ms hm hkey hproof holds hclaimOk hsmall
      havoid) nv hsat hmv h1
  refine ⟨v, ?_, hv1⟩
  have hpub : stepPublicInput E V (inp.statement msg) = inp.publicInputAt E V ms :=
    stepPublicInput_congr_msg E V (inp.statement msg) msg _ (by simpa using hmsg)
  rw [← hpub]
  exact hvr

/-- What a verified slot certifies of the step proof its deferred values came from
(`StepFinalizeReads` at the slot's cells): given that proof's group half from the wrap circuit,
the ties and `SgOk`, `kimchiVerify` accepts it. -/
def VerifyOneInput.ScalarReads (Es : Env IpaVesta.curve ncs) (D : KnownDomains Es)
    (V : Valuation Fp) (inp : VerifyOneInput Es.σ.k k ncw ncs w) : Prop :=
  StepFinalizeReads Es D V ⟨inp.deferred, true_, inp.spongeDigest⟩ inp.evals inp.proofMask
    inp.prevChallenges inp.branchData.domainLog2

/-- One slot reads as the scalar half of the step proof its deferred values came from: with the
mask cells boolean, when the slot must verify and the verdict reads `1`, the slot satisfies
`ScalarReads`, for any `verify`. -/
theorem verifyOne_scalarReads (Es : Env IpaVesta.curve ncs) (D : KnownDomains Es)
    (hw : w ≤ MaxProofsVerified)
    (verify : SpongeVar Fp → BoolVar Fp →
      WrapStatement Es.σ.k (FVar Fp) (BoolVar Fp) (Type1 (FVar Fp)) →
      UnfinalizedProof k (FVar Fp) (BoolVar Fp) (Type2 (SplitField (FVar Fp) (BoolVar Fp))) →
      IvpInput k ncw (FVar Fp) (BoolVar Fp) (Type2 (SplitField (FVar Fp) (BoolVar Fp))) →
      CircuitM Fp (Builder V (KimchiConstraint Fp)) (BoolVar Fp))
    (vk : VkComms ncw (AffinePoint (FVar Fp))) (inp : VerifyOneInput Es.σ.k k ncw ncs w) :
    ⦃⌜True⌝⦄ verifyOneBy verify (FopParams.ofEnv Es Linearization.fpTokens) D.list vk inp
    ⦃⇓ o _ => ⌜(∃ ms : Vector Bool w, CircuitType.Reads V inp.proofMask ms) →
      CircuitType.Reads V inp.mustVerify true → (↑o.2 : CVar Fp).val V = 1 →
      inp.ScalarReads Es D V⌝⦄ := by
  have hfin := finalizeOtherProofStepAt_finalizeReads Es V D ⟨inp.deferred, true_, inp.spongeDigest⟩
    inp.evals inp.proofMask inp.prevChallenges inp.branchData.domainLog2 hw
  simp only [finalizeOtherProofStepAt] at hfin
  have hfop := builder_spec_and _ _ _ hfin
    (finalizeOtherProofStep_finalized_bit (V := V) (k := Es.σ.k)
      (FopParams.ofEnv Es Linearization.fpTokens) D.list ⟨inp.deferred, true_, inp.spongeDigest⟩
      inp.evals inp.proofMask.toList (inp.prevChallenges.toList.map Vector.toList)
      inp.branchData.domainLog2)
  have hh := fun p vk' a pr => builder_spec_true
    (hashMessagesForNextStepProofOpt (c := Builder V (KimchiConstraint Fp)) (nc := ncw) p vk' a pr)
  have hv := fun sv b st u cells => builder_spec_true (verify sv b st u cells)
  simp only [verifyOneBy]
  mvcgen [hfop, hh, hv, and_val, or_val, -Snarky.and_spec, -Snarky.or_spec]
  rename_i _ _ _ _ _ hF _ _ _ _ ver _ hVer _ _ hRes
  intro hmask hmv hres
  obtain ⟨hreads, bf, hbf⟩ := hF
  have hnot : (↑(Snarky.not inp.mustVerify) : CVar Fp).val V = 0 := by
    rw [not_val (CircuitType.reads_boolVar.mp hmv)]
    simp [bit]
  rw [hres, hnot] at hRes
  have hver : (↑ver : CVar Fp).val V = 1 := by linear_combination -hRes
  rw [hVer] at hver
  cases bf
  · rw [hbf, bit, if_neg (by decide), mul_zero] at hver
    exact absurd hver zero_ne_one
  · exact hreads hmask (by simpa [bit] using hbf)

end Reads

end Pickles
