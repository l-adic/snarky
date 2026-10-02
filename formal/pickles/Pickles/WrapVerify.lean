import Pickles.IncrementallyVerify
import Pickles.MessageHash
import Pickles.TwoHalves
import Pickles.Verify
import Pickles.Encoding
import Pickles.ShiftedClaims

/-!
# The wrap circuit's verify block

Transcribed from `Pickles/Wrap/Verify.purs`. `wrapVerify` is the wrap circuit's group half over
the step proof it verifies: `incrementallyVerifyProof` on the conditional sponge, then four
assertions:

* the opening's success bit holds outright, where `verifyProof` on the step side returns it;
* the accumulator advice hashes to the statement's claimed digest
  (`hashMessagesForNextWrapProof`), binding this proof's `sg` and round challenges to the
  statement the next proof verifies;
* the fq digest equals the claimed `spongeDigestBeforeEvaluations`;
* each returned round prechallenge equals its claim.

The message sponge is the caller's: the deployed block starts it from the checkpoint that has
already absorbed the dummy padding, so those absorptions stay out of the circuit.

`wrapVerify_reads` is the block's read, the counterpart of `verifyProof_reads` with the success
bit forced to `1`; `wrapVerify_wrap_reads` is it at the deployed Vesta constants, and
`ivpHyps_of_reads_wrap` discharges its hypotheses from the cells' reads, the form the wrap
circuit's read composes (`wrapMainVerify_reads`). `wrapVerify_frame` carries what the
public-input commitment's rows force out of the block. The packed step statement's leaves sit at
the key's Lagrange table (`wrapLeavesAt`, `XhatTable.ofKey`), and `wrapPublicInput_toList` states
the wrap public input as the packed step statement reduced into the scalar field
(`PackedScalar.reduced`). `wrapVerifyWith` is the block with the SRS blinding base and the
Lagrange points as constants.
-/

namespace Pickles

open Snarky Snarky.Kimchi

variable {F c : Type} [Field F] [DecidableEq F] [ToNat F] [BasicSystem F c] [KimchiSystem F c]

/-- The wrap circuit's verify block: the group half, then its four assertions. -/
def wrapVerify [ConstraintHolds F c] [LawfulBasicSystem F c] {sf : Type} {k kw nw np : ℕ}
    (ops : IpaScalarOps F c sf) (e : IpaEndo F)
    (p : Poseidon.Params F) (endo : FVar F) (gm : GroupMapParams F) (sqrtF : F → Option F)
    (blindingH : AffinePoint (FVar F)) (spongeAfterIndex : SpongeVar F)
    (computeXHat : CircuitM F c (Vector (AffinePoint (FVar F)) nc)) (msgSponge : SpongeVar F)
    (newBpChallenges : Vector (Vector (FVar F) kw) nw) (claimedMsgDigest : FVar F)
    (u : UnfinalizedProof k (FVar F) (BoolVar F) sf)
    (cells : IvpInput k nc np (FVar F) (BoolVar F) sf) : CircuitM F c PUnit := do
  let o ← incrementallyVerifyProof ops e p endo gm sqrtF true blindingH spongeAfterIndex
    computeXHat (cells.withClaims u)
  assert o.success
  let d ← hashMessagesForNextWrapProof p msgSponge ⟨cells.opening.sg, newBpChallenges⟩
  assertEqual claimedMsgDigest d
  assertEqual u.spongeDigestBeforeEvaluations o.spongeDigest
  for cc in (u.deferredValues.bulletproofChallenges.zip o.bulletproofChallenges).toList do
    assertEqual cc.1.val cc.2.val
  pure PUnit.unit

/-! ## A frame for the public-input commitment -/

section Frame

variable {F : Type} [Field F] [DecidableEq F] [ToNat F] {V : Valuation F}

open Std.Do in
/-- Whatever the public-input commitment's rows force of the valuation, the verify block's rows
force too (`incrementallyVerifyProof_frame`). -/
theorem wrapVerify_frame {sf : Type} {k kw nw np : ℕ}
    (ops : IpaScalarOps F (Builder V (KimchiConstraint F)) sf) (e : IpaEndo F)
    (p : Poseidon.Params F) (endo : FVar F) (gm : GroupMapParams F) (sqrtF : F → Option F)
    (blindingH : AffinePoint (FVar F)) (spongeAfterIndex : SpongeVar F)
    (computeXHat : CircuitM F (Builder V (KimchiConstraint F)) (Vector (AffinePoint (FVar F)) nc))
    (msgSponge : SpongeVar F) (newBpChallenges : Vector (Vector (FVar F) kw) nw)
    (claimedMsgDigest : FVar F) (u : UnfinalizedProof k (FVar F) (BoolVar F) sf)
    (cells : IvpInput k nc np (FVar F) (BoolVar F) sf) (P : Prop)
    (hX : ⦃⌜True⌝⦄ computeXHat ⦃⇓ _ _ => ⌜P⌝⦄) :
    ⦃⌜True⌝⦄
    wrapVerify ops e p endo gm sqrtF blindingH spongeAfterIndex computeXHat msgSponge
      newBpChallenges claimedMsgDigest u cells
    ⦃⇓ _ _ => ⌜P⌝⦄ := by
  have hivp := incrementallyVerifyProof_frame ops e p endo gm sqrtF blindingH spongeAfterIndex
    computeXHat (cells.withClaims u) P hX
  have hh := fun m => builder_spec_true
    (hashMessagesForNextWrapProof (c := Builder V (KimchiConstraint F)) (w := nw) (k := kw) p
      msgSponge m)
  simp only [wrapVerify]
  mvcgen [hivp, hh] invariants
    · ⇓⟨_, _⟩ => ⌜P⌝

open Std.Do in
/-- The verify block asserts its message's digest: at the padding sponge, `claimedMsgDigest` reads
as the wrap-message digest of the opening `sg` and the new challenges the cells read as. -/
theorem wrapVerify_msgDigest {sf : Type} {k kw nw np : ℕ}
    (ops : IpaScalarOps F (Builder V (KimchiConstraint F)) sf) (e : IpaEndo F)
    (p : Poseidon.Params F) (hsize : p.roundConstants.size = Poseidon.fullRounds)
    (endo : FVar F) (gm : GroupMapParams F) (sqrtF : F → Option F)
    (blindingH : AffinePoint (FVar F)) (spongeAfterIndex : SpongeVar F)
    (computeXHat : CircuitM F (Builder V (KimchiConstraint F)) (Vector (AffinePoint (FVar F)) nc))
    (dummy : Vector F kw) (newBpChallenges : Vector (Vector (FVar F) kw) nw)
    (claimedMsgDigest : FVar F) (u : UnfinalizedProof k (FVar F) (BoolVar F) sf)
    (cells : IvpInput k nc np (FVar F) (BoolVar F) sf) :
    ⦃⌜True⌝⦄
    wrapVerify ops e p endo gm sqrtF blindingH spongeAfterIndex computeXHat
      (wrapPaddingSponge p dummy (MaxProofsVerified - nw)) newBpChallenges claimedMsgDigest u cells
    ⦃⇓ _ _ => ⌜∀ (sgv : AffinePoint F) (cv : Vector (Vector F kw) nw),
      CircuitType.Reads V cells.opening.sg sgv → CircuitType.Reads V newBpChallenges cv →
      claimedMsgDigest.val V = wrapMsgDigest p dummy ⟨sgv, cv⟩⌝⦄ := by
  have hivp := builder_spec_true (incrementallyVerifyProof ops e p endo gm sqrtF true blindingH
    spongeAfterIndex computeXHat (cells.withClaims u))
  have hh := hashMessagesForNextWrapProof_padded (V := V) p hsize dummy newBpChallenges
    cells.opening.sg
  simp only [wrapVerify]
  mvcgen [hivp, hh] invariants
    · ⇓⟨_, _⟩ => ⌜∀ (sgv : AffinePoint F) (cv : Vector (Vector F kw) nw),
      CircuitType.Reads V cells.opening.sg sgv → CircuitType.Reads V newBpChallenges cv →
      claimedMsgDigest.val V = wrapMsgDigest p dummy ⟨sgv, cv⟩⌝
  rename_i hd _ _ heq _ _ _
  intro sgv cv hs hc
  rw [heq]
  exact hd sgv cv hs hc

end Frame

/-! ## The read -/

section Read

open Std.Do Kimchi.Verifier Bulletproof Bulletproof.Ipa
open CompElliptic.CurveForms.ShortWeierstrass

variable {C : KimchiCurve} {V : Valuation C.BaseField} {sf : Type}
  {ops : IpaScalarOps C.BaseField (Builder V (KimchiConstraint C.BaseField)) sf}

/-- **The verify block reads as the group half, with its success bit forced.** On side `S`, with
`computeXHat` reading as the wire's public commitment and `IvpHyps` at the claims-substituted
cells, the output satisfies `VerifyReads` at a bit that reads `1`, since the block asserts it.
The message-digest assertion is read trivially: no statement of the group half mentions the
advice it hashes. -/
theorem wrapVerify_reads {nc kw nw np : ℕ} (S : IvpSide C V ops) (σ : SRS C.Point)
    (cvk : KimchiVK C nc) (cp : KimchiProof C nc σ.k) (pub : Array C.ScalarField)
    (endo : FVar C.BaseField) (sqrtF : C.BaseField → Option C.BaseField)
    (blindingH : AffinePoint (FVar C.BaseField)) (spongeAfterIndex : SpongeVar C.BaseField)
    (computeXHat : CircuitM C.BaseField (Builder V (KimchiConstraint C.BaseField))
      (Vector (AffinePoint (FVar C.BaseField)) nc))
    (msgSponge : SpongeVar C.BaseField) (newBpChallenges : Vector (Vector (FVar C.BaseField) kw) nw)
    (claimedMsgDigest : FVar C.BaseField)
    (u : UnfinalizedProof σ.k (FVar C.BaseField) (BoolVar C.BaseField) sf)
    (cells : IvpInput σ.k nc np (FVar C.BaseField) (BoolVar C.BaseField) sf)
    (oldsW : Vector (C.Point × Bool) np)
    (hXhat : ⦃⌜True⌝⦄ computeXHat
      ⦃⇓ pts _ => ⌜CommReads C V pts.toList (runPublicComm C σ cvk pub).toList⌝⦄)
    (hh : OnCurveAt C.E.toAffine V blindingH (SWPoint.equivPoint C.E σ.h))
    (h : IvpHyps S σ cvk cp pub true spongeAfterIndex (cells.withClaims u) oldsW) :
    ⦃⌜True⌝⦄
    wrapVerify (c := Builder V (KimchiConstraint C.BaseField)) ops S.curve.e C.sponge.params
      endo (.ofSpec C.groupMap) sqrtF blindingH spongeAfterIndex computeXHat msgSponge
      newBpChallenges claimedMsgDigest u cells
    ⦃⇓ _ _ => ⌜∃ v : BoolVar C.BaseField,
      VerifyReads S σ cvk cp pub u false v ∧ (↑v : CVar C.BaseField).val V = 1⌝⦄ := by
  have hivp := incrementallyVerifyProof_reads S σ cvk cp pub endo sqrtF true blindingH
    spongeAfterIndex computeXHat (cells.withClaims u) oldsW hXhat hh h
  have hmsg := builder_spec_true (V := V) (c := KimchiConstraint C.BaseField)
    (hashMessagesForNextWrapProof C.sponge.params msgSponge ⟨cells.opening.sg, newBpChallenges⟩)
  simp only [wrapVerify]
  mvcgen [hivp, hmsg] invariants
    · ⇓⟨xs, _⟩ => ⌜∀ p ∈ xs.prefix, p.1.val.val V = p.2.val.val V⌝
  · -- the loop step: the compared pair reads equal, the earlier ones by the invariant
    rename_i pref cur suff _ _ _ hinv _ _ hcur
    intro p hp
    rw [List.mem_append, List.mem_singleton] at hp
    rcases hp with hp | rfl
    · exact hinv p hp
    · exact hcur
  · -- the loop entry: nothing compared yet
    intro p hp
    exact absurd hp List.not_mem_nil
  · -- the exit: the group half's read at the asserted bit
    rename_i o _ hivp' _ _ hsucc _ _ _ _ _ _ _ hdig _ _ hall
    refine ⟨o.success, ⟨o, hivp', rfl, hdig, fun _ i => ?_, true, by simp [bit, hsucc]⟩, hsucc⟩
    simpa using hall _ (Vector.mem_toList_iff.mpr (Vector.getElem_mem
      (xs := u.deferredValues.bulletproofChallenges.zip o.bulletproofChallenges) i.isLt))

end Read

/-! ## The read at the deployed wrap side -/

section WrapRead

open Std.Do Kimchi.Verifier Bulletproof Bulletproof.Ipa
open CompElliptic.Fields.Pasta CompElliptic.Curves.Pasta
open CompElliptic.CurveForms.ShortWeierstrass

/-- `wrapVerify_reads` at `wrapSide` and the deployed Vesta constants; the counterpart of
`verifyProof_step_reads`. -/
theorem wrapVerify_wrap_reads {nc kw nw np : ℕ} {V : Valuation Fq}
    (σ : SRS IpaVesta.curve.Point) (cvk : KimchiVK IpaVesta.curve nc)
    (cp : KimchiProof IpaVesta.curve nc σ.k) (pub : Array Fp)
    (endo : FVar Fq) (sqrtF : Fq → Option Fq) (blindingH : AffinePoint (FVar Fq))
    (spongeAfterIndex : SpongeVar Fq)
    (computeXHat : CircuitM Fq (Builder V (KimchiConstraint Fq))
      (Vector (AffinePoint (FVar Fq)) nc))
    (msgSponge : SpongeVar Fq) (newBpChallenges : Vector (Vector (FVar Fq) kw) nw)
    (claimedMsgDigest : FVar Fq)
    (u : UnfinalizedProof σ.k (FVar Fq) (BoolVar Fq) (Type1 (FVar Fq)))
    (cells : IvpInput σ.k nc np (FVar Fq) (BoolVar Fq) (Type1 (FVar Fq)))
    (oldsW : Vector (IpaVesta.curve.Point × Bool) np)
    (hXhat : ⦃⌜True⌝⦄ computeXHat ⦃⇓ pts _ =>
      ⌜CommReads IpaVesta.curve V pts.toList (runPublicComm IpaVesta.curve σ cvk pub).toList⌝⦄)
    (hh : OnCurveAt IpaVesta.curve.E.toAffine V blindingH
      (SWPoint.equivPoint IpaVesta.curve.E σ.h))
    (h : IvpHyps (wrapSide V) σ cvk cp pub true spongeAfterIndex (cells.withClaims u) oldsW) :
    ⦃⌜True⌝⦄
    wrapVerify (c := Builder V (KimchiConstraint Fq)) IpaScalarOps.wrap IpaEndo.vesta
      IpaVesta.curve.sponge.params endo groupMapParamsVesta sqrtF blindingH spongeAfterIndex
      computeXHat msgSponge newBpChallenges claimedMsgDigest u cells
    ⦃⇓ _ _ => ⌜∃ v : BoolVar Fq,
      VerifyReads (wrapSide V) σ cvk cp pub u false v ∧ (↑v : CVar Fq).val V = 1⌝⦄ :=
  wrapVerify_reads (wrapSide V) σ cvk cp pub endo sqrtF blindingH spongeAfterIndex computeXHat
    msgSponge newBpChallenges claimedMsgDigest u cells oldsW hXhat hh h

/-! ## The block at a key -/

/-- The step statement's public-input leaves at the key's Lagrange points, one per packed
scalar. -/
def wrapLeavesAt {ks n nc : ℕ} (σ : SRS IpaVesta.curve.Point) (cvk : KimchiVK IpaVesta.curve nc)
    (statement : StepStatement (UnfinalizedProof ks (FVar Fq) (BoolVar Fq)
      (Type2 (SplitField (FVar Fq) (BoolVar Fq)))) (FVar Fq) n) : List (Leaf Fq nc) :=
  packLeavesOf statement.packed
    (XhatTable.ofKey statement.packed (cvk.lagrangePoints σ
      (CircuitType.size Fp (StepStatement (UnfVal ks) Fp n))))

/-- The public input the step statement packs to under `V`: what the verified step proof's
public input must be. -/
def wrapPublicInput {ks n nc : ℕ} (σ : SRS IpaVesta.curve.Point) (cvk : KimchiVK IpaVesta.curve nc)
    (V : Valuation Fq)
    (statement : StepStatement (UnfinalizedProof ks (FVar Fq) (BoolVar Fq)
      (Type2 (SplitField (FVar Fq) (BoolVar Fq)))) (FVar Fq) n) : Array Fp :=
  pubOf IpaVesta.curve V (wrapLeavesAt σ cvk statement)

/-- The public input a step statement packs to is its packed scalars reduced into the scalar
field (`PackedScalar.reduced`). -/
theorem wrapPublicInput_toList {ks n nc : ℕ} (σ : SRS IpaVesta.curve.Point)
    (cvk : KimchiVK IpaVesta.curve nc) (V : Valuation Fq)
    (statement : StepStatement (UnfinalizedProof ks (FVar Fq) (BoolVar Fq)
      (Type2 (SplitField (FVar Fq) (BoolVar Fq)))) (FVar Fq) n) :
    (wrapPublicInput σ cvk V statement).toList
      = statement.packed.toList.map (PackedScalar.reduced IpaVesta.curve V) := by
  unfold wrapPublicInput wrapLeavesAt
  rw [packLeavesOf_ofKey (C := IpaVesta.curve) statement.packed
    (cvk.lagrangePoints σ (CircuitType.size Fp (StepStatement (UnfVal ks) Fp n)))]
  exact pubOf_zipWith_constLeaf _ _

/-- The verify block at the deployed Vesta constants, the blinding base `h` as a constant cell,
and the public-input commitment of the packed step statement at the Lagrange points `lagrange`.
The CS-equality corpus pins this gadget at its dumps' points. -/
def wrapVerifyWith {c : Type} [BasicSystem Fq c] [ConstraintHolds Fq c]
    [LawfulBasicSystem Fq c] [KimchiSystem Fq c]
    {ks n k kw nw nc np : ℕ}
    (h : IpaVesta.curve.Point)
    (lagrange : Vector (Vector IpaVesta.curve.Point nc)
      (CircuitType.size Fp (StepStatement (UnfVal ks) Fp n)))
    (statement : StepStatement (UnfinalizedProof ks (FVar Fq) (BoolVar Fq)
      (Type2 (SplitField (FVar Fq) (BoolVar Fq)))) (FVar Fq) n)
    (spongeAfterIndex msgSponge : SpongeVar Fq) (newBpChallenges : Vector (Vector (FVar Fq) kw) nw)
    (claimedMsgDigest : FVar Fq)
    (u : UnfinalizedProof k (FVar Fq) (BoolVar Fq) (Type1 (FVar Fq)))
    (cells : IvpInput k nc np (FVar Fq) (BoolVar Fq) (Type1 (FVar Fq))) : CircuitM Fq c PUnit :=
  wrapVerify IpaScalarOps.wrap IpaEndo.vesta IpaVesta.curve.sponge.params
    (.const ((Pasta.pallasLam : ℤ) : Fq)) groupMapParamsVesta vestaBase.sqrt? (constPt h)
    spongeAfterIndex
    (publicInputCommitFull (constPt h)
      (packLeavesOf statement.packed (XhatTable.ofKey statement.packed lagrange)))
    msgSponge newBpChallenges claimedMsgDigest u cells

/-- A packed step statement opens with a full scalar: the first slot's combined inner product,
or with no slot the `messagesForNextStepProof` digest. -/
private theorem StepStatement.packed_head {ks n : ℕ}
    (st : StepStatement (UnfinalizedProof ks (FVar Fq) (BoolVar Fq)
      (Type2 (SplitField (FVar Fq) (BoolVar Fq)))) (FVar Fq) n) :
    ∃ x rest, st.packed.toList = .full x :: rest := by
  simp only [StepStatement.packed, Vector.toList_mk]
  cases st.proofState.unfinalizedProofs.toList with
  | nil =>
    simp only [List.flatMap_nil, List.nil_append, List.cons_append]
    exact ⟨_, _, rfl⟩
  | cons u us =>
    simp only [List.flatMap_cons, UnfinalizedProof.packed, Vector.toList_mk, List.append_assoc,
      List.cons_append]
    exact ⟨_, _, rfl⟩

/-- A packed step statement's constant leaves reach a scalar leaf, at any Lagrange table of its
size. -/
theorem StepStatement.leafHasScalar_packed {ks n nc : ℕ}
    (st : StepStatement (UnfinalizedProof ks (FVar Fq) (BoolVar Fq)
      (Type2 (SplitField (FVar Fq) (BoolVar Fq)))) (FVar Fq) n)
    (lagrange : Vector (Vector IpaVesta.curve.Point nc)
      (CircuitType.size Fp (StepStatement (UnfVal ks) Fp n))) :
    leafHasScalar (List.zipWith (constLeaf (C := IpaVesta.curve)) st.packed.toList
      lagrange.toList) := by
  obtain ⟨x, rest, hx⟩ := st.packed_head
  obtain ⟨Ps, lb, hlb⟩ := List.exists_cons_of_ne_nil (l := lagrange.toList)
    (by simp [StepStatement.size_eq])
  rw [hlb, hx]
  simp [constLeaf, leafHasScalar]

open scoped Kimchi in
/-- A step key has at most `2^32` chunks: its domain exponent is at most `Fp`'s two-adicity,
`32` (`Key.domainLog2_le`), and the chunk count is at most the domain size. -/
private theorem nc_le_vesta {nc : ℕ} (σ : SRS IpaVesta.curve.Point) (K : Key IpaVesta.curve nc)
    (hnc : nc = chunkCount σ.k K.cvk.domainLog2) : nc ≤ 2 ^ 32 := by
  have hd : K.cvk.domainLog2 ≤ 32 := K.domainLog2_le
  calc nc ≤ K.cvk.n := (Key.nc_le_n hnc)
    _ = 2 ^ K.cvk.domainLog2 := rfl
    _ ≤ 2 ^ 32 := Nat.pow_le_pow_right two_pos hd

/-- The wrap side's base field's characteristic exceeds the group half's absorb count. -/
private theorem char_guard_fq (m : ℕ) (hm : m ≤ 5 + 48 * 2 ^ 32) (h0 : (m : Fq) = 0) :
    m = 0 := by
  have hd : PALLAS_SCALAR_CARD ∣ m := (ZMod.natCast_eq_zero_iff m PALLAS_SCALAR_CARD).mp h0
  exact Nat.eq_zero_of_dvd_of_lt hd (lt_of_le_of_lt hm (by norm_num [PALLAS_SCALAR_CARD]))

open scoped Kimchi in
/-- The wrap side's group-half hypotheses at masked `sg` cells, at most two, from the proof
cells reading as `cp`'s, the `sg` cells as its old accumulators' under their bits, and the key
cells and the sponge after the key as `VkReads`, with the shifted claims' `IvpSide.ClaimOk`
(`wrapSide_claimOk`) and the shape guards proved. -/
theorem ivpHyps_of_reads_wrap {nc np : ℕ} {V : Valuation Fq} {S : Srs IpaVesta.curve}
    {K : Key IpaVesta.curve nc} (hnc : nc = chunkCount S.σ.k K.cvk.domainLog2)
    {cp : KimchiProof IpaVesta.curve nc S.σ.k} {pub : Array Fp}
    {keyCells : VkComms nc (AffinePoint (FVar Fq))} {spongeAfterIndex : SpongeVar Fq}
    (dv : DeferredValues S.σ.k (FVar Fq) (Type1 (FVar Fq)))
    (sgOld : Vector (Option (BoolVar Fq) × AffinePoint (FVar Fq)) np)
    (proof : IvpProof S.σ.k nc (FVar Fq) (Type1 (FVar Fq)))
    (u : UnfinalizedProof S.σ.k (FVar Fq) (BoolVar Fq) (Type1 (FVar Fq)))
    (oldsW : Vector (IpaVesta.curve.Point × Bool) np)
    (hmask : ∀ m ∈ sgOld, m.1.isSome = true) (hnp : np ≤ MaxProofsVerified)
    (hproof : ProofReads (wrapSide V) proof.wComm proof.zComm proof.tComm proof.opening cp)
    (holds : OldsRead V sgOld cp oldsW)
    (hvk : VkReads K.cvk V spongeAfterIndex keyCells) :
    IvpHyps (wrapSide V) S.σ K.cvk cp pub true spongeAfterIndex
      ((ivpInputOf dv sgOld keyCells proof).withClaims u) oldsW := by
  refine
    { idx := hvk.idx, mask := hmask
      ties :=
        { olds := holds, proof := hproof, key := hvk.key
          claimOk := fun x _ => wrapSide_claimOk V x }
      nc_pos := K.cvk.nc_pos, k_pos := S.rounds_pos, char := ?char }
  case char =>
    intro m hm h0
    refine char_guard_fq m (le_trans hm ?_) h0
    have h1 := hnp
    simp only [MaxProofsVerified] at h1
    have h5 := nc_le_vesta S.σ K hnc
    omega

end WrapRead

/-! Sealed after its read: a consumer composes `wrapVerify_reads`. -/
attribute [irreducible] wrapVerify

end Pickles
