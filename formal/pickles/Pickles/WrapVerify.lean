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
bit forced to `1`. `wrapVerifyAt` fixes the environment: the SRS blinding base as a constant
cell, and the public-input commitment `publicInputCommitFull` over the packed step statement at
the key's Lagrange table (`XhatTable.ofKey`). Its read `wrapVerifyAt_reads` proves the table's
reading from the environment rather than assuming it. `wrapVerify_frame` carries what the
public-input commitment's rows force out of the block, and `wrapPublicInput_toList` states the
wrap public input as the packed step statement reduced into the scalar field
(`PackedScalar.reduced`).

`StepProof.groupCircuit` is the block as a circuit of its input (`StepProof.GroupIn`), with the
key's cells and the two sponges as constants; the top-level statement
(`stepProof_kimchiVerify_vesta`) compiles it.
-/

namespace Pickles

open Snarky Snarky.Kimchi

variable {F c : Type} [Field F] [DecidableEq F] [ToNat F] [BasicSystem F c] [KimchiSystem F c]

/-- The wrap circuit's verify block: the group half, then its four assertions. -/
def wrapVerify {sf : Type} {k : ℕ} (ops : IpaScalarOps F c sf) (e : IpaEndo F)
    (p : Poseidon.Params F) (endo : FVar F) (gm : GroupMapParams F) (sqrtF : F → Option F)
    (blindingH : AffinePoint (FVar F)) (spongeAfterIndex : SpongeVar F)
    (computeXHat : CircuitM F c (List (AffinePoint (FVar F)))) (msgSponge : SpongeVar F)
    (newBpChallenges : List (List (FVar F))) (claimedMsgDigest : FVar F)
    (u : UnfinalizedProof k (FVar F) (BoolVar F) sf)
    (cells : IvpInput k nc (FVar F) (BoolVar F) sf) : CircuitM F c PUnit := do
  let o ← incrementallyVerifyProof ops e p endo gm sqrtF true blindingH spongeAfterIndex
    computeXHat (cells.withClaims u)
  assert o.success
  let d ← hashMessagesForNextWrapProof p msgSponge newBpChallenges cells.opening.sg
  assertEqual claimedMsgDigest d
  assertEqual u.spongeDigestBeforeEvaluations o.spongeDigest
  for cc in u.deferredValues.bulletproofChallenges.toList.zip o.bulletproofChallenges do
    assertEqual cc.1.val cc.2.val
  pure PUnit.unit

/-! ## A frame for the public-input commitment -/

section Frame

variable {F : Type} [Field F] [DecidableEq F] [ToNat F] {V : Valuation F}

open Std.Do in
/-- Whatever the public-input commitment's rows force of the valuation, the verify block's rows
force too (`incrementallyVerifyProof_frame`). -/
theorem wrapVerify_frame {sf : Type} {k : ℕ}
    (ops : IpaScalarOps F (Builder V (KimchiConstraint F)) sf) (e : IpaEndo F)
    (p : Poseidon.Params F) (endo : FVar F) (gm : GroupMapParams F) (sqrtF : F → Option F)
    (blindingH : AffinePoint (FVar F)) (spongeAfterIndex : SpongeVar F)
    (computeXHat : CircuitM F (Builder V (KimchiConstraint F)) (List (AffinePoint (FVar F))))
    (msgSponge : SpongeVar F) (newBpChallenges : List (List (FVar F)))
    (claimedMsgDigest : FVar F) (u : UnfinalizedProof k (FVar F) (BoolVar F) sf)
    (cells : IvpInput k nc (FVar F) (BoolVar F) sf) (P : Prop)
    (hX : ⦃⌜True⌝⦄ computeXHat ⦃⇓ _ _ => ⌜P⌝⦄) :
    ⦃⌜True⌝⦄
    wrapVerify ops e p endo gm sqrtF blindingH spongeAfterIndex computeXHat msgSponge
      newBpChallenges claimedMsgDigest u cells
    ⦃⇓ _ _ => ⌜P⌝⦄ := by
  have hivp := incrementallyVerifyProof_frame ops e p endo gm sqrtF blindingH spongeAfterIndex
    computeXHat (cells.withClaims u) P hX
  have hh := fun sg => builder_spec_true
    (hashMessagesForNextWrapProof (c := Builder V (KimchiConstraint F)) p msgSponge
      newBpChallenges sg)
  simp only [wrapVerify]
  mvcgen [hivp, hh] invariants
    · ⇓⟨_, _⟩ => ⌜P⌝

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
theorem wrapVerify_reads {nc : ℕ} (S : IvpSide C V ops) (σ : SRS C.Point)
    (cvk : KimchiVK C nc) (cp : KimchiProof C nc σ.k) (pub : Array C.ScalarField)
    (endo : FVar C.BaseField) (sqrtF : C.BaseField → Option C.BaseField)
    (blindingH : AffinePoint (FVar C.BaseField)) (spongeAfterIndex : SpongeVar C.BaseField)
    (computeXHat : CircuitM C.BaseField (Builder V (KimchiConstraint C.BaseField))
      (List (AffinePoint (FVar C.BaseField))))
    (msgSponge : SpongeVar C.BaseField) (newBpChallenges : List (List (FVar C.BaseField)))
    (claimedMsgDigest : FVar C.BaseField)
    (u : UnfinalizedProof σ.k (FVar C.BaseField) (BoolVar C.BaseField) sf)
    (cells : IvpInput σ.k nc (FVar C.BaseField) (BoolVar C.BaseField) sf)
    (oldsW : List (C.Point × Bool))
    (hXhat : ⦃⌜True⌝⦄ computeXHat
      ⦃⇓ pts _ => ⌜CommReads C V pts (publicCommitment C σ cvk pub).toList⌝⦄)
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
    (hashMessagesForNextWrapProof C.sponge.params msgSponge newBpChallenges cells.opening.sg)
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
    exact ⟨o.success, ⟨o, hivp', rfl, hdig, fun _ => hall, true, by simp [bit, hsucc]⟩, hsucc⟩

end Read

/-! ## The read at the deployed wrap side -/

section WrapRead

open Std.Do Kimchi.Verifier Bulletproof Bulletproof.Ipa
open CompElliptic.Fields.Pasta CompElliptic.Curves.Pasta
open CompElliptic.CurveForms.ShortWeierstrass

/-- `wrapVerify_reads` at `wrapSide` and the deployed Vesta constants; the counterpart of
`verifyProof_step_reads`. -/
theorem wrapVerify_wrap_reads {nc : ℕ} {V : Valuation Fq}
    (σ : SRS IpaVesta.curve.Point) (cvk : KimchiVK IpaVesta.curve nc)
    (cp : KimchiProof IpaVesta.curve nc σ.k) (pub : Array Fp)
    (endo : FVar Fq) (sqrtF : Fq → Option Fq) (blindingH : AffinePoint (FVar Fq))
    (spongeAfterIndex : SpongeVar Fq)
    (computeXHat : CircuitM Fq (Builder V (KimchiConstraint Fq)) (List (AffinePoint (FVar Fq))))
    (msgSponge : SpongeVar Fq) (newBpChallenges : List (List (FVar Fq)))
    (claimedMsgDigest : FVar Fq)
    (u : UnfinalizedProof σ.k (FVar Fq) (BoolVar Fq) (Type1 (FVar Fq)))
    (cells : IvpInput σ.k nc (FVar Fq) (BoolVar Fq) (Type1 (FVar Fq)))
    (oldsW : List (IpaVesta.curve.Point × Bool))
    (hXhat : ⦃⌜True⌝⦄ computeXHat ⦃⇓ pts _ =>
      ⌜CommReads IpaVesta.curve V pts (publicCommitment IpaVesta.curve σ cvk pub).toList⌝⦄)
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

/-! ## The block at an environment -/

/-- The step statement's public-input leaves at the key's own Lagrange table. -/
def wrapLeavesAt {ks n nc : ℕ} (E : Env IpaVesta.curve nc)
    (statement : StepStatement ks n (FVar Fq) (BoolVar Fq)
      (Type2 (SplitField (FVar Fq) (BoolVar Fq)))) : List (Leaf Fq nc) :=
  packLeavesOf statement.packed (XhatTable.ofKey statement.packed E.cvk.lagrangeBasis.toList)

/-- The public input the step statement packs to under `V`: what the verified step proof's
public input must be. -/
def wrapPublicInput {ks n nc : ℕ} (E : Env IpaVesta.curve nc) (V : Valuation Fq)
    (statement : StepStatement ks n (FVar Fq) (BoolVar Fq)
      (Type2 (SplitField (FVar Fq) (BoolVar Fq)))) : Array Fp :=
  pubOf IpaVesta.curve V (wrapLeavesAt E statement)

/-- The public input a step statement packs to is its packed scalars reduced into the scalar
field (`PackedScalar.reduced`), when the key has a Lagrange point per packed scalar. -/
theorem wrapPublicInput_toList {ks n nc : ℕ} (E : Env IpaVesta.curve nc) (V : Valuation Fq)
    (statement : StepStatement ks n (FVar Fq) (BoolVar Fq)
      (Type2 (SplitField (FVar Fq) (BoolVar Fq))))
    (hlen : statement.packed.length ≤ E.cvk.lagrangeBasis.size) :
    (wrapPublicInput E V statement).toList
      = statement.packed.map (PackedScalar.reduced IpaVesta.curve V) := by
  unfold wrapPublicInput wrapLeavesAt
  rw [packLeavesOf_ofKey (C := IpaVesta.curve) statement.packed E.cvk.lagrangeBasis.toList]
  exact pubOf_zipWith_constLeaf _ _ (by simpa using hlen)

/-- The verify block at the deployed Vesta constants, the blinding base `h` as a constant cell,
and the public-input commitment of the packed step statement at the Lagrange points `lagrange`.
The CS-equality corpus pins this gadget at its dumps' points. -/
def wrapVerifyWith {c : Type} [BasicSystem Fq c] [KimchiSystem Fq c] {ks n k nc : ℕ}
    (h : IpaVesta.curve.Point) (lagrange : List (Vector IpaVesta.curve.Point nc))
    (statement : StepStatement ks n (FVar Fq) (BoolVar Fq)
      (Type2 (SplitField (FVar Fq) (BoolVar Fq))))
    (spongeAfterIndex msgSponge : SpongeVar Fq) (newBpChallenges : List (List (FVar Fq)))
    (claimedMsgDigest : FVar Fq)
    (u : UnfinalizedProof k (FVar Fq) (BoolVar Fq) (Type1 (FVar Fq)))
    (cells : IvpInput k nc (FVar Fq) (BoolVar Fq) (Type1 (FVar Fq))) : CircuitM Fq c PUnit :=
  wrapVerify IpaScalarOps.wrap IpaEndo.vesta IpaVesta.curve.sponge.params
    (.const ((Pasta.pallasLam : ℤ) : Fq)) groupMapParamsVesta vestaBase.sqrt? (constPt h)
    spongeAfterIndex
    (Vector.toList <$> publicInputCommitFull (constPt h)
      (packLeavesOf statement.packed (XhatTable.ofKey statement.packed lagrange)))
    msgSponge newBpChallenges claimedMsgDigest u cells

/-- `wrapVerifyWith` at the environment's SRS blinding base and the key's Lagrange points. -/
def wrapVerifyAt {c : Type} [BasicSystem Fq c] [KimchiSystem Fq c] {ks n k nc : ℕ}
    (E : Env IpaVesta.curve nc)
    (statement : StepStatement ks n (FVar Fq) (BoolVar Fq)
      (Type2 (SplitField (FVar Fq) (BoolVar Fq))))
    (spongeAfterIndex msgSponge : SpongeVar Fq) (newBpChallenges : List (List (FVar Fq)))
    (claimedMsgDigest : FVar Fq)
    (u : UnfinalizedProof k (FVar Fq) (BoolVar Fq) (Type1 (FVar Fq)))
    (cells : IvpInput k nc (FVar Fq) (BoolVar Fq) (Type1 (FVar Fq))) : CircuitM Fq c PUnit :=
  wrapVerifyWith E.σ.h E.cvk.lagrangeBasis.toList statement spongeAfterIndex msgSponge
    newBpChallenges claimedMsgDigest u cells

/-- A packed step statement opens with a full scalar: the first slot's combined inner product,
or with no slot the `messagesForNextStepProof` digest. -/
theorem StepStatement.packed_head {ks n : ℕ}
    (st : StepStatement ks n (FVar Fq) (BoolVar Fq) (Type2 (SplitField (FVar Fq) (BoolVar Fq)))) :
    ∃ x rest, st.packed = .full x :: rest := by
  unfold StepStatement.packed
  cases st.proofState.unfinalizedProofs.toList with
  | nil =>
    simp only [List.flatMap_nil, List.nil_append, List.cons_append]
    exact ⟨_, _, rfl⟩
  | cons u us =>
    simp only [List.flatMap_cons, List.append_assoc, List.cons_append]
    exact ⟨_, _, rfl⟩

/-- **The block at an environment reads as the group half at the packed statement.** The
public-input and blinding-cell premises of `wrapVerify_wrap_reads` are proved from the
environment (`xhatBinding_const`). Left as hypotheses: the SRS avoids the Lagrange relations,
and `IvpHyps`. The boolean leaves'
booleanity is not left: the commitment gadget constrains it. -/
theorem wrapVerifyAt_reads {ks n nc : ℕ} {V : Valuation Fq}
    (E : Env IpaVesta.curve nc) (cp : KimchiProof IpaVesta.curve nc E.σ.k)
    (statement : StepStatement ks n (FVar Fq) (BoolVar Fq)
      (Type2 (SplitField (FVar Fq) (BoolVar Fq))))
    (spongeAfterIndex msgSponge : SpongeVar Fq) (newBpChallenges : List (List (FVar Fq)))
    (claimedMsgDigest : FVar Fq)
    (u : UnfinalizedProof E.σ.k (FVar Fq) (BoolVar Fq) (Type1 (FVar Fq)))
    (cells : IvpInput E.σ.k nc (FVar Fq) (BoolVar Fq) (Type1 (FVar Fq)))
    (havoid : E.σ.Avoids E.lagrangeRelations)
    (hivp : ∃ oldsW, IvpHyps (wrapSide V) E.σ E.cvk cp (wrapPublicInput E V statement) true
      spongeAfterIndex (cells.withClaims u) oldsW) :
    ⦃⌜True⌝⦄
    wrapVerifyAt (c := Builder V (KimchiConstraint Fq)) E statement spongeAfterIndex msgSponge
      newBpChallenges claimedMsgDigest u cells
    ⦃⇓ _ _ => ⌜∃ v : BoolVar Fq,
      VerifyReads (wrapSide V) E.σ E.cvk cp (wrapPublicInput E V statement) u false v ∧
        (↑v : CVar Fq).val V = 1⌝⦄ := by
  obtain ⟨oldsW, hivp⟩ := hivp
  have hleaves : wrapLeavesAt E statement
      = List.zipWith constLeaf statement.packed E.cvk.lagrangeBasis.toList := by
    unfold wrapLeavesAt
    exact packLeavesOf_ofKey (C := IpaVesta.curve) _ _
  -- the binding at each chunk, under the boolean leaves' booleanity, which the commitment's
  -- read supplies
  have hbind := fun (ci : Fin nc) (hb : ∀ leaf ∈ wrapLeavesAt E statement, leaf.bitBoolean V) =>
    xhatBinding_const (V := V) pastaShapeVesta ci E.σ E.cvk statement.packed E.h_ne
      (fun Ps h => E.lagrange_ne pastaShapeVesta havoid Ps h ci) (hleaves ▸ hb)
  have hscalar : leafHasScalar (wrapLeavesAt E statement) := by
    obtain ⟨x, rest, hx⟩ := statement.packed_head
    obtain ⟨Ps, lb, hlb⟩ := List.exists_cons_of_ne_nil
      (l := E.cvk.lagrangeBasis.toList) (by
        intro h0
        have := E.lagrange_pos
        simp [← Array.length_toList, h0] at this)
    rw [hleaves, hx, hlb]
    simp [constLeaf, leafHasScalar]
  have hX : ⦃⌜True⌝⦄
      (Vector.toList <$> publicInputCommitFull (S := Builder V (KimchiConstraint Fq))
        (constPt E.σ.h) (wrapLeavesAt E statement))
      ⦃⇓ pts _ => ⌜CommReads IpaVesta.curve V pts (publicCommitment IpaVesta.curve E.σ E.cvk
        (wrapPublicInput E V statement)).toList⌝⦄ := by
    have h0 := builder_spec_forall _ (fun _ : Fin nc => True) _ fun ci _ =>
      xHat_reads_publicCommitment pastaShapeVesta ci E.σ E.cvk (constPt E.σ.h)
        (wrapLeavesAt E statement) _ _ (fun hb => hleaves ▸ hbind ci hb) hscalar
    mvcgen -trivial [h0]
    intro hr
    exact List.forall₂_iff_get.mpr ⟨by simp [wrapPublicInput], fun i h₁ h₂ => by
      simpa [wrapPublicInput] using hr ⟨i, by simpa using h₁⟩⟩
  exact wrapVerify_wrap_reads E.σ E.cvk cp _ _ _ _ spongeAfterIndex _ msgSponge newBpChallenges
    claimedMsgDigest u cells oldsW hX (onCurveAt_constPt E.σ.h E.h_ne) hivp

open scoped Kimchi in
/-- A step key has at most `2^32` chunks: its domain size divides `|Fp| − 1`, whose two-adic
part is `2^32`, and the chunk count is at most the domain size. -/
private theorem nc_le_vesta {nc : ℕ} (E : Env IpaVesta.curve nc) : nc ≤ 2 ^ 32 := by
  have hω0 : E.cvk.omega ≠ 0 := E.omega_prim.ne_zero (by rw [KimchiVK.n]; positivity)
  have hn : E.cvk.n ∣ PALLAS_BASE_CARD - 1 :=
    E.omega_prim.dvd_of_pow_eq_one _ (ZMod.pow_card_sub_one_eq_one hω0)
  have hd : E.cvk.domainLog2 ≤ 32 := by
    by_contra h
    have h33 : 2 ^ 33 ∣ PALLAS_BASE_CARD - 1 :=
      (Nat.pow_dvd_pow 2 (show 33 ≤ E.cvk.domainLog2 by omega)).trans hn
    exact absurd h33 (by norm_num [PALLAS_BASE_CARD])
  calc nc ≤ E.cvk.n := E.nc_le_n
    _ = 2 ^ E.cvk.domainLog2 := rfl
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
theorem ivpHyps_of_reads_wrap {nc : ℕ} {V : Valuation Fq} {E : Env IpaVesta.curve nc}
    {cp : KimchiProof IpaVesta.curve nc E.σ.k} {pub : Array Fp}
    {keyCells : VkComms nc (AffinePoint (FVar Fq))} {spongeAfterIndex : SpongeVar Fq}
    (dv : DeferredValues E.σ.k (FVar Fq) (Type1 (FVar Fq)))
    (sgOld : List (Option (BoolVar Fq) × AffinePoint (FVar Fq)))
    (proof : IvpProof E.σ.k nc (FVar Fq) (Type1 (FVar Fq)))
    (u : UnfinalizedProof E.σ.k (FVar Fq) (BoolVar Fq) (Type1 (FVar Fq)))
    (oldsW : List (IpaVesta.curve.Point × Bool))
    (hmask : ∀ m ∈ sgOld, m.1.isSome = true) (hlen : sgOld.length ≤ 2)
    (hproof : ProofReads (wrapSide V) (proof.wComm.toList.map (·.toList)) proof.zComm.toList
      proof.tComm.toList proof.opening cp)
    (holds : OldsRead V sgOld cp oldsW)
    (hvk : VkReads E.cvk V spongeAfterIndex keyCells) :
    IvpHyps (wrapSide V) E.σ E.cvk cp pub true spongeAfterIndex
      ((ivpInputOf dv sgOld keyCells proof).withClaims u) oldsW := by
  have hl := ivpInputOf_lengths dv sgOld keyCells proof
  refine
    { idx := hvk.idx, mask := hmask
      ties :=
        { olds := holds, proof := hproof, key := hvk.key
          claimOk := fun x _ => wrapSide_claimOk V x }
      nc_pos := E.nc_pos, t_ne := ?tne, lr_ne := ?lrne, char := ?char }
  case tne =>
    intro he
    have he' : (ivpInputOf dv sgOld keyCells proof).tComm = [] := he
    have h4 : (ivpInputOf dv sgOld keyCells proof).tComm.length = quotChunks * nc := hl.2.2
    rw [he', List.length_nil] at h4
    have := E.nc_pos
    omega
  case lrne =>
    intro he
    have hlen' := congrArg List.length he
    rw [List.length_nil] at hlen'
    exact absurd (by simpa using hlen') (Nat.pos_iff_ne_zero.mp E.rounds_pos)
  case char =>
    intro m hm h0
    refine char_guard_fq m (le_trans hm ?_) h0
    have h2 : (ivpInputOf dv sgOld keyCells proof).wComm.flatten.length = 15 * nc := hl.1
    have h3 : (ivpInputOf dv sgOld keyCells proof).zComm.length = nc := hl.2.1
    have h4 : (ivpInputOf dv sgOld keyCells proof).tComm.length = quotChunks * nc := hl.2.2
    have h1 : (ivpInputOf dv sgOld keyCells proof).sgOld.length ≤ 2 := hlen
    have h5 := nc_le_vesta E
    simp only [IvpInput.withClaims] at *
    omega

end WrapRead

/-! ## The verify block, of its input -/

section Records

open CompElliptic.Fields.Pasta

/-- The wrap circuit's group half of a step proof, polymorphic in its cells, at the wrap
statement's `ks` rounds (the step proof's), the step statement's `kw` (its slots' wrap proofs')
and its `n` slots. The keep bits of the accumulators are the wrap statement's branch data. -/
structure WrapGroup (ks kw n nc : ℕ) (f b : Type) where
  /-- The wrap statement. -/
  statement : WrapStatement ks f b (Type1 f)
  /-- The step statement: the verified proof's public input. -/
  stepStatement : StepStatement kw n f b (Type2 (SplitField f b))
  /-- The step proof, at `nc` chunks. -/
  proof : IvpProof ks nc f (Type1 f)
  /-- The step proof's `n` accumulators' `sg`. -/
  sgOld : Vector (AffinePoint f) n

/-- A wrap-side group half is its two statements, the proof and the accumulators' `sg`. -/
def WrapGroup.equivProd (ks kw n nc : ℕ) (f b : Type) :
    WrapGroup ks kw n nc f b ≃
      WrapStatement ks f b (Type1 f) × StepStatement kw n f b (Type2 (SplitField f b)) ×
        IvpProof ks nc f (Type1 f) × Vector (AffinePoint f) n :=
  ⟨fun g => (g.statement, g.stepStatement, g.proof, g.sgOld),
   fun p => ⟨p.1, p.2.1, p.2.2.1, p.2.2.2⟩, fun _ => rfl, fun _ => rfl⟩

instance instWrapGroupCircuitType {F : Type} {ks kw n nc : ℕ} [CircuitType F Bool (BoolVar F)] :
    CircuitType F (WrapGroup ks kw n nc F Bool) (WrapGroup ks kw n nc (FVar F) (BoolVar F)) :=
  CircuitType.ofEquiv (WrapGroup.equivProd ks kw n nc F Bool)
    (WrapGroup.equivProd ks kw n nc (FVar F) (BoolVar F))

namespace StepProof

variable {k kw n nc : ℕ}

/-- The group circuit's input, polymorphic in its cells: the group half and the slots'
expanded round challenges the message hash absorbs. -/
structure GroupInput (k kw n nc : ℕ) (f b : Type) where
  /-- The group half. -/
  group : WrapGroup k kw n nc f b
  /-- The slots' expanded round challenges. -/
  newBp : Vector (Vector f kw) n

/-- A group input is the group half and the expanded round challenges. -/
def GroupInput.equivProd (k kw n nc : ℕ) (f b : Type) :
    GroupInput k kw n nc f b ≃ WrapGroup k kw n nc f b × Vector (Vector f kw) n :=
  ⟨fun g => (g.group, g.newBp), fun p => ⟨p.1, p.2⟩, fun _ => rfl, fun _ => rfl⟩

instance instGroupInputCircuitType {F : Type} [CircuitType F Bool (BoolVar F)] :
    CircuitType F (GroupInput k kw n nc F Bool) (GroupInput k kw n nc (FVar F) (BoolVar F)) :=
  CircuitType.ofEquiv (GroupInput.equivProd k kw n nc F Bool)
    (GroupInput.equivProd k kw n nc (FVar F) (BoolVar F))

/-- The group circuit's input, as values. Unchecked: the block's own rows constrain what it
reads. -/
abbrev GroupIn (k kw n nc : ℕ) : Type := UnChecked (GroupInput k kw n nc Fq Bool)

/-- `GroupIn`, as cells. -/
abbrev GroupVar (k kw n nc : ℕ) : Type :=
  UnChecked (GroupInput k kw n nc (FVar Fq) (BoolVar Fq))

/-- The step statement: the verified proof's public input. -/
def GroupVar.stepStatement (g : GroupVar k kw n nc) :
    StepStatement kw n (FVar Fq) (BoolVar Fq) (Type2 (SplitField (FVar Fq) (BoolVar Fq))) :=
  g.val.group.stepStatement

/-- The slots' expanded round challenges. -/
def GroupVar.newBp (g : GroupVar k kw n nc) : List (List (FVar Fq)) :=
  g.val.newBp.toList.map (·.toList)

/-- The wrap statement's `messagesForNextWrapProof` digest. -/
def GroupVar.msgDigest (g : GroupVar k kw n nc) : FVar Fq :=
  g.val.group.statement.proofState.messagesForNextWrapProof

/-- The wrap statement's deferred claims, as the unfinalized proof the block verifies. -/
def GroupVar.claims (g : GroupVar k kw n nc) :
    UnfinalizedProof k (FVar Fq) (BoolVar Fq) (Type1 (FVar Fq)) :=
  { deferredValues := g.val.group.statement.proofState.deferredValues.toDeferredValues
    shouldFinalize := true_
    spongeDigestBeforeEvaluations :=
      g.val.group.statement.proofState.spongeDigestBeforeEvaluations }

/-- The step proof's witness commitments, `nc` chunks each. -/
def GroupVar.wComm (g : GroupVar k kw n nc) : List (List (AffinePoint (FVar Fq))) :=
  g.val.group.proof.wComm.toList.map (·.toList)

/-- The step proof's permutation-accumulator commitment, `nc` chunks. -/
def GroupVar.zComm (g : GroupVar k kw n nc) : List (AffinePoint (FVar Fq)) :=
  g.val.group.proof.zComm.toList

/-- The step proof's quotient chunks. -/
def GroupVar.tComm (g : GroupVar k kw n nc) : List (AffinePoint (FVar Fq)) :=
  g.val.group.proof.tComm.toList

/-- The step proof's opening. -/
def GroupVar.opening (g : GroupVar k kw n nc) : BulletproofOpening k (FVar Fq) (Type1 (FVar Fq)) :=
  g.val.group.proof.opening

/-- The accumulators' `sg`, each under its keep bit: the last `n` of the branch data's mask. -/
def GroupVar.sgOld (g : GroupVar k kw n nc) : List (Option (BoolVar Fq) × AffinePoint (FVar Fq)) :=
  let bd := g.val.group.statement.proofState.deferredValues.branchData
  let mask := bd.proofsVerifiedMask.toList.drop (MaxProofsVerified - n)
  (mask.zip g.val.group.sgOld.toList).map fun (m, P) => (some m, P)

/-- The shifted scalars the block scales by: the claims' `perm`, `ζ^{2^k}`, `ζⁿ`, `cip`, `b`
and the opening's `z₁`, `z₂`. -/
def GroupVar.shifted (g : GroupVar k kw n nc) : List (Type1 (FVar Fq)) :=
  let dv := g.claims.deferredValues
  [dv.plonk.perm, dv.plonk.zetaToSrsLength, dv.plonk.zetaToDomainSize, dv.combinedInnerProduct,
   dv.b, g.opening.z1, g.opening.z2]

/-- What `incrementallyVerifyProof` consumes: the claims, the accumulators, the key's cells, the
proof. -/
def GroupVar.cells (keyCells : VkComms nc (AffinePoint (FVar Fq))) (g : GroupVar k kw n nc) :
    IvpInput k nc (FVar Fq) (BoolVar Fq) (Type1 (FVar Fq)) :=
  ivpInputOf g.val.group.statement.proofState.deferredValues.toDeferredValues g.sgOld keyCells
    g.val.group.proof

/-- The group circuit as a `GroupHalf`. -/
abbrev GroupVar.half (V : Valuation Fq) (g : GroupVar k kw n nc) :
    GroupHalf Bulletproof.IpaVesta.curve (Type1 (FVar Fq)) k := GroupHalf.wrap V g.claims

/-- The verify block as a circuit of its input: `wrapVerifyAt` on the input, with the key's
cells and the two sponges as constants. -/
def groupCircuit {c : Type} [BasicSystem Fq c] [KimchiSystem Fq c]
    (E : Env Bulletproof.IpaVesta.curve nc) (keyCells : VkComms nc (AffinePoint (FVar Fq)))
    (spongeAfterIndex msgSponge : SpongeVar Fq) (g : GroupVar k kw n nc) : CircuitM Fq c Unit := do
  wrapVerifyAt E g.stepStatement spongeAfterIndex msgSponge g.newBp g.msgDigest g.claims
    (g.cells keyCells)

open Std.Do in
/-- **The group circuit's read.** Every wrap-side claim satisfies `IvpSide.ClaimOk`
(`wrapSide_claimOk`), which `IvpHyps` may assume. With the SRS avoiding the Lagrange relations,
a satisfying valuation reads as `VerifyReads` with its success bit `1`. -/
theorem groupCircuit_reads {V : Valuation Fq} (E : Env Bulletproof.IpaVesta.curve nc)
    (cp : Kimchi.Verifier.KimchiProof Bulletproof.IpaVesta.curve nc E.σ.k)
    (keyCells : VkComms nc (AffinePoint (FVar Fq))) (spongeAfterIndex msgSponge : SpongeVar Fq)
    (g : GroupVar E.σ.k kw n nc) (havoid : E.σ.Avoids E.lagrangeRelations)
    (hivp : (∀ x ∈ g.shifted, (wrapSide V).ClaimOk x) →
      ∃ oldsW, IvpHyps (wrapSide V) E.σ E.cvk cp (wrapPublicInput E V g.stepStatement) true
        spongeAfterIndex ((g.cells keyCells).withClaims g.claims) oldsW) :
    ⦃⌜True⌝⦄
    groupCircuit (c := Builder V (KimchiConstraint Fq)) E keyCells spongeAfterIndex msgSponge g
    ⦃⇓ _ _ => ⌜∃ v : BoolVar Fq,
      VerifyReads (wrapSide V) E.σ E.cvk cp (wrapPublicInput E V g.stepStatement) g.claims false
        v ∧ (↑v : CVar Fq).val V = 1⌝⦄ := by
  simp only [groupCircuit]
  exact wrapVerifyAt_reads (V := V) E cp g.stepStatement spongeAfterIndex msgSponge g.newBp
    g.msgDigest g.claims (g.cells keyCells) havoid (hivp fun x _ => wrapSide_claimOk V x)

end StepProof

end Records

/-! Sealed after their reads: a consumer composes `wrapVerify_reads` and `wrapVerifyAt_reads`. -/
attribute [irreducible] wrapVerify wrapVerifyAt

end Pickles
