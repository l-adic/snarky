import Pickles.IncrementallyVerify
import Pickles.MessageHash
import Pickles.TwoHalves
import Pickles.Verify

/-!
# `Wrap.Main`'s verify block

The port of PS `Pickles.Wrap.Verify.wrapVerify`, the wrap circuit's group half over the step
proof it verifies. It is `incrementally_verify_proof` on the conditional sponge plus the four
assertions the block makes:

* the opening's success bit holds outright — the wrap side has no `should_finalize` to defer
  it to, unlike `Step_verifier.verify`, which returns the bit;
* the accumulator advice hashes to the `messages_for_next_wrap_proof` digest the statement
  claims (`hashMessagesForNextWrapProof`), which is what binds this proof's `sg` and round
  challenges to the statement the next proof verifies;
* the fq digest equals the claimed `sponge_digest_before_evaluations`;
* each returned round prechallenge equals its claim, pair by pair over the zip.

The message sponge is the caller's, as in PureScript: the deployed block starts it from the
checkpoint that has already absorbed the dummy padding, so those absorptions stay out of the
circuit.

`wrapVerify_reads` is the block's reading, the wrap-side counterpart of `verifyProof_reads`:
the group half at `IvpHyps` through `incrementallyVerifyProof_reads`, the assertion loop by
its invariant, and the success bit through `assert_spec`, so the read comes out as
`VerifyReads` at a bit that reads `1` rather than at a returned bit. The digest assertion is
read trivially (`builder_spec_true`): it ties the claimed digest to advice no statement of the
group half mentions.

`wrapVerify_wrap_reads` is that read at the deployed Vesta constants. `wrapVerifyAt` is the
block at an environment — the blinding base the SRS's, as a constant cell, and `x_hat`
computed the one way the deployed circuit computes it, `publicInputCommitFull` over the packed
step statement at the key's own Lagrange table (`XhatTable.ofKey`) — and `wrapVerifyAt_reads`
its read: the public input is then the packed statement's (`wrapPublicInput`), and what the
table reads as is proved from the environment's invariants rather than assumed.
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
    (cells : IvpInput k (FVar F) (BoolVar F) sf) : CircuitM F c PUnit := do
  let o ← incrementallyVerifyProof ops e p endo gm sqrtF true blindingH spongeAfterIndex
    computeXHat (cells.withClaims u)
  assert o.success
  let d ← hashMessagesForNextWrapProof p msgSponge newBpChallenges cells.opening.sg
  assertEqual claimedMsgDigest d
  assertEqual u.spongeDigestBeforeEvaluations o.spongeDigest
  for cc in u.deferredValues.bulletproofChallenges.toList.zip o.bulletproofChallenges do
    assertEqual cc.1.val cc.2.val
  pure PUnit.unit

/-! ## The read -/

section Read

open Std.Do Kimchi.Verifier Bulletproof Bulletproof.Ipa
open CompElliptic.CurveForms.ShortWeierstrass

variable {C : KimchiCurve} {V : Valuation C.BaseField} {sf : Type}
  {ops : IpaScalarOps C.BaseField (Builder V (KimchiConstraint C.BaseField)) sf}

/-- **`Wrap.Main`'s verify block reads as the group half, with its success bit forced.** On the
group side `S`, with `x_hat` bound to the wire's public commitment and the group half's
premises at the claims-substituted cells, the block's output satisfies `VerifyReads` at some
bit, and that bit reads `1` — the block asserts it rather than returning it, so a satisfying
valuation has it set. The message digest is read trivially: the block's own assertion ties the
claimed digest to the advice it hashes, which no statement of the group half mentions. This is
what discharges the wrap capstone's group-half hypothesis. -/
theorem wrapVerify_reads {nc : ℕ} (S : IvpSide C V ops) (σ : SRS C.Point)
    (cvk : KimchiVK C nc) (cp : KimchiProof C nc σ.k) (pub : Array C.ScalarField)
    (endo : FVar C.BaseField) (sqrtF : C.BaseField → Option C.BaseField)
    (blindingH : AffinePoint (FVar C.BaseField)) (spongeAfterIndex : SpongeVar C.BaseField)
    (computeXHat : CircuitM C.BaseField (Builder V (KimchiConstraint C.BaseField))
      (List (AffinePoint (FVar C.BaseField))))
    (msgSponge : SpongeVar C.BaseField) (newBpChallenges : List (List (FVar C.BaseField)))
    (claimedMsgDigest : FVar C.BaseField)
    (u : UnfinalizedProof σ.k (FVar C.BaseField) (BoolVar C.BaseField) sf)
    (cells : IvpInput σ.k (FVar C.BaseField) (BoolVar C.BaseField) sf)
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
    exact ⟨o.success, ⟨o, hivp', rfl, hdig, fun _ => hall⟩, hsucc⟩

end Read

/-! ## The read at the deployed wrap side -/

section WrapRead

open Std.Do Kimchi.Verifier Bulletproof Bulletproof.Ipa
open CompElliptic.Fields.Pasta CompElliptic.Curves.Pasta
open CompElliptic.CurveForms.ShortWeierstrass

/-- **`Wrap.Main`'s verify block reads as the group half on the wrap side**: `wrapVerify_reads`
at `wrapSide` and the deployed Vesta constants — the conditional sponge, `sg_old` under its
mask, the `Type1` claims. The wrap-side counterpart of `verifyProof_step_reads`. -/
theorem wrapVerify_wrap_reads {nc : ℕ} {V : Valuation Fq}
    (σ : SRS IpaVesta.curve.Point) (cvk : KimchiVK IpaVesta.curve nc)
    (cp : KimchiProof IpaVesta.curve nc σ.k) (pub : Array Fp)
    (endo : FVar Fq) (sqrtF : Fq → Option Fq) (blindingH : AffinePoint (FVar Fq))
    (spongeAfterIndex : SpongeVar Fq)
    (computeXHat : CircuitM Fq (Builder V (KimchiConstraint Fq)) (List (AffinePoint (FVar Fq))))
    (msgSponge : SpongeVar Fq) (newBpChallenges : List (List (FVar Fq)))
    (claimedMsgDigest : FVar Fq)
    (u : UnfinalizedProof σ.k (FVar Fq) (BoolVar Fq) (Type1 (FVar Fq)))
    (cells : IvpInput σ.k (FVar Fq) (BoolVar Fq) (Type1 (FVar Fq)))
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

/-- The step statement's `x_hat` leaves at the key's own table. -/
def wrapLeavesAt {ks n : ℕ} (E : Env IpaVesta.curve)
    (statement : StepStatement ks n (FVar Fq) (BoolVar Fq)
      (Type2 (SplitField (FVar Fq) (BoolVar Fq)))) : List (Leaf Fq 1) :=
  packLeavesOf statement.packed (XhatTable.ofKey statement.packed E.cvk.lagrangeBasis.toList)

/-- The public input the wrap circuit's statement packs to, under a valuation: what the
verified step proof's public input must be. -/
def wrapPublicInput {ks n : ℕ} (E : Env IpaVesta.curve) (V : Valuation Fq)
    (statement : StepStatement ks n (FVar Fq) (BoolVar Fq)
      (Type2 (SplitField (FVar Fq) (BoolVar Fq)))) : Array Fp :=
  pubOf IpaVesta.curve V (wrapLeavesAt E statement)

/-- The wrap circuit's verify block at an environment: the deployed Vesta constants, the SRS
blinding base as a constant cell, and `x_hat` from the packed step statement. -/
def wrapVerifyAt {c : Type} [BasicSystem Fq c] [KimchiSystem Fq c] {ks n k : ℕ}
    (E : Env IpaVesta.curve)
    (statement : StepStatement ks n (FVar Fq) (BoolVar Fq)
      (Type2 (SplitField (FVar Fq) (BoolVar Fq))))
    (spongeAfterIndex msgSponge : SpongeVar Fq) (newBpChallenges : List (List (FVar Fq)))
    (claimedMsgDigest : FVar Fq)
    (u : UnfinalizedProof k (FVar Fq) (BoolVar Fq) (Type1 (FVar Fq)))
    (cells : IvpInput k (FVar Fq) (BoolVar Fq) (Type1 (FVar Fq))) : CircuitM Fq c PUnit :=
  wrapVerify IpaScalarOps.wrap IpaEndo.vesta IpaVesta.curve.sponge.params
    (.const ((Pasta.pallasLam : ℤ) : Fq)) groupMapParamsVesta vestaBase.sqrt? (constPt E.σ.h)
    spongeAfterIndex
    (do
      let P ← publicInputCommitFull (0 : Fin 1) (constPt E.σ.h) (wrapLeavesAt E statement)
      pure [P])
    msgSponge newBpChallenges claimedMsgDigest u cells

/-- A packed step statement opens with a full scalar: a slot's split `cip`, or with no slot
the `messages_for_next_step_proof` digest. -/
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

/-- **The block at an environment reads as the group half at the packed statement.** What
`wrapVerify_wrap_reads` takes as premises about `x_hat` and the blinding cell is proved
here from the environment: the table is the key's by construction (`xhatBinding_const`).
What is left is what no table can give — the statement's full scalars avoid the ladder's
sixteen-value band, and the group half's cells are the proof's. The statement's boolean cells
being boolean is not left: the `x_hat` gadget constrains them itself. -/
theorem wrapVerifyAt_reads {ks n : ℕ} {V : Valuation Fq}
    (E : Env IpaVesta.curve) (cp : KimchiProof IpaVesta.curve 1 E.σ.k)
    (statement : StepStatement ks n (FVar Fq) (BoolVar Fq)
      (Type2 (SplitField (FVar Fq) (BoolVar Fq))))
    (spongeAfterIndex msgSponge : SpongeVar Fq) (newBpChallenges : List (List (FVar Fq)))
    (claimedMsgDigest : FVar Fq)
    (u : UnfinalizedProof E.σ.k (FVar Fq) (BoolVar Fq) (Type1 (FVar Fq)))
    (cells : IvpInput E.σ.k (FVar Fq) (BoolVar Fq) (Type1 (FVar Fq)))
    (hoff : ∀ leaf ∈ wrapLeavesAt E statement, Leaf.offBand IpaVesta.curve.scalar V leaf)
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
  -- the binding, under the boolean leaves' booleanity: the `x_hat` read supplies that
  have hbind := fun hb : ∀ leaf ∈ wrapLeavesAt E statement, leaf.bitBoolean V =>
    xhatBinding_const (V := V) pastaShapeVesta (0 : Fin 1) E.σ E.cvk statement.packed E.h_ne
      E.lagrange_ne (hleaves ▸ hb) (hleaves ▸ hoff)
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
      (do
        let P ← publicInputCommitFull (S := Builder V (KimchiConstraint Fq)) (0 : Fin 1)
          (constPt E.σ.h) (wrapLeavesAt E statement)
        pure [P])
      ⦃⇓ pts _ => ⌜CommReads IpaVesta.curve V pts (publicCommitment IpaVesta.curve E.σ E.cvk
        (wrapPublicInput E V statement)).toList⌝⦄ := by
    have h0 := xHat_reads_publicCommitment pastaShapeVesta (0 : Fin 1) E.σ E.cvk
      (constPt E.σ.h) (wrapLeavesAt E statement) _ _ (fun hb => hleaves ▸ hbind hb) hscalar
    have hl : ∀ pc : Vector IpaVesta.curve.Point 1, pc.toList = [pc[(0 : Fin 1)]] := by
      intro pc
      apply List.ext_getElem <;> simp
      rintro i rfl
      rfl
    mvcgen -trivial [h0]
    rename_i r _ hr
    rw [CommReads, hl]
    exact List.Forall₂.cons hr List.Forall₂.nil
  exact wrapVerify_wrap_reads E.σ E.cvk cp _ _ _ _ spongeAfterIndex _ msgSponge newBpChallenges
    claimedMsgDigest u cells oldsW hX (onCurveAt_constPt E.σ.h E.h_ne) hivp

end WrapRead

/-! The gadgets are sealed after their reads: a consumer composes `wrapVerify_reads` and
`wrapVerifyAt_reads`, never the bodies. -/
attribute [irreducible] wrapVerify wrapVerifyAt

end Pickles
