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

`wrapVerify_wrap_reads` is that read at the deployed Vesta constants, and
`wrapVerify_kimchiVerify_vesta` hands it to `twoHalves_kimchiVerify_vesta`: the step proof's
group half is then discharged by the circuit rather than assumed, and its success bit leaves
the equivalence — the block asserts it, so every satisfying valuation has it set. What
remains is the next step circuit's `finalized` bit, with `SgOk`, against the deployed
verifier at honest claims.
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
    (h : IvpHyps S σ cvk cp pub true blindingH spongeAfterIndex (cells.withClaims u) oldsW) :
    ⦃⌜True⌝⦄
    wrapVerify (c := Builder V (KimchiConstraint C.BaseField)) ops S.curve.e C.sponge.params
      endo (.ofSpec C.groupMap) sqrtF blindingH spongeAfterIndex computeXHat msgSponge
      newBpChallenges claimedMsgDigest u cells
    ⦃⇓ _ _ => ⌜∃ v : BoolVar C.BaseField,
      VerifyReads S σ cvk cp pub u false v ∧ (↑v : CVar C.BaseField).val V = 1⌝⦄ := by
  have hivp := incrementallyVerifyProof_reads S σ cvk cp pub endo sqrtF true blindingH
    spongeAfterIndex computeXHat (cells.withClaims u) oldsW hXhat h
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
    (h : IvpHyps (wrapSide V) σ cvk cp pub true blindingH spongeAfterIndex
      (cells.withClaims u) oldsW) :
    ⦃⌜True⌝⦄
    wrapVerify (c := Builder V (KimchiConstraint Fq)) IpaScalarOps.wrap IpaEndo.vesta
      IpaVesta.curve.sponge.params endo groupMapParamsVesta sqrtF blindingH spongeAfterIndex
      computeXHat msgSponge newBpChallenges claimedMsgDigest u cells
    ⦃⇓ _ _ => ⌜∃ v : BoolVar Fq,
      VerifyReads (wrapSide V) σ cvk cp pub u false v ∧ (↑v : CVar Fq).val V = 1⌝⦄ :=
  wrapVerify_reads (wrapSide V) σ cvk cp pub endo sqrtF blindingH spongeAfterIndex computeXHat
    msgSponge newBpChallenges claimedMsgDigest u cells oldsW hXhat h

/-! ## The vesta capstone, its group half run -/

/-- **Running `Wrap.Main`'s verify block, a step proof's remaining half decides
`kimchiVerify`.** `twoHalves_kimchiVerify_vesta` with its group half supplied by
`wrapVerify_wrap_reads`: on any valuation satisfying the block's constraints, the next step
circuit's `finalized` bit together with `SgOk` is equivalent to the deployed verifier
accepting at honest claims. The group half's success bit has left the statement — the block
asserts it. -/
theorem wrapVerify_kimchiVerify_vesta
    (E : Env IpaVesta.curve)
    (cp : KimchiProof IpaVesta.curve 1 E.σ.k)
    (pub : Array Fp)
    (hguard : Guards IpaVesta.curve E.cvk cp pub)
    -- the wrap circuit: its valuation, its statement's claims and the group half's cells,
    -- the block's constants, and the group half's premises
    (Vg : Valuation Fq)
    (claimsG : UnfinalizedProof E.σ.k (FVar Fq) (BoolVar Fq) (Type1 (FVar Fq)))
    (cells : IvpInput E.σ.k (FVar Fq) (BoolVar Fq) (Type1 (FVar Fq)))
    (endo : FVar Fq) (sqrtF : Fq → Option Fq) (blindingH : AffinePoint (FVar Fq))
    (spongeAfterIndex : SpongeVar Fq)
    (computeXHat : CircuitM Fq (Builder Vg (KimchiConstraint Fq)) (List (AffinePoint (FVar Fq))))
    (msgSponge : SpongeVar Fq) (newBpChallenges : List (List (FVar Fq)))
    (claimedMsgDigest : FVar Fq)
    (oldsW : List (IpaVesta.curve.Point × Bool))
    (hXhat : ⦃⌜True⌝⦄ computeXHat ⦃⇓ pts _ =>
      ⌜CommReads IpaVesta.curve Vg pts
        (publicCommitment IpaVesta.curve E.σ E.cvk pub).toList⌝⦄)
    (hivp : IvpHyps (wrapSide Vg) E.σ E.cvk cp pub true blindingH spongeAfterIndex
      (cells.withClaims claimsG) oldsW)
    -- the next step circuit: its valuation, its cells, its output, its read
    (Vs : Valuation Fp)
    (claimsS : UnfinalizedProof E.σ.k (FVar Fp) (BoolVar Fp) (Type1 (FVar Fp)))
    (evals : AllEvals (FVar Fp))
    (mask : Vector Bool MaxProofsVerified)
    (prevChallenges : Vector (Vector Fp E.σ.k) MaxProofsVerified)
    (outS : FopOutput Fp)
    (hs : (ScalarHalf.step Vs claimsS evals mask prevChallenges outS).Reads E cp)
    -- across the two, at whichever bit the block exports
    (ht : ∀ v : BoolVar Fq, HalvesTies E cp pub (GroupHalf.wrap Vg claimsG v)
      (ScalarHalf.step Vs claimsS evals mask prevChallenges outS)) :
    ⦃⌜True⌝⦄
    wrapVerify (c := Builder Vg (KimchiConstraint Fq)) IpaScalarOps.wrap IpaEndo.vesta
      IpaVesta.curve.sponge.params endo groupMapParamsVesta sqrtF blindingH spongeAfterIndex
      computeXHat msgSponge newBpChallenges claimedMsgDigest claimsG cells
    ⦃⇓ _ _ => ⌜((↑outS.finalized : CVar Fp).val Vs = 1 ∧ SgOk E cp pub)
      ↔ kimchiVerify IpaVesta.curve E.σ E.cvk cp pub = true ∧
        (ScalarHalf.step Vs claimsS evals mask prevChallenges outS).ClaimsHonest E cp pub⌝⦄ := by
  refine builder_spec_imp _ _ _
    (wrapVerify_wrap_reads (V := Vg) E.σ E.cvk cp pub endo sqrtF blindingH spongeAfterIndex
      computeXHat msgSponge newBpChallenges claimedMsgDigest claimsG cells oldsW hXhat hivp)
    ?_
  rintro _ ⟨v, hv, hv1⟩
  rw [← twoHalves_kimchiVerify_vesta E cp pub hguard Vg claimsG v hv Vs claimsS evals mask
    prevChallenges outS hs (ht v)]
  exact ⟨fun hf => ⟨⟨hv1, hf.1⟩, hf.2⟩, fun hf => ⟨hf.1.2, hf.2⟩⟩

end WrapRead

/-! The gadget is sealed after its read: a consumer composes `wrapVerify_reads`, never the
body. -/
attribute [irreducible] wrapVerify

end Pickles
