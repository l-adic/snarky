import Pickles.IncrementallyVerify
import Pickles.MessageHash
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

/-! The gadget is sealed after its read: a consumer composes `wrapVerify_reads`, never the
body. -/
attribute [irreducible] wrapVerify

end Pickles
