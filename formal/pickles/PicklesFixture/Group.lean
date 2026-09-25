import PicklesFixture.Layout
import Pickles.Verify
import Pickles.WrapVerify
import Pickles.StepGroupHalf
import Pickles.Encoding
import Kimchi.Verifier.Wire
import CompElliptic.Curves.Pasta.Fast.Projective.Core

/-!
# The two group halves, on the gadgets' records

The step side (`step_verifier.ml`) verifies a wrap proof with `Pickles.verifyProof`; the wrap
side (the verify block of `wrap_main.ml`) verifies a step proof with
`Pickles.incrementallyVerifyProof`. Each half takes one record (`Pickles.StepGroup`,
`Pickles.WrapGroup`), so a fixture supplies the records a proof projects to. The key's
commitments and the public-input tables are constants, as in the deployed circuit.
-/

namespace PicklesFixture

open Snarky Snarky.Kimchi Kimchi Kimchi.Verifier Pickles CompElliptic.Fields.Pasta

/-! ## The step-side public-input tables -/

/-- The Pallas curve of the step-side Lagrange bases (Fp coordinates). -/
abbrev XhatStepCurve := Bulletproof.IpaPallas.curve

open CompElliptic.Curves.Pasta.Fast.Projective.Core.PPoint in
/-- The shift correction `-(2^L)·P` at a Lagrange base `P`, as a native Pallas point. -/
def xhatStepCorrPt (L : ℕ) (P : XhatStepCurve.Point) : XhatStepCurve.Point :=
  -(smulFast XhatStepCurve.E (by decide) (by decide) (2 ^ L) P)

/-- A native Pallas point as a constant cell at the step field. -/
def xhatStepCell (P : XhatStepCurve.Point) : AffinePoint (FVar Fp) := ⟨.const P.x, .const P.y⟩

/-- A native Pallas point as a one-chunk constant point at the step field. -/
def xhatStepConst (P : XhatStepCurve.Point) : Vector (AffinePoint (FVar Fp)) 1 :=
  #v[xhatStepCell P]

/-- The ladder width of leaf `i` of `WrapStatement.packed`: 255 for a full scalar, 130 for a
128-bit one, 10 for the branch data. -/
def xhatStepWidth (i : ℕ) : ℕ :=
  if i < 5 ∨ (10 ≤ i ∧ i < 13) then 255 else if i = 29 then 10 else 130

/-- The shift correction of step leaf `i` at the Lagrange bases `pts`. -/
def xhatStepCorr (pts : Array XhatStepCurve.Point) (i : ℕ) : XhatStepCurve.Point :=
  xhatStepCorrPt (xhatStepWidth i) (pts[i]?.getD 0)

/-- Lagrange bases as the one-chunk points the public-input tables are computed from. -/
def oneChunk {C : Bulletproof.Ipa.KimchiCurve} (pts : Array C.Point) : List (Vector C.Point 1) :=
  pts.toList.map (#v[·])

/-- A key's commitments in the index digest's absorb order: `σ₀…σ₆`, the coefficients, then
the selectors. -/
def digestOrder {nc : ℕ} {f : Type} (k : VkComms nc f) : List (Vector f nc) :=
  k.sigmaComm.toList ++ k.coefficientsComm.toList ++ k.selectors

/-- Every commitment of a key record the same point: the constant key of the CS dumps. -/
def VkComms.replicate {nc : ℕ} {f : Type} (P : Vector f nc) : VkComms nc f :=
  ⟨Vector.replicate _ P, Vector.replicate _ P, P, P, P, P, P, P⟩

/-- The sponge after a key's index digest: every commitment's chunks in `digestOrder`, `x`
then `y`, absorbed into the fresh sponge. -/
def indexSponge {F c : Type} [Field F] [DecidableEq F] [BasicSystem F c]
    [KimchiSystem F c] {nc : ℕ} (p : Poseidon.Params F) (key : VkComms nc (AffinePoint (FVar F))) :
    CircuitM F c (SpongeVar F) :=
  ((digestOrder key).map Vector.toList).flatten.foldlM
    (fun sv P => do
      let sv ← SpongeVar.absorb p sv P.x
      SpongeVar.absorb p sv P.y)
    SpongeVar.init

/-- The sponge after the wrap key's index digest, at the step field. -/
def stepIndexSponge (key : VkComms 1 (AffinePoint (FVar Fp))) : CircuitM Fp C (SpongeVar Fp) :=
  indexSponge Bulletproof.IpaVesta.curve.frSponge.params key

/-! ## The step circuit's group half, on a wrap proof -/

/-- The step circuit's group half: the key's index sponge, then `verifyProofWith` over the
record, every old accumulator point unmasked. Returns the success bit. -/
def groupStepOn (key : VkComms 1 (AffinePoint (FVar Fp))) (basis : Array XhatStepCurve.Point)
    (blindingH : XhatStepCurve.Point) {ks kw : ℕ} (v : StepGroup ks kw 1 (FVar Fp) (BoolVar Fp)) :
    CircuitM Fp C (BoolVar Fp) := do
  let sv ← stepIndexSponge key
  verifyProofWith blindingH (oneChunk basis) sv v.isBaseCase v.statement v.claims
    (ivpInputOf v.claims.deferredValues (v.sgOld.toList.map (none, ·)) key v.proof)

/-! ## The wrap circuit's group half, on a step proof -/

/-- The Vesta curve of the wrap-side Lagrange bases (Fq coordinates). -/
abbrev XhatWrapCurve := Bulletproof.IpaVesta.curve

/-- A native Vesta point as a constant cell at the wrap field. -/
def xhatWrapCell (P : XhatWrapCurve.Point) : AffinePoint (FVar Fq) := ⟨.const P.x, .const P.y⟩

/-- The sponge after the step key's index digest, at the wrap field. -/
def wrapIndexSponge {nc : ℕ} (key : VkComms nc (AffinePoint (FVar Fq))) :
    CircuitM Fq Cq (SpongeVar Fq) :=
  indexSponge Bulletproof.IpaVesta.curve.sponge.params key

/-- The wrap circuit's group half: the step key's index sponge, the step statement's
public-input commitment, then `Pickles.incrementallyVerifyProof` with each old accumulator
point under its keep bit (the last `n` bits of the branch data's mask), then the digest and
round-challenge assertions against the wrap statement. Returns the success bit. -/
def groupWrapOn {nc : ℕ} (key : VkComms nc (AffinePoint (FVar Fq)))
    (basis : Array (Vector XhatWrapCurve.Point nc)) (blindingH : AffinePoint (FVar Fq))
    {ks kw n : ℕ} (v : WrapGroup ks kw n nc (FVar Fq) (BoolVar Fq)) :
    CircuitM Fq Cq (BoolVar Fq) := do
  let sv ← wrapIndexSponge key
  let computeXHat : CircuitM Fq Cq (List (AffinePoint (FVar Fq))) :=
    Vector.toList <$> publicInputCommitFull blindingH
      (packLeavesOf v.stepStatement.packed
        (XhatTable.ofKey v.stepStatement.packed basis.toList))
  let dv := v.statement.proofState.deferredValues
  let mask := dv.branchData.proofsVerifiedMask.toList.drop (MaxProofsVerified - n)
  let o ← incrementallyVerifyProof IpaScalarOps.wrap IpaEndo.vesta
    Bulletproof.IpaVesta.curve.sponge.params (.const endoPallasLam) groupMapParamsVesta
    vestaBase.sqrt? true blindingH sv computeXHat
    (ivpInputOf dv.toDeferredValues ((mask.zip v.sgOld.toList).map fun (m, P) => (some m, P))
      key v.proof)
  assertEqual v.statement.proofState.spongeDigestBeforeEvaluations o.spongeDigest
  for c in dv.bulletproofChallenges.toList.zip o.bulletproofChallenges do
    assertEqual c.1.val c.2.val
  pure o.success

/-- The wrap side's dummy IPA challenges, expanded. Transcribed, not derived: they come from
a Blake2s stream, which nothing in this tree implements. Every wrap proof of the SimpleChain
fixture carries them in its padding slot; a wrong value moves the sponge checkpoint and the
wrap-verify constraint-system check stops matching. -/
def dummyWrapChallenges : List Fq :=
  [7048930911355605315581096707847688535149125545610393399193999502037687877674,
   5945064094191074331354717685811267396540107129706976521474145740173204364019,
   20315491820009986698838977727629973056499886675589920515484193128018854963801,
   375929229548289966749422550601268097380795636681684498450629863247980915833,
   19682218496321100578766622300447982536359891434050417209656101638029891689955,
   516598185966802396400068849903674663130928531697254466925429658676832606723,
   23729760760563685146228624125180554011222918208600079938584869191222807389336,
   11155777282048225577422475738306432747575091690354122761439079853293714987855,
   24977767586983413450834833875715786066408803952857478894197349635213480783870,
   2813347787496113574506936084777563965225649411532015639663405402448028142689,
   22626141769059119580550800305467929090916842064220293932303261732461616709448,
   18748107085456859495495117012311103043200881556220793307463332157672741458218,
   22196219950929618042921320796106738233125483954115679355597636800196070731081,
   13054421325261400802177761929986025883530654947859503505174678618288142017333,
   4799483385651443229337780097631636300491234601736019220096005875687579936102]

/-- The message-hash sponge of a wrap circuit whose step statement has `n` real slots: the
state after absorbing one dummy challenge vector per padding slot, so the padding costs no
gates. -/
def wrapMsgSpongeState (n : ℕ) : Poseidon.State Fq :=
  Poseidon.absorb Bulletproof.IpaVesta.curve.sponge.params ⟨(0, 0, 0), .absorbed 0⟩
    (List.replicate (MaxProofsVerified - n) dummyWrapChallenges).flatten

end PicklesFixture
