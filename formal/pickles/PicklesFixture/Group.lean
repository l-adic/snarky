import PicklesFixture.Layout
import Pickles.Verify
import Pickles.WrapVerify
import Pickles.StepGroupHalf
import Pickles.Encoding
import Kimchi.Verifier.Wire
import CompElliptic.Curves.Pasta.Fast.Projective.Core

/-!
# The two group halves, on the gadgets' records

`Pickles.verifyProof` on the step side (`Step_verifier.verify`) verifies a wrap proof;
`Pickles.incrementallyVerifyProof` on the wrap side (`Wrap_verifier.incrementally_verify_proof`,
as `Wrap.Main`'s verify block runs it) verifies a step proof. Each half's input here is the
library's record of the gadgets' own records (`Pickles.StepGroup`, `Pickles.WrapGroup`) — the
statements, the unfinalized proof, the proof's commitments and opening (`IvpProof`), the
`sg_old` points — so a fixture supplies the records a proof projects to, and the harness
hands the allocated bundle to the gadget as it is, with the key's commitments and the `x_hat`
tables as constants, as the deployed circuit has them.
-/

namespace PicklesFixture

open Snarky Snarky.Kimchi Kimchi Kimchi.Verifier Pickles CompElliptic.Fields.Pasta

/-! ## The step-side `x_hat` tables -/

/-- The Pallas curve of the step-side `x_hat` Lagrange bases (Fp coordinates). -/
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

/-- The ladder width of step leaf `i` — `WrapStatement.packed`'s widths: the five shifted
scalars and the three digests full, the branch data 10 bits, the challenges 128. -/
def xhatStepWidth (i : ℕ) : ℕ :=
  if i < 5 ∨ (10 ≤ i ∧ i < 13) then 255 else if i = 29 then 10 else 130

/-- The shift correction of step leaf `i` at the Lagrange bases `pts`. -/
def xhatStepCorr (pts : Array XhatStepCurve.Point) (i : ℕ) : XhatStepCurve.Point :=
  xhatStepCorrPt (xhatStepWidth i) (pts[i]?.getD 0)

/-- Lagrange bases as the one-chunk points the library's `x_hat` tables are computed from. -/
def oneChunk {C : Bulletproof.Ipa.KimchiCurve} (pts : Array C.Point) : List (Vector C.Point 1) :=
  pts.toList.map (#v[·])

/-! ## A verified key as constants -/

/-- A key's commitments as constant cells, in the index digest's order: `σ₀…σ₆`, the 15
coefficient commitments, the six selectors (generic, poseidon, complete-add, mul, emul,
endomul-scalar) — each a chunk list. -/
def keyComms {C : Bulletproof.Ipa.KimchiCurve} {F : Type}
    (cell : C.Point → AffinePoint (FVar F)) (vk : Wire.KimchiVK C) :
    List (List (AffinePoint (FVar F))) :=
  let chunks (c : Array C.Point) : List (AffinePoint (FVar F)) := c.toList.map cell
  vk.sigmaComm.toList.map chunks ++ vk.coefficientsComm.toList.map chunks
    ++ [vk.genericComm, vk.poseidonComm, vk.completeAddComm, vk.mulComm, vk.emulComm,
        vk.endomulScalarComm].map chunks

/-- The sponge after a key's index digest (`VerifierIndex::digest`): every commitment's
chunks, `x` then `y`, absorbed into the fresh sponge. -/
def indexSponge {F c : Type} [Field F] [DecidableEq F] [BasicSystem F c]
    [KimchiSystem F c] (p : Poseidon.Params F) (comms : List (List (AffinePoint (FVar F)))) :
    CircuitM F c (SpongeVar F) :=
  comms.flatten.foldlM
    (fun sv P => do
      let sv ← SpongeVar.absorb p sv P.x
      SpongeVar.absorb p sv P.y)
    SpongeVar.init

/-- The sponge after the wrap key's index digest, at the step field. -/
def stepIndexSponge (vk : Wire.KimchiVK XhatStepCurve) : CircuitM Fp C (SpongeVar Fp) :=
  indexSponge Bulletproof.IpaVesta.curve.frSponge.params (keyComms xhatStepCell vk)

/-! ## The step circuit's group half, on a wrap proof -/

/-- The step circuit's group half on its records: the key's index sponge, then
`Pickles.verifyProof` at the deployed parameters over the records, the `x_hat` tables and the
blinding base, the claims from the unfinalized proof, every `sg_old` unmasked. Returns the
success bit; the digest and round-challenge assertions are the gadget's constraints. -/
def groupStepOn (vk : Wire.KimchiVK XhatStepCurve) (basis : Array XhatStepCurve.Point)
    (blindingH : XhatStepCurve.Point) {ks kw : ℕ} (v : StepGroup ks kw (FVar Fp) (BoolVar Fp)) :
    CircuitM Fp C (BoolVar Fp) := do
  let sv ← stepIndexSponge vk
  verifyProofWith blindingH (oneChunk basis) sv v.isBaseCase v.statement v.claims
    (ivpInputOf v.claims.deferredValues (v.sgOld.toList.map (none, ·)) (keyComms xhatStepCell vk)
      v.proof)

/-! ## The wrap circuit's group half, on a step proof -/

/-- The Vesta curve of the wrap-side `x_hat` Lagrange bases (Fq coordinates). -/
abbrev XhatWrapCurve := Bulletproof.IpaVesta.curve

/-- A native Vesta point as a constant cell at the wrap field. -/
def xhatWrapCell (P : XhatWrapCurve.Point) : AffinePoint (FVar Fq) := ⟨.const P.x, .const P.y⟩

/-- The sponge after the step key's index digest, at the wrap field. -/
def wrapIndexSponge (vk : Wire.KimchiVK XhatWrapCurve) : CircuitM Fq Cq (SpongeVar Fq) :=
  indexSponge Bulletproof.IpaVesta.curve.sponge.params (keyComms xhatWrapCell vk)

/-- The wrap circuit's group half on its records: the step key's index sponge, the step
statement's `x_hat` over its packed leaves at the Lagrange bases (whose boolean leaves
constrain their own bits) with the blinding base, `Pickles.incrementallyVerifyProof` on
the conditional sponge at the deployed parameters with each `sg_old` under its keep bit,
the last `n` of the branch data's mask — then the block's assertions: the digest against the wrap
statement's claim, each round challenge against its claim. Returns the success bit. -/
def groupWrapOn {nc : ℕ} (vk : Wire.KimchiVK XhatWrapCurve)
    (basis : Array (Vector XhatWrapCurve.Point nc)) (blindingH : AffinePoint (FVar Fq))
    {ks kw n : ℕ} (v : WrapGroup ks kw n nc (FVar Fq) (BoolVar Fq)) :
    CircuitM Fq Cq (BoolVar Fq) := do
  let sv ← wrapIndexSponge vk
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
      (keyComms xhatWrapCell vk) v.proof)
  assertEqual v.statement.proofState.spongeDigestBeforeEvaluations o.spongeDigest
  for c in dv.bulletproofChallenges.toList.zip o.bulletproofChallenges do
    assertEqual c.1.val c.2.val
  pure o.success

/-- The wrap side's dummy IPA challenges, expanded (PS `dummyIpaChallenges.wrapExpanded`).
Transcribed rather than derived: PureScript draws them from a Blake2s stream, and no Lean in
this tree or its dependencies implements Blake. Provenance — every wrap proof in
`proof-cache/SimpleChain.json` carries them in its padding slot, byte-identical across the
chain, and that slot's commitment is `dummyWrapSg`; a wrong value moves the sponge checkpoint
and `wrap_verify_circuit` stops matching. -/
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
state after absorbing one dummy challenge vector per padding slot, `MaxProofsVerified - n` of
them, in front (PS `dummyPaddingSpongeStates`), so the padding costs no gates. -/
def wrapMsgSpongeState (n : ℕ) : Poseidon.State Fq :=
  Poseidon.absorb Bulletproof.IpaVesta.curve.sponge.params ⟨(0, 0, 0), .absorbed 0⟩
    (List.replicate (MaxProofsVerified - n) dummyWrapChallenges).flatten

end PicklesFixture
