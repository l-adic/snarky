import PicklesFixture.Layout
import Pickles.Verify
import Pickles.Encoding
import Kimchi.Verifier.Wire
import CompElliptic.Curves.Pasta.Fast.Projective.Core

/-!
# The two group halves, on the gadgets' records

`Pickles.verifyProof` on the step side (`Step_verifier.verify`) verifies a wrap proof;
`Pickles.incrementallyVerifyProof` on the wrap side (`Wrap_verifier.incrementally_verify_proof`,
as `Wrap.Main`'s verify block runs it) verifies a step proof. Each half's input here is a
product of the gadgets' own records — the statements, the unfinalized proof, the proof's
commitments and opening (`IvpProof`), the `sg_old` points — so a fixture supplies the
records a proof projects to, and the harness hands the allocated bundle to the gadget as it
is, with the key's commitments and the `x_hat` tables as constants, as the deployed circuit
has them.
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

/-- The `x_hat` tables over the 30 packed scalars of a wrap statement at the Lagrange bases
`pts`: the bases, their constant corrections, and the known-domain fold's seed and sum. -/
def stepXhatTable (pts : Array XhatStepCurve.Point) : XhatTable Fp 1 :=
  { bases := (List.range 30).map fun i => xhatStepConst (pts[i]?.getD 0)
    corrs := (List.range 30).map fun i => xhatStepConst (xhatStepCorr pts i)
    corrHead := xhatStepConst (xhatStepCorr pts 0)
    corrSum := xhatStepConst ((List.range 30).map (xhatStepCorr pts)).sum }

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

/-- The key's cells as the group half's key records: `σ₆`, the six selectors, the 15
coefficients, `σ₀…σ₅`. -/
def keyRecords {F : Type} (comms : List (List (AffinePoint (FVar F)))) :
    List (AffinePoint (FVar F)) × List (List (AffinePoint (FVar F))) ×
      List (List (AffinePoint (FVar F))) × List (List (AffinePoint (FVar F))) :=
  (comms.getD 6 [], comms.drop 22, (comms.drop 7).take 15, comms.take 6)

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

/-! ## The proof part of `IvpInput` -/

/-- A one-chunk proof as the group half reads it: the 15 witness commitments, `z_comm`, the 7
quotient chunks, the opening at `k` rounds. `IvpInput` holds these as chunk lists; the
product is their sized form, so it is a `CircuitType` by its factors. -/
abbrev IvpProof (k : ℕ) (f sf : Type) : Type :=
  Vector (AffinePoint f) wCols × AffinePoint f × Vector (AffinePoint f) 7 ×
    BulletproofOpening k f sf

/-- The group half's input from a proof's deferred values (its claims), the `sg_old` points
under their keep bits, a key's commitments and the proof. -/
def ivpInputOf {F sf : Type} {k : ℕ} (dv : DeferredValues k (FVar F) sf)
    (sgOld : List (Option (BoolVar F) × AffinePoint (FVar F)))
    (comms : List (List (AffinePoint (FVar F)))) (pr : IvpProof k (FVar F) sf) :
    IvpInput k (FVar F) (BoolVar F) sf :=
  let (sigmaLast, indexComms, coefficientsComm, sigmaComm) := keyRecords comms
  let (wComm, zComm, tComm, opening) := pr
  { plonk := ⟨⟨dv.plonk.alpha, dv.plonk.beta, dv.plonk.gamma, dv.plonk.zeta⟩, dv.plonk.perm,
      dv.plonk.zetaToSrsLength, dv.plonk.zetaToDomainSize⟩
    xi := dv.xi
    deferred := ⟨dv.combinedInnerProduct, dv.b⟩
    sgOld, sigmaLast, indexComms, coefficientsComm, sigmaComm
    wComm := wComm.toList.map ([·])
    zComm := [zComm]
    tComm := tComm.toList
    opening }

/-! ## The step circuit's group half, on a wrap proof -/

/-- The step circuit's group half of a wrap proof, as values, at the wrap statement's `ks`
and the wrap proof's `kw` rounds: the wrap statement, the unfinalized proof it is checked
against (the step statement's slot), the wrap proof, its two `sg_old`, `is_base_case`. -/
abbrev StepGroup (ks kw : ℕ) : Type :=
  WrapStatement ks Fp Bool (Type1 Fp) ×
    UnfinalizedProof kw Fp Bool (Type2 (SplitField Fp Bool)) ×
    IvpProof kw Fp (Type2 (SplitField Fp Bool)) × Vector (AffinePoint Fp) MaxProofsVerified × Bool

/-- `StepGroup`, as cells. -/
abbrev StepGroupVar (ks kw : ℕ) : Type :=
  WrapStatement ks (FVar Fp) (BoolVar Fp) (Type1 (FVar Fp)) ×
    UnfinalizedProof kw (FVar Fp) (BoolVar Fp) (Type2 (SplitField (FVar Fp) (BoolVar Fp))) ×
    IvpProof kw (FVar Fp) (Type2 (SplitField (FVar Fp) (BoolVar Fp))) ×
    Vector (AffinePoint (FVar Fp)) MaxProofsVerified × BoolVar Fp

/-- The step circuit's group half on its records: the key's index sponge, then
`Pickles.verifyProof` at the deployed parameters over the records, the `x_hat` tables and the
blinding base, the claims from the unfinalized proof, every `sg_old` unmasked. Returns the
success bit; the digest and round-challenge assertions are the gadget's constraints. -/
def groupStepOn (vk : Wire.KimchiVK XhatStepCurve) (tab : XhatTable Fp 1)
    (blindingH : AffinePoint (FVar Fp)) {ks kw : ℕ} (v : StepGroupVar ks kw) :
    CircuitM Fp C (BoolVar Fp) := do
  let (statement, u, pr, sgOld, isBaseCase) := v
  let sv ← stepIndexSponge vk
  verifyProof IpaScalarOps.step IpaEndo.pallas Bulletproof.IpaVesta.curve.frSponge.params
    (.const endoVestaLam) groupMapParamsPallas pallasBase.sqrt? blindingH tab sv isBaseCase
    statement u
    (ivpInputOf u.deferredValues (sgOld.toList.map (none, ·)) (keyComms xhatStepCell vk) pr)

/-! ## The wrap circuit's group half, on a step proof -/

/-- The Vesta curve of the wrap-side `x_hat` Lagrange bases (Fq coordinates). -/
abbrev XhatWrapCurve := Bulletproof.IpaVesta.curve

open CompElliptic.Curves.Pasta.Fast.Projective.Core.PPoint in
/-- The shift correction `-(2^L)·P` at a Lagrange base `P`, as a one-chunk constant point:
`[2^L]·P` negated coordinatewise. -/
def xhatWrapCorr (L : ℕ) (P : XhatWrapCurve.Point) : Vector (AffinePoint (FVar Fq)) 1 :=
  let Q := smulFast XhatWrapCurve.E (by decide) (by decide) (2 ^ L) P
  #v[⟨.const Q.x, .const (-Q.y)⟩]

/-- A native Vesta point as a constant cell at the wrap field. -/
def xhatWrapCell (P : XhatWrapCurve.Point) : AffinePoint (FVar Fq) := ⟨.const P.x, .const P.y⟩

/-- A native Vesta point as a one-chunk constant point at the wrap field. -/
def xhatWrapBase (P : XhatWrapCurve.Point) : Vector (AffinePoint (FVar Fq)) 1 :=
  #v[xhatWrapCell P]

/-- The `x_hat` leaves of a packed scalar list at the Lagrange bases `pts`: leaf `i` at base
`i`, its correction at the kind's ladder width (255 full, 130 for 128 bits, 10 bits — and a
boolean cell has none). -/
def wrapLeaves (pts : Array XhatWrapCurve.Point) (ks : List (PackedScalar Fq)) :
    List (Leaf Fq 1) :=
  ks.zipIdx.map fun (k, i) =>
    let P := pts[i]?.getD 0
    match k with
    | .full s => .full s (xhatWrapBase P) (xhatWrapCorr 255 P)
    | .b128 s => .b128 s (xhatWrapBase P) (xhatWrapCorr 130 P)
    | .b10 s => .b10 s (xhatWrapBase P) (xhatWrapCorr 10 P)
    | .bit b => .condAdd b (xhatWrapBase P)

/-- The sponge after the step key's index digest, at the wrap field. -/
def wrapIndexSponge (vk : Wire.KimchiVK XhatWrapCurve) : CircuitM Fq Cq (SpongeVar Fq) :=
  indexSponge Bulletproof.IpaVesta.curve.sponge.params (keyComms xhatWrapCell vk)

/-- The wrap circuit's group half of a step proof, as values, at the wrap statement's `ks`
rounds (the step proof's), the step statement's `kw` (its slots' wrap proofs') and its `n`
slots: the wrap statement, the step statement, the step proof, its `n` accumulators' `sg`.
The keep bits are the wrap statement's branch data. -/
abbrev WrapGroup (ks kw n : ℕ) : Type :=
  WrapStatement ks Fq Bool (Type1 Fq) × StepStatement kw n Fq Bool (Type2 (SplitField Fq Bool)) ×
    IvpProof ks Fq (Type1 Fq) × Vector (AffinePoint Fq) n

/-- `WrapGroup`, as cells. -/
abbrev WrapGroupVar (ks kw n : ℕ) : Type :=
  WrapStatement ks (FVar Fq) (BoolVar Fq) (Type1 (FVar Fq)) ×
    StepStatement kw n (FVar Fq) (BoolVar Fq) (Type2 (SplitField (FVar Fq) (BoolVar Fq))) ×
    IvpProof ks (FVar Fq) (Type1 (FVar Fq)) × Vector (AffinePoint (FVar Fq)) n

/-- The wrap circuit's group half on its records: the step key's index sponge, the step
statement's `x_hat` over its packed leaves at the Lagrange bases (whose boolean leaves
constrain their own bits) with the blinding base, `Pickles.incrementallyVerifyProof` on
the conditional sponge at the deployed parameters with each `sg_old` under its keep bit,
the last `n` of the branch data's mask — then the block's assertions: the digest against the wrap
statement's claim, each round challenge against its claim. Returns the success bit. -/
def groupWrapOn (vk : Wire.KimchiVK XhatWrapCurve) (basis : Array XhatWrapCurve.Point)
    (blindingH : AffinePoint (FVar Fq)) {ks kw n : ℕ} (v : WrapGroupVar ks kw n) :
    CircuitM Fq Cq (BoolVar Fq) := do
  let (statement, stepStatement, pr, sgOld) := v
  let sv ← wrapIndexSponge vk
  let computeXHat : CircuitM Fq Cq (List (AffinePoint (FVar Fq))) := do
    let P ← publicInputCommitFull (0 : Fin 1) blindingH (wrapLeaves basis stepStatement.packed)
    pure [P]
  let dv := statement.proofState.deferredValues
  let mask := dv.branchData.proofsVerifiedMask.toList.drop (MaxProofsVerified - n)
  let o ← incrementallyVerifyProof IpaScalarOps.wrap IpaEndo.vesta
    Bulletproof.IpaVesta.curve.sponge.params (.const endoPallasLam) groupMapParamsVesta
    vestaBase.sqrt? true blindingH sv computeXHat
    (ivpInputOf dv.toDeferredValues ((mask.zip sgOld.toList).map fun (m, P) => (some m, P))
      (keyComms xhatWrapCell vk) pr)
  assertEqual statement.proofState.spongeDigestBeforeEvaluations o.spongeDigest
  for c in dv.bulletproofChallenges.toList.zip o.bulletproofChallenges do
    assertEqual c.1.val c.2.val
  pure o.success

end PicklesFixture
