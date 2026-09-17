import PicklesFixture.Layout
import Pickles.Verify
import Kimchi.Verifier.Wire
import CompElliptic.Curves.Pasta.Fast.Projective.Core

/-!
# The step circuit's group half, on a wrap proof

`Pickles.verifyProof` on the step side (`Step_verifier.verify`) verifies a wrap proof: the
key's commitments absorbed into the index sponge, `x_hat` from the wrap statement over the
Lagrange bases, the fq-sponge transcript over the proof's commitments, `ft_comm`, the
opening check, and the two assertions against the unfinalized proof the step statement
carries. `GroupStepInput` names the cells that vary per proof — the wrap statement, the
unfinalized proof, the wrap proof, the two `sg_old` — and `groupStepOn` runs the gadget on
them with the key's commitments and the `x_hat` tables as constants, as the deployed circuit
has them.
-/

namespace PicklesFixture

open Snarky Snarky.Kimchi Kimchi.Verifier Pickles CompElliptic.Fields.Pasta

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
private def keyComms {C : Bulletproof.Ipa.KimchiCurve} {F : Type} [Field F]
    (cell : C.Point → AffinePoint (FVar F)) (vk : Wire.KimchiVK C) :
    List (List (AffinePoint (FVar F))) :=
  let chunks (c : Array C.Point) : List (AffinePoint (FVar F)) := c.toList.map cell
  vk.sigmaComm.toList.map chunks ++ vk.coefficientsComm.toList.map chunks
    ++ [vk.genericComm, vk.poseidonComm, vk.completeAddComm, vk.mulComm, vk.emulComm,
        vk.endomulScalarComm].map chunks

/-- The key's cells as the group half's key records: `σ₆`, the six selectors, the 15
coefficients, `σ₀…σ₅`. -/
private def keyRecords {F : Type} [Field F] (comms : List (List (AffinePoint (FVar F)))) :
    List (AffinePoint (FVar F)) × List (List (AffinePoint (FVar F))) ×
      List (List (AffinePoint (FVar F))) × List (List (AffinePoint (FVar F))) :=
  (comms.getD 6 [], comms.drop 22, (comms.drop 7).take 15, comms.take 6)

/-- The sponge after a key's index digest (`VerifierIndex::digest`): every commitment's
chunks, `x` then `y`, absorbed into the fresh sponge. -/
private def indexSponge {F c : Type} [Field F] [DecidableEq F] [BasicSystem F c]
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

/-! ## The bundle cells -/

/-- Cell `i` of a block. -/
private def cell {F : Type} [Field F] {n : ℕ} (v : Vector (FVar F) n) (i : ℕ) : FVar F :=
  v[i]?.getD (.const 0)

/-- The point at cells `i, i + 1`. -/
private def pointAt {F : Type} [Field F] {n : ℕ} (v : Vector (FVar F) n) (i : ℕ) :
    AffinePoint (FVar F) :=
  ⟨cell v i, cell v (i + 1)⟩

/-- The split `Type2` scalar at cells `i, i + 1`: the half and the parity bit. -/
private def splitAt {n : ℕ} (v : Vector (FVar Fp) n) (i : ℕ) :
    Type2 (SplitField (FVar Fp) (BoolVar Fp)) :=
  ⟨⟨cell v i, .unchecked (cell v (i + 1))⟩⟩

/-! ## The step circuit's bundle -/

/-- The step circuit's group half of a wrap proof, by name: what varies per proof. -/
structure GroupStepInput (α : Type) where
  /-- The wrap statement's 29 packed scalars in `WrapStatement.packed`'s order — `cip, b,
  ζ^{2^k}, ζⁿ, perm` (the step proof's Type1 cells), `β, γ`, `α, ζ, ξ`, the three digests
  `sponge_digest, msg_wrap, msg_step`, the 16 round challenges — then `domain_log2` and the
  two mask bits of the branch data. -/
  statement : Vector α 32
  /-- The unfinalized proof the wrap proof is checked against, in the step statement's slot
  layout at 15 rounds: `cip, b, ζ^{2^k}, ζⁿ, perm` as `(half, parity)` pairs, the digest,
  `β, γ`, `α, ζ, ξ`, the 15 round challenges, `should_finalize`. -/
  unfinalized : Vector α 32
  /-- The wrap proof: the 15 `w_comm` points, `z_comm`, the 7 `t_comm` points, the 15
  `(L, R)` pairs, `z₁`, `z₂` as `(half, parity)` pairs, `δ`, `sg`. -/
  proof : Vector α 114
  /-- The two `sg_old` points. -/
  sgOld : Vector α 4
  /-- `is_base_case`. -/
  isBaseCase : α

/-- The bundle is its five components, in cell order. -/
@[simps apply symm_apply] def GroupStepInput.equivProd {α : Type} :
    GroupStepInput α ≃ Vector α 32 × Vector α 32 × Vector α 114 × Vector α 4 × α where
  toFun i := (i.statement, i.unfinalized, i.proof, i.sgOld, i.isBaseCase)
  invFun p := ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The bundle encodes as its 183 cells, components in cell order. -/
instance instGroupStepInputCircuitType :
    CircuitType Fp (GroupStepInput Fp) (GroupStepInput (FVar Fp)) :=
  CircuitType.ofEquiv GroupStepInput.equivProd GroupStepInput.equivProd

/-- The bundle is unchecked: a fixture supplies its cells, so nothing is asserted of them. -/
instance instGroupStepInputCheckedType :
    CheckedType Fp C (GroupStepInput Fp) (GroupStepInput (FVar Fp)) :=
  CheckedType.ofEquiv GroupStepInput.equivProd GroupStepInput.equivProd

/-- A bundle is in scope when its five components are. -/
@[simp] theorem scoped_groupStepInput {st : ProverState Fp} {v : GroupStepInput (FVar Fp)} :
    CircuitType.Scoped (val := GroupStepInput Fp) st v ↔
      CircuitType.Scoped (val := Vector Fp 32 × Vector Fp 32 × Vector Fp 114 × Vector Fp 4 × Fp)
        st (GroupStepInput.equivProd v) :=
  CircuitType.scoped_ofEquiv _ _

/-- A bundle reads componentwise. -/
@[simp] theorem reads_groupStepInput {V : Valuation Fp} {v : GroupStepInput (FVar Fp)}
    {x : GroupStepInput Fp} :
    CircuitType.Reads V v x ↔
      CircuitType.Reads V (GroupStepInput.equivProd v) (GroupStepInput.equivProd x) :=
  CircuitType.reads_ofEquiv _ _

/-- The wrap statement from the bundle's statement block. -/
def GroupStepInput.wrapStatement (inp : GroupStepInput (FVar Fp)) :
    WrapStatement Fp (Type1 (FVar Fp)) :=
  let g := cell inp.statement
  { proofState :=
      { deferredValues :=
          { plonk := { alpha := ⟨g 7⟩, beta := ⟨g 5⟩, gamma := ⟨g 6⟩, zeta := ⟨g 8⟩,
                       perm := ⟨g 4⟩, zetaToSrsLength := ⟨g 2⟩, zetaToDomainSize := ⟨g 3⟩ }
            combinedInnerProduct := ⟨g 0⟩, b := ⟨g 1⟩, xi := ⟨g 9⟩
            bulletproofChallenges := (List.range 16).map fun j => ⟨g (13 + j)⟩
            branchData := { domainLog2 := g 29,
                            proofsVerifiedMask := [.unchecked (g 30), .unchecked (g 31)] } }
        spongeDigestBeforeEvaluations := g 10
        messagesForNextWrapProof := g 11 }
    messagesForNextStepProof := g 12 }

/-- The unfinalized proof from the bundle's slot block. -/
def GroupStepInput.unfinalizedProof (inp : GroupStepInput (FVar Fp)) :
    UnfinalizedProof Fp (Type2 (SplitField (FVar Fp) (BoolVar Fp))) :=
  let g := cell inp.unfinalized
  let s := splitAt inp.unfinalized
  { deferredValues :=
      { plonk := { alpha := ⟨g 13⟩, beta := ⟨g 11⟩, gamma := ⟨g 12⟩, zeta := ⟨g 14⟩,
                   perm := s 8, zetaToSrsLength := s 4, zetaToDomainSize := s 6 }
        combinedInnerProduct := s 0, b := s 2, xi := ⟨g 15⟩
        bulletproofChallenges := (List.range 15).map fun j => ⟨g (16 + j)⟩ }
    shouldFinalize := .unchecked (g 31)
    spongeDigestBeforeEvaluations := g 10 }

/-- The group half's cells: the wrap proof's commitments and opening and the two `sg_old`
from the bundle, the key's commitments as constants; the claims are `verifyProof`'s to
substitute from the unfinalized proof. -/
def GroupStepInput.cells (vk : Wire.KimchiVK XhatStepCurve) (inp : GroupStepInput (FVar Fp)) :
    IvpInput Fp (Type2 (SplitField (FVar Fp) (BoolVar Fp))) :=
  let p := pointAt inp.proof
  let s := splitAt inp.proof
  let dv := inp.unfinalizedProof.deferredValues
  let (sigmaLast, indexComms, coefficientsComm, sigmaComm) := keyRecords (keyComms xhatStepCell vk)
  { plonk := ⟨⟨dv.plonk.alpha, dv.plonk.beta, dv.plonk.gamma, dv.plonk.zeta⟩, dv.plonk.perm,
      dv.plonk.zetaToSrsLength, dv.plonk.zetaToDomainSize⟩
    xi := dv.xi
    deferred := ⟨dv.combinedInnerProduct, dv.b⟩
    sgOld := [(none, pointAt inp.sgOld 0), (none, pointAt inp.sgOld 2)]
    sigmaLast, indexComms, coefficientsComm, sigmaComm
    wComm := (List.range 15).map fun j => [p (2 * j)]
    zComm := [p 30]
    tComm := (List.range 7).map fun j => p (32 + 2 * j)
    opening := { lr := (List.range 15).map fun j => (p (46 + 4 * j), p (48 + 4 * j))
                 z1 := s 106, z2 := s 108, delta := p 110, sg := p 112 } }

/-- The step circuit's group half on the bundle: the key's index sponge, then
`Pickles.verifyProof` at the deployed parameters over the bundle's records, the `x_hat`
tables and the blinding base. Returns the success bit; the digest and round-challenge
assertions are the gadget's constraints. -/
def groupStepOn (vk : Wire.KimchiVK XhatStepCurve) (tab : XhatTable Fp 1)
    (blindingH : AffinePoint (FVar Fp)) (inp : GroupStepInput (FVar Fp)) :
    CircuitM Fp C (BoolVar Fp) := do
  let sv ← stepIndexSponge vk
  verifyProof IpaScalarOps.step IpaEndo.pallas Bulletproof.IpaVesta.curve.frSponge.params
    (.const endoVestaLam) groupMapParamsPallas pallasBase.sqrt? blindingH tab sv
    (.unchecked inp.isBaseCase) inp.wrapStatement inp.unfinalizedProof (inp.cells vk)

/-! ## The wrap circuit's group half, on a step proof

`Pickles.incrementallyVerifyProof` on the wrap side (`Wrap_verifier.incrementally_verify_proof`
as `Wrap.Main`'s verify block runs it): `x_hat` from the step statement over the Lagrange
bases with in-circuit corrections, the conditional sponge with each `sg_old` under its keep
bit, the claims from the wrap statement itself, then the assertions the block makes — the
digest against the claimed `sponge_digest_before_evaluations`, each round challenge against
its claim — and the success bit. -/

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

/-- The parity and `should_finalize` cells of a step statement's slot, relative to the slot. -/
def stepSlotBits : List ℕ := [1, 3, 5, 7, 9, 31]

/-- The leaves of a step statement of `n` slots at the Lagrange bases `pts`, leaf `i` reading
cell `i` (`Pickles.PackedStepPublicInput`'s walk): per slot, the five split claims as a full
half and a conditional-add parity, the digest full, the 20 128-bit challenges, and
`should_finalize` as a conditional add; then `messages_for_next_step_proof` and the `n`
`messages_for_next_wrap_proof` digests, full. -/
def xhatWrapLeaves (pts : Array XhatWrapCurve.Point) (n : ℕ) (get : ℕ → FVar Fq) :
    List (Leaf Fq 1) :=
  let pt (i : ℕ) : XhatWrapCurve.Point := pts[i]?.getD 0
  let full (i : ℕ) : Leaf Fq 1 := .full (get i) (xhatWrapBase (pt i)) (xhatWrapCorr 255 (pt i))
  let b128 (i : ℕ) : Leaf Fq 1 := .b128 (get i) (xhatWrapBase (pt i)) (xhatWrapCorr 130 (pt i))
  let cond (i : ℕ) : Leaf Fq 1 := .condAdd (.unchecked (get i)) (xhatWrapBase (pt i))
  let slot (s : ℕ) : List (Leaf Fq 1) :=
    let b := 32 * s
    (List.range 5).flatMap (fun k => [full (b + 2 * k), cond (b + 2 * k + 1)]) ++ [full (b + 10)]
      ++ (List.range 20).map (fun j => b128 (b + 11 + j)) ++ [cond (b + 31)]
  (List.range n).flatMap slot ++ [full (32 * n)]
    ++ (List.range n).map fun i => full (32 * n + 1 + i)

/-- The sponge after the step key's index digest, at the wrap field. -/
def wrapIndexSponge (vk : Wire.KimchiVK XhatWrapCurve) : CircuitM Fq Cq (SpongeVar Fq) :=
  indexSponge Bulletproof.IpaVesta.curve.sponge.params (keyComms xhatWrapCell vk)

/-- The wrap circuit's group half of a step proof, by name, at `n` accumulator slots and `r`
opening rounds: what varies per proof. -/
structure GroupWrapInput (n r : ℕ) (α : Type) where
  /-- The wrap statement's 29 packed scalars in `WrapStatement.packed`'s order: `cip, b,
  ζ^{2^k}, ζⁿ, perm` (Type1 cells), `β, γ`, `α, ζ, ξ`, the three digests, the `r` round
  challenges. -/
  statement : Vector α 29
  /-- The step statement, `n` slots of 32 cells then `messages_for_next_step_proof` and `n`
  `messages_for_next_wrap_proof` digests. -/
  stepStatement : Vector α (33 * n + 1)
  /-- The step proof: the 15 `w_comm` points, `z_comm`, the 7 `t_comm` points, the `r`
  `(L, R)` pairs, `z₁`, `z₂` as Type1 cells, `δ`, `sg`. -/
  proof : Vector α (52 + 4 * r)
  /-- The `n` `sg_old` points — the step proof's accumulators, in its order. -/
  sgOld : Vector α (2 * n)
  /-- The keep bit of each `sg_old`. -/
  mask : Vector α n

/-- The bundle is its five components, in cell order. -/
@[simps apply symm_apply] def GroupWrapInput.equivProd {n r : ℕ} {α : Type} :
    GroupWrapInput n r α ≃
      Vector α 29 × Vector α (33 * n + 1) × Vector α (52 + 4 * r) × Vector α (2 * n) ×
        Vector α n where
  toFun i := (i.statement, i.stepStatement, i.proof, i.sgOld, i.mask)
  invFun p := ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The bundle encodes as its cells, components in cell order. -/
instance instGroupWrapInputCircuitType {n r : ℕ} :
    CircuitType Fq (GroupWrapInput n r Fq) (GroupWrapInput n r (FVar Fq)) :=
  CircuitType.ofEquiv GroupWrapInput.equivProd GroupWrapInput.equivProd

/-- The bundle is unchecked: a fixture supplies its cells, so nothing is asserted of them. -/
instance instGroupWrapInputCheckedType {n r : ℕ} :
    CheckedType Fq Cq (GroupWrapInput n r Fq) (GroupWrapInput n r (FVar Fq)) :=
  CheckedType.ofEquiv GroupWrapInput.equivProd GroupWrapInput.equivProd

/-- A bundle is in scope when its five components are. -/
@[simp] theorem scoped_groupWrapInput {n r : ℕ} {st : ProverState Fq}
    {v : GroupWrapInput n r (FVar Fq)} :
    CircuitType.Scoped (val := GroupWrapInput n r Fq) st v ↔
      CircuitType.Scoped (val := Vector Fq 29 × Vector Fq (33 * n + 1) × Vector Fq (52 + 4 * r) ×
        Vector Fq (2 * n) × Vector Fq n) st (GroupWrapInput.equivProd v) :=
  CircuitType.scoped_ofEquiv _ _

/-- A bundle reads componentwise. -/
@[simp] theorem reads_groupWrapInput {n r : ℕ} {V : Valuation Fq}
    {v : GroupWrapInput n r (FVar Fq)} {x : GroupWrapInput n r Fq} :
    CircuitType.Reads V v x ↔
      CircuitType.Reads V (GroupWrapInput.equivProd v) (GroupWrapInput.equivProd x) :=
  CircuitType.reads_ofEquiv _ _

/-- The group half's cells: the claims from the wrap statement, the step proof's commitments
and opening and the `sg_old` under their keep bits from the bundle, the key's commitments as
constants. -/
def GroupWrapInput.cells {n r : ℕ} (vk : Wire.KimchiVK XhatWrapCurve)
    (inp : GroupWrapInput n r (FVar Fq)) : IvpInput Fq (Type1 (FVar Fq)) :=
  let g := cell inp.statement
  let p := pointAt inp.proof
  let (sigmaLast, indexComms, coefficientsComm, sigmaComm) := keyRecords (keyComms xhatWrapCell vk)
  { plonk := ⟨⟨⟨g 7⟩, ⟨g 5⟩, ⟨g 6⟩, ⟨g 8⟩⟩, ⟨g 4⟩, ⟨g 2⟩, ⟨g 3⟩⟩
    xi := ⟨g 9⟩
    deferred := ⟨⟨g 0⟩, ⟨g 1⟩⟩
    sgOld := (List.range n).map fun i =>
      (some (.unchecked (cell inp.mask i)), pointAt inp.sgOld (2 * i))
    sigmaLast, indexComms, coefficientsComm, sigmaComm
    wComm := (List.range 15).map fun j => [p (2 * j)]
    zComm := [p 30]
    tComm := (List.range 7).map fun j => p (32 + 2 * j)
    opening := { lr := (List.range r).map fun j => (p (46 + 4 * j), p (48 + 4 * j))
                 z1 := ⟨cell inp.proof (46 + 4 * r)⟩, z2 := ⟨cell inp.proof (47 + 4 * r)⟩
                 delta := p (48 + 4 * r), sg := p (50 + 4 * r) } }

/-- The wrap circuit's group half on the bundle: the step key's index sponge, the step
statement's booleanity checks (its packing's), `x_hat` over its leaves at the Lagrange bases
with the blinding base, `Pickles.incrementallyVerifyProof` on the conditional sponge at the
deployed parameters, then the block's assertions — the digest against the wrap statement's
claim, each round challenge against its claim. Returns the success bit. -/
def groupWrapOn {n r : ℕ} (vk : Wire.KimchiVK XhatWrapCurve) (basis : Array XhatWrapCurve.Point)
    (blindingH : AffinePoint (FVar Fq)) (inp : GroupWrapInput n r (FVar Fq)) :
    CircuitM Fq Cq (BoolVar Fq) := do
  let sv ← wrapIndexSponge vk
  let get := cell inp.stepStatement
  for s in List.range n do
    for i in stepSlotBits do
      addConstraint (BasicSystem.boolean (get (32 * s + i)) : Cq)
  let computeXHat : CircuitM Fq Cq (List (AffinePoint (FVar Fq))) := do
    let P ← publicInputCommitFull (0 : Fin 1) blindingH (xhatWrapLeaves basis n get)
    pure [P]
  let o ← incrementallyVerifyProof IpaScalarOps.wrap IpaEndo.vesta
    Bulletproof.IpaVesta.curve.sponge.params (.const endoPallasLam) groupMapParamsVesta
    vestaBase.sqrt? true blindingH sv computeXHat (inp.cells vk)
  assertEqual (cell inp.statement 10) o.spongeDigest
  for c in ((List.range r).map fun j => cell inp.statement (13 + j)).zip o.bulletproofChallenges do
    assertEqual c.1 c.2.val
  pure o.success

end PicklesFixture
