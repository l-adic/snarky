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

/-! ## The wrap key as constants -/

/-- A wire commitment's chunks as constant cells. -/
private def chunkCells (c : Array XhatStepCurve.Point) : List (AffinePoint (FVar Fp)) :=
  c.toList.map xhatStepCell

/-- The key's six selector commitments in the index digest's order: generic, poseidon,
complete-add, mul, emul, endomul-scalar. -/
private def selectorComms (vk : Wire.KimchiVK XhatStepCurve) :
    List (List (AffinePoint (FVar Fp))) :=
  [vk.genericComm, vk.poseidonComm, vk.completeAddComm, vk.mulComm, vk.emulComm,
   vk.endomulScalarComm].map chunkCells

/-- The sponge after the wrap key's index digest (`VerifierIndex::digest`): `σ₀…σ₆`, the 15
coefficient commitments and the six selectors, each chunk's `x` then `y`, absorbed into the
fresh sponge. -/
def stepIndexSponge (vk : Wire.KimchiVK XhatStepCurve) : CircuitM Fp C (SpongeVar Fp) :=
  let comms := vk.sigmaComm.toList.map chunkCells ++ vk.coefficientsComm.toList.map chunkCells
    ++ selectorComms vk
  comms.flatten.foldlM
    (fun sv P => do
      let sv ← SpongeVar.absorb Bulletproof.IpaVesta.curve.frSponge.params sv P.x
      SpongeVar.absorb Bulletproof.IpaVesta.curve.frSponge.params sv P.y)
    SpongeVar.init

/-! ## The input bundle -/

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

/-! ## The bundle as the gadget's records -/

/-- Cell `i` of a block. -/
private def cell {n : ℕ} (v : Vector (FVar Fp) n) (i : ℕ) : FVar Fp := v[i]?.getD (.const 0)

/-- The point at cells `i, i + 1`. -/
private def pointAt {n : ℕ} (v : Vector (FVar Fp) n) (i : ℕ) : AffinePoint (FVar Fp) :=
  ⟨cell v i, cell v (i + 1)⟩

/-- The split `Type2` scalar at cells `i, i + 1`: the half and the parity bit. -/
private def splitAt {n : ℕ} (v : Vector (FVar Fp) n) (i : ℕ) :
    Type2 (SplitField (FVar Fp) (BoolVar Fp)) :=
  ⟨⟨cell v i, .unchecked (cell v (i + 1))⟩⟩

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
  { plonk := ⟨⟨dv.plonk.alpha, dv.plonk.beta, dv.plonk.gamma, dv.plonk.zeta⟩, dv.plonk.perm,
      dv.plonk.zetaToSrsLength, dv.plonk.zetaToDomainSize⟩
    xi := dv.xi
    deferred := ⟨dv.combinedInnerProduct, dv.b⟩
    sgOld := [(none, pointAt inp.sgOld 0), (none, pointAt inp.sgOld 2)]
    sigmaLast := chunkCells (vk.sigmaComm.toList.getD 6 #[])
    indexComms := selectorComms vk
    coefficientsComm := vk.coefficientsComm.toList.map chunkCells
    sigmaComm := (vk.sigmaComm.toList.take 6).map chunkCells
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

end PicklesFixture
