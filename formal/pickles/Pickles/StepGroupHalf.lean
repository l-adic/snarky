import Pickles.TwoHalves

/-!
# The step circuit's group half, at an environment

`Step_verifier.verify` with the deployed Pallas constants. Unlike the wrap block this one
computes `x_hat` itself, from the key's Lagrange tables (`XhatTable.Bound`), so the public
input is the packed statement's rather than a free argument.

`WrapProof.groupCircuit` is the gadget as a circuit of its input (`WrapProof.GroupIn`) with its
success bit asserted, and `WrapProof.groupCircuit_reads` its read: what the wrap proof's
top-level statement compiles (`wrapProof_kimchiVerify_pallas`).
-/

namespace Pickles

open Std.Do Snarky Snarky.Kimchi Kimchi.Verifier Bulletproof Bulletproof.Ipa
open CompElliptic.Fields.Pasta CompElliptic.Curves.Pasta

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

/-- `verify` at the deployed step constants: the Pallas scalar ops, endomorphism, sponge and
group map. -/
def verifyProofAt {c : Type} [BasicSystem Fp c] [KimchiSystem Fp c] {nc ks : ℕ}
    (endo : FVar Fp) (sqrtF : Fp → Option Fp) (blindingH : AffinePoint (FVar Fp))
    (tab : XhatTable Fp nc) (spongeAfterIndex : SpongeVar Fp) (isBaseCase : BoolVar Fp)
    (statement : WrapStatement ks (FVar Fp) (BoolVar Fp) (Type1 (FVar Fp)))
    {k : ℕ}
    (u : UnfinalizedProof k (FVar Fp) (BoolVar Fp) (Type2 (SplitField (FVar Fp) (BoolVar Fp))))
    (cells : IvpInput k (FVar Fp) (BoolVar Fp) (Type2 (SplitField (FVar Fp) (BoolVar Fp)))) :
    CircuitM Fp c (BoolVar Fp) :=
  verifyProof IpaScalarOps.step IpaEndo.pallas IpaPallas.curve.sponge.params endo
    groupMapParamsPallas sqrtF blindingH tab spongeAfterIndex isBaseCase statement u cells

/-! ## The circuit of its input -/

namespace WrapProof

variable {ks k : ℕ}

/-- The group circuit's input: the wrap statement, the slot's unfinalized proof, the wrap proof,
its two `sg_old`, and `is_base_case`. -/
abbrev GroupIn (ks k : ℕ) : Type := UnChecked (StepGroup ks k)
/-- `GroupIn`, as cells. -/
abbrev GroupVar (ks k : ℕ) : Type := UnChecked (StepGroupVar ks k)

/-- The wrap statement: the verified proof's public input. -/
def GroupVar.statement (g : GroupVar ks k) :
    WrapStatement ks (FVar Fp) (BoolVar Fp) (Type1 (FVar Fp)) := g.val.1
/-- The slot's deferred claims. -/
def GroupVar.claims (g : GroupVar ks k) :
    UnfinalizedProof k (FVar Fp) (BoolVar Fp) (Type2 (SplitField (FVar Fp) (BoolVar Fp))) :=
  g.val.2.1
/-- `is_base_case`: the negation of the slot's `must_verify`. -/
def GroupVar.isBaseCase (g : GroupVar ks k) : BoolVar Fp := g.val.2.2.2.2
/-- The wrap proof's witness commitments, one chunk each. -/
def GroupVar.wComm (g : GroupVar ks k) : List (List (AffinePoint (FVar Fp))) :=
  g.val.2.2.1.1.toList.map ([·])
/-- The wrap proof's permutation-accumulator commitment. -/
def GroupVar.zComm (g : GroupVar ks k) : List (AffinePoint (FVar Fp)) := [g.val.2.2.1.2.1]
/-- The wrap proof's quotient chunks. -/
def GroupVar.tComm (g : GroupVar ks k) : List (AffinePoint (FVar Fp)) := g.val.2.2.1.2.2.1.toList
/-- The wrap proof's opening. -/
def GroupVar.opening (g : GroupVar ks k) :
    BulletproofOpening k (FVar Fp) (Type2 (SplitField (FVar Fp) (BoolVar Fp))) :=
  g.val.2.2.1.2.2.2
/-- The old accumulators' `sg` cells, one per slot. -/
def GroupVar.sgOld (g : GroupVar ks k) : List (AffinePoint (FVar Fp)) := g.val.2.2.2.1.toList
/-- The shifted scalars the block scales by: the claims' `perm`, `ζ^{2^k}`, `ζⁿ`, `cip`, `b`
and the opening's `z₁`, `z₂`. -/
def GroupVar.shifted (g : GroupVar ks k) :
    List (Type2 (SplitField (FVar Fp) (BoolVar Fp))) :=
  let dv := g.claims.deferredValues
  [dv.plonk.perm, dv.plonk.zetaToSrsLength, dv.plonk.zetaToDomainSize, dv.combinedInnerProduct,
   dv.b, g.opening.z1, g.opening.z2]
/-- What `incrementallyVerifyProof` consumes: the claims, every `sg_old` unmasked, the key's
cells, the proof. -/
def GroupVar.cells (keyCells : List (List (AffinePoint (FVar Fp)))) (g : GroupVar ks k) :
    IvpInput k (FVar Fp) (BoolVar Fp) (Type2 (SplitField (FVar Fp) (BoolVar Fp))) :=
  ivpInputOf g.claims.deferredValues (g.sgOld.map (none, ·)) keyCells g.val.2.2.1
/-- The group circuit as a `GroupHalf`. -/
abbrev GroupVar.half (V : Valuation Fp) (g : GroupVar ks k) :
    GroupHalf IpaPallas.curve (Type2 (SplitField (FVar Fp) (BoolVar Fp))) k :=
  GroupHalf.step V g.claims

/-- `Step_verifier.verify` as a circuit of its input, its success bit asserted: the deployed
`(verified ∧ finalized) ∨ ¬must_verify` at a slot that must verify. -/
def groupCircuit {c : Type} [BasicSystem Fp c] [KimchiSystem Fp c]
    (endo : FVar Fp) (sqrtF : Fp → Option Fp) (blindingH : AffinePoint (FVar Fp))
    (tab : XhatTable Fp 1) (keyCells : List (List (AffinePoint (FVar Fp))))
    (spongeAfterIndex : SpongeVar Fp) (g : GroupVar ks k) : CircuitM Fp c Unit := do
  let v ← verifyProofAt endo sqrtF blindingH tab spongeAfterIndex g.isBaseCase g.statement
    g.claims (g.cells keyCells)
  assert v

/-- **The group circuit's read**: the group half's read at a bit that reads `1`. -/
theorem groupCircuit_reads {V : Valuation Fp} (E : Env IpaPallas.curve)
    (cp : KimchiProof IpaPallas.curve 1 E.σ.k)
    (endo : FVar Fp) (sqrtF : Fp → Option Fp) (blindingH : AffinePoint (FVar Fp))
    (tab : XhatTable Fp 1) (keyCells : List (List (AffinePoint (FVar Fp))))
    (spongeAfterIndex : SpongeVar Fp) (g : GroupVar ks E.σ.k)
    (oldsW : List (IpaPallas.curve.Point × Bool))
    (hbase : CircuitType.Reads V g.isBaseCase false)
    (htab : tab.Bound pastaShapePallas V E.σ E.cvk blindingH (packLeaves g.statement tab))
    (hivp : IvpHyps (stepSide V) E.σ E.cvk cp
      (pubOf IpaPallas.curve V (packLeaves g.statement tab)) false spongeAfterIndex
      ((g.cells keyCells).withClaims g.claims) oldsW) :
    ⦃⌜True⌝⦄
    groupCircuit (c := Builder V (KimchiConstraint Fp)) endo sqrtF blindingH tab keyCells
      spongeAfterIndex g
    ⦃⇓ _ _ => ⌜∃ v : BoolVar Fp,
      (g.half V).Reads E cp (pubOf IpaPallas.curve V (packLeaves g.statement tab)) v ∧
        (↑v : CVar Fp).val V = 1⌝⦄ := by
  have hv := verifyProof_step_reads (V := V) E.σ E.cvk cp endo sqrtF blindingH tab
    spongeAfterIndex g.isBaseCase g.statement g.claims (g.cells keyCells) false oldsW hbase htab
    hivp
  simp only [groupCircuit, verifyProofAt]
  mvcgen -trivial [hv]
  rename_i v _ hr _ _
  intro h1
  exact ⟨v, hr, h1⟩

end WrapProof

end Pickles
