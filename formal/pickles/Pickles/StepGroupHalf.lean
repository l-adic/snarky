import Pickles.TwoHalves

/-!
# The step circuit's group half, at an environment

`Step_verifier.verify` at an environment: the deployed Pallas constants, the SRS blinding base
as a constant cell, and the `x_hat` table computed from the key's Lagrange points
(`XhatTable.ofKeyKnown`), so the public input is the packed statement's
(`stepPublicInput`) and what the table reads as is proved from the environment's invariants
rather than assumed (`verifyProofAt_reads`).

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

/-- The step circuit's `x_hat` table at an environment: computed from the key's Lagrange points
at the wrap statement's packing (`XhatTable.ofKeyKnown`). It reads the packing's kinds, never
its cells. -/
def xhatTableAt {ks : ℕ} (E : Env IpaPallas.curve)
    (statement : WrapStatement ks (FVar Fp) (BoolVar Fp) (Type1 (FVar Fp))) : XhatTable Fp 1 :=
  XhatTable.ofKeyKnown (C := IpaPallas.curve) statement.packed E.cvk.lagrangeBasis.toList

/-- The `x_hat` leaves at an environment: the packed wrap statement over the key's table. -/
def stepLeavesAt {ks : ℕ} (E : Env IpaPallas.curve)
    (statement : WrapStatement ks (FVar Fp) (BoolVar Fp) (Type1 (FVar Fp))) : List (Leaf Fp 1) :=
  packLeaves statement (xhatTableAt E statement)

/-- The wire's public input of a wrap statement: the packed statement's scalars, reduced to the
scalar field. -/
def stepPublicInput {ks : ℕ} (E : Env IpaPallas.curve) (V : Valuation Fp)
    (statement : WrapStatement ks (FVar Fp) (BoolVar Fp) (Type1 (FVar Fp))) : Array Fq :=
  pubOf IpaPallas.curve V (stepLeavesAt E statement)

/-- The constant the known-domain fold adds: the sum of the leaves' shift corrections. -/
def stepCorrSumAt {ks : ℕ} (E : Env IpaPallas.curve)
    (statement : WrapStatement ks (FVar Fp) (BoolVar Fp) (Type1 (FVar Fp))) :
    IpaPallas.curve.Point :=
  corrSumPt (C := IpaPallas.curve) statement.packed E.cvk.lagrangeBasis.toList 0

/-- `verify` at an environment: the deployed Pallas scalar ops, endomorphism, sponge, group
map and square root, the SRS blinding base as a constant cell, and the `x_hat` table the
key's. -/
def verifyProofAt {c : Type} [BasicSystem Fp c] [KimchiSystem Fp c] {ks k : ℕ}
    (E : Env IpaPallas.curve) (spongeAfterIndex : SpongeVar Fp) (isBaseCase : BoolVar Fp)
    (statement : WrapStatement ks (FVar Fp) (BoolVar Fp) (Type1 (FVar Fp)))
    (u : UnfinalizedProof k (FVar Fp) (BoolVar Fp) (Type2 (SplitField (FVar Fp) (BoolVar Fp))))
    (cells : IvpInput k (FVar Fp) (BoolVar Fp) (Type2 (SplitField (FVar Fp) (BoolVar Fp)))) :
    CircuitM Fp c (BoolVar Fp) :=
  verifyProof IpaScalarOps.step IpaEndo.pallas IpaPallas.curve.sponge.params
    (.const ((Pasta.vestaLam : ℤ) : Fp)) groupMapParamsPallas pallasBase.sqrt? (constPt E.σ.h)
    (xhatTableAt E statement) spongeAfterIndex isBaseCase statement u cells

/-- **`verify` at an environment reads as the group half at the packed statement.** The table
is the key's, so what `XhatTable.Bound` asks beyond the environment's invariants is the band
(`hoff`) and the constant correction sum being a finite point (`hsum`): the deployed fold adds
it with `addFast`, and no invariant of the key gives it — it is one fixed relation among the
Lagrange points. -/
theorem verifyProofAt_reads {ks : ℕ} {V : Valuation Fp} (E : Env IpaPallas.curve)
    (cp : KimchiProof IpaPallas.curve 1 E.σ.k)
    (spongeAfterIndex : SpongeVar Fp) (isBaseCase : BoolVar Fp)
    (statement : WrapStatement ks (FVar Fp) (BoolVar Fp) (Type1 (FVar Fp)))
    (u : UnfinalizedProof E.σ.k (FVar Fp) (BoolVar Fp)
      (Type2 (SplitField (FVar Fp) (BoolVar Fp))))
    (cells : IvpInput E.σ.k (FVar Fp) (BoolVar Fp) (Type2 (SplitField (FVar Fp) (BoolVar Fp))))
    (oldsW : List (IpaPallas.curve.Point × Bool))
    (hbase : CircuitType.Reads V isBaseCase false)
    (hoff : ∀ leaf ∈ stepLeavesAt E statement, Leaf.offBand IpaPallas.curve.scalar V leaf)
    (hsum : stepCorrSumAt E statement ≠ 0)
    (hivp : IvpHyps (stepSide V) E.σ E.cvk cp (stepPublicInput E V statement) false
      spongeAfterIndex (cells.withClaims u) oldsW) :
    ⦃⌜True⌝⦄
    verifyProofAt (c := Builder V (KimchiConstraint Fp)) E spongeAfterIndex isBaseCase statement
      u cells
    ⦃⇓ v _ => ⌜VerifyReads (stepSide V) E.σ E.cvk cp (stepPublicInput E V statement) u false
      v⌝⦄ := by
  have hleaves : stepLeavesAt E statement
      = List.zipWith (constLeaf (C := IpaPallas.curve)) statement.packed
        E.cvk.lagrangeBasis.toList := by
    unfold stepLeavesAt packLeaves xhatTableAt
    exact packLeavesOf_ofKeyKnown (C := IpaPallas.curve) _ _
  have hlb : E.cvk.lagrangeBasis.toList ≠ [] := by
    have := E.lagrange_pos
    intro h0
    simp [← Array.length_toList, h0] at this
  have htab : (xhatTableAt E statement).Bound pastaShapePallas V E.σ E.cvk (constPt E.σ.h)
      (packLeaves statement (xhatTableAt E statement)) := by
    have hb := bound_ofKeyKnown (V := V) pastaShapePallas E.σ E.cvk statement.packed E.h_ne
      (fun Ps h ci => by rw [Fin.fin_one_eq_zero ci]; exact E.lagrange_ne Ps h)
      (by simp [WrapStatement.packed]) hlb
      (bitBoolean_constLeaf_of_isScalar _ _ statement.packed_isScalar) (hleaves ▸ hoff)
      (fun ci => by rw [Fin.fin_one_eq_zero ci]; exact hsum)
    rw [← hleaves] at hb
    exact hb
  exact verifyProof_step_reads (V := V) E.σ E.cvk cp (.const ((Pasta.vestaLam : ℤ) : Fp))
    pallasBase.sqrt? (constPt E.σ.h) (xhatTableAt E statement) spongeAfterIndex isBaseCase
    statement u cells false oldsW hbase htab hivp

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
def groupCircuit {c : Type} [BasicSystem Fp c] [KimchiSystem Fp c] (E : Env IpaPallas.curve)
    (keyCells : List (List (AffinePoint (FVar Fp)))) (spongeAfterIndex : SpongeVar Fp)
    (g : GroupVar ks k) : CircuitM Fp c Unit := do
  let v ← verifyProofAt E spongeAfterIndex g.isBaseCase g.statement g.claims (g.cells keyCells)
  assert v

/-- **The group circuit's read**: the group half's read at a bit that reads `1`. -/
theorem groupCircuit_reads {V : Valuation Fp} (E : Env IpaPallas.curve)
    (cp : KimchiProof IpaPallas.curve 1 E.σ.k)
    (keyCells : List (List (AffinePoint (FVar Fp)))) (spongeAfterIndex : SpongeVar Fp)
    (g : GroupVar ks E.σ.k) (oldsW : List (IpaPallas.curve.Point × Bool))
    (hbase : CircuitType.Reads V g.isBaseCase false)
    (hoff : ∀ leaf ∈ stepLeavesAt E g.statement, Leaf.offBand IpaPallas.curve.scalar V leaf)
    (hsum : stepCorrSumAt E g.statement ≠ 0)
    (hivp : IvpHyps (stepSide V) E.σ E.cvk cp (stepPublicInput E V g.statement) false
      spongeAfterIndex ((g.cells keyCells).withClaims g.claims) oldsW) :
    ⦃⌜True⌝⦄
    groupCircuit (c := Builder V (KimchiConstraint Fp)) E keyCells spongeAfterIndex g
    ⦃⇓ _ _ => ⌜∃ v : BoolVar Fp,
      (g.half V).Reads E cp (stepPublicInput E V g.statement) v ∧
        (↑v : CVar Fp).val V = 1⌝⦄ := by
  have hv := verifyProofAt_reads (V := V) E cp spongeAfterIndex g.isBaseCase g.statement
    g.claims (g.cells keyCells) oldsW hbase hoff hsum hivp
  simp only [groupCircuit]
  mvcgen -trivial [hv]
  rename_i v _ hr _ _
  intro h1
  exact ⟨v, hr, h1⟩

end WrapProof

/-! The gadget is sealed after its read: a consumer composes `verifyProofAt_reads`, never the
body. -/
attribute [irreducible] verifyProofAt

end Pickles
