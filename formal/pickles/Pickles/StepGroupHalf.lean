import Pickles.Encoding
import Pickles.LadderBand
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

/-- The step circuit's group half of a wrap proof, polymorphic in its cells, at the wrap
statement's `ks` and the wrap proof's `kw` rounds, the proof's commitments `nc` chunks each. -/
structure StepGroup (ks kw nc : ℕ) (f b : Type) where
  /-- The wrap statement: the verified proof's public input. -/
  statement : WrapStatement ks f b (Type1 f)
  /-- The unfinalized proof the wrap proof is checked against: the step statement's slot. -/
  claims : UnfinalizedProof kw f b (Type2 (SplitField f b))
  /-- The wrap proof. -/
  proof : IvpProof kw nc f (Type2 (SplitField f b))
  /-- The wrap proof's two `sg_old`. -/
  sgOld : Vector (AffinePoint f) MaxProofsVerified
  /-- `is_base_case`: the negation of the slot's `must_verify`. -/
  isBaseCase : b

/-- A step-side group half is the statement, the slot's claims, the proof, its `sg_old` and
`is_base_case`. -/
def StepGroup.equivProd (ks kw nc : ℕ) (f b : Type) :
    StepGroup ks kw nc f b ≃
      WrapStatement ks f b (Type1 f) × UnfinalizedProof kw f b (Type2 (SplitField f b)) ×
        IvpProof kw nc f (Type2 (SplitField f b)) × Vector (AffinePoint f) MaxProofsVerified ×
          b :=
  ⟨fun g => (g.statement, g.claims, g.proof, g.sgOld, g.isBaseCase),
   fun p => ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2⟩, fun _ => rfl, fun _ => rfl⟩

instance instStepGroupCircuitType {F : Type} {ks kw nc : ℕ} [CircuitType F Bool (BoolVar F)] :
    CircuitType F (StepGroup ks kw nc F Bool) (StepGroup ks kw nc (FVar F) (BoolVar F)) :=
  CircuitType.ofEquiv (StepGroup.equivProd ks kw nc F Bool)
    (StepGroup.equivProd ks kw nc (FVar F) (BoolVar F))

@[simp] theorem scoped_stepGroup {F : Type} {ks kw nc : ℕ} [CircuitType F Bool (BoolVar F)]
    {st : ProverState F} {x : StepGroup ks kw nc (FVar F) (BoolVar F)} :
    CircuitType.Scoped (val := StepGroup ks kw nc F Bool) st x ↔
      CircuitType.Scoped (val := WrapStatement ks F Bool (Type1 F) ×
        UnfinalizedProof kw F Bool (Type2 (SplitField F Bool)) ×
        IvpProof kw nc F (Type2 (SplitField F Bool)) × Vector (AffinePoint F) MaxProofsVerified ×
        Bool) st (StepGroup.equivProd ks kw nc (FVar F) (BoolVar F) x) :=
  CircuitType.scoped_ofEquiv _ _

@[simp] theorem reads_stepGroup {F : Type} {ks kw nc : ℕ} [Add F] [Mul F] [Zero F]
    [CircuitType F Bool (BoolVar F)] {V : Valuation F}
    {x : StepGroup ks kw nc (FVar F) (BoolVar F)} {a : StepGroup ks kw nc F Bool} :
    CircuitType.Reads V x a ↔
      CircuitType.Reads V (StepGroup.equivProd ks kw nc (FVar F) (BoolVar F) x)
        (StepGroup.equivProd ks kw nc F Bool a) :=
  CircuitType.reads_ofEquiv _ _

/-- The step circuit's `x_hat` table at an environment: computed from the key's Lagrange points
at the wrap statement's packing (`XhatTable.ofKeyKnown`). It reads the packing's kinds, never
its cells. -/
private def xhatTableAt {ks nc : ℕ} (E : Env IpaPallas.curve nc)
    (statement : WrapStatement ks (FVar Fp) (BoolVar Fp) (Type1 (FVar Fp))) : XhatTable Fp nc :=
  XhatTable.ofKeyKnown (C := IpaPallas.curve) statement.packed E.cvk.lagrangeBasis.toList

/-- The `x_hat` leaves at an environment: the packed wrap statement over the key's table. -/
def stepLeavesAt {ks nc : ℕ} (E : Env IpaPallas.curve nc)
    (statement : WrapStatement ks (FVar Fp) (BoolVar Fp) (Type1 (FVar Fp))) :
    List (Leaf Fp nc) :=
  packLeaves statement (xhatTableAt E statement)

/-- The wire's public input of a wrap statement: the packed statement's scalars, reduced to the
scalar field.

A deployed wrap proof's public input carries ten more cells after these: eight feature flags
and the lookup option's flag and scalar challenge (`composition_types.ml`,
`Wrap.Statement.In_circuit.spec`; PS `Pickles.Wrap.Types.StatementPacked`). With every optional
feature off, which is the modeled fragment, they are constant zero and no circuit reads them,
so the packing leaves them out. They change nothing the verifier computes
(`Kimchi.Verifier.kimchiVerify_append_zeros`): a check against a deployed proof drops them, or
appends them by that lemma. -/
def stepPublicInput {ks nc : ℕ} (E : Env IpaPallas.curve nc) (V : Valuation Fp)
    (statement : WrapStatement ks (FVar Fp) (BoolVar Fp) (Type1 (FVar Fp))) : Array Fq :=
  pubOf IpaPallas.curve V (stepLeavesAt E statement)

/-- Chunk `c` of the key's Lagrange relations: each Lagrange polynomial's coefficients on the
chunk. -/
def chunkRelations {nc : ℕ} (E : Env IpaPallas.curve nc) (c : ℕ) :
    List (Fin (2 ^ E.σ.k) → IpaPallas.curve.ScalarField) :=
  (List.range E.cvk.lagrangeBasis.size).map fun i => lagrangeCoeffs E.σ.k E.cvk.n E.cvk.omega i c

/-- The relations the step circuit's `x_hat` needs the SRS to avoid: per chunk, the
coefficients of the constant the known-domain fold adds (the sum of the leaves' shift
corrections), then the Lagrange vectors. It reads the packing's kinds, never its cells. -/
def stepRelationsAt {ks nc : ℕ} (E : Env IpaPallas.curve nc)
    (statement : WrapStatement ks (FVar Fp) (BoolVar Fp) (Type1 (FVar Fp))) :
    List (Fin (2 ^ E.σ.k) → IpaPallas.curve.ScalarField) :=
  (List.finRange nc).map (fun c : Fin nc => corrCoeffs (C := IpaPallas.curve) statement.packed
    (chunkRelations E c.val)) ++ E.lagrangeRelations

/-- Chunk `c` of the correction sum is the commitment to its coefficients on the chunk. -/
private theorem corrSumPt_eq_msm {ks nc : ℕ} (E : Env IpaPallas.curve nc)
    (statement : WrapStatement ks (FVar Fp) (BoolVar Fp) (Type1 (FVar Fp))) (c : Fin nc) :
    corrSumPt (C := IpaPallas.curve) statement.packed E.cvk.lagrangeBasis.toList c
      = msm IpaPallas.curve E.σ.g
          (corrCoeffs (C := IpaPallas.curve) statement.packed (chunkRelations E c.val)) := by
  have hchunk : corrSumPt (C := IpaPallas.curve) statement.packed E.cvk.lagrangeBasis.toList c
      = corrSumPt (C := IpaPallas.curve) statement.packed
          (E.cvk.lagrangeBasis.toList.map fun Ps => #v[Ps[c]]) 0 := by
    simp [corrSumPt, List.zipWith_map_right]
  have hmap : E.cvk.lagrangeBasis.toList.map (fun Ps => #v[Ps[c]])
      = (chunkRelations E c.val).map fun a => #v[msm IpaPallas.curve E.σ.g a] := by
    rw [E.lagrangeBasis_toList, List.map_map, chunkRelations, List.map_map]
    refine List.map_congr_left fun i _ => ?_
    simp
  rw [hchunk, hmap, corrSumPt_map_msm]

/-- The fold's constant is a finite point at every chunk where the SRS avoids its relations
and the statement packs no more leaves than the SRS has points. Chunk `c`'s coefficients are
the leaves' shift polynomial at the chunk's domain points (`zipWith_lagrangeCoeffs_ne_zero`):
nonzero, its constant term the first leaf's shift. -/
private theorem corrSumPt_ne_zero {ks nc : ℕ} (E : Env IpaPallas.curve nc)
    (statement : WrapStatement ks (FVar Fp) (BoolVar Fp) (Type1 (FVar Fp)))
    (hsmall : statement.packed.length ≤ 2 ^ E.σ.k)
    (h : E.σ.Avoids (stepRelationsAt E statement)) (c : Fin nc) :
    corrSumPt (C := IpaPallas.curve) statement.packed E.cvk.lagrangeBasis.toList c ≠ 0 := by
  rw [corrSumPt_eq_msm]
  refine h _ (List.mem_append_left _ (List.mem_map.2 ⟨c, List.mem_finRange c, rfl⟩))
    fun h0 => ?_
  obtain ⟨k, rest, hk⟩ := List.exists_cons_of_ne_nil
    (l := statement.packed) (by simp [WrapStatement.packed])
  have hsize := E.lagrange_pos
  have hle := E.lagrange_le
  have hroom := E.chunk_add_le c
  rw [hk, List.length_cons] at hsmall
  refine zipWith_lagrangeCoeffs_ne_zero (k := E.σ.k) E.omega_prim
    (E.natCast_n_ne_zero pastaShapePallas) c E.cvk.lagrangeBasis.size (shiftCoeff k)
    (rest.map shiftCoeff) (shiftCoeff_ne_zero pastaShapePallas k
      (statement.packed_isScalar k (hk ▸ List.mem_cons_self))) hsize
    (by simp only [List.length_map]; omega) (by simp only [List.length_map]; omega) ?_
  rw [← h0, corrCoeffs, chunkRelations, hk, ← List.map_cons, List.zipWith_map_left]

/-- Whether the SRS avoids the step relations, read off the key: each chunk of the correction
sum is the commitment to that chunk's coefficients (`corrSumPt_eq_msm`), the Lagrange
vectors' the points themselves. -/
private theorem avoids_stepRelationsAt_iff {ks nc : ℕ} (E : Env IpaPallas.curve nc)
    (statement : WrapStatement ks (FVar Fp) (BoolVar Fp) (Type1 (FVar Fp)))
    (hsmall : statement.packed.length ≤ 2 ^ E.σ.k) :
    E.σ.Avoids (stepRelationsAt E statement)
      ↔ (∀ c : Fin nc,
          corrSumPt (C := IpaPallas.curve) statement.packed E.cvk.lagrangeBasis.toList c ≠ 0)
        ∧ ∀ Ps ∈ E.cvk.lagrangeBasis.toList, ∀ c : Fin nc, Ps[c] ≠ 0 := by
  refine ⟨fun h => ⟨corrSumPt_ne_zero E statement hsmall h, E.lagrange_ne pastaShapePallas
    fun a ha => h a (List.mem_append_right _ ha)⟩, fun ⟨hsum, hL⟩ a ha hne => ?_⟩
  rcases List.mem_append.1 ha with ha | ha
  · obtain ⟨c, -, rfl⟩ := List.mem_map.1 ha
    rw [← corrSumPt_eq_msm]
    exact hsum c
  · exact (E.avoids_lagrangeRelations_iff pastaShapePallas).2 hL a ha hne

/-- Decided on the key's points, with no commitment recomputed; the bounded `∀` is pinned to
the list walk, as in `Env.decidableAvoids`. -/
def decidableAvoidsStepRelations {ks nc : ℕ} (E : Env IpaPallas.curve nc)
    (statement : WrapStatement ks (FVar Fp) (BoolVar Fp) (Type1 (FVar Fp)))
    (hsmall : statement.packed.length ≤ 2 ^ E.σ.k) :
    Decidable (E.σ.Avoids (stepRelationsAt E statement)) :=
  haveI : Decidable (∀ Ps ∈ E.cvk.lagrangeBasis.toList, ∀ c : Fin nc, Ps[c] ≠ 0) :=
    List.decidableBAll _ _
  decidable_of_iff _ (avoids_stepRelationsAt_iff E statement hsmall).symm

/-- `verify` at its constants as data: the deployed Pallas scalar ops, endomorphism, sponge,
group map and square root, the blinding base `h` as a constant cell, and the `x_hat` table
that of the Lagrange points `lagrange`. The CS-equality corpus pins this gadget, at its dump's
points. -/
def verifyProofWith {c : Type} [BasicSystem Fp c] [KimchiSystem Fp c] {ks k nc : ℕ}
    (h : IpaPallas.curve.Point) (lagrange : List (Vector IpaPallas.curve.Point nc))
    (spongeAfterIndex : SpongeVar Fp) (isBaseCase : BoolVar Fp)
    (statement : WrapStatement ks (FVar Fp) (BoolVar Fp) (Type1 (FVar Fp)))
    (u : UnfinalizedProof k (FVar Fp) (BoolVar Fp) (Type2 (SplitField (FVar Fp) (BoolVar Fp))))
    (cells : IvpInput k nc (FVar Fp) (BoolVar Fp) (Type2 (SplitField (FVar Fp) (BoolVar Fp)))) :
    CircuitM Fp c (BoolVar Fp) :=
  verifyProof IpaScalarOps.step IpaEndo.pallas IpaPallas.curve.sponge.params
    (.const ((Pasta.vestaLam : ℤ) : Fp)) groupMapParamsPallas pallasBase.sqrt? (constPt h)
    (XhatTable.ofKeyKnown (C := IpaPallas.curve) statement.packed lagrange) spongeAfterIndex
    isBaseCase statement u cells

/-- `verify` at an environment: `verifyProofWith` at the SRS blinding base and the key's
Lagrange points. -/
def verifyProofAt {c : Type} [BasicSystem Fp c] [KimchiSystem Fp c] {ks k nc : ℕ}
    (E : Env IpaPallas.curve nc) (spongeAfterIndex : SpongeVar Fp) (isBaseCase : BoolVar Fp)
    (statement : WrapStatement ks (FVar Fp) (BoolVar Fp) (Type1 (FVar Fp)))
    (u : UnfinalizedProof k (FVar Fp) (BoolVar Fp) (Type2 (SplitField (FVar Fp) (BoolVar Fp))))
    (cells : IvpInput k nc (FVar Fp) (BoolVar Fp) (Type2 (SplitField (FVar Fp) (BoolVar Fp)))) :
    CircuitM Fp c (BoolVar Fp) :=
  verifyProofWith E.σ.h E.cvk.lagrangeBasis.toList spongeAfterIndex isBaseCase statement u cells

/-- **`verify` at an environment reads as the group half at the packed statement.** The table
is the key's, so what `XhatTable.Bound` asks beyond the environment's invariants is the band
(`hoff`) and that the Lagrange points and the constant correction sum are finite points: the
deployed fold adds the sum with `addFast`. No invariant of the key gives these; they are
relations the SRS avoids (`havoid`, `stepRelationsAt`). -/
theorem verifyProofAt_reads {ks nc : ℕ} {V : Valuation Fp} (E : Env IpaPallas.curve nc)
    (cp : KimchiProof IpaPallas.curve nc E.σ.k)
    (spongeAfterIndex : SpongeVar Fp) (isBaseCase : BoolVar Fp)
    (statement : WrapStatement ks (FVar Fp) (BoolVar Fp) (Type1 (FVar Fp)))
    (u : UnfinalizedProof E.σ.k (FVar Fp) (BoolVar Fp)
      (Type2 (SplitField (FVar Fp) (BoolVar Fp))))
    (cells : IvpInput E.σ.k nc (FVar Fp) (BoolVar Fp) (Type2 (SplitField (FVar Fp) (BoolVar Fp))))
    (oldsW : List (IpaPallas.curve.Point × Bool))
    (hbase : CircuitType.Reads V isBaseCase false)
    (hoff : ∀ leaf ∈ stepLeavesAt E statement, Leaf.offBand IpaPallas.curve.scalar V leaf)
    (hsmall : statement.packed.length ≤ 2 ^ E.σ.k)
    (havoid : E.σ.Avoids (stepRelationsAt E statement))
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
      (fun Ps h ci => E.lagrange_ne pastaShapePallas
        (fun a ha => havoid a (List.mem_append_right _ ha)) Ps h ci)
      (by simp [WrapStatement.packed]) hlb
      (bitBoolean_constLeaf_of_isScalar _ _ statement.packed_isScalar) (hleaves ▸ hoff)
      (corrSumPt_ne_zero E statement hsmall havoid)
    rw [← hleaves] at hb
    exact hb
  exact verifyProof_step_reads (V := V) E.σ E.cvk cp (.const ((Pasta.vestaLam : ℤ) : Fp))
    pallasBase.sqrt? (constPt E.σ.h) (xhatTableAt E statement) spongeAfterIndex isBaseCase
    statement u cells false oldsW hbase htab hivp

/-! ## The circuit of its input -/

namespace WrapProof

variable {ks k nc : ℕ}

/-- The group circuit's input: the wrap statement, the slot's unfinalized proof, the wrap proof,
its two `sg_old`, and `is_base_case`. -/
abbrev GroupIn (ks k nc : ℕ) : Type := UnChecked (StepGroup ks k nc Fp Bool)
/-- `GroupIn`, as cells. -/
abbrev GroupVar (ks k nc : ℕ) : Type := UnChecked (StepGroup ks k nc (FVar Fp) (BoolVar Fp))

/-- The wrap statement: the verified proof's public input. -/
def GroupVar.statement (g : GroupVar ks k nc) :
    WrapStatement ks (FVar Fp) (BoolVar Fp) (Type1 (FVar Fp)) := g.val.statement
/-- The slot's deferred claims. -/
def GroupVar.claims (g : GroupVar ks k nc) :
    UnfinalizedProof k (FVar Fp) (BoolVar Fp) (Type2 (SplitField (FVar Fp) (BoolVar Fp))) :=
  g.val.claims
/-- `is_base_case`: the negation of the slot's `must_verify`. -/
def GroupVar.isBaseCase (g : GroupVar ks k nc) : BoolVar Fp := g.val.isBaseCase
/-- The wrap proof's witness commitments, `nc` chunks each. -/
def GroupVar.wComm (g : GroupVar ks k nc) : List (List (AffinePoint (FVar Fp))) :=
  g.val.proof.wComm.toList.map (·.toList)
/-- The wrap proof's permutation-accumulator commitment. -/
def GroupVar.zComm (g : GroupVar ks k nc) : List (AffinePoint (FVar Fp)) :=
  g.val.proof.zComm.toList
/-- The wrap proof's quotient chunks. -/
def GroupVar.tComm (g : GroupVar ks k nc) : List (AffinePoint (FVar Fp)) :=
  g.val.proof.tComm.toList
/-- The wrap proof's opening. -/
def GroupVar.opening (g : GroupVar ks k nc) :
    BulletproofOpening k (FVar Fp) (Type2 (SplitField (FVar Fp) (BoolVar Fp))) :=
  g.val.proof.opening
/-- The old accumulators' `sg` cells, one per slot. -/
def GroupVar.sgOld (g : GroupVar ks k nc) : List (AffinePoint (FVar Fp)) := g.val.sgOld.toList
/-- The shifted scalars the block scales by: the claims' `perm`, `ζ^{2^k}`, `ζⁿ`, `cip`, `b`
and the opening's `z₁`, `z₂`. -/
def GroupVar.shifted (g : GroupVar ks k nc) :
    List (Type2 (SplitField (FVar Fp) (BoolVar Fp))) :=
  let dv := g.claims.deferredValues
  [dv.plonk.perm, dv.plonk.zetaToSrsLength, dv.plonk.zetaToDomainSize, dv.combinedInnerProduct,
   dv.b, g.opening.z1, g.opening.z2]
/-- What `incrementallyVerifyProof` consumes: the claims, every `sg_old` unmasked, the key's
cells, the proof. -/
def GroupVar.cells (keyCells : VkComms nc (AffinePoint (FVar Fp))) (g : GroupVar ks k nc) :
    IvpInput k nc (FVar Fp) (BoolVar Fp) (Type2 (SplitField (FVar Fp) (BoolVar Fp))) :=
  ivpInputOf g.claims.deferredValues (g.sgOld.map (none, ·)) keyCells g.val.proof
/-- The group circuit as a `GroupHalf`. -/
abbrev GroupVar.half (V : Valuation Fp) (g : GroupVar ks k nc) :
    GroupHalf IpaPallas.curve (Type2 (SplitField (FVar Fp) (BoolVar Fp))) k :=
  GroupHalf.step V g.claims

/-- `Step_verifier.verify` as a circuit of its input, its success bit asserted: the deployed
`(verified ∧ finalized) ∨ ¬must_verify` at a slot that must verify. Before it, the ladder band
asserted on the cells `verify` scales — the seven shifted scalars and the `x_hat` full leaves
(`Pickles.LadderBand`; a harness assertion, not part of the shared gadget). -/
def groupCircuit {c : Type} [BasicSystem Fp c] [KimchiSystem Fp c] (E : Env IpaPallas.curve nc)
    (keyCells : VkComms nc (AffinePoint (FVar Fp))) (spongeAfterIndex : SpongeVar Fp)
    (g : GroupVar ks k nc) : CircuitM Fp c Unit := do
  assertClaimsOffBandStep g.shifted
  assertLeavesOffBand IpaPallas.curve.scalar (stepLeavesAt E g.statement)
  let v ← verifyProofAt E spongeAfterIndex g.isBaseCase g.statement g.claims (g.cells keyCells)
  assert v

/-- **The group circuit's read**: the group half's read at a bit that reads `1`. -/
theorem groupCircuit_reads {V : Valuation Fp} (E : Env IpaPallas.curve nc)
    (cp : KimchiProof IpaPallas.curve nc E.σ.k)
    (keyCells : VkComms nc (AffinePoint (FVar Fp))) (spongeAfterIndex : SpongeVar Fp)
    (g : GroupVar ks E.σ.k nc)
    (hbase : CircuitType.Reads V g.isBaseCase false)
    (hsmall : g.statement.packed.length ≤ 2 ^ E.σ.k)
    (havoid : E.σ.Avoids (stepRelationsAt E g.statement))
    (hivp : (∀ x ∈ g.shifted, (stepSide V).ClaimOk x) →
      ∃ oldsW, IvpHyps (stepSide V) E.σ E.cvk cp (stepPublicInput E V g.statement) false
        spongeAfterIndex ((g.cells keyCells).withClaims g.claims) oldsW) :
    ⦃⌜True⌝⦄
    groupCircuit (c := Builder V (KimchiConstraint Fp)) E keyCells spongeAfterIndex g
    ⦃⇓ _ _ => ⌜∃ v : BoolVar Fp,
      (g.half V).Reads E cp (stepPublicInput E V g.statement) v ∧
        (↑v : CVar Fp).val V = 1⌝⦄ := by
  simp only [groupCircuit]
  refine builder_spec_bind_of _ _ _ _ (assertClaimsOffBandStep_spec (V := V) g.shifted)
    fun hclaimOk _ => ?_
  refine builder_spec_bind_of _ _ _ _
    (assertLeavesOffBand_spec (V := V) IpaPallas.curve.scalar (stepLeavesAt E g.statement))
    fun hoff _ => ?_
  obtain ⟨oldsW, hivp⟩ := hivp hclaimOk
  have hv := verifyProofAt_reads (V := V) E cp spongeAfterIndex g.isBaseCase g.statement
    g.claims (g.cells keyCells) oldsW hbase hoff hsmall havoid hivp
  mvcgen -trivial [hv]
  rename_i v _ hr _ _
  intro h1
  exact ⟨v, hr, h1⟩

end WrapProof

/-! The gadget is sealed after its read: a consumer composes `verifyProofAt_reads`, never the
body. -/
attribute [irreducible] verifyProofAt

end Pickles
