import Kimchi.Columns
import Pickles.Encoding
import Pickles.ShiftedClaims
import Pickles.TwoHalves

/-!
# The step circuit's group half, at an environment

The step circuit's `verifyProof` at an environment: the deployed Pallas constants, the SRS
blinding base as a constant cell, and the public-input commitment table computed from the key's
Lagrange points (`XhatTable.ofKeyKnown`). The public input is then the packed statement's
(`stepPublicInput`), and what the table reads as is proved from the environment's invariants
rather than assumed (`verifyProofAt_reads`).

`WrapProof.groupCircuit` is the gadget as a circuit of its input, its success bit asserted;
its read `WrapProof.groupCircuit_reads` is what `wrapProof_kimchiVerify_pallas` compiles.
-/

namespace Pickles

open Std.Do Snarky Snarky.Kimchi Kimchi.Verifier Bulletproof Bulletproof.Ipa
open CompElliptic.Fields.Pasta CompElliptic.Curves.Pasta

/-- The input of the step circuit's group half, over cells `f` and bits `b`: a wrap statement
at `ks` rounds, and a wrap proof at `kw` rounds whose commitments have `nc` chunks each. -/
structure StepGroup (ks kw nc : ℕ) (f b : Type) where
  /-- The wrap statement: the verified proof's public input. -/
  statement : WrapStatement ks f b (Type1 f)
  /-- The unfinalized proof the wrap proof is checked against: the step statement's slot. -/
  claims : UnfinalizedProof kw f b (Type2 (SplitField f b))
  /-- The wrap proof. -/
  proof : IvpProof kw nc f (Type2 (SplitField f b))
  /-- The old accumulators' `sg` points, one per slot. -/
  sgOld : Vector (AffinePoint f) MaxProofsVerified
  /-- Whether the slot is a base case: the negation of its must-verify flag. -/
  isBaseCase : b

/-- `StepGroup` as the tuple of its fields. -/
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

/-- The public-input commitment table at an environment, computed from the key's Lagrange
points at the statement's packing. It reads the packing's kinds, never its cells. -/
private def xhatTableAt {ks nc : ℕ} (E : Env IpaPallas.curve nc)
    (statement : WrapStatement ks (FVar Fp) (BoolVar Fp) (Type1 (FVar Fp))) : XhatTable Fp nc :=
  XhatTable.ofKeyKnown (C := IpaPallas.curve) statement.packed E.cvk.lagrangeBasis.toList

/-- The public-input leaves at an environment: the packed wrap statement over the key's
table. -/
def stepLeavesAt {ks nc : ℕ} (E : Env IpaPallas.curve nc)
    (statement : WrapStatement ks (FVar Fp) (BoolVar Fp) (Type1 (FVar Fp))) :
    List (Leaf Fp nc) :=
  packLeaves statement (xhatTableAt E statement)

/-- The wire's public input of a wrap statement: the packed statement's scalars, reduced to the
scalar field.

A deployed wrap proof's public input carries ten more cells: eight feature flags and the
lookup option's flag and scalar challenge. In the modeled fragment every optional feature is
off, so they are constant zero, no circuit reads them, and the packing leaves them out. -/
def stepPublicInput {ks nc : ℕ} (E : Env IpaPallas.curve nc) (V : Valuation Fp)
    (statement : WrapStatement ks (FVar Fp) (BoolVar Fp) (Type1 (FVar Fp))) : Array Fq :=
  pubOf IpaPallas.curve V (stepLeavesAt E statement)

/-- The public input reads the step-message digest only through its value. -/
theorem stepPublicInput_congr_msg {ks nc : ℕ} (E : Env IpaPallas.curve nc) (V : Valuation Fp)
    (st : WrapStatement ks (FVar Fp) (BoolVar Fp) (Type1 (FVar Fp))) (a b : FVar Fp)
    (h : a.val V = b.val V) :
    stepPublicInput E V { st with messagesForNextStepProof := a }
      = stepPublicInput E V { st with messagesForNextStepProof := b } := by
  simp only [stepPublicInput, stepLeavesAt, packLeaves, xhatTableAt]
  refine pubOf_ofKeyKnown_congr (C := IpaPallas.curve) (V := V) _ ?_
  have r := fun k => PackedScalar.sameReading_refl (V := V) (C := IpaPallas.curve) k
  simp only [WrapStatement.packed]
  refine List.rel_append (List.rel_append ?_ (List.forall₂_same.mpr fun k _ => r k))
    (List.forall₂_same.mpr fun k _ => r k)
  exact .cons (r _) (.cons (r _) (.cons (r _) (.cons (r _) (.cons (r _) (.cons (r _)
    (.cons (r _) (.cons (r _) (.cons (r _) (.cons (r _) (.cons (r _) (.cons (r _)
    (.cons h .nil))))))))))))

/-- Chunk `c` of the key's Lagrange relations: each Lagrange polynomial's coefficients on the
chunk. -/
def chunkRelations {nc : ℕ} (E : Env IpaPallas.curve nc) (c : ℕ) :
    List (Fin (2 ^ E.σ.k) → IpaPallas.curve.ScalarField) :=
  (List.range E.cvk.lagrangeBasis.size).map fun i => lagrangeCoeffs E.σ.k E.cvk.n E.cvk.omega i c

/-- The relations the public-input commitment needs the SRS to avoid: per chunk, the
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

/-- Each chunk of the correction sum is a finite point when the SRS avoids the step relations
and the statement packs no more leaves than the SRS has points. The chunk's coefficients are the
leaves' shift polynomial at the chunk's domain points (`zipWith_lagrangeCoeffs_ne_zero`),
nonzero because its constant term is the first leaf's shift. -/
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

/-- The SRS avoids the step relations iff every chunk of the correction sum and every Lagrange
point is finite: a chunk of the sum commits to that chunk's coefficients
(`corrSumPt_eq_msm`). -/
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

/-- Whether the SRS avoids the step relations, decided on the key's points with no commitment
recomputed; the bounded `∀` is pinned to the list walk, as in `Env.decidableAvoids`. -/
def decidableAvoidsStepRelations {ks nc : ℕ} (E : Env IpaPallas.curve nc)
    (statement : WrapStatement ks (FVar Fp) (BoolVar Fp) (Type1 (FVar Fp)))
    (hsmall : statement.packed.length ≤ 2 ^ E.σ.k) :
    Decidable (E.σ.Avoids (stepRelationsAt E statement)) :=
  haveI : Decidable (∀ Ps ∈ E.cvk.lagrangeBasis.toList, ∀ c : Fin nc, Ps[c] ≠ 0) :=
    List.decidableBAll _ _
  decidable_of_iff _ (avoids_stepRelationsAt_iff E statement hsmall).symm

/-- `verifyProof` at the deployed Pallas scalar ops, endomorphism, sponge, group map and
square root, with the blinding base `h` as a constant cell and the public-input commitment
table of the Lagrange points `lagrange`. The constraint-system check compares it to the
production dump at the dump's points. -/
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

/-- `verifyProofWith` at the SRS blinding base and the key's Lagrange points. -/
def verifyProofAt {c : Type} [BasicSystem Fp c] [KimchiSystem Fp c] {ks k nc : ℕ}
    (E : Env IpaPallas.curve nc) (spongeAfterIndex : SpongeVar Fp) (isBaseCase : BoolVar Fp)
    (statement : WrapStatement ks (FVar Fp) (BoolVar Fp) (Type1 (FVar Fp)))
    (u : UnfinalizedProof k (FVar Fp) (BoolVar Fp) (Type2 (SplitField (FVar Fp) (BoolVar Fp))))
    (cells : IvpInput k nc (FVar Fp) (BoolVar Fp) (Type2 (SplitField (FVar Fp) (BoolVar Fp)))) :
    CircuitM Fp c (BoolVar Fp) :=
  verifyProofWith E.σ.h E.cvk.lagrangeBasis.toList spongeAfterIndex isBaseCase statement u cells

/-- **`verifyProofAt` reads as the group half at the packed statement's public input.** The
table is the key's, so `XhatTable.Bound` needs beyond the environment's invariants only that
the Lagrange points and the constant correction sum are finite, since the fold adds the sum
with `addFast`. No invariant of the key gives these; they are relations
the SRS avoids (`havoid`, `stepRelationsAt`). -/
theorem verifyProofAt_reads {ks nc : ℕ} {V : Valuation Fp} (E : Env IpaPallas.curve nc)
    (cp : KimchiProof IpaPallas.curve nc E.σ.k)
    (spongeAfterIndex : SpongeVar Fp) (isBaseCase : BoolVar Fp)
    (statement : WrapStatement ks (FVar Fp) (BoolVar Fp) (Type1 (FVar Fp)))
    (u : UnfinalizedProof E.σ.k (FVar Fp) (BoolVar Fp)
      (Type2 (SplitField (FVar Fp) (BoolVar Fp))))
    (cells : IvpInput E.σ.k nc (FVar Fp) (BoolVar Fp) (Type2 (SplitField (FVar Fp) (BoolVar Fp))))
    (oldsW : List (IpaPallas.curve.Point × Bool))
    (hbase : CircuitType.Reads V isBaseCase false)
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
    exact packLeavesOf_ofKey (C := IpaPallas.curve) _ _
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
      (bitBoolean_constLeaf_of_isScalar _ _ statement.packed_isScalar)
      (corrSumPt_ne_zero E statement hsmall havoid)
    rw [← hleaves] at hb
    exact hb
  exact verifyProof_step_reads (V := V) E.σ E.cvk cp (.const ((Pasta.vestaLam : ℤ) : Fp))
    pallasBase.sqrt? (constPt E.σ.h) (xhatTableAt E statement) spongeAfterIndex isBaseCase
    statement u cells false oldsW hbase htab hivp

/-- A wrap key has at most `2^32` chunks: its domain size divides `|Fq| − 1`, whose two-adic
part is `2^32`, and the chunk count is at most the domain size. -/
private theorem nc_le {nc : ℕ} (E : Env IpaPallas.curve nc) : nc ≤ 2 ^ 32 := by
  have hω0 : E.cvk.omega ≠ 0 := E.omega_prim.ne_zero (by rw [KimchiVK.n]; positivity)
  have hn : E.cvk.n ∣ PALLAS_SCALAR_CARD - 1 :=
    E.omega_prim.dvd_of_pow_eq_one _ (ZMod.pow_card_sub_one_eq_one hω0)
  have hd : E.cvk.domainLog2 ≤ 32 := by
    by_contra h
    have h33 : 2 ^ 33 ∣ PALLAS_SCALAR_CARD - 1 :=
      (Nat.pow_dvd_pow 2 (show 33 ≤ E.cvk.domainLog2 by omega)).trans hn
    exact absurd h33 (by norm_num [PALLAS_SCALAR_CARD])
  calc nc ≤ E.cvk.n := E.nc_le_n
    _ = 2 ^ E.cvk.domainLog2 := rfl
    _ ≤ 2 ^ 32 := Nat.pow_le_pow_right two_pos hd

/-- The base field's characteristic exceeds the group half's absorb count. -/
private theorem char_guard (m : ℕ) (hm : m ≤ 5 + 48 * 2 ^ 32) (h0 : (m : Fp) = 0) : m = 0 := by
  have hd : PALLAS_BASE_CARD ∣ m := (ZMod.natCast_eq_zero_iff m PALLAS_BASE_CARD).mp h0
  exact Nat.eq_zero_of_dvd_of_lt hd (lt_of_le_of_lt hm (by norm_num [PALLAS_BASE_CARD]))

open scoped Kimchi in
/-- The step side's group-half hypotheses at an unmasked `sg` list of at most two points, from
the proof cells reading as `cp`'s, the `sg` cells as its old accumulators', the key cells and
the sponge after the key as `VkReads`, and the shifted claims' `IvpSide.ClaimOk`, with the
shape guards proved. -/
theorem ivpHyps_of_reads {nc : ℕ} {V : Valuation Fp} {E : Env IpaPallas.curve nc}
    {cp : KimchiProof IpaPallas.curve nc E.σ.k} {pub : Array Fq}
    {keyCells : VkComms nc (AffinePoint (FVar Fp))} {spongeAfterIndex : SpongeVar Fp}
    (claims : UnfinalizedProof E.σ.k (FVar Fp) (BoolVar Fp)
      (Type2 (SplitField (FVar Fp) (BoolVar Fp))))
    (sgOld : List (AffinePoint (FVar Fp)))
    (proof : IvpProof E.σ.k nc (FVar Fp) (Type2 (SplitField (FVar Fp) (BoolVar Fp))))
    (hlen : sgOld.length ≤ 2)
    (hproof : ProofReads (stepSide V) (proof.wComm.toList.map (·.toList)) proof.zComm.toList
      proof.tComm.toList proof.opening cp)
    (holds : CommReads IpaPallas.curve V sgOld (cp.olds.map (·.sg)).toList)
    (hvk : VkReads E.cvk V spongeAfterIndex keyCells)
    (hclaimOk : ∀ x ∈ (ivpInputOf claims.deferredValues (sgOld.map (none, ·)) keyCells
      proof).shifted, (stepSide V).ClaimOk x) :
    ∃ oldsW, IvpHyps (stepSide V) E.σ E.cvk cp pub false spongeAfterIndex
      ((ivpInputOf claims.deferredValues (sgOld.map (none, ·)) keyCells proof).withClaims claims)
      oldsW := by
  refine ⟨(cp.olds.map (·.sg)).toList.map (·, true),
    { idx := hvk.idx, mask := ?mask
      ties :=
        { olds := ⟨?olds, ?kept⟩, proof := hproof
          key := hvk.key
          claimOk := hclaimOk }
      nc_pos := E.nc_pos, t_ne := ?tne, lr_ne := ?lrne, char := ?char }⟩
  case mask =>
    intro m hm
    have hm' : m ∈ sgOld.map (none, ·) := hm
    simp only [List.mem_map] at hm'
    obtain ⟨q, -, rfl⟩ := hm'
    rfl
  case olds =>
    show List.Forall₂ (MaskedBaseReads IpaPallas.curve.E.toAffine V)
      ((sgOld.map (none, ·)).map fun m => (m.2, m.1)) _
    simp only [List.map_map, List.forall₂_map_left_iff, List.forall₂_map_right_iff]
    exact holds.imp fun _ _ h => ⟨h, rfl⟩
  case kept => simp [List.filter_map, Function.comp_def]
  case tne =>
    intro he
    have he' : proof.tComm.toList = [] := he
    have hlen := congrArg List.length he'
    simp at hlen
    exact absurd hlen (Nat.pos_iff_ne_zero.mp E.nc_pos)
  case lrne =>
    intro he
    have he' : proof.opening.lr.toList = [] := he
    have hlen := congrArg List.length he'
    rw [Vector.length_toList, List.length_nil] at hlen
    exact absurd hlen (Nat.pos_iff_ne_zero.mp E.rounds_pos)
  case char =>
    intro m hm h0
    refine char_guard m (le_trans hm ?_) h0
    have h1 : ((ivpInputOf claims.deferredValues (sgOld.map (none, ·)) keyCells
        proof).withClaims claims).sgOld.length ≤ 2 := by
      show (sgOld.map (none, ·)).length ≤ 2
      simpa using hlen
    have hl := ivpInputOf_lengths claims.deferredValues (sgOld.map (none, ·)) keyCells proof
    have h2 : ((ivpInputOf claims.deferredValues (sgOld.map (none, ·)) keyCells
        proof).withClaims claims).wComm.flatten.length = 15 * nc := hl.1
    have h3 : ((ivpInputOf claims.deferredValues (sgOld.map (none, ·)) keyCells
        proof).withClaims claims).zComm.length = nc := hl.2.1
    have h4 : ((ivpInputOf claims.deferredValues (sgOld.map (none, ·)) keyCells
        proof).withClaims claims).tComm.length = quotChunks * nc := hl.2.2
    have h5 := nc_le E
    omega

/-- Under any valuation satisfying the emitted constraints, `verifyProofAt`'s returned bit reads
as a bit (`verifyProof_success_bit`). -/
theorem verifyProofAt_success_bit {ks k nc : ℕ} {V : Valuation Fp} (E : Env IpaPallas.curve nc)
    (spongeAfterIndex : SpongeVar Fp) (isBaseCase : BoolVar Fp)
    (statement : WrapStatement ks (FVar Fp) (BoolVar Fp) (Type1 (FVar Fp)))
    (u : UnfinalizedProof k (FVar Fp) (BoolVar Fp) (Type2 (SplitField (FVar Fp) (BoolVar Fp))))
    (cells : IvpInput k nc (FVar Fp) (BoolVar Fp) (Type2 (SplitField (FVar Fp) (BoolVar Fp)))) :
    ⦃⌜True⌝⦄
    verifyProofAt (c := Builder V (KimchiConstraint Fp)) E spongeAfterIndex isBaseCase statement
      u cells
    ⦃⇓ v _ => ⌜∃ b : Bool, (↑v : CVar Fp).val V = bit b⌝⦄ :=
  verifyProof_success_bit _ _ _ _ _ _ _ _ _ _ _ _ _

/-! ## The circuit of its input -/

namespace WrapProof

variable {ks k nc : ℕ}

/-- The group circuit's input: a `StepGroup` of values, allocated with no check. -/
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
/-- Whether the slot is a base case. -/
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
/-- What `incrementallyVerifyProof` consumes: the claims, every `sg` unmasked, the key's
cells and the proof. -/
def GroupVar.cells (keyCells : VkComms nc (AffinePoint (FVar Fp))) (g : GroupVar ks k nc) :
    IvpInput k nc (FVar Fp) (BoolVar Fp) (Type2 (SplitField (FVar Fp) (BoolVar Fp))) :=
  ivpInputOf g.claims.deferredValues (g.sgOld.map (none, ·)) keyCells g.val.proof
/-- The group circuit as a `GroupHalf`. -/
abbrev GroupVar.half (V : Valuation Fp) (g : GroupVar ks k nc) :
    GroupHalf IpaPallas.curve (Type2 (SplitField (FVar Fp) (BoolVar Fp))) k :=
  GroupHalf.step V g.claims

/-- `verifyProofAt` as a circuit of its input, its success bit asserted. Before it, the shifted
scalars' parity cells are asserted boolean (`assertClaimBitsStep`), the allocation check the
deployed circuit's split type makes and this harness's unchecked input lacks. -/
def groupCircuit {c : Type} [BasicSystem Fp c] [KimchiSystem Fp c] (E : Env IpaPallas.curve nc)
    (keyCells : VkComms nc (AffinePoint (FVar Fp))) (spongeAfterIndex : SpongeVar Fp)
    (g : GroupVar ks k nc) : CircuitM Fp c Unit := do
  assertClaimBitsStep g.shifted
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
  refine builder_spec_bind_of _ _ _ _ (assertClaimBitsStep_spec (V := V) g.shifted)
    fun hclaimOk _ => ?_
  obtain ⟨oldsW, hivp⟩ := hivp hclaimOk
  have hv := verifyProofAt_reads (V := V) E cp spongeAfterIndex g.isBaseCase g.statement
    g.claims (g.cells keyCells) oldsW hbase hsmall havoid hivp
  mvcgen -trivial [hv]
  rename_i v _ hr _ _
  intro h1
  exact ⟨v, hr, h1⟩

end WrapProof

/-! The gadget is sealed after its read: a consumer composes `verifyProofAt_reads`, never the
body. -/
attribute [irreducible] verifyProofAt

end Pickles
