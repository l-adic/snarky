import Kimchi.Columns
import Pickles.Encoding
import Pickles.ShiftedClaims
import Pickles.TwoHalves

/-!
# The step circuit's group half, at a key

The step circuit's `verifyProof` at a key: the deployed Pallas constants, the SRS
blinding base as a constant cell, and the public-input commitment table computed from the key's
Lagrange points (`XhatTable.ofKeyKnown`). The public input is the wrap circuit's packed statement,
flattened (`stepPublicInput`), and what the table reads as is proved from the key's invariants
rather than assumed (`verifyProofAt_reads`), the read the step circuit's slot read composes
(`verifyOne_reads`).
-/

namespace Pickles

open Std.Do Snarky Snarky.Kimchi Kimchi.Verifier Bulletproof Bulletproof.Ipa
open CompElliptic.Fields.Pasta CompElliptic.Curves.Pasta

/-- The public-input commitment table at a key, computed from the key's Lagrange
points at the statement's packing, one point per packed scalar. It reads the packing's kinds,
never its cells. -/
private def xhatTableAt {ks nc : ℕ} (σ : SRS IpaPallas.curve.Point)
    (cvk : KimchiVK IpaPallas.curve nc)
    (statement : WrapStatement ks (FVar Fp) (BoolVar Fp) (Type1 (FVar Fp))) :
    XhatTable Fp nc (CircuitType.size Fp (PackedWrapStatement ks (Type1 Fp) Fp)) :=
  XhatTable.ofKeyKnown (C := IpaPallas.curve) statement.packed
    (cvk.lagrangePoints σ (CircuitType.size Fp (PackedWrapStatement ks (Type1 Fp) Fp)))

/-- The public-input leaves at a key: the packed wrap statement over the key's table. -/
def stepLeavesAt {ks nc : ℕ} (σ : SRS IpaPallas.curve.Point) (cvk : KimchiVK IpaPallas.curve nc)
    (statement : WrapStatement ks (FVar Fp) (BoolVar Fp) (Type1 (FVar Fp))) :
    List (Leaf Fp nc) :=
  packLeaves statement (xhatTableAt σ cvk statement)

/-- A wrap statement's cells as the wrap circuit's packed public input: each scalar reduced into
the scalar field, the optional-feature cells off. -/
def WrapStatement.toPacked {ks : ℕ} (V : Valuation Fp)
    (st : WrapStatement ks (FVar Fp) (BoolVar Fp) (Type1 (FVar Fp))) :
    StatementPacked ks (Type1 Fq) Fq :=
  let r (x : FVar Fp) : Fq := ((ToNat.toNat (x.val V) : ℕ) : Fq)
  let dv := st.proofState.deferredValues
  let pl := dv.plonk
  { fpFields := #v[⟨r dv.combinedInnerProduct.val⟩, ⟨r dv.b.val⟩, ⟨r pl.zetaToSrsLength.val⟩,
      ⟨r pl.zetaToDomainSize.val⟩, ⟨r pl.perm.val⟩]
    challenges := #v[r pl.beta.val, r pl.gamma.val]
    scalarChallenges := #v[r pl.alpha.val, r pl.zeta.val, r dv.xi.val]
    digests := #v[r st.proofState.spongeDigestBeforeEvaluations,
      r st.proofState.messagesForNextWrapProof, r st.messagesForNextStepProof]
    bulletproofChallenges := dv.bulletproofChallenges.map fun c => r c.val
    branchData := r dv.branchData.packed
    featureFlags := Vector.replicate 8 0
    lookupOptFlag := 0
    lookupOptScalarChallenge := 0 }

/-- The wire's public input of a wrap statement: the wrap circuit's packed statement
(`WrapStatement.toPacked`), flattened. The optional-feature cells are fields of that record, off
in the modeled fragment. -/
def stepPublicInput {ks : ℕ} (V : Valuation Fp)
    (statement : WrapStatement ks (FVar Fp) (BoolVar Fp) (Type1 (FVar Fp))) : Array Fq :=
  (CircuitType.valueToFields (F := Fq) (var := StatementPacked ks (Type1 (FVar Fq)) (FVar Fq))
    (statement.toPacked V)).toArray

/-- The public input reads the step-message digest only through its value. -/
theorem stepPublicInput_congr_msg {ks : ℕ} (V : Valuation Fp)
    (st : WrapStatement ks (FVar Fp) (BoolVar Fp) (Type1 (FVar Fp))) (a b : FVar Fp)
    (h : a.val V = b.val V) :
    stepPublicInput V { st with messagesForNextStepProof := a }
      = stepPublicInput V { st with messagesForNextStepProof := b } := by
  simp only [stepPublicInput, WrapStatement.toPacked, h]

/-- **The packed statement is the leaves' public input, then zero cells.** Flattened, `toPacked`
is the public input the leaves commit to (`pubOf`), followed by the optional-feature cells, all
zero. -/
theorem stepPublicInput_eq_append {ks nc : ℕ} (σ : SRS IpaPallas.curve.Point)
    (cvk : KimchiVK IpaPallas.curve nc) (V : Valuation Fp)
    (st : WrapStatement ks (FVar Fp) (BoolVar Fp) (Type1 (FVar Fp))) :
    ∃ zs : Array Fq, (∀ z ∈ zs, z = 0) ∧
      stepPublicInput V st = pubOf IpaPallas.curve V (stepLeavesAt σ cvk st) ++ zs := by
  refine ⟨Array.replicate 10 0, fun z hz => (Array.mem_replicate.mp hz).2, ?_⟩
  have hpub : (pubOf IpaPallas.curve V (stepLeavesAt σ cvk st)).toList
      = st.packed.toList.map (PackedScalar.reduced IpaPallas.curve V) := by
    have hk : packLeavesOf st.packed
        (XhatTable.ofKeyKnown (C := IpaPallas.curve) st.packed
          (cvk.lagrangePoints σ (CircuitType.size Fp (PackedWrapStatement ks (Type1 Fp) Fp))))
        = List.zipWith (constLeaf (C := IpaPallas.curve)) st.packed.toList
          (cvk.lagrangePoints σ
            (CircuitType.size Fp (PackedWrapStatement ks (Type1 Fp) Fp))).toList :=
      packLeavesOf_ofKey st.packed
        (cvk.lagrangePoints σ (CircuitType.size Fp (PackedWrapStatement ks (Type1 Fp) Fp)))
    simp only [stepLeavesAt, packLeaves, xhatTableAt]
    rw [hk]
    exact pubOf_zipWith_constLeaf _ _
  apply Array.toList_inj.mp
  rw [Array.toList_append, hpub]
  unfold stepPublicInput
  rw [Vector.toList_toArray]
  change (CircuitType.valueToFields (F := Fq)
    (var := Vector (Type1 (FVar Fq)) 5 × Vector (FVar Fq) 2 × Vector (FVar Fq) 3 ×
      Vector (FVar Fq) 3 × Vector (FVar Fq) ks × FVar Fq × Vector (FVar Fq) 8 × FVar Fq × FVar Fq)
    (StatementPacked.equivProd ks (Type1 Fq) Fq (st.toPacked V))).toList = _
  have h1 : ∀ x : Type1 Fq, CircuitType.valueToFields (F := Fq) (var := Type1 (FVar Fq)) x
      = #v[x.val] := fun _ => rfl
  have h2 : ∀ x : Fq, CircuitType.valueToFields (F := Fq) (var := FVar Fq) x = #v[x] :=
    fun _ => rfl
  simp only [StatementPacked.equivProd, Equiv.coe_fn_mk, CircuitType.valueToFields_prod,
    CircuitType.valueToFields_vector]
  simp [WrapStatement.toPacked, WrapStatement.packed, PackedScalar.reduced, PackedScalar.cell,
    mapVec_eq_map, h1, h2, Function.comp_def]
  rw [toList_flatten_singletons st.proofState.deferredValues.bulletproofChallenges
    fun x => ((ToNat.toNat (CVar.val x.val V) : ℕ) : Fq)]
  simp only [List.append_cancel_left_eq, List.cons.injEq, true_and]
  rw [show Vector.replicate 8 #v[(0 : Fq)] = (Vector.replicate 8 (0 : Fq)).map fun c => #v[c] by
    simp, toList_flatten_singletons]
  simp

/-- Chunk `c` of the key's first `m` Lagrange relations: each Lagrange polynomial's coefficients
on the chunk. -/
def chunkRelations {nc : ℕ} (σ : SRS IpaPallas.curve.Point) (cvk : KimchiVK IpaPallas.curve nc)
    (m c : ℕ) :
    List (Fin (2 ^ σ.k) → IpaPallas.curve.ScalarField) :=
  (List.range m).map fun i => lagrangeCoeffs σ.k cvk.n cvk.omega i c

/-- The relations the public-input commitment needs the SRS to avoid: per chunk, the
coefficients of the constant the known-domain fold adds (the sum of the leaves' shift
corrections), then the Lagrange vectors, one per packed scalar. It reads the packing's kinds,
never its cells. -/
def stepRelationsAt {ks nc : ℕ} (σ : SRS IpaPallas.curve.Point) (cvk : KimchiVK IpaPallas.curve nc)
    (statement : WrapStatement ks (FVar Fp) (BoolVar Fp) (Type1 (FVar Fp))) :
    List (Fin (2 ^ σ.k) → IpaPallas.curve.ScalarField) :=
  (List.finRange nc).map (fun c : Fin nc =>
    corrCoeffs (C := IpaPallas.curve) statement.packed.toList
      (chunkRelations σ cvk (CircuitType.size Fp (PackedWrapStatement ks (Type1 Fp) Fp)) c.val))
    ++ cvk.lagrangeRelations σ.k (CircuitType.size Fp (PackedWrapStatement ks (Type1 Fp) Fp))

/-- Chunk `c` of the correction sum is the commitment to its coefficients on the chunk. -/
private theorem corrSumPt_eq_msm {ks nc : ℕ} (σ : SRS IpaPallas.curve.Point)
    (cvk : KimchiVK IpaPallas.curve nc)
    (statement : WrapStatement ks (FVar Fp) (BoolVar Fp) (Type1 (FVar Fp))) (m : ℕ) (c : Fin nc) :
    corrSumPt (C := IpaPallas.curve) statement.packed.toList (cvk.lagrangePoints σ m).toList c
      = msm IpaPallas.curve σ.g
          (corrCoeffs (C := IpaPallas.curve) statement.packed.toList
            (chunkRelations σ cvk m c.val)) := by
  have hchunk : corrSumPt (C := IpaPallas.curve) statement.packed.toList
      (cvk.lagrangePoints σ m).toList c
      = corrSumPt (C := IpaPallas.curve) statement.packed.toList
          ((cvk.lagrangePoints σ m).toList.map fun Ps => #v[Ps[c]]) 0 := by
    simp [corrSumPt, List.zipWith_map_right]
  have hmap : (cvk.lagrangePoints σ m).toList.map (fun Ps => #v[Ps[c]])
      = (chunkRelations σ cvk m c.val).map fun a => #v[msm IpaPallas.curve σ.g a] := by
    rw [cvk.lagrangePoints_toList σ, List.map_map, chunkRelations, List.map_map]
    refine List.map_congr_left fun i _ => ?_
    simp
  rw [hchunk, hmap, corrSumPt_map_msm]

/-- Each chunk of the correction sum is a finite point when the SRS avoids the step relations
and the statement packs no more leaves than the SRS has points or the domain has elements. The
chunk's coefficients are the leaves' shift polynomial at the chunk's domain points
(`zipWith_lagrangeCoeffs_ne_zero`), nonzero because its constant term is the first leaf's
shift. -/
private theorem corrSumPt_ne_zero {ks nc : ℕ} (σ : SRS IpaPallas.curve.Point)
    (K : Key IpaPallas.curve nc) (hnc : nc = chunkCount σ.k K.cvk.domainLog2)
    (statement : WrapStatement ks (FVar Fp) (BoolVar Fp) (Type1 (FVar Fp)))
    (hsmall : CircuitType.size Fp (PackedWrapStatement ks (Type1 Fp) Fp) ≤ 2 ^ σ.k)
    (hn : CircuitType.size Fp (PackedWrapStatement ks (Type1 Fp) Fp) ≤ K.cvk.n)
    (h : σ.Avoids (stepRelationsAt σ K.cvk statement)) (c : Fin nc) :
    corrSumPt (C := IpaPallas.curve) statement.packed.toList
      (K.cvk.lagrangePoints σ (CircuitType.size Fp (PackedWrapStatement ks (Type1 Fp) Fp))).toList c
      ≠ 0 := by
  rw [corrSumPt_eq_msm]
  refine h _ (List.mem_append_left _ (List.mem_map.2 ⟨c, List.mem_finRange c, rfl⟩))
    fun h0 => ?_
  obtain ⟨k, rest, hk⟩ := List.exists_cons_of_ne_nil
    (l := statement.packed.toList) (by simp [WrapStatement.packed])
  have hroom := Key.chunk_add_le hnc c
  have hlen : rest.length + 1 = CircuitType.size Fp (PackedWrapStatement ks (Type1 Fp) Fp) := by
    rw [← List.length_cons, ← hk, Vector.length_toList]
  refine zipWith_lagrangeCoeffs_ne_zero (k := σ.k) K.omega_prim
    (K.natCast_n_ne_zero pastaShapePallas) c
    (CircuitType.size Fp (PackedWrapStatement ks (Type1 Fp) Fp)) (shiftCoeff k)
    (rest.map shiftCoeff) (shiftCoeff_ne_zero pastaShapePallas k
      (statement.packed_isScalar k (Vector.mem_toList_iff.mp (hk ▸ List.mem_cons_self)))) (by omega)
    (by simp only [List.length_map]; omega) (by simp only [List.length_map]; omega) ?_
  rw [← h0, corrCoeffs, chunkRelations, hk, ← List.map_cons, List.zipWith_map_left]

/-- The SRS avoids the step relations iff every chunk of the correction sum and every Lagrange
point is finite: a chunk of the sum commits to that chunk's coefficients
(`corrSumPt_eq_msm`). A driver decides the right side on points it computed once. -/
theorem avoids_stepRelationsAt_iff {ks nc : ℕ} (σ : SRS IpaPallas.curve.Point)
    (K : Key IpaPallas.curve nc) (hnc : nc = chunkCount σ.k K.cvk.domainLog2)
    (statement : WrapStatement ks (FVar Fp) (BoolVar Fp) (Type1 (FVar Fp)))
    (hsmall : CircuitType.size Fp (PackedWrapStatement ks (Type1 Fp) Fp) ≤ 2 ^ σ.k)
    (hn : CircuitType.size Fp (PackedWrapStatement ks (Type1 Fp) Fp) ≤ K.cvk.n) :
    σ.Avoids (stepRelationsAt σ K.cvk statement)
      ↔ (∀ c : Fin nc, corrSumPt (C := IpaPallas.curve) statement.packed.toList
            (K.cvk.lagrangePoints σ
              (CircuitType.size Fp (PackedWrapStatement ks (Type1 Fp) Fp))).toList c ≠ 0)
        ∧ ∀ Ps ∈ (K.cvk.lagrangePoints σ
            (CircuitType.size Fp (PackedWrapStatement ks (Type1 Fp) Fp))).toList,
            ∀ c : Fin nc, Ps[c] ≠ 0 := by
  refine ⟨fun h => ⟨corrSumPt_ne_zero σ K hnc statement hsmall hn h, Key.lagrange_ne
    pastaShapePallas σ hnc
    fun a ha => h a (List.mem_append_right _ ha)⟩, fun ⟨hsum, hL⟩ a ha hne => ?_⟩
  rcases List.mem_append.1 ha with ha | ha
  · obtain ⟨c, -, rfl⟩ := List.mem_map.1 ha
    rw [← corrSumPt_eq_msm]
    exact hsum c
  · exact (Key.avoids_lagrangeRelations_iff pastaShapePallas σ hnc _).2 hL a ha hne

/-- `verifyProof` at the deployed Pallas scalar ops, endomorphism, sponge, group map and
square root, with the blinding base `h` as a constant cell and the public-input commitment
table of the Lagrange points `lagrange`. The constraint-system check compares it to the
production dump at the dump's points. -/
def verifyProofWith {c : Type} [BasicSystem Fp c] [ConstraintHolds Fp c]
    [LawfulBasicSystem Fp c] [KimchiSystem Fp c]
    {ks k nc np : ℕ}
    (h : IpaPallas.curve.Point)
    (lagrange : Vector (Vector IpaPallas.curve.Point nc)
      (CircuitType.size Fp (PackedWrapStatement ks (Type1 Fp) Fp)))
    (spongeAfterIndex : SpongeVar Fp) (isBaseCase : BoolVar Fp)
    (statement : WrapStatement ks (FVar Fp) (BoolVar Fp) (Type1 (FVar Fp)))
    (u : UnfinalizedProof k (FVar Fp) (BoolVar Fp) (Type2 (SplitField (FVar Fp) (BoolVar Fp))))
    (cells : IvpInput k nc np (FVar Fp) (BoolVar Fp) (Type2 (SplitField (FVar Fp) (BoolVar Fp)))) :
    CircuitM Fp c (BoolVar Fp) :=
  verifyProof IpaScalarOps.step IpaEndo.pallas IpaPallas.curve.sponge.params
    (.const ((Pasta.vestaLam : ℤ) : Fp)) groupMapParamsPallas pallasBase.sqrt? (constPt h)
    (XhatTable.ofKeyKnown (C := IpaPallas.curve) statement.packed lagrange) spongeAfterIndex
    isBaseCase statement u cells

/-- `verifyProofWith` at the SRS blinding base and the key's Lagrange points, one per packed
scalar. -/
def verifyProofAt {c : Type} [BasicSystem Fp c] [ConstraintHolds Fp c]
    [LawfulBasicSystem Fp c] [KimchiSystem Fp c]
    {ks k nc np : ℕ}
    (σ : SRS IpaPallas.curve.Point) (cvk : KimchiVK IpaPallas.curve nc)
    (spongeAfterIndex : SpongeVar Fp) (isBaseCase : BoolVar Fp)
    (statement : WrapStatement ks (FVar Fp) (BoolVar Fp) (Type1 (FVar Fp)))
    (u : UnfinalizedProof k (FVar Fp) (BoolVar Fp) (Type2 (SplitField (FVar Fp) (BoolVar Fp))))
    (cells : IvpInput k nc np (FVar Fp) (BoolVar Fp) (Type2 (SplitField (FVar Fp) (BoolVar Fp)))) :
    CircuitM Fp c (BoolVar Fp) :=
  verifyProofWith σ.h
    (cvk.lagrangePoints σ (CircuitType.size Fp (PackedWrapStatement ks (Type1 Fp) Fp)))
    spongeAfterIndex isBaseCase statement u cells

/-- **`verifyProofAt` reads as the group half at the packed statement's public input.** The
table is the key's, so `XhatTable.Bound` needs beyond the key's invariants only that
the Lagrange points and the constant correction sum are finite, since the fold adds the sum
with `addFast`. No invariant of the key gives these; they are relations the SRS avoids
(`havoid`, `stepRelationsAt`). The optional-feature cells the table leaves out are zero
(`stepPublicInput_eq_append`). -/
theorem verifyProofAt_reads {ks nc np : ℕ} {V : Valuation Fp} (S : Srs IpaPallas.curve)
    (K : Key IpaPallas.curve nc) (hnc : nc = chunkCount S.σ.k K.cvk.domainLog2)
    (cp : KimchiProof IpaPallas.curve nc S.σ.k)
    (spongeAfterIndex : SpongeVar Fp) (isBaseCase : BoolVar Fp)
    (statement : WrapStatement ks (FVar Fp) (BoolVar Fp) (Type1 (FVar Fp)))
    (u : UnfinalizedProof S.σ.k (FVar Fp) (BoolVar Fp)
      (Type2 (SplitField (FVar Fp) (BoolVar Fp))))
    (cells : IvpInput S.σ.k nc np (FVar Fp) (BoolVar Fp)
      (Type2 (SplitField (FVar Fp) (BoolVar Fp))))
    (oldsW : Vector (IpaPallas.curve.Point × Bool) np)
    (hbase : CircuitType.Reads V isBaseCase false)
    (hsmall : CircuitType.size Fp (PackedWrapStatement ks (Type1 Fp) Fp) ≤ 2 ^ S.σ.k)
    (hn : CircuitType.size Fp (PackedWrapStatement ks (Type1 Fp) Fp) ≤ K.cvk.n)
    (havoid : S.σ.Avoids (stepRelationsAt S.σ K.cvk statement))
    (hivp : IvpHyps (stepSide V) S.σ K.cvk cp (stepPublicInput V statement) false
      spongeAfterIndex (cells.withClaims u) oldsW) :
    ⦃⌜True⌝⦄
    verifyProofAt (c := Builder V (KimchiConstraint Fp)) S.σ K.cvk spongeAfterIndex isBaseCase
      statement u cells
    ⦃⇓ v _ => ⌜VerifyReads (stepSide V) S.σ K.cvk cp (stepPublicInput V statement) u false
      v⌝⦄ := by
  have hleaves : stepLeavesAt S.σ K.cvk statement
      = List.zipWith (constLeaf (C := IpaPallas.curve)) statement.packed.toList
        (K.cvk.lagrangePoints S.σ
          (CircuitType.size Fp (PackedWrapStatement ks (Type1 Fp) Fp))).toList := by
    unfold stepLeavesAt packLeaves xhatTableAt
    exact packLeavesOf_ofKey (C := IpaPallas.curve) _ _
  have hsz : (pubOf IpaPallas.curve V (packLeaves statement (xhatTableAt S.σ K.cvk statement))).size
      = (CircuitType.size Fp (PackedWrapStatement ks (Type1 Fp) Fp)) := by
    rw [← stepLeavesAt, hleaves]
    simp [pubOf]
  have htab : (xhatTableAt S.σ K.cvk statement).Bound pastaShapePallas V S.σ
      (K.cvk.lagrangePoints S.σ
        (pubOf IpaPallas.curve V (packLeaves statement (xhatTableAt S.σ K.cvk
          statement))).size).toArray
      (constPt S.σ.h) (packLeaves statement (xhatTableAt S.σ K.cvk statement)) := by
    rw [hsz]
    have hb := bound_ofKeyKnown (V := V) pastaShapePallas S.σ
      (K.cvk.lagrangePoints S.σ (CircuitType.size Fp (PackedWrapStatement ks (Type1 Fp) Fp)))
      statement.packed S.h_ne
      (fun Ps h ci => Key.lagrange_ne pastaShapePallas S.σ hnc
        (fun a ha => havoid a (List.mem_append_right _ ha)) Ps h ci)
      (bitBoolean_constLeaf_of_isScalar _ _
        fun k hk => statement.packed_isScalar k (Vector.mem_toList_iff.mp hk))
      (corrSumPt_ne_zero S.σ K hnc statement hsmall hn havoid)
    rw [← hleaves] at hb
    exact hb
  obtain ⟨zs, hz, hpub⟩ := stepPublicInput_eq_append S.σ K.cvk V statement
  rw [hpub] at hivp ⊢
  have hr := verifyProof_step_reads (V := V) S.σ K.cvk cp (.const ((Pasta.vestaLam : ℤ) : Fp))
    pallasBase.sqrt? (constPt S.σ.h) (xhatTableAt S.σ K.cvk statement) spongeAfterIndex isBaseCase
    statement u cells false oldsW hbase htab
    ⟨hivp.idx, hivp.mask, hivp.ties, hivp.nc_pos, hivp.k_pos, hivp.char⟩
  exact builder_spec_imp _ _ _ hr fun _ h => VerifyReads.append_zero hz h

/-- A wrap key has at most `2^32` chunks: its domain size divides `|Fq| − 1`, whose two-adic
part is `2^32`, and the chunk count is at most the domain size. -/
private theorem nc_le {nc : ℕ} (σ : SRS IpaPallas.curve.Point) (K : Key IpaPallas.curve nc)
    (hnc : nc = chunkCount σ.k K.cvk.domainLog2) : nc ≤ 2 ^ 32 := by
  have hω0 : K.cvk.omega ≠ 0 := K.omega_prim.ne_zero (by rw [KimchiVK.n]; positivity)
  have hn : K.cvk.n ∣ PALLAS_SCALAR_CARD - 1 :=
    K.omega_prim.dvd_of_pow_eq_one _ (ZMod.pow_card_sub_one_eq_one hω0)
  have hd : K.cvk.domainLog2 ≤ 32 := by
    by_contra h
    have h33 : 2 ^ 33 ∣ PALLAS_SCALAR_CARD - 1 :=
      (Nat.pow_dvd_pow 2 (show 33 ≤ K.cvk.domainLog2 by omega)).trans hn
    exact absurd h33 (by norm_num [PALLAS_SCALAR_CARD])
  calc nc ≤ K.cvk.n := (Key.nc_le_n hnc)
    _ = 2 ^ K.cvk.domainLog2 := rfl
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
theorem ivpHyps_of_reads {nc : ℕ} {V : Valuation Fp} {S : Srs IpaPallas.curve}
    {K : Key IpaPallas.curve nc} (hnc : nc = chunkCount S.σ.k K.cvk.domainLog2)
    {cp : KimchiProof IpaPallas.curve nc S.σ.k} {pub : Array Fq}
    {keyCells : VkComms nc (AffinePoint (FVar Fp))} {spongeAfterIndex : SpongeVar Fp}
    (claims : UnfinalizedProof S.σ.k (FVar Fp) (BoolVar Fp)
      (Type2 (SplitField (FVar Fp) (BoolVar Fp))))
    (sgOld : Vector (AffinePoint (FVar Fp)) MaxProofsVerified)
    (proof : IvpProof S.σ.k nc (FVar Fp) (Type2 (SplitField (FVar Fp) (BoolVar Fp))))
    (hproof : ProofReads (stepSide V) proof.wComm proof.zComm proof.tComm proof.opening cp)
    (holds : CommReads IpaPallas.curve V sgOld.toList (cp.olds.map (·.sg)).toList)
    (hvk : VkReads K.cvk V spongeAfterIndex keyCells)
    (hclaimOk : ∀ x ∈ (ivpInputOf claims.deferredValues (sgOld.map (none, ·)) keyCells
      proof).shifted, (stepSide V).ClaimOk x) :
    ∃ oldsW, IvpHyps (stepSide V) S.σ K.cvk cp pub false spongeAfterIndex
      ((ivpInputOf claims.deferredValues (sgOld.map (none, ·)) keyCells proof).withClaims claims)
      oldsW := by
  -- the proof's old accumulators, one per `sg` cell
  obtain ⟨sgW, hsgW, -⟩ := exists_vector_of_forall₂ holds
  refine ⟨sgW.map (·, true),
    { idx := hvk.idx, mask := ?mask
      ties :=
        { olds := ⟨?olds, ?kept⟩, proof := hproof
          key := hvk.key
          claimOk := hclaimOk }
      nc_pos := K.cvk.nc_pos, k_pos := S.rounds_pos, char := ?char }⟩
  case mask =>
    intro m hm
    have hm' : m ∈ sgOld.map (none, ·) := hm
    obtain ⟨q, -, rfl⟩ := Vector.mem_map.mp hm'
    rfl
  case olds =>
    show List.Forall₂ (MaskedBaseReads IpaPallas.curve.E.toAffine V)
      ((sgOld.map (none, ·)).toList.map fun m => (m.2, m.1)) _
    simp only [Vector.toList_map, List.map_map, List.forall₂_map_left_iff,
      List.forall₂_map_right_iff, hsgW]
    exact holds.imp fun _ _ h => ⟨h, rfl⟩
  case kept => simp [Vector.toList_map, hsgW, List.filter_map, Function.comp_def]
  case char =>
    intro m hm h0
    refine char_guard m (le_trans hm ?_) h0
    have h5 := nc_le S.σ K hnc
    simp only [MaxProofsVerified]
    omega

/-- Under any valuation satisfying the emitted constraints, `verifyProofWith`'s returned bit
reads as a bit (`verifyProof_success_bit`). -/
theorem verifyProofWith_success_bit {ks k nc np : ℕ} {V : Valuation Fp}
    (h : IpaPallas.curve.Point)
    (lagrange : Vector (Vector IpaPallas.curve.Point nc)
      (CircuitType.size Fp (PackedWrapStatement ks (Type1 Fp) Fp)))
    (spongeAfterIndex : SpongeVar Fp) (isBaseCase : BoolVar Fp)
    (statement : WrapStatement ks (FVar Fp) (BoolVar Fp) (Type1 (FVar Fp)))
    (u : UnfinalizedProof k (FVar Fp) (BoolVar Fp) (Type2 (SplitField (FVar Fp) (BoolVar Fp))))
    (cells : IvpInput k nc np (FVar Fp) (BoolVar Fp) (Type2 (SplitField (FVar Fp) (BoolVar Fp)))) :
    ⦃⌜True⌝⦄
    verifyProofWith (c := Builder V (KimchiConstraint Fp)) h lagrange spongeAfterIndex
      isBaseCase statement u cells
    ⦃⇓ v _ => ⌜∃ b : Bool, (↑v : CVar Fp).val V = bit b⌝⦄ :=
  verifyProof_success_bit _ _ _ _ _ _ _ _ _ _ _ _ _

/-! The gadget is sealed after its read: a consumer composes `verifyProofAt_reads`, never the
body. -/
attribute [irreducible] verifyProofAt

end Pickles
