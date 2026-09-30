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

/-- The public-input commitment table at a key, computed from the key's Lagrange
points at the statement's packing, one point per packed scalar. It reads the packing's kinds,
never its cells. -/
private def xhatTableAt {ks nc : ℕ} (σ : SRS IpaPallas.curve.Point)
    (cvk : KimchiVK IpaPallas.curve nc)
    (statement : WrapStatement ks (FVar Fp) (BoolVar Fp) (Type1 (FVar Fp))) : XhatTable Fp nc :=
  XhatTable.ofKeyKnown (C := IpaPallas.curve) statement.packed
    (cvk.lagrangePoints σ statement.packed.length).toList

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

/-- The public input has a cell per packed scalar: the packed statement, then the
optional-feature cells. -/
theorem packed_length_le_stepPublicInput {ks : ℕ} (V : Valuation Fp)
    (st : WrapStatement ks (FVar Fp) (BoolVar Fp) (Type1 (FVar Fp))) :
    st.packed.length ≤ (stepPublicInput V st).size := by
  have hs : (stepPublicInput V st).size = CircuitType.size Fq (Vector (Type1 Fq) 5 ×
      Vector Fq 2 × Vector Fq 3 × Vector Fq 3 × Vector Fq ks × Fq × Vector Fq 8 × Fq × Fq) := by
    simp only [stepPublicInput, Vector.size_toArray]
    rfl
  have h1 : CircuitType.size Fq Fq = 1 := rfl
  have ht : CircuitType.size Fq (Type1 Fq) = 1 := rfl
  have h1' : CircuitType.size Fp Fp = 1 := rfl
  have ht' : CircuitType.size Fp (Type1 Fp) = 1 := rfl
  rw [hs, WrapStatement.packed_length]
  simp only [CircuitType.size_prod, CircuitType.size_vector, h1, ht, h1', ht']
  omega

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
      = st.packed.map (PackedScalar.reduced IpaPallas.curve V) := by
    have hk : packLeavesOf st.packed (XhatTable.ofKeyKnown (C := IpaPallas.curve) st.packed
        (cvk.lagrangePoints σ st.packed.length).toList)
        = List.zipWith (constLeaf (C := IpaPallas.curve)) st.packed
          (cvk.lagrangePoints σ st.packed.length).toList :=
      packLeavesOf_ofKey st.packed (cvk.lagrangePoints σ st.packed.length).toList
    simp only [stepLeavesAt, packLeaves, xhatTableAt]
    rw [hk]
    exact pubOf_zipWith_constLeaf _ _ (by simp)
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
  (List.finRange nc).map (fun c : Fin nc => corrCoeffs (C := IpaPallas.curve) statement.packed
    (chunkRelations σ cvk statement.packed.length c.val))
    ++ cvk.lagrangeRelations σ.k statement.packed.length

/-- Chunk `c` of the correction sum is the commitment to its coefficients on the chunk. -/
private theorem corrSumPt_eq_msm {ks nc : ℕ} (σ : SRS IpaPallas.curve.Point)
    (cvk : KimchiVK IpaPallas.curve nc)
    (statement : WrapStatement ks (FVar Fp) (BoolVar Fp) (Type1 (FVar Fp))) (m : ℕ) (c : Fin nc) :
    corrSumPt (C := IpaPallas.curve) statement.packed (cvk.lagrangePoints σ m).toList c
      = msm IpaPallas.curve σ.g
          (corrCoeffs (C := IpaPallas.curve) statement.packed (chunkRelations σ cvk m c.val)) := by
  have hchunk : corrSumPt (C := IpaPallas.curve) statement.packed
      (cvk.lagrangePoints σ m).toList c
      = corrSumPt (C := IpaPallas.curve) statement.packed
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
    (hsmall : statement.packed.length ≤ 2 ^ σ.k) (hn : statement.packed.length ≤ K.cvk.n)
    (h : σ.Avoids (stepRelationsAt σ K.cvk statement)) (c : Fin nc) :
    corrSumPt (C := IpaPallas.curve) statement.packed
      (K.cvk.lagrangePoints σ statement.packed.length).toList c ≠ 0 := by
  rw [corrSumPt_eq_msm]
  refine h _ (List.mem_append_left _ (List.mem_map.2 ⟨c, List.mem_finRange c, rfl⟩))
    fun h0 => ?_
  obtain ⟨k, rest, hk⟩ := List.exists_cons_of_ne_nil
    (l := statement.packed) (by simp [WrapStatement.packed])
  have hroom := Key.chunk_add_le hnc c
  rw [hk, List.length_cons] at hsmall hn
  refine zipWith_lagrangeCoeffs_ne_zero (k := σ.k) K.omega_prim
    (K.natCast_n_ne_zero pastaShapePallas) c statement.packed.length (shiftCoeff k)
    (rest.map shiftCoeff) (shiftCoeff_ne_zero pastaShapePallas k
      (statement.packed_isScalar k (hk ▸ List.mem_cons_self))) (by rw [hk]; simp)
    (by simp only [List.length_map, hk, List.length_cons, Nat.min_self]; omega)
    (by simp only [List.length_map, hk, List.length_cons, Nat.min_self]; omega) ?_
  rw [← h0, corrCoeffs, chunkRelations, hk, ← List.map_cons, List.zipWith_map_left]

/-- The SRS avoids the step relations iff every chunk of the correction sum and every Lagrange
point is finite: a chunk of the sum commits to that chunk's coefficients
(`corrSumPt_eq_msm`). A driver decides the right side on points it computed once. -/
theorem avoids_stepRelationsAt_iff {ks nc : ℕ} (σ : SRS IpaPallas.curve.Point)
    (K : Key IpaPallas.curve nc) (hnc : nc = chunkCount σ.k K.cvk.domainLog2)
    (statement : WrapStatement ks (FVar Fp) (BoolVar Fp) (Type1 (FVar Fp)))
    (hsmall : statement.packed.length ≤ 2 ^ σ.k) (hn : statement.packed.length ≤ K.cvk.n) :
    σ.Avoids (stepRelationsAt σ K.cvk statement)
      ↔ (∀ c : Fin nc, corrSumPt (C := IpaPallas.curve) statement.packed
            (K.cvk.lagrangePoints σ statement.packed.length).toList c ≠ 0)
        ∧ ∀ Ps ∈ (K.cvk.lagrangePoints σ statement.packed.length).toList, ∀ c : Fin nc,
            Ps[c] ≠ 0 := by
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
    {ks k nc : ℕ}
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

/-- `verifyProofWith` at the SRS blinding base and the key's Lagrange points, one per packed
scalar. -/
def verifyProofAt {c : Type} [BasicSystem Fp c] [ConstraintHolds Fp c]
    [LawfulBasicSystem Fp c] [KimchiSystem Fp c]
    {ks k nc : ℕ}
    (σ : SRS IpaPallas.curve.Point) (cvk : KimchiVK IpaPallas.curve nc)
    (spongeAfterIndex : SpongeVar Fp) (isBaseCase : BoolVar Fp)
    (statement : WrapStatement ks (FVar Fp) (BoolVar Fp) (Type1 (FVar Fp)))
    (u : UnfinalizedProof k (FVar Fp) (BoolVar Fp) (Type2 (SplitField (FVar Fp) (BoolVar Fp))))
    (cells : IvpInput k nc (FVar Fp) (BoolVar Fp) (Type2 (SplitField (FVar Fp) (BoolVar Fp)))) :
    CircuitM Fp c (BoolVar Fp) :=
  verifyProofWith σ.h (cvk.lagrangePoints σ statement.packed.length).toList spongeAfterIndex
    isBaseCase statement u cells

/-- **`verifyProofAt` reads as the group half at the packed statement's public input.** The
table is the key's, so `XhatTable.Bound` needs beyond the key's invariants only that
the Lagrange points and the constant correction sum are finite, since the fold adds the sum
with `addFast`. No invariant of the key gives these; they are relations the SRS avoids
(`havoid`, `stepRelationsAt`). The optional-feature cells the table leaves out are zero
(`stepPublicInput_eq_append`). -/
theorem verifyProofAt_reads {ks nc : ℕ} {V : Valuation Fp} (S : Srs IpaPallas.curve)
    (K : Key IpaPallas.curve nc) (hnc : nc = chunkCount S.σ.k K.cvk.domainLog2)
    (cp : KimchiProof IpaPallas.curve nc S.σ.k)
    (spongeAfterIndex : SpongeVar Fp) (isBaseCase : BoolVar Fp)
    (statement : WrapStatement ks (FVar Fp) (BoolVar Fp) (Type1 (FVar Fp)))
    (u : UnfinalizedProof S.σ.k (FVar Fp) (BoolVar Fp)
      (Type2 (SplitField (FVar Fp) (BoolVar Fp))))
    (cells : IvpInput S.σ.k nc (FVar Fp) (BoolVar Fp) (Type2 (SplitField (FVar Fp) (BoolVar Fp))))
    (oldsW : List (IpaPallas.curve.Point × Bool))
    (hbase : CircuitType.Reads V isBaseCase false)
    (hsmall : statement.packed.length ≤ 2 ^ S.σ.k) (hn : statement.packed.length ≤ K.cvk.n)
    (havoid : S.σ.Avoids (stepRelationsAt S.σ K.cvk statement))
    (hivp : IvpHyps (stepSide V) S.σ K.cvk cp (stepPublicInput V statement) false
      spongeAfterIndex (cells.withClaims u) oldsW) :
    ⦃⌜True⌝⦄
    verifyProofAt (c := Builder V (KimchiConstraint Fp)) S.σ K.cvk spongeAfterIndex isBaseCase
      statement u cells
    ⦃⇓ v _ => ⌜VerifyReads (stepSide V) S.σ K.cvk cp (stepPublicInput V statement) u false
      v⌝⦄ := by
  have hleaves : stepLeavesAt S.σ K.cvk statement
      = List.zipWith (constLeaf (C := IpaPallas.curve)) statement.packed
        (K.cvk.lagrangePoints S.σ statement.packed.length).toList := by
    unfold stepLeavesAt packLeaves xhatTableAt
    exact packLeavesOf_ofKey (C := IpaPallas.curve) _ _
  have hsz : (pubOf IpaPallas.curve V (packLeaves statement (xhatTableAt S.σ K.cvk statement))).size
      = statement.packed.length := by
    rw [← stepLeavesAt, hleaves]
    simp [pubOf]
  have hlb : (K.cvk.lagrangePoints S.σ statement.packed.length).toList ≠ [] := by
    simp [WrapStatement.packed]
  have htab : (xhatTableAt S.σ K.cvk statement).Bound pastaShapePallas V S.σ
      (K.cvk.lagrangePoints S.σ
        (pubOf IpaPallas.curve V (packLeaves statement (xhatTableAt S.σ K.cvk
          statement))).size).toArray
      (constPt S.σ.h) (packLeaves statement (xhatTableAt S.σ K.cvk statement)) := by
    rw [hsz]
    have hb := bound_ofKeyKnown (V := V) pastaShapePallas S.σ
      (K.cvk.lagrangePoints S.σ statement.packed.length).toArray statement.packed S.h_ne
      (fun Ps h ci => Key.lagrange_ne pastaShapePallas S.σ hnc
        (fun a ha => havoid a (List.mem_append_right _ ha)) Ps h ci)
      (by simp [WrapStatement.packed]) hlb
      (bitBoolean_constLeaf_of_isScalar _ _ statement.packed_isScalar)
      (corrSumPt_ne_zero S.σ K hnc statement hsmall hn havoid)
    rw [Vector.toList_toArray, ← hleaves] at hb
    exact hb
  obtain ⟨zs, hz, hpub⟩ := stepPublicInput_eq_append S.σ K.cvk V statement
  rw [hpub] at hivp ⊢
  have hr := verifyProof_step_reads (V := V) S.σ K.cvk cp (.const ((Pasta.vestaLam : ℤ) : Fp))
    pallasBase.sqrt? (constPt S.σ.h) (xhatTableAt S.σ K.cvk statement) spongeAfterIndex isBaseCase
    statement u cells false oldsW hbase htab
    ⟨hivp.idx, hivp.mask, hivp.ties, hivp.nc_pos, hivp.t_ne, hivp.k_pos, hivp.char⟩
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
    (sgOld : List (AffinePoint (FVar Fp)))
    (proof : IvpProof S.σ.k nc (FVar Fp) (Type2 (SplitField (FVar Fp) (BoolVar Fp))))
    (hlen : sgOld.length ≤ 2)
    (hproof : ProofReads (stepSide V) (proof.wComm.toList.map (·.toList)) proof.zComm.toList
      proof.tComm.toList proof.opening cp)
    (holds : CommReads IpaPallas.curve V sgOld (cp.olds.map (·.sg)).toList)
    (hvk : VkReads K.cvk V spongeAfterIndex keyCells)
    (hclaimOk : ∀ x ∈ (ivpInputOf claims.deferredValues (sgOld.map (none, ·)) keyCells
      proof).shifted, (stepSide V).ClaimOk x) :
    ∃ oldsW, IvpHyps (stepSide V) S.σ K.cvk cp pub false spongeAfterIndex
      ((ivpInputOf claims.deferredValues (sgOld.map (none, ·)) keyCells proof).withClaims claims)
      oldsW := by
  refine ⟨(cp.olds.map (·.sg)).toList.map (·, true),
    { idx := hvk.idx, mask := ?mask
      ties :=
        { olds := ⟨?olds, ?kept⟩, proof := hproof
          key := hvk.key
          claimOk := hclaimOk }
      nc_pos := K.cvk.nc_pos, t_ne := ?tne, k_pos := S.rounds_pos, char := ?char }⟩
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
    exact absurd hlen (Nat.pos_iff_ne_zero.mp K.cvk.nc_pos)
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
    have h5 := nc_le S.σ K hnc
    omega

/-- Under any valuation satisfying the emitted constraints, `verifyProofWith`'s returned bit
reads as a bit (`verifyProof_success_bit`). -/
theorem verifyProofWith_success_bit {ks k nc : ℕ} {V : Valuation Fp} (h : IpaPallas.curve.Point)
    (lagrange : List (Vector IpaPallas.curve.Point nc)) (spongeAfterIndex : SpongeVar Fp)
    (isBaseCase : BoolVar Fp)
    (statement : WrapStatement ks (FVar Fp) (BoolVar Fp) (Type1 (FVar Fp)))
    (u : UnfinalizedProof k (FVar Fp) (BoolVar Fp) (Type2 (SplitField (FVar Fp) (BoolVar Fp))))
    (cells : IvpInput k nc (FVar Fp) (BoolVar Fp) (Type2 (SplitField (FVar Fp) (BoolVar Fp)))) :
    ⦃⌜True⌝⦄
    verifyProofWith (c := Builder V (KimchiConstraint Fp)) h lagrange spongeAfterIndex
      isBaseCase statement u cells
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

/-- `verifyProofWith` as a circuit of its input, its success bit asserted, at the blinding base
`h` and the Lagrange points `lagrange`: what a driver runs at points it computed once. Before
it, the shifted scalars' parity cells are asserted boolean (`assertClaimBitsStep`), the
allocation check the deployed circuit's split type makes and this harness's unchecked input
lacks. -/
def groupCircuitWith {c : Type} [BasicSystem Fp c] [ConstraintHolds Fp c] [LawfulBasicSystem Fp c]
    [KimchiSystem Fp c]
    (h : IpaPallas.curve.Point) (lagrange : List (Vector IpaPallas.curve.Point nc))
    (keyCells : VkComms nc (AffinePoint (FVar Fp))) (spongeAfterIndex : SpongeVar Fp)
    (g : GroupVar ks k nc) : CircuitM Fp c Unit := do
  assertClaimBitsStep g.shifted
  let v ← verifyProofWith h lagrange spongeAfterIndex g.isBaseCase g.statement g.claims
    (g.cells keyCells)
  assert v

/-- `groupCircuitWith` at the SRS blinding base and the key's Lagrange points, one per packed
scalar: `verifyProofAt` as a circuit of its input. -/
def groupCircuit {c : Type} [BasicSystem Fp c] [ConstraintHolds Fp c] [LawfulBasicSystem Fp c]
    [KimchiSystem Fp c]
    (σ : SRS IpaPallas.curve.Point) (cvk : KimchiVK IpaPallas.curve nc)
    (keyCells : VkComms nc (AffinePoint (FVar Fp))) (spongeAfterIndex : SpongeVar Fp)
    (g : GroupVar ks k nc) : CircuitM Fp c Unit :=
  groupCircuitWith σ.h (cvk.lagrangePoints σ g.statement.packed.length).toList keyCells
    spongeAfterIndex g

/-- **The group circuit's read**: the group half's read at a bit that reads `1`. -/
theorem groupCircuit_reads {V : Valuation Fp} (S : Srs IpaPallas.curve)
    (K : Key IpaPallas.curve nc) (hnc : nc = chunkCount S.σ.k K.cvk.domainLog2)
    (cp : KimchiProof IpaPallas.curve nc S.σ.k)
    (keyCells : VkComms nc (AffinePoint (FVar Fp))) (spongeAfterIndex : SpongeVar Fp)
    (g : GroupVar ks S.σ.k nc)
    (hbase : CircuitType.Reads V g.isBaseCase false)
    (hsmall : g.statement.packed.length ≤ 2 ^ S.σ.k) (hn : g.statement.packed.length ≤ K.cvk.n)
    (havoid : S.σ.Avoids (stepRelationsAt S.σ K.cvk g.statement))
    (hivp : (∀ x ∈ g.shifted, (stepSide V).ClaimOk x) →
      ∃ oldsW, IvpHyps (stepSide V) S.σ K.cvk cp (stepPublicInput V g.statement) false
        spongeAfterIndex ((g.cells keyCells).withClaims g.claims) oldsW) :
    ⦃⌜True⌝⦄
    groupCircuit (c := Builder V (KimchiConstraint Fp)) S.σ K.cvk keyCells spongeAfterIndex g
    ⦃⇓ _ _ => ⌜∃ v : BoolVar Fp,
      (g.half V).Reads S.σ K.cvk cp (stepPublicInput V g.statement) v ∧
        (↑v : CVar Fp).val V = 1⌝⦄ := by
  simp only [groupCircuit, groupCircuitWith]
  refine builder_spec_bind_of _ _ _ _ (assertClaimBitsStep_spec (V := V) g.shifted)
    fun hclaimOk _ => ?_
  obtain ⟨oldsW, hivp⟩ := hivp hclaimOk
  have hv := verifyProofAt_reads (V := V) S K hnc cp spongeAfterIndex g.isBaseCase g.statement
    g.claims (g.cells keyCells) oldsW hbase hsmall hn havoid hivp
  unfold verifyProofAt at hv
  mvcgen -trivial [hv]
  rename_i v _ hr _ _
  intro h1
  exact ⟨v, hr, h1⟩

end WrapProof

/-! The gadget is sealed after its read: a consumer composes `verifyProofAt_reads`, never the
body. -/
attribute [irreducible] verifyProofAt

end Pickles
