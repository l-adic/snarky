import Snarky.Kimchi.Circuit.AddComplete
import Pickles.FrSponge
import Pickles.ListLemmas
import Pickles.OptSponge
import Pickles.Statement
import Pickles.VkComms
import Poseidon.RandomOracle

set_option mvcgen.warning false

/-!
# The accumulator digests

Transcribed from `Pickles/Wrap/MessageHash.purs` and `Pickles/Step/MessageHash.purs`. A digest
binds a proof's accumulator advice — the opening's `sg` and the expanded round challenges — to
the statement the next proof verifies. The wrap digest's starting sponge is the caller's:
`wrapVerify` starts it from a checkpoint that has already absorbed the dummy padding, keeping
those absorptions out of the circuit. The step digest starts fresh and absorbs the key
(`spongeAfterIndex`) and the application state: the outer digest then absorbs each proof's
advice on the plain sponge, the per-slot one keeps it under the proof's mask.

## Main results

* `hashMessagesForNextWrapProof_padded`: from the padding sponge (`wrapPaddingSponge`), the wrap
  digest is the wire's messages-for-next-wrap-proof digest of the accumulator (`wrapMsgDigest`);
* `spongeAfterIndex_spec`: the sponge after the key reads as the key's coordinates absorbed;
* `hashMessagesForNextStepProofOpt_spec`: the per-slot digest reads as the plain sponge's
  squeeze after the key, the application state and the kept proofs' advice.
-/

namespace Pickles

open Snarky Snarky.Kimchi

variable {F c : Type} [Field F] [DecidableEq F] [BasicSystem F c] [KimchiSystem F c]

/-- The digest of the message `m` from the sponge `sv`: every challenge vector absorbed in order,
then the commitment's `x` and `y`, then one squeeze. -/
def hashMessagesForNextWrapProof [ConstraintHolds F c] {w k : ℕ} (p : Poseidon.Params F)
    (sv : SpongeVar F)
    (m : MessagesForNextWrapProof (AffinePoint (FVar F)) (Vector (Vector (FVar F) k) w)) :
    CircuitM F c (FVar F) := do
  let sv ← absorbList p sv m.oldBulletproofChallenges.flatten.toList
  let sv ← SpongeVar.absorb p sv m.challengePolynomialCommitment.x
  let sv ← SpongeVar.absorb p sv m.challengePolynomialCommitment.y
  let (digest, _) ← SpongeVar.squeeze p sv
  pure digest

/-- The sponge state after absorbing `pad` copies of the dummy challenge vector `dummy`. -/
def wrapPaddingState {k : ℕ} (p : Poseidon.Params F) (dummy : Vector F k) (pad : ℕ) :
    Poseidon.State F :=
  Poseidon.absorb p Poseidon.init (List.replicate pad dummy.toList).flatten

/-- `wrapPaddingState` as constant cells: a slot with `pad` padding entries starts its
accumulator digest here, so the padding emits no rows. -/
def wrapPaddingSponge {k : ℕ} (p : Poseidon.Params F) (dummy : Vector F k) (pad : ℕ) :
    SpongeVar F :=
  SpongeVar.ofConstants (wrapPaddingState p dummy pad)

/-- What the wrap digest of the message `m` absorbs: its old bulletproof challenges,
front-padded with `dummy` to `MaxProofsVerified`, then its commitment. -/
def wrapMsgInput {w k : ℕ} (dummy : Vector F k)
    (m : MessagesForNextWrapProof (AffinePoint F) (Vector (Vector F k) w)) : List F :=
  (List.replicate (MaxProofsVerified - w) dummy.toList).flatten
    ++ m.oldBulletproofChallenges.flatten.toList
    ++ [m.challengePolynomialCommitment.x, m.challengePolynomialCommitment.y]

/-- The wire's messages-for-next-wrap-proof digest of the message `m`: `wrapMsgInput` absorbed
from the fresh sponge and squeezed. -/
def wrapMsgDigest {w k : ℕ} (p : Poseidon.Params F) (dummy : Vector F k)
    (m : MessagesForNextWrapProof (AffinePoint F) (Vector (Vector F k) w)) : F :=
  (Poseidon.squeeze p (Poseidon.absorb p Poseidon.init (wrapMsgInput dummy m))).1

/-- The sponge after the key: its commitments absorbed chunk by chunk, `x` then `y`, in the
order `σ₀…σ₆`, the coefficients, the selectors. -/
def spongeAfterIndex [ConstraintHolds F c] {nc : ℕ} (p : Poseidon.Params F)
    (vk : VkComms nc (AffinePoint (FVar F))) : CircuitM F c (SpongeVar F) :=
  vk.indexPoints.foldlM
    (fun sv P => do
      let sv ← SpongeVar.absorb p sv P.x
      SpongeVar.absorb p sv P.y)
    SpongeVar.init

/-- The digest of the step message `m` on the plain sponge: after its key, its application
state, then per proof `sg` and its challenges, then one squeeze. -/
def hashMessagesForNextStepProof [ConstraintHolds F c] {nc s n k : ℕ} (p : Poseidon.Params F)
    (m : MessagesForNextStepProof (VkComms nc (AffinePoint (FVar F))) (Vector (FVar F) s)
      (Vector (AffinePoint (FVar F)) n) (Vector (Vector (FVar F) k) n)) :
    CircuitM F c (FVar F) := do
  let sv ← spongeAfterIndex p m.dlogPlonkIndex
  let sv ← m.appState.toList.foldlM (SpongeVar.absorb p) sv
  let sv ← (m.proofs.toList.flatMap fun (sg, chals) => sg.x :: sg.y :: chals.toList).foldlM
    (SpongeVar.absorb p) sv
  let (digest, _) ← SpongeVar.squeeze p sv
  pure digest

/-- What the step digest of the message `m` absorbs: its key's coordinates, its application
state, then per proof `sg` and its challenges. -/
def stepMsgInput {nc s n k : ℕ}
    (m : MessagesForNextStepProof (VkComms nc (AffinePoint F)) (Vector F s)
      (Vector (AffinePoint F) n) (Vector (Vector F k) n)) : List F :=
  m.dlogPlonkIndex.indexPoints.flatMap (fun P => [P.x, P.y]) ++ m.appState.toList ++
    m.proofs.toList.flatMap fun (sg, chals) => sg.x :: sg.y :: chals.toList

/-- The wire's messages-for-next-step-proof digest of the message `m`: `stepMsgInput` absorbed
from the fresh sponge and squeezed. -/
def stepMsgDigest {nc s n k : ℕ} (p : Poseidon.Params F)
    (m : MessagesForNextStepProof (VkComms nc (AffinePoint F)) (Vector F s)
      (Vector (AffinePoint F) n) (Vector (Vector F k) n)) : F :=
  (Poseidon.squeeze p (Poseidon.absorb p Poseidon.init (stepMsgInput m))).1

/-- The inputs `xs` and `ys` absorb different blocks (`Poseidon.RandomOracle.toBlocks`), but have
one Poseidon digest. Distinct inputs can share their blocks: the hash pads an odd tail with `0`,
so `xs` and `xs ++ [0]` hash alike without a collision. -/
def Collision (p : Poseidon.Params F) (xs ys : List F) : Prop :=
  Poseidon.RandomOracle.toBlocks xs ≠ Poseidon.RandomOracle.toBlocks ys ∧
    Poseidon.RandomOracle.hash p xs = Poseidon.RandomOracle.hash p ys

omit [DecidableEq F] in
/-- Distinct inputs of one length that hash alike collide. -/
theorem Collision.of_length_eq {p : Poseidon.Params F} {xs ys : List F}
    (hl : xs.length = ys.length) (hne : xs ≠ ys)
    (hh : Poseidon.RandomOracle.hash p xs = Poseidon.RandomOracle.hash p ys) :
    Collision p xs ys :=
  ⟨fun h => hne (Poseidon.RandomOracle.eq_of_toBlocks_eq hl h), hh⟩

omit [DecidableEq F] in
/-- Nonempty inputs whose lengths are two or more apart and that hash alike collide. -/
theorem Collision.of_length_apart {p : Poseidon.Params F} {xs ys : List F} (hx : xs ≠ [])
    (hy : ys ≠ []) (hl : xs.length + 2 ≤ ys.length ∨ ys.length + 2 ≤ xs.length)
    (hh : Poseidon.RandomOracle.hash p xs = Poseidon.RandomOracle.hash p ys) :
    Collision p xs ys :=
  ⟨Poseidon.RandomOracle.toBlocks_ne_of_length hx hy hl, hh⟩

/-- The digest of the step message `m` with each proof's advice kept under its bit of `mask`, and
the sponge after the key, which the verify block resumes from: after the key and the application
state, per proof `sg` and its challenges on the conditional sponge. With no proofs there is no
masked input, and the plain sponge squeezes. -/
def hashMessagesForNextStepProofOpt [ConstraintHolds F c] {nc s n k : ℕ}
    (p : Poseidon.Params F) (mask : Vector (BoolVar F) n)
    (m : MessagesForNextStepProof (VkComms nc (AffinePoint (FVar F))) (Vector (FVar F) s)
      (Vector (AffinePoint (FVar F)) n) (Vector (Vector (FVar F) k) n)) :
    CircuitM F c (FVar F × SpongeVar F) := do
  let afterIndex ← spongeAfterIndex p m.dlogPlonkIndex
  let sv ← m.appState.toList.foldlM (SpongeVar.absorb p) afterIndex
  match (mask.zip m.proofs).toList with
  | [] => do
    let (digest, _) ← SpongeVar.squeeze p sv
    pure (digest, afterIndex)
  | proofs => do
    let ov ← OptSponge.ofSponge p sv
    let ov := proofs.foldl (fun ov (b, sg, chals) =>
      (sg.x :: sg.y :: chals.toList).foldl (fun ov x => OptSponge.optAbsorb ov (b, x)) ov) ov
    let (digest, _) ← OptSponge.optSqueeze p ov
    pure (digest, afterIndex)

/-! ## Reading the digests -/

section Reads

open Std.Do

variable {V : Valuation F}

/-- Under any valuation satisfying the emitted constraints, from a sponge reading as `s`, the
wrap digest of `m` reads as the squeeze after absorbing its challenges' readings, then its
commitment's. -/
theorem hashMessagesForNextWrapProof_spec {w k : ℕ} (p : Poseidon.Params F)
    (hsize : p.roundConstants.size = Poseidon.fullRounds) (sv : SpongeVar F)
    (m : MessagesForNextWrapProof (AffinePoint (FVar F)) (Vector (Vector (FVar F) k) w)) :
    ⦃⌜True⌝⦄ hashMessagesForNextWrapProof (c := Builder V (KimchiConstraint F)) p sv m
    ⦃⇓ d _ => ⌜∀ s, SpongeVar.ReadsAt V sv s → d.val V = (Poseidon.squeeze p (Poseidon.absorb p s
      (m.oldBulletproofChallenges.flatten.toList.map (·.val V) ++
        [m.challengePolynomialCommitment.x.val V,
          m.challengePolynomialCommitment.y.val V]))).1⌝⦄ := by
  have hl := fun sv => absorbList_spec (V := V) p hsize sv
    m.oldBulletproofChallenges.flatten.toList
  have hx := fun sv x => SpongeVar.absorb_spec (V := V) p hsize sv x
  have hsq := fun sv => SpongeVar.squeeze_spec (V := V) p hsize sv
  simp only [hashMessagesForNextWrapProof]
  mvcgen [hl, hx, hsq]
  rename_i _ _ hl' _ _ hx1 _ _ hy1 _ _ hsq'
  intro s hs
  rw [(hsq' _ (hy1 _ (hx1 _ (hl' s hs)))).1]
  simp [Poseidon.absorb, List.foldl_append]

/-- **The padded wrap digest.** From the padding sponge for the stacks it is given, the digest
of the message of cells reading as an accumulator `sg` and its challenges `chals` is the wire's
messages-for-next-wrap-proof digest of the message they read as (`wrapMsgDigest`). -/
theorem hashMessagesForNextWrapProof_padded {w k : ℕ} (p : Poseidon.Params F)
    (hsize : p.roundConstants.size = Poseidon.fullRounds) (dummy : Vector F k)
    (chals : Vector (Vector (FVar F) k) w) (sg : AffinePoint (FVar F)) :
    ⦃⌜True⌝⦄ hashMessagesForNextWrapProof (c := Builder V (KimchiConstraint F)) p
      (wrapPaddingSponge p dummy (MaxProofsVerified - w)) ⟨sg, chals⟩
    ⦃⇓ d _ => ⌜∀ (sgv : AffinePoint F) (cv : Vector (Vector F k) w), CircuitType.Reads V sg sgv →
      CircuitType.Reads V chals cv → d.val V = wrapMsgDigest p dummy ⟨sgv, cv⟩⌝⦄ := by
  refine builder_spec_imp _ _ _
    (hashMessagesForNextWrapProof_spec p hsize _ ⟨sg, chals⟩) fun d hd => ?_
  intro sgv cv hsg hcv
  rw [hd _ (SpongeVar.ReadsAt.ofConstants _)]
  obtain ⟨hx, hy⟩ := reads_affinePoint.mp hsg
  -- the challenge cells read as the challenges
  have hvals : ∀ {cs : List (Vector (FVar F) k)} {vs : List (Vector F k)},
      List.Forall₂ (CircuitType.Reads V) cs vs →
      (cs.map Vector.toList).flatten.map (·.val V) = (vs.map Vector.toList).flatten := by
    intro cs vs h
    induction h with
    | nil => rfl
    | cons hr _ ih =>
      simp only [List.map_cons, List.flatten_cons, List.map_append, ih]
      congr 1
      apply List.ext_getElem (by simp)
      intro i h1 h2
      have := (CircuitType.reads_vector.mp hr) i (by simpa using h2)
      simpa [CircuitType.reads_fvar] using this
  have hcv' := CircuitType.reads_vector_iff_forall₂.mp hcv
  simp only [wrapMsgDigest, wrapMsgInput, wrapPaddingState, Poseidon.absorb, List.foldl_append,
    toList_flatten', hvals hcv', hx, hy]

/-- Under any valuation satisfying the emitted constraints, the sponge after the key reads as
the fresh value sponge after absorbing the key's coordinates in order. -/
theorem spongeAfterIndex_spec {nc : ℕ} (p : Poseidon.Params F)
    (hsize : p.roundConstants.size = Poseidon.fullRounds)
    (vk : VkComms nc (AffinePoint (FVar F))) :
    ⦃⌜True⌝⦄ spongeAfterIndex (c := Builder V (KimchiConstraint F)) p vk
    ⦃⇓ r _ => ⌜SpongeVar.ReadsAt V r (Poseidon.absorb p Poseidon.init
      (vk.indexPoints.flatMap fun P => [P.x.val V, P.y.val V]))⌝⦄ := by
  simp only [spongeAfterIndex]
  have hx := fun sv x => SpongeVar.absorb_spec (V := V) p hsize sv x
  mvcgen [hx] invariants
    · ⇓⟨xs, sv⟩ => ⌜SpongeVar.ReadsAt V sv (Poseidon.absorb p Poseidon.init
        (xs.prefix.flatMap fun P => [P.x.val V, P.y.val V]))⌝
  · exact fun h => h
  · rename_i _ _ _ _ _ _ _ hinv _ _ h1 _
    intro _ h2
    simpa [List.flatMap_append, Poseidon.absorb, List.foldl_append] using h2 _ (h1 _ hinv)
  · intro _ _
    exact hsize

omit [DecidableEq F] in
/-- Point cells reading entrywise as points have their coordinates. -/
private theorem coords_of_forall₂ {ps : List (AffinePoint (FVar F))} {qs : List (AffinePoint F)}
    (h : List.Forall₂ (CircuitType.Reads V) ps qs) :
    ps.flatMap (fun P => [P.x.val V, P.y.val V]) = qs.flatMap fun P => [P.x, P.y] := by
  induction h with
  | nil => rfl
  | cons hr _ ih =>
    obtain ⟨hx, hy⟩ := reads_affinePoint.mp hr
    simp only [List.flatMap_cons, hx, hy, ih]

omit [DecidableEq F] in
/-- Key cells reading as the key `v` have its coordinates, in absorb order. -/
theorem VkComms.indexCoords_of_reads {nc : ℕ} {key : VkComms nc (AffinePoint (FVar F))}
    {v : VkComms nc (AffinePoint F)} (h : CircuitType.Reads V key v) :
    key.indexPoints.flatMap (fun P => [P.x.val V, P.y.val V])
      = v.indexPoints.flatMap fun P => [P.x, P.y] := by
  rw [CircuitType.reads_ofEquiv] at h
  simp only [VkComms.equivProd, Equiv.coe_fn_mk, CircuitType.reads_prod] at h
  obtain ⟨hs, hc, hg, hp, hca, hm, he, hes⟩ := h
  have hsel : List.Forall₂ (CircuitType.Reads V) key.selectors.toList v.selectors.toList :=
    .cons hg (.cons hp (.cons hca (.cons hm (.cons he (.cons hes .nil)))))
  have hcols : List.Forall₂ (CircuitType.Reads V)
      (key.sigmaComm.toList ++ key.coefficientsComm.toList ++ key.selectors.toList)
      (v.sigmaComm.toList ++ v.coefficientsComm.toList ++ v.selectors.toList) :=
    List.rel_append (List.rel_append (CircuitType.reads_vector_iff_forall₂.mp hs)
      (CircuitType.reads_vector_iff_forall₂.mp hc)) hsel
  simp only [VkComms.indexPoints]
  generalize key.sigmaComm.toList ++ key.coefficientsComm.toList ++ key.selectors.toList = cs
    at hcols ⊢
  generalize v.sigmaComm.toList ++ v.coefficientsComm.toList ++ v.selectors.toList = ds
    at hcols ⊢
  induction hcols with
  | nil => rfl
  | cons hr _ ih =>
    simp only [List.flatMap_cons, List.flatMap_append, ih,
      coords_of_forall₂ (CircuitType.reads_vector_iff_forall₂.mp hr)]

/-- Under any valuation satisfying the emitted constraints, the step digest of `m` reads as the
wire's (`stepMsgDigest`) at its cells' readings. -/
theorem hashMessagesForNextStepProof_spec {nc s n k : ℕ} (p : Poseidon.Params F)
    (hsize : p.roundConstants.size = Poseidon.fullRounds)
    (m : MessagesForNextStepProof (VkComms nc (AffinePoint (FVar F))) (Vector (FVar F) s)
      (Vector (AffinePoint (FVar F)) n) (Vector (Vector (FVar F) k) n)) :
    ⦃⌜True⌝⦄ hashMessagesForNextStepProof (c := Builder V (KimchiConstraint F)) p m
    ⦃⇓ d _ => ⌜∀ (vk : VkComms nc (AffinePoint F)) (sgs : Vector (AffinePoint F) n)
        (chals : Vector (Vector F k) n),
      CircuitType.Reads V m.dlogPlonkIndex vk →
      CircuitType.Reads V m.challengePolynomialCommitments sgs →
      CircuitType.Reads V m.oldBulletproofChallenges chals →
      d.val V = stepMsgDigest p ⟨m.appState.map (·.val V), vk, sgs, chals⟩⌝⦄ := by
  have hidx := spongeAfterIndex_spec (V := V) p hsize m.dlogPlonkIndex
  have hx := fun sv x => SpongeVar.absorb_spec (V := V) p hsize sv x
  have hsq := fun sv => SpongeVar.squeeze_spec (V := V) p hsize sv
  simp only [hashMessagesForNextStepProof]
  mvcgen [hidx, hx, hsq] invariants
    · ⇓⟨xs, sv⟩ => ⌜SpongeVar.ReadsAt V sv (Poseidon.absorb p Poseidon.init
        (m.dlogPlonkIndex.indexPoints.flatMap (fun P => [P.x.val V, P.y.val V]) ++
          xs.prefix.map (·.val V)))⌝
    · ⇓⟨xs, sv⟩ => ⌜SpongeVar.ReadsAt V sv (Poseidon.absorb p Poseidon.init
        (m.dlogPlonkIndex.indexPoints.flatMap (fun P => [P.x.val V, P.y.val V]) ++
          m.appState.toList.map (·.val V) ++ xs.prefix.map (·.val V)))⌝
  -- the absorb loops and their starts
  all_goals first
    | (rename_i hinv _
       intro _ h
       simpa [Poseidon.absorb, List.foldl_append] using h _ hinv)
    | (rename_i h
       simpa using h)
    | exact fun _ _ => hsize
    | skip
  -- the squeeze, at the message's readings
  rename_i hafter _ _ hsq'
  intro vk sgs chals hk hs hc
  have hsgs : sgs = m.challengePolynomialCommitments.map fun P => ⟨P.x.val V, P.y.val V⟩ := by
    refine Vector.ext fun i hi => ?_
    obtain ⟨hx, hy⟩ := reads_affinePoint.mp (CircuitType.reads_vector.mp hs i hi)
    rw [Vector.getElem_map, hx, hy]
  have hchals : chals = m.oldBulletproofChallenges.map (·.map (·.val V)) := by
    refine Vector.ext fun i hi => Vector.ext fun j hj => ?_
    rw [Vector.getElem_map, Vector.getElem_map, ← CircuitType.reads_fvar.mp
      (CircuitType.reads_vector.mp (CircuitType.reads_vector.mp hc i hi) j hj)]
  subst hsgs hchals
  rw [(hsq' _ hafter).1, stepMsgDigest, stepMsgInput, VkComms.indexCoords_of_reads hk]
  simp [MessagesForNextStepProof.proofs, Vector.toList_zip, Vector.toList_map, List.zip_map,
    List.flatMap_map, List.map_flatMap]

/-- Guarded absorbs append their readings to the pending ones. -/
private theorem foldl_optAbsorb_reads {p : Poseidon.Params F} {ib nf : Bool}
    {ps₀ : Poseidon.State F} :
    ∀ (es : List (BoolVar F × FVar F)) (vs : List (Bool × F)),
      List.Forall₂ (CircuitType.Reads V) es vs →
      ∀ (ov : OptSponge.OptSpongeVar F) (pend : List (Bool × F)),
        OptSponge.AbsorbingReads p V ov ib ps₀ pend nf →
        OptSponge.AbsorbingReads p V (es.foldl OptSponge.optAbsorb ov) ib ps₀ (pend ++ vs) nf
  | [], [], .nil, _, _, h => by simpa using h
  | _ :: es, _ :: vs, .cons he hes, ov, pend, h => by
    simpa using foldl_optAbsorb_reads es vs hes _ _ (OptSponge.optAbsorb_reads_absorbing h he)

/-- The step digest's guarded inputs: each proof's `sg` and challenges under its mask. -/
private def guarded {k : ℕ}
    (proofs : List (BoolVar F × AffinePoint (FVar F) × Vector (FVar F) k)) :
    List (BoolVar F × FVar F) :=
  proofs.flatMap fun (b, sg, chals) => (sg.x :: sg.y :: chals.toList).map (b, ·)

/-- The kept values: each proof's `sg` and challenges where its mask reads `true`. -/
def keptValues {n k : ℕ} (V : Valuation F) (ms : Vector Bool n)
    (proofs : Vector (AffinePoint (FVar F) × Vector (FVar F) k) n) : List F :=
  (Vector.zipWith (fun b (q : AffinePoint (FVar F) × Vector (FVar F) k) =>
    if b then (q.1.x :: q.1.y :: q.2.toList).map (·.val V) else []) ms proofs).toList.flatten

omit [DecidableEq F] in
/-- The nested per-proof absorbs are one fold over the guarded inputs. -/
private theorem foldl_guarded {k : ℕ} (ov : OptSponge.OptSpongeVar F) :
    ∀ proofs : List (BoolVar F × AffinePoint (FVar F) × Vector (FVar F) k),
      proofs.foldl (fun ov q => (q.2.1.x :: q.2.1.y :: q.2.2.toList).foldl
          (fun ov x => OptSponge.optAbsorb ov (q.1, x)) ov) ov
        = (guarded proofs).foldl OptSponge.optAbsorb ov := by
  intro proofs
  induction proofs generalizing ov with
  | nil => rfl
  | cons q qs ih =>
    obtain ⟨b, sg, chals⟩ := q
    simp only [List.foldl_cons, guarded, List.flatMap_cons, List.foldl_append, List.foldl_map]
    exact ih _

/-- The guarded inputs' readings: each value under its proof's mask. -/
private def guardedVals {k : ℕ} (V : Valuation F) (ms : List Bool)
    (proofs : List (BoolVar F × AffinePoint (FVar F) × Vector (FVar F) k)) : List (Bool × F) :=
  (List.zipWith (fun m (q : BoolVar F × AffinePoint (FVar F) × Vector (FVar F) k) =>
    (q.2.1.x :: q.2.1.y :: q.2.2.toList).map fun x => (m, x.val V)) ms proofs).flatten

omit [BasicSystem F c] [KimchiSystem F c] in
private theorem guarded_reads {k : ℕ} :
    ∀ (proofs : List (BoolVar F × AffinePoint (FVar F) × Vector (FVar F) k)) (ms : List Bool),
      List.Forall₂ (fun q m => CircuitType.Reads V q.1 m) proofs ms →
      List.Forall₂ (CircuitType.Reads V) (guarded proofs) (guardedVals V ms proofs)
  | [], [], .nil => .nil
  | q :: qs, m :: ms, .cons hq hqs => by
    simp only [guarded, guardedVals, List.flatMap_cons, List.zipWith_cons_cons,
      List.flatten_cons] at *
    refine List.rel_append ?_ (guarded_reads qs ms hqs)
    simp only [List.map_cons]
    refine .cons ?_ (.cons ?_ ?_)
    · exact CircuitType.reads_prod.mpr ⟨hq, by simp⟩
    · exact CircuitType.reads_prod.mpr ⟨hq, by simp⟩
    · simp only [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
      exact List.forall₂_same.mpr fun x _ =>
        CircuitType.reads_prod.mpr ⟨hq, by simp⟩

omit [DecidableEq F] [BasicSystem F c] [KimchiSystem F c] in
private theorem guardedVals_kept {k : ℕ} :
    ∀ (ms : List Bool) (masks : List (BoolVar F))
      (proofs : List (AffinePoint (FVar F) × Vector (FVar F) k)), masks.length = proofs.length →
      ((guardedVals V ms (masks.zip proofs)).filter (·.1)).map (·.2)
        = (List.zipWith (fun b (q : AffinePoint (FVar F) × Vector (FVar F) k) =>
          if b then (q.1.x :: q.1.y :: q.2.toList).map (·.val V) else []) ms proofs).flatten
  | [], _, _, _ => by simp [guardedVals]
  | _ :: _, [], [], _ => by simp [guardedVals]
  | _ :: _, [], _ :: _, h => by simp at h
  | _ :: _, _ :: _, [], h => by simp at h
  | m :: ms, _ :: masks, q :: qs, h => by
    have ih := guardedVals_kept ms masks qs (by simpa using h)
    simp only [guardedVals, List.zip_cons_cons, List.zipWith_cons_cons, List.flatten_cons,
      List.filter_append, List.map_append] at ih ⊢
    rw [ih]
    cases m <;> simp [List.filter_map, Function.comp_def]

/-- A relation on a list's entries carries to its zip with an equally long list. -/
private theorem forall₂_zip_fst {α β γ : Type} {R : α → γ → Prop} :
    ∀ (as : List α) (bs : List β) (cs : List γ), List.Forall₂ R as cs →
      bs.length = as.length → List.Forall₂ (fun q c => R q.1 c) (as.zip bs) cs
  | [], _, [], .nil, _ => by simp
  | a :: as, b :: bs, c :: cs, .cons h hs, hl => by
    simp only [List.zip_cons_cons]
    exact .cons h (forall₂_zip_fst as bs cs hs (by simpa using hl))
  | _ :: _, [], _, _, hl => by simp at hl

/-- Under any valuation satisfying the emitted constraints, with the mask reading as `ms`, the
digest reads as the first squeeze of the value sponge after the key's coordinates, the
application state, and the kept proofs' `sg` and challenges, and the returned sponge reads as
the one after the key. -/
theorem hashMessagesForNextStepProofOpt_spec {nc s n k : ℕ} (p : Poseidon.Params F)
    (hsize : p.roundConstants.size = Poseidon.fullRounds)
    (hall : ∀ j k : ℕ, j ≤ 3 → k ≤ 3 → (j : F) = k → j = k)
    (mask : Vector (BoolVar F) n)
    (m : MessagesForNextStepProof (VkComms nc (AffinePoint (FVar F))) (Vector (FVar F) s)
      (Vector (AffinePoint (FVar F)) n) (Vector (Vector (FVar F) k) n)) (ms : Vector Bool n)
    (hms : CircuitType.Reads V mask ms)
    (hchar : ∀ j : ℕ, j ≤ n * (k + 2) → (j : F) = 0 → j = 0) :
    ⦃⌜True⌝⦄ hashMessagesForNextStepProofOpt (c := Builder V (KimchiConstraint F)) p mask m
    ⦃⇓ r _ => ⌜SpongeVar.ReadsAt V r.2 (Poseidon.absorb p Poseidon.init
        (m.dlogPlonkIndex.indexPoints.flatMap fun P => [P.x.val V, P.y.val V])) ∧
      r.1.val V = (Poseidon.squeeze p (Poseidon.absorb p Poseidon.init
        (m.dlogPlonkIndex.indexPoints.flatMap (fun P => [P.x.val V, P.y.val V]) ++
          m.appState.toList.map (·.val V) ++ keptValues V ms m.proofs))).1⌝⦄ := by
  obtain ⟨appState, vk, cpcs, obc⟩ := m
  dsimp only [MessagesForNextStepProof.proofs]
  -- the kept values, the mask readings and the absorb count, over the zipped proofs
  have hkept : keptValues V ms (cpcs.zip obc) = ((guardedVals V ms.toList
      (mask.zip (cpcs.zip obc)).toList).filter (·.1)).map (·.2) := by
    rw [Vector.toList_zip, guardedVals_kept _ _ _ (by simp)]
    simp [keptValues]
  have hms' : List.Forall₂ (fun q b => CircuitType.Reads V q.1 b)
      (mask.zip (cpcs.zip obc)).toList ms.toList := by
    rw [Vector.toList_zip]
    exact forall₂_zip_fst _ _ _ (CircuitType.reads_vector_iff_forall₂.mp hms) (by simp)
  have hchar' : ∀ j : ℕ, j ≤ (guarded (mask.zip (cpcs.zip obc)).toList).length →
      (j : F) = 0 → j = 0 := fun j hj => hchar j (hj.trans_eq (by simp [guarded]))
  rw [hkept]
  clear hkept hms hchar
  have hidx := spongeAfterIndex_spec (V := V) p hsize vk
  have hx := fun sv x => SpongeVar.absorb_spec (V := V) p hsize sv x
  have hsq := fun sv => SpongeVar.squeeze_spec (V := V) p hsize sv
  have hof := fun sv => OptSponge.ofSponge_spec (V := V) p hsize sv
  have hosq : ∀ ov : OptSponge.OptSpongeVar F,
      ⦃⌜True⌝⦄ OptSponge.optSqueeze (c := Builder V (KimchiConstraint F)) p ov
      ⦃⇓ r _ => ⌜∀ ib ps₀ pend nf, OptSponge.AbsorbingReads p V ov ib ps₀ pend nf →
        ((∃ v ∈ pend, v.1 = true) ∨ ((∀ n, ps₀.mode ≠ .squeezed n) ∧
          (ib = false → (nf = true ↔ ps₀.mode = .absorbed 0)))) →
        (∀ k : ℕ, k ≤ pend.length → (k : F) = 0 → k = 0) →
        r.1.val V
          = (Poseidon.squeeze p (Poseidon.absorb p ps₀ ((pend.filter (·.1)).map (·.2)))).1⌝⦄ :=
    fun ov => by
      rw [builder_spec_iff]
      intro nv hsat ib ps₀ pend nf h hne hc
      exact ((builder_spec_iff _ _).mp
        (OptSponge.optSqueeze_absorbing_spec p hsize hall ov ib ps₀ pend nf h hne hc) nv hsat).1
  simp only [hashMessagesForNextStepProofOpt, MessagesForNextStepProof.proofs]
  generalize (mask.zip (cpcs.zip obc)).toList = proofs at hms' hchar' ⊢
  cases proofs with
  | nil =>
    simp only
    mvcgen [hidx, hx, hsq] invariants
      · ⇓⟨xs, sv⟩ => ⌜SpongeVar.ReadsAt V sv (Poseidon.absorb p Poseidon.init
          (vk.indexPoints.flatMap (fun P => [P.x.val V, P.y.val V]) ++
            xs.prefix.map (·.val V)))⌝
    · rename_i hinv _
      intro _ h
      simpa [Poseidon.absorb, List.foldl_append] using h _ hinv
    · intro _ _
      exact hsize
    · rename_i h
      simpa using h
    · rename_i hA _ _ hApp _ _ hS
      refine ⟨hA, ?_⟩
      rw [(hS _ hApp).1]
      simp [guardedVals]
  | cons q qs =>
    simp only
    mvcgen [hidx, hx, hof, hosq] invariants
      · ⇓⟨xs, sv⟩ => ⌜SpongeVar.ReadsAt V sv (Poseidon.absorb p Poseidon.init
          (vk.indexPoints.flatMap (fun P => [P.x.val V, P.y.val V]) ++
            xs.prefix.map (·.val V)))⌝
    · rename_i hinv _
      intro _ h
      simpa [Poseidon.absorb, List.foldl_append] using h _ hinv
    · intro _ _
      exact hsize
    · rename_i h
      simpa using h
    · rename_i hA _ _ hApp _ _ hOf _ _ hS
      refine ⟨hA, ?_⟩
      have hsq : ∀ n, (Poseidon.absorb p Poseidon.init
          (vk.indexPoints.flatMap (fun P => [P.x.val V, P.y.val V]) ++
            appState.toList.map (·.val V))).mode ≠ .squeezed n := by
        intro n hn
        obtain ⟨m, hm⟩ := OptSponge.absorb_mode_absorbed p _ Poseidon.init ⟨0, rfl⟩
        rw [hm] at hn
        exact nomatch hn
      obtain ⟨ib, nf, hab, hnf⟩ := hOf _ hApp hsq
      have hab' := foldl_optAbsorb_reads _ _ (guarded_reads _ ms.toList hms') _ _ hab
      rw [← foldl_guarded] at hab'
      have hlen := (guarded_reads _ ms.toList hms').length_eq
      rw [hS _ _ _ _ hab' (Or.inr ⟨hsq, hnf⟩) (fun j hj => hchar' j (hj.trans_eq hlen.symm)),
        List.nil_append]
      simp [Poseidon.absorb, List.foldl_append]

end Reads

end Pickles
