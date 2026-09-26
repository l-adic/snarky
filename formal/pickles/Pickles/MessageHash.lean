import Snarky.Kimchi.Circuit.AddComplete
import Pickles.FrSponge
import Pickles.OptSponge
import Pickles.Statement
import Pickles.VkComms

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

/-- The accumulator digest from the sponge `sv`: every challenge vector absorbed in order, then
`sg.x` and `sg.y`, then one squeeze. -/
def hashMessagesForNextWrapProof (p : Poseidon.Params F) (sv : SpongeVar F)
    (allChallenges : List (List (FVar F))) (sg : AffinePoint (FVar F)) :
    CircuitM F c (FVar F) := do
  let sv ← absorbList p sv allChallenges.flatten
  let sv ← SpongeVar.absorb p sv sg.x
  let sv ← SpongeVar.absorb p sv sg.y
  let (digest, _) ← SpongeVar.squeeze p sv
  pure digest

/-- The sponge after absorbing `pad` copies of the dummy challenge vector `dummy`, as constant
cells: a slot with `pad` padding entries starts its accumulator digest here, so the padding
emits no rows. -/
def wrapPaddingSponge {k : ℕ} (p : Poseidon.Params F) (dummy : Vector F k) (pad : ℕ) :
    SpongeVar F :=
  SpongeVar.ofConstants
    (Poseidon.absorb p Poseidon.init (List.replicate pad dummy.toList).flatten)

/-- The wire's messages-for-next-wrap-proof digest: an accumulator's `sg` and its old bulletproof
challenges, front-padded with `dummy` to `MaxProofsVerified`, absorbed from the fresh sponge and
squeezed. -/
def wrapMsgDigest {k : ℕ} (p : Poseidon.Params F) (dummy : Vector F k) (sg : AffinePoint F)
    (chals : List (Vector F k)) : F :=
  (Poseidon.squeeze p (Poseidon.absorb p Poseidon.init
    ((List.replicate (MaxProofsVerified - chals.length) dummy.toList).flatten
      ++ (chals.map Vector.toList).flatten ++ [sg.x, sg.y]))).1

/-- The sponge after the key: its commitments absorbed chunk by chunk, `x` then `y`, in the
order `σ₀…σ₆`, the coefficients, the selectors. -/
def spongeAfterIndex {nc : ℕ} (p : Poseidon.Params F) (vk : VkComms nc (AffinePoint (FVar F))) :
    CircuitM F c (SpongeVar F) :=
  vk.indexPoints.foldlM
    (fun sv P => do
      let sv ← SpongeVar.absorb p sv P.x
      SpongeVar.absorb p sv P.y)
    SpongeVar.init

/-- The step proof's accumulator digest on the plain sponge: after the key, the application
state, then per proof `sg` and its challenges, then one squeeze. -/
def hashMessagesForNextStepProof {nc : ℕ} (p : Poseidon.Params F)
    (vk : VkComms nc (AffinePoint (FVar F))) (appState : List (FVar F))
    (proofs : List (AffinePoint (FVar F) × List (FVar F))) : CircuitM F c (FVar F) := do
  let sv ← spongeAfterIndex p vk
  let sv ← appState.foldlM (SpongeVar.absorb p) sv
  let sv ← (proofs.flatMap fun (sg, chals) => sg.x :: sg.y :: chals).foldlM
    (SpongeVar.absorb p) sv
  let (digest, _) ← SpongeVar.squeeze p sv
  pure digest

/-- The step proof's accumulator digest with each proof's advice kept under its mask, and the
sponge after the key, which the verify block resumes from: after the key and the application
state, per proof `sg` and its challenges on the conditional sponge. With no proofs there is no
masked input, and the plain sponge squeezes. -/
def hashMessagesForNextStepProofOpt {nc : ℕ} (p : Poseidon.Params F)
    (vk : VkComms nc (AffinePoint (FVar F))) (appState : List (FVar F))
    (proofs : List (BoolVar F × AffinePoint (FVar F) × List (FVar F))) :
    CircuitM F c (FVar F × SpongeVar F) := do
  let afterIndex ← spongeAfterIndex p vk
  let sv ← appState.foldlM (SpongeVar.absorb p) afterIndex
  match proofs with
  | [] => do
    let (digest, _) ← SpongeVar.squeeze p sv
    pure (digest, afterIndex)
  | _ => do
    let ov ← OptSponge.ofSponge p sv
    let ov := proofs.foldl (fun ov (b, sg, chals) =>
      (sg.x :: sg.y :: chals).foldl (fun ov x => OptSponge.optAbsorb ov (b, x)) ov) ov
    let (digest, _) ← OptSponge.optSqueeze p ov
    pure (digest, afterIndex)

/-! ## Reading the digests -/

section Reads

open Std.Do

variable {V : Valuation F}

/-- Under any valuation satisfying the emitted constraints, from a sponge reading as `s`, the
wrap digest reads as the squeeze after absorbing the challenges' readings, then `sg`. -/
theorem hashMessagesForNextWrapProof_spec (p : Poseidon.Params F)
    (hsize : p.roundConstants.size = Poseidon.fullRounds) (sv : SpongeVar F)
    (allChallenges : List (List (FVar F))) (sg : AffinePoint (FVar F)) :
    ⦃⌜True⌝⦄ hashMessagesForNextWrapProof (c := Builder V (KimchiConstraint F)) p sv
      allChallenges sg
    ⦃⇓ d _ => ⌜∀ s, SpongeVar.ReadsAt V sv s → d.val V = (Poseidon.squeeze p (Poseidon.absorb p s
      (allChallenges.flatten.map (·.val V) ++ [sg.x.val V, sg.y.val V]))).1⌝⦄ := by
  have hl := fun sv => absorbList_spec (V := V) p hsize sv allChallenges.flatten
  have hx := fun sv x => SpongeVar.absorb_spec (V := V) p hsize sv x
  have hsq := fun sv => SpongeVar.squeeze_spec (V := V) p hsize sv
  simp only [hashMessagesForNextWrapProof]
  mvcgen [hl, hx, hsq]
  rename_i _ _ hl' _ _ hx1 _ _ hy1 _ _ hsq'
  intro s hs
  rw [(hsq' _ (hy1 _ (hx1 _ (hl' s hs)))).1]
  simp [Poseidon.absorb, List.foldl_append]

/-- **The padded wrap digest.** From the padding sponge for the stacks it is given, the digest
of cells reading as an accumulator `sg` and its challenges `chals` is the wire's
messages-for-next-wrap-proof digest of them (`wrapMsgDigest`). -/
theorem hashMessagesForNextWrapProof_padded {k : ℕ} (p : Poseidon.Params F)
    (hsize : p.roundConstants.size = Poseidon.fullRounds) (dummy : Vector F k)
    (chals : List (Vector (FVar F) k)) (sg : AffinePoint (FVar F)) :
    ⦃⌜True⌝⦄ hashMessagesForNextWrapProof (c := Builder V (KimchiConstraint F)) p
      (wrapPaddingSponge p dummy (MaxProofsVerified - chals.length)) (chals.map Vector.toList) sg
    ⦃⇓ d _ => ⌜∀ (sgv : AffinePoint F) (cv : List (Vector F k)), CircuitType.Reads V sg sgv →
      List.Forall₂ (CircuitType.Reads V) chals cv → d.val V = wrapMsgDigest p dummy sgv cv⌝⦄ := by
  refine builder_spec_imp _ _ _
    (hashMessagesForNextWrapProof_spec p hsize _ (chals.map Vector.toList) sg) fun d hd => ?_
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
  simp only [wrapMsgDigest, hcv.length_eq, Poseidon.absorb, List.foldl_append, hvals hcv, hx, hy]

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
private def guarded (proofs : List (BoolVar F × AffinePoint (FVar F) × List (FVar F))) :
    List (BoolVar F × FVar F) :=
  proofs.flatMap fun (b, sg, chals) => (sg.x :: sg.y :: chals).map (b, ·)

/-- The kept values: each proof's `sg` and challenges where its mask reads `true`. -/
def keptValues (V : Valuation F) (ms : List Bool)
    (proofs : List (BoolVar F × AffinePoint (FVar F) × List (FVar F))) : List F :=
  (List.zipWith (fun m (q : BoolVar F × AffinePoint (FVar F) × List (FVar F)) =>
    if m then (q.2.1.x :: q.2.1.y :: q.2.2).map (·.val V) else []) ms proofs).flatten

omit [DecidableEq F] in
/-- The nested per-proof absorbs are one fold over the guarded inputs. -/
private theorem foldl_guarded (ov : OptSponge.OptSpongeVar F) :
    ∀ proofs : List (BoolVar F × AffinePoint (FVar F) × List (FVar F)),
      proofs.foldl (fun ov q =>
          (q.2.1.x :: q.2.1.y :: q.2.2).foldl (fun ov x => OptSponge.optAbsorb ov (q.1, x)) ov) ov
        = (guarded proofs).foldl OptSponge.optAbsorb ov := by
  intro proofs
  induction proofs generalizing ov with
  | nil => rfl
  | cons q qs ih =>
    obtain ⟨b, sg, chals⟩ := q
    simp only [List.foldl_cons, guarded, List.flatMap_cons, List.foldl_append, List.foldl_map]
    exact ih _

/-- The guarded inputs' readings: each value under its proof's mask. -/
private def guardedVals (V : Valuation F) (ms : List Bool)
    (proofs : List (BoolVar F × AffinePoint (FVar F) × List (FVar F))) : List (Bool × F) :=
  (List.zipWith (fun m (q : BoolVar F × AffinePoint (FVar F) × List (FVar F)) =>
    (q.2.1.x :: q.2.1.y :: q.2.2).map fun x => (m, x.val V)) ms proofs).flatten

omit [BasicSystem F c] [KimchiSystem F c] in
private theorem guarded_reads :
    ∀ (proofs : List (BoolVar F × AffinePoint (FVar F) × List (FVar F))) (ms : List Bool),
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
private theorem guardedVals_kept (ms : List Bool)
    (proofs : List (BoolVar F × AffinePoint (FVar F) × List (FVar F))) :
    ((guardedVals V ms proofs).filter (·.1)).map (·.2) = keptValues V ms proofs := by
  induction proofs generalizing ms with
  | nil => cases ms <;> rfl
  | cons q qs ih =>
    cases ms with
    | nil => rfl
    | cons m ms =>
      simp only [guardedVals, keptValues, List.zipWith_cons_cons, List.flatten_cons,
        List.filter_append, List.map_append] at *
      rw [ih]
      cases m <;> simp [List.filter_map, Function.comp_def]

/-- Under any valuation satisfying the emitted constraints, with each proof's mask reading as
`ms`, the digest reads as the first squeeze of the value sponge after the key's coordinates,
the application state, and the kept proofs' `sg` and challenges, and the returned sponge reads
as the one after the key. -/
theorem hashMessagesForNextStepProofOpt_spec {nc : ℕ} (p : Poseidon.Params F)
    (hsize : p.roundConstants.size = Poseidon.fullRounds)
    (hall : ∀ j k : ℕ, j ≤ 3 → k ≤ 3 → (j : F) = k → j = k)
    (vk : VkComms nc (AffinePoint (FVar F))) (appState : List (FVar F))
    (proofs : List (BoolVar F × AffinePoint (FVar F) × List (FVar F))) (ms : List Bool)
    (hms : List.Forall₂ (fun q m => CircuitType.Reads V q.1 m) proofs ms)
    (hchar : ∀ k : ℕ, k ≤ (proofs.map fun q => q.2.2.length + 2).sum → (k : F) = 0 → k = 0) :
    ⦃⌜True⌝⦄ hashMessagesForNextStepProofOpt (c := Builder V (KimchiConstraint F)) p vk
      appState proofs
    ⦃⇓ r _ => ⌜SpongeVar.ReadsAt V r.2 (Poseidon.absorb p Poseidon.init
        (vk.indexPoints.flatMap fun P => [P.x.val V, P.y.val V])) ∧
      r.1.val V = (Poseidon.squeeze p (Poseidon.absorb p Poseidon.init
        (vk.indexPoints.flatMap (fun P => [P.x.val V, P.y.val V]) ++ appState.map (·.val V) ++
          keptValues V ms proofs))).1⌝⦄ := by
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
  simp only [hashMessagesForNextStepProofOpt]
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
      simp [keptValues]
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
            appState.map (·.val V))).mode ≠ .squeezed n := by
        intro n hn
        obtain ⟨m, hm⟩ := OptSponge.absorb_mode_absorbed p _ Poseidon.init ⟨0, rfl⟩
        rw [hm] at hn
        exact nomatch hn
      obtain ⟨ib, nf, hab, hnf⟩ := hOf _ hApp hsq
      have hab' := foldl_optAbsorb_reads _ _ (guarded_reads _ ms hms) _ _ hab
      rw [← foldl_guarded] at hab'
      have hlen := (guarded_reads _ ms hms).length_eq
      have hglen : (guarded (q :: qs)).length = ((q :: qs).map fun q => q.2.2.length + 2).sum := by
        simp only [guarded, List.length_flatMap, List.length_map, List.length_cons]
      rw [hS _ _ _ _ hab' (Or.inr ⟨hsq, hnf⟩) (by simpa [← hlen, hglen] using hchar),
        List.nil_append,
        guardedVals_kept]
      simp [Poseidon.absorb, List.foldl_append]

end Reads

end Pickles
