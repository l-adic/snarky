import Snarky.Kimchi.Circuit.Poseidon
import Poseidon.RandomOracle

/-!
# The in-circuit block-mode hash

Port of `Snarky.Circuit.RandomOracle`
(packages/random-oracle/src/Snarky/Circuit/RandomOracle.purs), the circuit twin of
`Poseidon/RandomOracle.lean`: chunk the input into rate-2 blocks (constant-zero pads,
one zero block for empty input), add each block into the state and permute, read
slot 0. Unlike the duplex sponge there is no seal — blocks feed bare `add_` sums
straight into the permutation gadget, as the PS source does.

The chunking is metadata (list structure over `FVar`s), so a hash of `n` variables
emits exactly the `poseidon` blocks — `⌈n/2⌉` of them, or one for `n = 0` — and
nothing else.

Name map: `update`/`hash2`/`hashVec` keep their names; PS `initialState` stays private
as `initState` (PS does not export it); the private helpers mirror the value module's
`toBlocks`/`chunk`/`addBlock`. The state is `Poseidon.Triple (FVar F)`, blocks are
pairs, and the laws quote the generic reading vocabulary (`readVal`, `Snarky.Reads`,
`Snarky.ReadsAll`).

Deviations from the PS original:
- PS's ambient `PoseidonField` class arrives as the explicit `p : Poseidon.Params F`.
- PS's width-3 / width-2 `Vector`s render as `Poseidon.Triple` and the pair; PS `Array`
  inputs render as `List`.
- The `Digest` newtype with its `CircuitType`/`CheckedType`/`AssertEqual` instances,
  and the `Hashable`/`HashInput` classes with `hashOf`, are not ported: they are PS
  generic-deriving and dispatch ergonomics; the operations are the port surface, and
  Lean callers apply them directly (digests are bare `FVar`s).
- PS's pad-then-`Vector.chunk` chunking renders as the structural recursion
  `chunkVar`, preserving the odd-tail pad and the empty-input rule — matching the
  value module's rendering.
-/

namespace Snarky.Kimchi

open Snarky

variable {F c : Type}

namespace RandomOracle

/-- The fresh state (PS `initialState`, unexported there): constant-zero cells. -/
private def initState [Zero F] : Poseidon.Triple (FVar F) :=
  ⟨.const 0, .const 0, .const 0⟩

/-- Rate-2 chunks with a constant-zero odd-tail pad — `Poseidon.RandomOracle.chunk`
over circuit variables. -/
private def chunkVar [Zero F] : List (FVar F) → List (FVar F × FVar F)
  | [] => []
  | [x] => [(x, .const 0)]
  | x :: y :: rest => (x, y) :: chunkVar rest

/-- The block decomposition — `Poseidon.RandomOracle.toBlocks` over circuit
variables: rate-2 chunks, one constant-zero block for empty input. -/
private def toBlocksVar [Zero F] : List (FVar F) → List (FVar F × FVar F)
  | [] => [(.const 0, .const 0)]
  | xs => chunkVar xs

/-- Add a block into the rate slots (PS `addBlock`): bare `add_` sums, no seal, no
constraints. -/
private def addBlockVar [Add F] (st : Poseidon.Triple (FVar F)) (b : FVar F × FVar F) :
    Poseidon.Triple (FVar F) :=
  ⟨CVar.add_ st.s0 b.1, CVar.add_ st.s1 b.2, st.s2⟩

/-- Absorb one block (PS `updateBlock`): add into the rate slots, permute. -/
private def updateBlock [Field F] [KimchiSystem F c]
    (p : Poseidon.Params F) (st : Poseidon.Triple (FVar F)) (b : FVar F × FVar F) :
    CircuitM F c (Poseidon.Triple (FVar F)) :=
  poseidon p (addBlockVar st b)

/-- Fold the input into the state block by block (PS `update`). -/
def update [Field F] [KimchiSystem F c] (p : Poseidon.Params F)
    (st : Poseidon.Triple (FVar F)) (xs : List (FVar F)) :
    CircuitM F c (Poseidon.Triple (FVar F)) :=
  (toBlocksVar xs).foldlM (updateBlock p) st

/-- Hash exactly two elements (PS `hash2`): one block, one permutation. -/
def hash2 [Field F] [KimchiSystem F c] (p : Poseidon.Params F) (a b : FVar F) :
    CircuitM F c (FVar F) := do
  let st ← updateBlock p initState (a, b)
  pure st.s0

/-- Hash a list of elements (PS `hashVec`): update the fresh state, read slot 0. -/
def hashVec [Field F] [KimchiSystem F c] (p : Poseidon.Params F)
    (xs : List (FVar F)) : CircuitM F c (FVar F) := do
  let st ← update p initState xs
  pure st.s0

/-! ## The laws

Each op reads as its `Poseidon.RandomOracle` value counterpart: `update` as the block
fold, `hash2`/`hashVec` as `hash`. The block fold is walked once, generalized over the
block list; the public laws instantiate it at the chunking, bridged by the pure
chunk-alignment lemmas. Input lists are read by the generic `Snarky.ReadsAll` — at
the base instance for the inputs, at the pair instance for the blocks. -/

open Std.Do

/-- The circuit chunking reads as the value chunking. -/
private theorem chunkVar_map_val [Field F] (V : Valuation F) :
    ∀ xs : List (FVar F),
      (chunkVar xs).map (readVal V)
        = Poseidon.RandomOracle.chunk (xs.map (fun x => x.val V))
  | [] => rfl
  | [x] => by
    simp [chunkVar, Poseidon.RandomOracle.chunk, readVal_prod, readVal_fvar,
      CVar.val]
  | x :: y :: rest => by
    simp only [chunkVar, Poseidon.RandomOracle.chunk, List.map_cons,
      chunkVar_map_val V rest, readVal_prod, readVal_fvar]

/-- The circuit block decomposition reads as the value block decomposition. -/
private theorem toBlocksVar_map_val [Field F] (V : Valuation F) :
    ∀ xs : List (FVar F),
      (toBlocksVar xs).map (readVal V)
        = Poseidon.RandomOracle.toBlocks (xs.map (fun x => x.val V))
  | [] => by
    simp [toBlocksVar, Poseidon.RandomOracle.toBlocks, readVal_prod, readVal_fvar,
      CVar.val]
  | [x] => chunkVar_map_val V [x]
  | x :: y :: rest => chunkVar_map_val V (x :: y :: rest)

/-- `updateBlock` is sound: the output state reads as one value block step —
`blockCipher` of `addBlock` at the state and block readings. -/
@[spec] private theorem updateBlock_spec {V : Valuation F} [Field F] [DecidableEq F]
    (p : Poseidon.Params F) (hsize : p.roundConstants.size = Poseidon.fullRounds)
    (st : Poseidon.Triple (FVar F)) (b : FVar F × FVar F) :
    ⦃⌜True⌝⦄
    (updateBlock (c := Builder V (KimchiConstraint F)) p st b)
    ⦃⇓ r _ => ⌜readVal V r = Poseidon.blockCipher p
          (Poseidon.RandomOracle.addBlock (readVal V st) (readVal V b))⌝⦄ := by
  simp only [updateBlock]
  have pspec := Poseidon.poseidon_spec (V := V) p hsize
  mvcgen [pspec]
  intro hpos
  exact hpos.trans (by
    simp [addBlockVar, readVal_prod, readVal_fvar,
      Poseidon.RandomOracle.addBlock, CVar.val_add_])

/-- `updateBlock` is complete: the honest run accepts on a readable state and block,
and the output state reads back as the value block step. -/
@[spec] private theorem updateBlock_complete_spec [Field F] [DecidableEq F]
    (p : Poseidon.Params F) (hsize : p.roundConstants.size = Poseidon.fullRounds)
    (st : Poseidon.Triple (FVar F)) (b : FVar F × FVar F)
    (Q : PostCond (Poseidon.Triple (FVar F)) (.arg (ProverState F) (.except EvalError .pure))) :
    ⦃Complete
        (fun env => Readable (Poseidon.Triple F) env st ∧ Readable (F × F) env b)
        (fun env (r : Poseidon.Triple (FVar F)) env' =>
          ∀ sv bv, Snarky.Reads env st sv → Snarky.Reads env b bv →
            Snarky.Reads env' r (Poseidon.blockCipher p
              (Poseidon.RandomOracle.addBlock sv bv)))
        Q⦄
    (updateBlock (c := KimchiProverC F) p st b)
    ⦃Q⦄ := by
  simp only [updateBlock]
  intro s hpre
  obtain ⟨⟨hstok, hbok⟩, hk⟩ := hpre
  obtain ⟨sv0, hsv0⟩ := exists_reads hstok
  obtain ⟨bv0, hbv0⟩ := exists_reads hbok
  have hs := hsv0
  simp only [reads_prod_iff, reads_fvar_iff] at hs
  have hb := reads_prod_iff.mp hbv0
  have hb1 := reads_fvar_iff.mp hb.1
  have hb2 := reads_fvar_iff.mp hb.2
  have hadd : Snarky.Reads s.env (addBlockVar st b)
      (Poseidon.RandomOracle.addBlock sv0 bv0) :=
    by simp only [reads_prod_iff, reads_fvar_iff]
       exact ⟨CVar.eval_add_ hs.1 hb1, CVar.eval_add_ hs.2.1 hb2, hs.2.2⟩
  refine Poseidon.poseidon_complete_spec p hsize _ Q s
    ⟨Snarky.Reads.readable hadd, fun r st₁ hpos hle => ?_⟩
  have hpos := hpos _ hadd
  refine hk _ _ (fun sv bv hst hbv => ?_) hle
  obtain rfl := Snarky.Reads.unique hsv0 hst
  obtain rfl := Snarky.Reads.unique hbv0 hbv
  exact hpos

/-- The block fold is sound, generalized over the block list: the output state reads
as the value fold of the block readings. -/
private theorem foldBlocks_spec {V : Valuation F} [Field F] [DecidableEq F]
    (p : Poseidon.Params F) (hsize : p.roundConstants.size = Poseidon.fullRounds)
    (bs : List (FVar F × FVar F)) (st : Poseidon.Triple (FVar F)) :
    ⦃⌜True⌝⦄
    (bs.foldlM (updateBlock (c := Builder V (KimchiConstraint F)) p) st)
    ⦃⇓ r _ => ⌜readVal V r = (bs.map (readVal V)).foldl
        (fun s b => Poseidon.blockCipher p (Poseidon.RandomOracle.addBlock s b))
        (readVal V st)⌝⦄ := by
  mvcgen
  case inv1 =>
    exact ⇓ c _ => ⌜readVal V c.2 = (c.1.prefix.map (readVal V)).foldl
      (fun s b => Poseidon.blockCipher p (Poseidon.RandomOracle.addBlock s b))
      (readVal V st)⌝
  case vc1.pre => simp
  case vc2.post.success =>
    intro h
    simpa using h
  case vc3.post.success =>
    rename_i hinv r
    intro _ hr
    simp at hinv ⊢
    rw [hr, hinv]
  case vc4 =>
    intro _ _
    exact hsize

/-- Pinned inputs chunk to pinned blocks (the constant pads read as the value pads). -/
private theorem readsAll_chunkVar [Field F] {env : Assignments F} :
    ∀ {xs : List (FVar F)} {vs : List F}, ReadsAll env xs vs →
      ReadsAll env (chunkVar xs) (Poseidon.RandomOracle.chunk vs)
  | [], _, h => by cases h; exact .nil
  | [x], _, h => by
    cases h with
    | cons hx hrest =>
      cases hrest
      exact .cons (reads_prod_iff.mpr ⟨hx, reads_fvar_iff.mpr rfl⟩) .nil
  | x :: y :: rest, _, h => by
    cases h with
    | cons hx h2 =>
      cases h2 with
      | cons hy hrest =>
        exact .cons (reads_prod_iff.mpr ⟨hx, hy⟩) (readsAll_chunkVar hrest)

/-- Pinned inputs decompose to pinned blocks. -/
private theorem readsAll_toBlocksVar [Field F] {env : Assignments F}
    {xs : List (FVar F)} {vs : List F} (h : ReadsAll env xs vs) :
    ReadsAll env (toBlocksVar xs) (Poseidon.RandomOracle.toBlocks vs) := by
  cases h with
  | nil =>
    exact .cons (reads_prod_iff.mpr
      ⟨reads_fvar_iff.mpr rfl, reads_fvar_iff.mpr rfl⟩) .nil
  | @cons x v xs' vs' hx hrest =>
    show ReadsAll env (chunkVar (x :: xs'))
      (Poseidon.RandomOracle.chunk (v :: vs'))
    exact readsAll_chunkVar (.cons hx hrest)

/-- Evaluable inputs chunk to readable blocks. -/
private theorem chunkVar_readable [Field F] {env : Assignments F} :
    ∀ xs : List (FVar F), (∀ x ∈ xs, (x.eval env).isOk) →
      ∀ b ∈ chunkVar xs, Readable (F × F) env b
  | [], _ => by simp [chunkVar]
  | [x], h => by
    simp only [chunkVar, List.mem_singleton, forall_eq]
    exact readable_prod_iff.mpr
      ⟨readable_fvar_iff.mpr (h x (by simp)), readable_fvar_iff.mpr (by rfl)⟩
  | x :: y :: rest, h => by
    simp only [chunkVar, List.mem_cons, forall_eq_or_imp]
    refine ⟨readable_prod_iff.mpr
      ⟨readable_fvar_iff.mpr (h x (by simp)),
        readable_fvar_iff.mpr (h y (by simp))⟩, ?_⟩
    exact fun b hb =>
      chunkVar_readable rest (fun z hz => h z (by simp [hz])) b hb

/-- Evaluable inputs decompose to readable blocks. -/
private theorem toBlocksVar_readable [Field F] {env : Assignments F} :
    ∀ xs : List (FVar F), (∀ x ∈ xs, (x.eval env).isOk) →
      ∀ b ∈ toBlocksVar xs, Readable (F × F) env b
  | [], _ => by
    simp only [toBlocksVar, List.mem_singleton, forall_eq]
    exact readable_prod_iff.mpr
      ⟨readable_fvar_iff.mpr (by rfl), readable_fvar_iff.mpr (by rfl)⟩
  | [x], h => chunkVar_readable [x] h
  | x :: y :: rest, h => chunkVar_readable (x :: y :: rest) h

/-- The block fold is complete, generalized over the block list: the honest run
accepts on a readable state and blocks, and the output state reads back as the value
fold. -/
private theorem foldBlocks_complete_spec [Field F] [DecidableEq F]
    (p : Poseidon.Params F) (hsize : p.roundConstants.size = Poseidon.fullRounds) :
    ∀ (bs : List (FVar F × FVar F)) (st : Poseidon.Triple (FVar F))
      (Q : PostCond (Poseidon.Triple (FVar F)) (.arg (ProverState F) (.except EvalError .pure))),
      ⦃Complete
          (fun env => Readable (Poseidon.Triple F) env st ∧
            ∀ b ∈ bs, Readable (F × F) env b)
          (fun env (r : Poseidon.Triple (FVar F)) env' =>
            ∀ sv vs, Snarky.Reads env st sv → ReadsAll env bs vs →
              Snarky.Reads env' r (vs.foldl
                (fun s b =>
                  Poseidon.blockCipher p (Poseidon.RandomOracle.addBlock s b)) sv))
          Q⦄
      (bs.foldlM (updateBlock (c := KimchiProverC F) p) st)
      ⦃Q⦄
  | [], st, Q => by
    simp only [List.foldlM_nil]
    mvcgen
    rename_i s hpre
    obtain ⟨⟨hstok, _⟩, hk⟩ := hpre
    refine hk _ s (fun sv vs hst hr => ?_) (Assignments.Le.refl _)
    cases hr
    exact hst
  | b :: bs, st, Q => by
    simp only [List.foldlM_cons]
    have ih := foldBlocks_complete_spec p hsize bs
    intro s hpre
    obtain ⟨⟨hstok, hblocks⟩, hk⟩ := hpre
    have hbok := hblocks b (by simp)
    obtain ⟨sv0, hsv0⟩ := exists_reads hstok
    obtain ⟨bv0, hbv0⟩ := exists_reads hbok
    simp only [WPMonad.wp_bind, PredTrans.apply_Bind_bind]
    refine updateBlock_complete_spec p hsize st b _ s
      ⟨⟨hstok, hbok⟩, fun r₁ st₁ hout hle₁ => ?_⟩
    have houtv := hout _ _ hsv0 hbv0
    refine ih r₁ _ st₁
      ⟨⟨Snarky.Reads.readable houtv,
        fun b' hb' => Readable.le hle₁ (hblocks b' (by simp [hb']))⟩,
      fun r₂ st₂ hrest hle₂ => ?_⟩
    refine hk _ _ (fun sv vs hst hr => ?_) (hle₁.trans hle₂)
    obtain rfl := Snarky.Reads.unique hsv0 hst
    cases hr with
    | cons hv hr' =>
      obtain rfl := Snarky.Reads.unique hbv0 hv
      simp only [List.foldl_cons]
      exact hrest _ _ houtv (ReadsAll.le hle₁ hr')

/-- `update` is sound: the output state reads as `Poseidon.RandomOracle.update` of the
state and input readings. -/
@[spec] theorem update_spec {V : Valuation F} [Field F] [DecidableEq F] (p : Poseidon.Params F)
    (hsize : p.roundConstants.size = Poseidon.fullRounds) (st : Poseidon.Triple (FVar F))
    (xs : List (FVar F)) :
    ⦃⌜True⌝⦄
    (update (c := Builder V (KimchiConstraint F)) p st xs)
    ⦃⇓ r _ => ⌜readVal V r = Poseidon.RandomOracle.update p (readVal V st)
          (xs.map (fun x => x.val V))⌝⦄ := by
  simp only [update, Poseidon.RandomOracle.update, ← toBlocksVar_map_val]
  exact foldBlocks_spec p hsize (toBlocksVar xs) st

/-- `update` is complete: the honest run accepts on a readable state and evaluable
inputs, and the output state reads back as `Poseidon.RandomOracle.update` of the
values. -/
@[spec] theorem update_complete_spec [Field F] [DecidableEq F] (p : Poseidon.Params F)
    (hsize : p.roundConstants.size = Poseidon.fullRounds) (st : Poseidon.Triple (FVar F))
    (xs : List (FVar F))
    (Q : PostCond (Poseidon.Triple (FVar F)) (.arg (ProverState F) (.except EvalError .pure))) :
    ⦃Complete
        (fun env => Readable (Poseidon.Triple F) env st ∧
          ∀ x ∈ xs, (x.eval env).isOk)
        (fun env (r : Poseidon.Triple (FVar F)) env' =>
          ∀ sv vs, Snarky.Reads env st sv → ReadsAll env xs vs →
            Snarky.Reads env' r (Poseidon.RandomOracle.update p sv vs))
        Q⦄
    (update (c := KimchiProverC F) p st xs)
    ⦃Q⦄ := by
  simp only [update]
  intro s hpre
  obtain ⟨⟨hstok, hxs⟩, hk⟩ := hpre
  refine foldBlocks_complete_spec p hsize (toBlocksVar xs) st _ s
    ⟨⟨hstok, toBlocksVar_readable xs hxs⟩, fun r st' hout hle => ?_⟩
  refine hk _ _ (fun sv vs hst hr => ?_) hle
  exact hout sv (Poseidon.RandomOracle.toBlocks vs) hst (readsAll_toBlocksVar hr)

/-- The fresh state reads as the value module's fresh state, on any table. -/
private theorem reads_initState [Field F] (env : Assignments F) :
    Snarky.Reads env (initState (F := F))
      (Poseidon.RandomOracle.initialState (F := F)) :=
  by simp only [reads_prod_iff, reads_fvar_iff]
     exact ⟨rfl, rfl, rfl⟩

/-- `hash2` is sound: the digest reads as the value `hash` of the two readings. -/
@[spec] theorem hash2_spec {V : Valuation F} [Field F] [DecidableEq F] (p : Poseidon.Params F)
    (hsize : p.roundConstants.size = Poseidon.fullRounds) (a b : FVar F) :
    ⦃⌜True⌝⦄
    (hash2 (c := Builder V (KimchiConstraint F)) p a b)
    ⦃⇓ r _ => ⌜r.val V = Poseidon.RandomOracle.hash p [a.val V, b.val V]⌝⦄ := by
  simp only [hash2]
  have u := updateBlock_spec (V := V) p hsize
  mvcgen [u]
  rename_i r _ h
  simp only [readVal_prod, readVal_fvar] at h
  have h1 := congrArg Prod.fst h
  simpa [Poseidon.RandomOracle.hash, Poseidon.RandomOracle.update,
    Poseidon.RandomOracle.toBlocks, Poseidon.RandomOracle.chunk,
    Poseidon.RandomOracle.digest, Poseidon.RandomOracle.initialState,
    initState, CVar.val] using h1

/-- `hash2` is complete: the honest run accepts on readable operands, and the digest
reads back as the value `hash` of their values. -/
@[spec] theorem hash2_complete_spec [Field F] [DecidableEq F] (p : Poseidon.Params F)
    (hsize : p.roundConstants.size = Poseidon.fullRounds) (a b : FVar F)
    (Q : PostCond (FVar F) (.arg (ProverState F) (.except EvalError .pure))) :
    ⦃Complete
        (fun env => (a.eval env).isOk ∧ (b.eval env).isOk)
        (fun env (r : FVar F) env' => ∀ av bv, a.eval env = .ok av →
          b.eval env = .ok bv →
          r.eval env' = .ok (Poseidon.RandomOracle.hash p [av, bv]))
        Q⦄
    (hash2 (c := KimchiProverC F) p a b)
    ⦃Q⦄ := by
  simp only [hash2]
  have u := updateBlock_complete_spec p hsize
  mvcgen [u]
  rename_i s hpre
  obtain ⟨⟨ha, hb⟩, hk⟩ := hpre
  obtain ⟨av, ha⟩ := CVar.evalOk ha
  obtain ⟨bv, hb⟩ := CVar.evalOk hb
  refine ⟨⟨Snarky.Reads.readable (reads_initState s.env),
    readable_prod_iff.mpr ⟨readable_fvar_iff.mpr (isOk_of_eq ha),
      readable_fvar_iff.mpr (isOk_of_eq hb)⟩⟩, fun r₁ st₁ hout hle₁ => ?_⟩
  have hab : Snarky.Reads s.env (a, b) ((av, bv) : F × F) :=
    reads_prod_iff.mpr ⟨reads_fvar_iff.mpr ha, reads_fvar_iff.mpr hb⟩
  have hout := hout _ _ (reads_initState s.env) hab
  simp only [wp, PredTrans.apply, prove]
  intro hf
  refine hk _ ⟨st₁.nv, st₁.env, hf⟩ (fun av' bv' ha' hb' => ?_) hle₁
  rw [ha] at ha'; rw [hb] at hb'
  injection ha' with ha'; injection hb' with hb'
  subst ha' hb'
  simp only [reads_prod_iff, reads_fvar_iff] at hout
  have h0 := hout.1
  simpa [Poseidon.RandomOracle.hash, Poseidon.RandomOracle.update,
    Poseidon.RandomOracle.toBlocks, Poseidon.RandomOracle.chunk,
    Poseidon.RandomOracle.digest] using h0

/-- `hashVec` is sound: the digest reads as the value `hash` of the input readings. -/
@[spec] theorem hashVec_spec {V : Valuation F} [Field F] [DecidableEq F] (p : Poseidon.Params F)
    (hsize : p.roundConstants.size = Poseidon.fullRounds) (xs : List (FVar F)) :
    ⦃⌜True⌝⦄
    (hashVec (c := Builder V (KimchiConstraint F)) p xs)
    ⦃⇓ r _ => ⌜r.val V = Poseidon.RandomOracle.hash p (xs.map (fun x => x.val V))⌝⦄ := by
  simp only [hashVec]
  have u := update_spec (V := V) p hsize
  mvcgen [u]
  rename_i r _ h
  simp only [readVal_prod, readVal_fvar] at h
  have h1 := congrArg Prod.fst h
  simpa [Poseidon.RandomOracle.hash, Poseidon.RandomOracle.digest,
    Poseidon.RandomOracle.initialState, initState, CVar.val] using h1

/-- `hashVec` is complete: the honest run accepts on evaluable inputs, and the digest
reads back as the value `hash` of their values. -/
@[spec] theorem hashVec_complete_spec [Field F] [DecidableEq F]
    (p : Poseidon.Params F) (hsize : p.roundConstants.size = Poseidon.fullRounds)
    (xs : List (FVar F))
    (Q : PostCond (FVar F) (.arg (ProverState F) (.except EvalError .pure))) :
    ⦃Complete
        (fun env => ∀ x ∈ xs, (x.eval env).isOk)
        (fun env (r : FVar F) env' => ∀ vs, ReadsAll env xs vs →
          r.eval env' = .ok (Poseidon.RandomOracle.hash p vs))
        Q⦄
    (hashVec (c := KimchiProverC F) p xs)
    ⦃Q⦄ := by
  simp only [hashVec]
  have u := update_complete_spec p hsize
  mvcgen [u]
  rename_i s hpre
  obtain ⟨hxs, hk⟩ := hpre
  refine ⟨⟨Snarky.Reads.readable (reads_initState s.env), hxs⟩,
    fun r₁ st₁ hout hle₁ => ?_⟩
  simp only [wp, PredTrans.apply, prove]
  intro hf
  refine hk _ ⟨st₁.nv, st₁.env, hf⟩ (fun vs hr => ?_) hle₁
  have hout := hout _ vs (reads_initState s.env) hr
  simp only [reads_prod_iff, reads_fvar_iff] at hout
  have h0 := hout.1
  simpa [Poseidon.RandomOracle.hash, Poseidon.RandomOracle.digest] using h0

end RandomOracle

end Snarky.Kimchi
