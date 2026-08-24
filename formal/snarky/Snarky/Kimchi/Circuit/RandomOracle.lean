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
chunk-alignment lemmas. Input lists are read elementwise — `CVar.val` at the inputs,
`readVal` at the pair instance for the blocks. -/

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

/-- The summed slots are in scope when the state and block are. -/
private theorem addBlockVar_scoped [Field F] {st : ProverState F} {s : Poseidon.Triple (FVar F)}
    {b : FVar F × FVar F} (hs : CircuitType.Scoped (Poseidon.Triple F) st s)
    (hb : CircuitType.Scoped (F × F) st b) :
    CircuitType.Scoped (Poseidon.Triple F) st (addBlockVar s b) := by
  simp only [addBlockVar, scoped_prod_iff, scoped_fvar_iff] at hs hb ⊢
  exact ⟨hs.1.add_ hb.1, hs.2.1.add_ hb.2, hs.2.2⟩

/-- The summed slots read as `Poseidon.RandomOracle.addBlock` of the readings. -/
private theorem readVal_addBlockVar [Field F] (V : Valuation F) (s : Poseidon.Triple (FVar F))
    (b : FVar F × FVar F) :
    readVal (val := Poseidon.Triple F) V (addBlockVar s b)
      = Poseidon.RandomOracle.addBlock (readVal (val := Poseidon.Triple F) V s)
        (readVal (val := F × F) V b) := by
  simp [addBlockVar, readVal_prod, readVal_fvar, Poseidon.RandomOracle.addBlock, CVar.val_add_]

/-- The state and result of `updateBlock`'s honest run: the permutation's, on the
summed slots. -/
private def updateBlockRun [Field F] (p : Poseidon.Params F) (st : ProverState F)
    (s : Poseidon.Triple (FVar F)) (b : FVar F × FVar F) :
    ProverState F × Poseidon.Triple (FVar F) :=
  Poseidon.poseidonRun p st (addBlockVar s b)

/-- `updateBlockRun` grows the table, with its result in scope. -/
private theorem updateBlockRun_scope [Field F] (p : Poseidon.Params F) (st : ProverState F)
    (s : Poseidon.Triple (FVar F)) (b : FVar F × FVar F) :
    st.env.Le (updateBlockRun p st s b).1.env ∧
      CircuitType.Scoped (Poseidon.Triple F) (updateBlockRun p st s b).1
        (updateBlockRun p st s b).2 :=
  Poseidon.poseidonRun_scope p st (addBlockVar s b)

/-- `updateBlock`'s honest run on an in-scope state and block lands at
`updateBlockRun`. -/
private theorem updateBlock_run [Field F] [DecidableEq F] (p : Poseidon.Params F)
    {s : Poseidon.Triple (FVar F)} {b : FVar F × FVar F} (st : ProverState F)
    (hs : CircuitType.Scoped (Poseidon.Triple F) st s) (hb : CircuitType.Scoped (F × F) st b) :
    prove (Checker.holds (F := F) (c := KimchiConstraint F))
      (updateBlock (c := KimchiConstraint F) p s b) st.nv st.env
      = .ok ((updateBlockRun p st s b).1.out (updateBlockRun p st s b).2) :=
  Poseidon.poseidon_run p st (addBlockVar_scoped hs hb)

/-- `updateBlockRun` reads as one value block step. -/
private theorem updateBlockRun_grants [Field F] (p : Poseidon.Params F)
    (hsize : p.roundConstants.size = Poseidon.fullRounds) {st : ProverState F}
    {s : Poseidon.Triple (FVar F)} {b : FVar F × FVar F} :
    Grants (Poseidon.Triple F) st (updateBlockRun p st s b)
      (Poseidon.blockCipher p (Poseidon.RandomOracle.addBlock (readVal st.env.toValuation s)
        (readVal st.env.toValuation b))) := by
  have h := Poseidon.poseidonRun_grants p hsize st (addBlockVar s b)
  rw [readVal_addBlockVar] at h
  exact h

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

/-- In-scope inputs chunk to in-scope blocks (the constant pads are in scope). -/
private theorem chunkVar_scoped [Field F] {st : ProverState F} :
    ∀ {xs : List (FVar F)}, (∀ x ∈ xs, x.Scoped st) →
      ∀ b ∈ chunkVar xs, CircuitType.Scoped (F × F) st b
  | [], _, _, hb => by simp [chunkVar] at hb
  | [x], h, b, hb => by
    simp only [chunkVar, List.mem_singleton] at hb
    subst hb
    exact scoped_prod_iff.mpr ⟨scoped_fvar_iff.mpr (h x (by simp)), scoped_fvar_iff.mpr trivial⟩
  | x :: y :: rest, h, b, hb => by
    simp only [chunkVar, List.mem_cons] at hb
    rcases hb with rfl | hb
    · exact scoped_prod_iff.mpr
        ⟨scoped_fvar_iff.mpr (h x (by simp)), scoped_fvar_iff.mpr (h y (by simp))⟩
    · exact chunkVar_scoped (fun z hz => h z (by simp [hz])) b hb

/-- In-scope inputs decompose to in-scope blocks. -/
private theorem toBlocksVar_scoped [Field F] {st : ProverState F} :
    ∀ {xs : List (FVar F)}, (∀ x ∈ xs, x.Scoped st) →
      ∀ b ∈ toBlocksVar xs, CircuitType.Scoped (F × F) st b
  | [], _, b, hb => by
    simp only [toBlocksVar, List.mem_singleton] at hb
    subst hb
    exact scoped_prod_iff.mpr ⟨scoped_fvar_iff.mpr trivial, scoped_fvar_iff.mpr trivial⟩
  | [x], h, b, hb => chunkVar_scoped h b hb
  | x :: y :: rest, h, b, hb => chunkVar_scoped h b hb

/-- The state and result of the block fold's honest run: `updateBlockRun` folded over
the blocks. -/
private def foldBlocksRun [Field F] (p : Poseidon.Params F) (st : ProverState F)
    (s : Poseidon.Triple (FVar F)) (bs : List (FVar F × FVar F)) :
    ProverState F × Poseidon.Triple (FVar F) :=
  bs.foldl (fun acc b => updateBlockRun p acc.1 acc.2 b) (st, s)

/-- `foldBlocksRun` reads as the value fold of the block readings. -/
private theorem foldBlocksRun_grants [Field F] (p : Poseidon.Params F)
    (hsize : p.roundConstants.size = Poseidon.fullRounds) :
    ∀ (bs : List (FVar F × FVar F)) (st : ProverState F) (s : Poseidon.Triple (FVar F)),
      CircuitType.Scoped (Poseidon.Triple F) st s →
      (∀ b ∈ bs, CircuitType.Scoped (F × F) st b) →
      Grants (Poseidon.Triple F) st (foldBlocksRun p st s bs)
        ((bs.map (readVal st.env.toValuation)).foldl
          (fun s b => Poseidon.blockCipher p (Poseidon.RandomOracle.addBlock s b))
          (readVal st.env.toValuation s))
  | [], _, _, hs, _ => ⟨Assignments.Le.refl _, hs, rfl⟩
  | b :: bs, st, s, hs, hbs => by
    have hb := hbs b (List.mem_cons_self ..)
    have h1 := updateBlockRun_grants p hsize (st := st) (s := s) (b := b)
    have ih := foldBlocksRun_grants p hsize bs (updateBlockRun p st s b).1
      (updateBlockRun p st s b).2 h1.scope
      (fun b' hb' => (hbs b' (List.mem_cons_of_mem _ hb')).of_le h1.le)
    refine ⟨h1.le.trans ih.le, ih.scope, ?_⟩
    show readVal (foldBlocksRun p (updateBlockRun p st s b).1 (updateBlockRun p st s b).2 bs).1.env.toValuation
      (foldBlocksRun p (updateBlockRun p st s b).1 (updateBlockRun p st s b).2 bs).2 = _
    rw [ih.read, h1.read, List.map_cons, List.foldl_cons,
      List.map_congr_left fun b' hb' => readVal_of_le h1.le (hbs b' (List.mem_cons_of_mem _ hb'))]

/-- The block fold's honest run on an in-scope state and blocks lands at
`foldBlocksRun`. -/
private theorem foldBlocks_run [Field F] [DecidableEq F] (p : Poseidon.Params F) :
    ∀ (bs : List (FVar F × FVar F)) (st : ProverState F) (s : Poseidon.Triple (FVar F)),
      CircuitType.Scoped (Poseidon.Triple F) st s →
      (∀ b ∈ bs, CircuitType.Scoped (F × F) st b) →
      prove (Checker.holds (F := F) (c := KimchiConstraint F))
        (bs.foldlM (updateBlock (c := KimchiConstraint F) p) s) st.nv st.env
        = .ok ((foldBlocksRun p st s bs).1.out (foldBlocksRun p st s bs).2)
  | [], _, _, _, _ => rfl
  | b :: bs, st, s, hs, hbs => by
    have h1 := updateBlockRun_scope p st s b
    simp only [List.foldlM_cons, prove_bind,
      updateBlock_run p st hs (hbs b (List.mem_cons_self ..)), Except.bind]
    exact foldBlocks_run p bs _ _ h1.2
      (fun b' hb' => (hbs b' (List.mem_cons_of_mem _ hb')).of_le h1.1)

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

/-- The state and result of `update`'s honest run: the block fold over the input's
blocks. -/
def updateRun [Field F] (p : Poseidon.Params F) (st : ProverState F)
    (s : Poseidon.Triple (FVar F)) (xs : List (FVar F)) :
    ProverState F × Poseidon.Triple (FVar F) :=
  foldBlocksRun p st s (toBlocksVar xs)

/-- `update`'s honest run on an in-scope state and inputs lands at `updateRun`. -/
theorem update_run [Field F] [DecidableEq F] (p : Poseidon.Params F)
    {s : Poseidon.Triple (FVar F)} {xs : List (FVar F)} (st : ProverState F)
    (hs : CircuitType.Scoped (Poseidon.Triple F) st s) (hxs : ∀ x ∈ xs, x.Scoped st) :
    prove (Checker.holds (F := F) (c := KimchiConstraint F))
      (update (c := KimchiConstraint F) p s xs) st.nv st.env
      = .ok ((updateRun p st s xs).1.out (updateRun p st s xs).2) :=
  foldBlocks_run p (toBlocksVar xs) st s hs (toBlocksVar_scoped hxs)

/-- `updateRun` reads as `Poseidon.RandomOracle.update` of the readings. -/
theorem updateRun_grants [Field F] (p : Poseidon.Params F)
    (hsize : p.roundConstants.size = Poseidon.fullRounds) {st : ProverState F}
    {s : Poseidon.Triple (FVar F)} {xs : List (FVar F)}
    (hs : CircuitType.Scoped (Poseidon.Triple F) st s) (hxs : ∀ x ∈ xs, x.Scoped st) :
    Grants (Poseidon.Triple F) st (updateRun p st s xs)
      (Poseidon.RandomOracle.update p (readVal st.env.toValuation s)
        (xs.map (fun x => x.val st.env.toValuation))) := by
  have h := foldBlocksRun_grants p hsize (toBlocksVar xs) st s hs (toBlocksVar_scoped hxs)
  rw [toBlocksVar_map_val] at h
  exact h

/-- The fresh state is in scope on any table. -/
private theorem initState_scoped [Field F] (st : ProverState F) :
    CircuitType.Scoped (Poseidon.Triple F) st (initState (F := F)) := by
  simp [initState, scoped_prod_iff, scoped_fvar_iff]

/-- The fresh state reads as the value module's fresh state, at any valuation. -/
private theorem readVal_initState [Field F] (V : Valuation F) :
    readVal V (initState (F := F)) = Poseidon.RandomOracle.initialState (F := F) := by
  simp only [initState, readVal_prod, readVal_fvar]
  rfl

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

/-- The state and result of `hash2`'s honest run: one block step from the fresh state,
slot 0. -/
def hash2Run [Field F] (p : Poseidon.Params F) (st : ProverState F) (a b : FVar F) :
    ProverState F × FVar F :=
  let r := updateBlockRun p st initState (a, b)
  (r.1, r.2.s0)

/-- `hash2`'s honest run on in-scope operands lands at `hash2Run`. -/
theorem hash2_run [Field F] [DecidableEq F] (p : Poseidon.Params F) {a b : FVar F}
    (st : ProverState F) (ha : a.Scoped st) (hb : b.Scoped st) :
    prove (Checker.holds (F := F) (c := KimchiConstraint F))
      (hash2 (c := KimchiConstraint F) p a b) st.nv st.env
      = .ok ((hash2Run p st a b).1.out (hash2Run p st a b).2) := by
  have hab : CircuitType.Scoped (F × F) st (a, b) :=
    scoped_prod_iff.mpr ⟨scoped_fvar_iff.mpr ha, scoped_fvar_iff.mpr hb⟩
  simp only [hash2, hash2Run, prove_bind, Except.bind, updateBlock_run p st (initState_scoped st) hab]
  rfl

/-- `hash2Run` reads as the value `hash` of the operands' readings. -/
theorem hash2Run_grants [Field F] (p : Poseidon.Params F)
    (hsize : p.roundConstants.size = Poseidon.fullRounds) {st : ProverState F} (a b : FVar F) :
    Grants F st (hash2Run p st a b)
      (Poseidon.RandomOracle.hash p [a.val st.env.toValuation, b.val st.env.toValuation]) := by
  have h := updateBlockRun_grants p hsize (st := st) (s := initState) (b := (a, b))
  show Grants F st ((updateBlockRun p st initState (a, b)).1,
    (updateBlockRun p st initState (a, b)).2.s0) _
  generalize updateBlockRun p st initState (a, b) = r at h ⊢
  have hr := h.read
  rw [readVal_initState] at hr
  simp only [readVal_prod, readVal_fvar, Prod.ext_iff] at hr
  exact Grants.fvar h.le (scoped_fvar_iff.mp (scoped_prod_iff.mp h.scope).1) (by
    rw [hr.1]
    simp [Poseidon.RandomOracle.hash, Poseidon.RandomOracle.update,
      Poseidon.RandomOracle.toBlocks, Poseidon.RandomOracle.chunk,
      Poseidon.RandomOracle.digest])

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

/-- The state and result of `hashVec`'s honest run: `update` from the fresh state,
slot 0. -/
def hashVecRun [Field F] (p : Poseidon.Params F) (st : ProverState F) (xs : List (FVar F)) :
    ProverState F × FVar F :=
  let r := updateRun p st initState xs
  (r.1, r.2.s0)

/-- `hashVec`'s honest run on in-scope inputs lands at `hashVecRun`. -/
theorem hashVec_run [Field F] [DecidableEq F] (p : Poseidon.Params F) {xs : List (FVar F)}
    (st : ProverState F) (hxs : ∀ x ∈ xs, x.Scoped st) :
    prove (Checker.holds (F := F) (c := KimchiConstraint F))
      (hashVec (c := KimchiConstraint F) p xs) st.nv st.env
      = .ok ((hashVecRun p st xs).1.out (hashVecRun p st xs).2) := by
  simp only [hashVec, hashVecRun, prove_bind, Except.bind,
    update_run p st (initState_scoped st) hxs]
  rfl

/-- `hashVecRun` reads as the value `hash` of the inputs' readings. -/
theorem hashVecRun_grants [Field F] (p : Poseidon.Params F)
    (hsize : p.roundConstants.size = Poseidon.fullRounds) {st : ProverState F}
    {xs : List (FVar F)} (hxs : ∀ x ∈ xs, x.Scoped st) :
    Grants F st (hashVecRun p st xs)
      (Poseidon.RandomOracle.hash p (xs.map (fun x => x.val st.env.toValuation))) := by
  have h := updateRun_grants p hsize (initState_scoped st) hxs
  show Grants F st ((updateRun p st initState xs).1, (updateRun p st initState xs).2.s0) _
  generalize updateRun p st initState xs = r at h ⊢
  have hr := h.read
  rw [readVal_initState] at hr
  simp only [readVal_prod, readVal_fvar, Prod.ext_iff] at hr
  exact Grants.fvar h.le (scoped_fvar_iff.mp (scoped_prod_iff.mp h.scope).1) (by
    rw [hr.1]
    simp [Poseidon.RandomOracle.hash, Poseidon.RandomOracle.digest])

end RandomOracle

end Snarky.Kimchi
