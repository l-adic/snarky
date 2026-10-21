import Snarky.Kimchi.Circuit.Poseidon
import Poseidon.RandomOracle

/-!
# The in-circuit block-mode hash

Transcribes packages/random-oracle/src/Snarky/Circuit/RandomOracle.purs, the circuit twin of
`Poseidon.RandomOracle`: chunk the input into rate-2 blocks (constant-zero pads, one zero
block for empty input), add each block into the state and permute, read slot 0. Unlike the
in-circuit duplex sponge nothing is sealed: blocks feed bare `CVar.add_` sums straight into
the `poseidon` gadget.

Chunking is metadata (list structure over `FVar`s), so hashing `n` variables emits only the
`poseidon` blocks: `⌈n/2⌉` of them, or one for `n = 0`.

The state is the gadget's `SpongeState` and blocks are pairs; input lists are read
entrywise by `List.Forall₂`. The upstream digest newtype and hashing classes are not
ported: digests are bare `FVar`s.
-/

namespace Snarky.Kimchi

open Snarky

variable {F c : Type}

namespace RandomOracle

/-! ## The block decomposition

Metadata: no rows. Each piece matches its `Poseidon.RandomOracle` counterpart twice: at the
total reading, for soundness, and at `CircuitType.ReadsAs`, for completeness. -/

/-- The fresh state: constant-zero cells. -/
private def initState [Zero F] : SpongeState F :=
  ⟨.const 0, .const 0, .const 0⟩

/-- `Poseidon.RandomOracle.chunk` over circuit variables: rate-2 chunks, constant-zero
odd-tail pad. -/
private def chunkVar [Zero F] : List (FVar F) → List (FVar F × FVar F)
  | [] => []
  | [x] => [(x, .const 0)]
  | x :: y :: rest => (x, y) :: chunkVar rest

/-- `Poseidon.RandomOracle.toBlocks` over circuit variables: one constant-zero block for
empty input, `chunkVar` otherwise. -/
private def toBlocksVar [Zero F] : List (FVar F) → List (FVar F × FVar F)
  | [] => [(.const 0, .const 0)]
  | xs => chunkVar xs

/-- Add a block into the rate slots: bare `CVar.add_` sums, no seal. -/
private def addBlockVar [Add F] (st : SpongeState F) (b : FVar F × FVar F) :
    SpongeState F :=
  ⟨CVar.add_ st.s0 b.1, CVar.add_ st.s1 b.2, st.s2⟩

/-- The circuit chunking reads as the value chunking. -/
private theorem chunkVar_readVal [Field F] (V : Valuation F) :
    ∀ xs : List (FVar F),
      (chunkVar xs).map (CircuitType.readVal (val := F × F) V)
        = Poseidon.RandomOracle.chunk (xs.map (fun x => x.val V))
  | [] => rfl
  | [x] => by
    simp [chunkVar, Poseidon.RandomOracle.chunk, CVar.val]
  | x :: y :: rest => by
    simp only [chunkVar, Poseidon.RandomOracle.chunk, List.map_cons,
      chunkVar_readVal V rest, CircuitType.readVal_prod, CircuitType.readVal_fvar]

/-- The circuit block decomposition reads as the value block decomposition. -/
private theorem toBlocksVar_readVal [Field F] (V : Valuation F) :
    ∀ xs : List (FVar F),
      (toBlocksVar xs).map (CircuitType.readVal (val := F × F) V)
        = Poseidon.RandomOracle.toBlocks (xs.map (fun x => x.val V))
  | [] => by simp [toBlocksVar, Poseidon.RandomOracle.toBlocks, CVar.val]
  | [x] => chunkVar_readVal V [x]
  | x :: y :: rest => chunkVar_readVal V (x :: y :: rest)

/-- Read inputs chunk to read blocks; the constant pads read as the value pads. -/
private theorem chunkVar_readsAs [Field F] {st : ProverState F} :
    ∀ {xs : List (FVar F)} {vs : List F},
      List.Forall₂ (CircuitType.ReadsAs (val := F) st) xs vs →
        List.Forall₂ (CircuitType.ReadsAs (val := F × F) st) (chunkVar xs)
          (Poseidon.RandomOracle.chunk vs)
  | [], _, h => by cases h; exact .nil
  | [x], _, h => by
    cases h with
    | cons hx hrest =>
      cases hrest
      refine .cons ⟨CircuitType.scoped_prod.mpr
        ⟨hx.1, CircuitType.scoped_fvar.mpr trivial⟩,
        CircuitType.reads_prod.mpr ⟨hx.2, CircuitType.reads_fvar.mpr rfl⟩⟩ .nil
  | x :: y :: rest, _, h => by
    cases h with
    | cons hx h2 =>
      cases h2 with
      | cons hy hrest =>
        exact .cons ⟨CircuitType.scoped_prod.mpr ⟨hx.1, hy.1⟩,
          CircuitType.reads_prod.mpr ⟨hx.2, hy.2⟩⟩ (chunkVar_readsAs hrest)

/-- Read inputs decompose to read blocks. -/
private theorem toBlocksVar_readsAs [Field F] {st : ProverState F}
    {xs : List (FVar F)} {vs : List F}
    (h : List.Forall₂ (CircuitType.ReadsAs (val := F) st) xs vs) :
    List.Forall₂ (CircuitType.ReadsAs (val := F × F) st) (toBlocksVar xs)
      (Poseidon.RandomOracle.toBlocks vs) := by
  cases h with
  | nil =>
    exact .cons ⟨CircuitType.scoped_prod.mpr
      ⟨CircuitType.scoped_fvar.mpr trivial, CircuitType.scoped_fvar.mpr trivial⟩,
      CircuitType.reads_prod.mpr
        ⟨CircuitType.reads_fvar.mpr rfl, CircuitType.reads_fvar.mpr rfl⟩⟩ .nil
  | @cons x v xs' vs' hx hrest =>
    show List.Forall₂ _ (chunkVar (x :: xs')) (Poseidon.RandomOracle.chunk (v :: vs'))
    exact chunkVar_readsAs (.cons hx hrest)

attribute [irreducible] chunkVar toBlocksVar

/-! ## One block -/

/-- Absorb one block: add into the rate slots, permute. -/
private def updateBlock [Field F] [BasicSystem F c] [ConstraintHolds F c] [KimchiSystem F c]
    (p : Poseidon.Params F) (st : SpongeState F) (b : FVar F × FVar F) :
    CircuitM F c (SpongeState F) :=
  poseidon p (addBlockVar st b)

open Std.WP in
/-- **Soundness** (`updateBlock`): the output state reads as one value block step —
`blockCipher` of `addBlock` at the state and block readings. -/
@[spec] private theorem updateBlock_spec {V : Valuation F} [Field F] [DecidableEq F]
    (p : Poseidon.Params F) (hsize : p.roundConstants.size = Poseidon.fullRounds)
    (st : SpongeState F) (b : FVar F × FVar F) :
    ⦃fun _ => True⦄
    updateBlock (c := Builder V (KimchiConstraint F)) p st b
    ⦃fun r _ => CircuitType.readVal (val := SpongeStateVal F) V r
      = Poseidon.blockCipher p (Poseidon.RandomOracle.addBlock
          (CircuitType.readVal (val := SpongeStateVal F) V st)
          (CircuitType.readVal (val := F × F) V b))⦄ := by
  obtain ⟨b0, b1⟩ := b
  simp only [updateBlock]
  have pspec := Poseidon.poseidon_spec (V := V) p hsize
  vcgen [pspec] <;>
    simp_all [addBlockVar, Poseidon.RandomOracle.addBlock, CVar.val_add_]

attribute [irreducible] addBlockVar updateBlock

/-! ## The block fold -/

/-- Fold the input into the state block by block. -/
def update [Field F] [BasicSystem F c] [ConstraintHolds F c]
    [KimchiSystem F c] (p : Poseidon.Params F)
    (st : SpongeState F) (xs : List (FVar F)) :
    CircuitM F c (SpongeState F) :=
  (toBlocksVar xs).foldlM (updateBlock p) st

open Std.WP in
/-- The block fold is sound, generalized over the block list: the output state reads as
the value fold of the block readings. -/
private theorem foldBlocks_spec {V : Valuation F} [Field F] [DecidableEq F]
    (p : Poseidon.Params F) (hsize : p.roundConstants.size = Poseidon.fullRounds)
    (bs : List (FVar F × FVar F)) (st : SpongeState F) :
    ⦃fun _ => True⦄
    bs.foldlM (updateBlock (c := Builder V (KimchiConstraint F)) p) st
    ⦃fun r _ => CircuitType.readVal (val := SpongeStateVal F) V r
      = (bs.map (CircuitType.readVal (val := F × F) V)).foldl
          (fun s b => Poseidon.blockCipher p (Poseidon.RandomOracle.addBlock s b))
          (CircuitType.readVal (val := SpongeStateVal F) V st)⦄ := by
  have ub := updateBlock_spec (V := V) p hsize
  vcgen [ub] invariants
  · fun pref _ q _ => CircuitType.readVal (val := SpongeStateVal F) V q
      = (pref.map (CircuitType.readVal (val := F × F) V)).foldl
          (fun s b => Poseidon.blockCipher p (Poseidon.RandomOracle.addBlock s b))
          (CircuitType.readVal (val := SpongeStateVal F) V st)
  all_goals simp_all

open Std.WP in
/-- **Soundness** (`update`): the output state reads as `Poseidon.RandomOracle.update`
of the state and input readings. -/
@[spec] theorem update_spec {V : Valuation F} [Field F] [DecidableEq F]
    (p : Poseidon.Params F) (hsize : p.roundConstants.size = Poseidon.fullRounds)
    (st : SpongeState F) (xs : List (FVar F)) :
    ⦃fun _ => True⦄
    update (c := Builder V (KimchiConstraint F)) p st xs
    ⦃fun r _ => CircuitType.readVal (val := SpongeStateVal F) V r
      = Poseidon.RandomOracle.update p
          (CircuitType.readVal (val := SpongeStateVal F) V st)
          (xs.map (fun x => x.val V))⦄ := by
  have h := foldBlocks_spec (V := V) p hsize (toBlocksVar xs) st
  rw [toBlocksVar_readVal] at h
  simpa only [update, Poseidon.RandomOracle.update] using h

attribute [irreducible] update

/-! ## Hashing two elements -/

/-- Hash exactly two elements: one block, one permutation. -/
def hash2 [Field F] [BasicSystem F c] [ConstraintHolds F c]
    [KimchiSystem F c] (p : Poseidon.Params F)
    (a b : FVar F) : CircuitM F c (FVar F) := do
  let st ← updateBlock p initState (a, b)
  pure st.s0

open Std.WP in
/-- **Soundness** (`hash2`): the digest reads as the value `hash` of the two
readings. -/
@[spec] theorem hash2_spec {V : Valuation F} [Field F] [DecidableEq F]
    (p : Poseidon.Params F) (hsize : p.roundConstants.size = Poseidon.fullRounds)
    (a b : FVar F) :
    ⦃fun _ => True⦄
    hash2 (c := Builder V (KimchiConstraint F)) p a b
    ⦃fun r _ => r.val V = Poseidon.RandomOracle.hash p [a.val V, b.val V]⦄ := by
  simp only [hash2]
  have ub := updateBlock_spec (V := V) p hsize
  vcgen [ub]
  rename_i r _ h
  have h1 := congrArg Prod.fst h
  simpa [Poseidon.RandomOracle.hash, Poseidon.RandomOracle.update,
    Poseidon.RandomOracle.toBlocks, Poseidon.RandomOracle.chunk,
    Poseidon.RandomOracle.digest, Poseidon.RandomOracle.initialState, initState,
    CVar.val] using h1

attribute [irreducible] hash2

/-! ## Hashing a list -/

/-- Hash a list: `update` the fresh state, read slot 0. -/
def hashVec [Field F] [BasicSystem F c] [ConstraintHolds F c]
    [KimchiSystem F c] (p : Poseidon.Params F)
    (xs : List (FVar F)) : CircuitM F c (FVar F) := do
  let st ← update p initState xs
  pure st.s0

open Std.WP in
/-- **Soundness** (`hashVec`): the digest reads as the value `hash` of the input
readings. -/
@[spec] theorem hashVec_spec {V : Valuation F} [Field F] [DecidableEq F]
    (p : Poseidon.Params F) (hsize : p.roundConstants.size = Poseidon.fullRounds)
    (xs : List (FVar F)) :
    ⦃fun _ => True⦄
    hashVec (c := Builder V (KimchiConstraint F)) p xs
    ⦃fun r _ => r.val V = Poseidon.RandomOracle.hash p (xs.map (fun x => x.val V))⦄ := by
  simp only [hashVec]
  have uspec := update_spec (V := V) p hsize
  vcgen [uspec]
  rename_i r _ h
  have h1 := congrArg Prod.fst h
  simpa [Poseidon.RandomOracle.hash, Poseidon.RandomOracle.digest,
    Poseidon.RandomOracle.initialState, initState, CVar.val] using h1

attribute [irreducible] hashVec

/-! ## The completeness laws

Each gadget's law at the prover's reading (`Snarky.Prover.VCGen`): the state's and the inputs'
readings in, the result's reading out, the values as parameters. The block fold is proved by
induction on the blocks, the others by composition through the laws of the gadgets they call. -/

section ProverReading

open Snarky.Prover Std.WP

/-- A state reads a triple exactly when its cells are in scope and read the components. -/
private theorem Prover.reads_spongeState_apply [Field F] (s : SpongeState F)
    (v : SpongeStateVal F) (st : ProverState F) :
    Reads s v st ↔ s.s0.Scoped st ∧ s.s1.Scoped st ∧ s.s2.Scoped st ∧
      s.s0.val st.env.get = v.1 ∧ s.s1.val st.env.get = v.2.1 ∧
        s.s2.val st.env.get = v.2.2 := by
  change CircuitType.ReadsAs st s v ↔ _
  simp only [CircuitType.ReadsAs, scoped_spongeState, reads_spongeState, and_assoc]

/-- Read inputs decompose to read blocks. -/
private theorem Prover.toBlocksVar_reads [Field F] (xs : List (FVar F)) (vs : List F) :
    All₂ (Reads (F := F)) xs vs ≤
      All₂ (Reads (F := F)) (toBlocksVar xs) (Poseidon.RandomOracle.toBlocks vs) := by
  intro st h
  change All₂ (Reads (F := F)) xs vs st at h
  change All₂ (Reads (F := F)) (toBlocksVar xs) (Poseidon.RandomOracle.toBlocks vs) st
  rw [All₂.apply] at h ⊢
  exact toBlocksVar_readsAs h

/-- `updateBlock`'s completeness: the output state reads `Poseidon.blockCipher` of
`Poseidon.RandomOracle.addBlock` at the state's and the block's readings. -/
private theorem Prover.updateBlock_spec [Field F] [DecidableEq F] (p : Poseidon.Params F)
    (hsize : p.roundConstants.size = Poseidon.fullRounds) (st : SpongeState F)
    (b : FVar F × FVar F) (v : SpongeStateVal F) (w : F × F) :
    ⦃Reads st v ⊓ Reads b w⦄ updateBlock (c := Prover (KimchiConstraint F)) p st b
    ⦃fun r ↦ Reads (val := SpongeStateVal F) r
      (Poseidon.blockCipher p (Poseidon.RandomOracle.addBlock v w))⦄ := by
  have hp := Poseidon.Prover.poseidon_spec p hsize (addBlockVar st b)
    (Poseidon.RandomOracle.addBlock v w)
  unfold updateBlock
  vcgen [hp]
  all_goals prover_assert with
    (intros; simp_all [Prover.reads_spongeState_apply, Reads.prod_apply, Reads.fvar_apply,
      addBlockVar, Poseidon.RandomOracle.addBlock, CVar.val_add_, CVar.Scoped.add_])

/-- The block fold's completeness, generalized over the block list: the output state reads the
value fold of the blocks' readings. -/
private theorem Prover.foldBlocks_spec [Field F] [DecidableEq F] (p : Poseidon.Params F)
    (hsize : p.roundConstants.size = Poseidon.fullRounds) :
    ∀ (bs : List (FVar F × FVar F)) (ws : List (F × F)) (st : SpongeState F)
      (v : SpongeStateVal F),
      ⦃Reads st v ⊓ All₂ Reads bs ws⦄
      bs.foldlM (updateBlock (c := Prover (KimchiConstraint F)) p) st
      ⦃fun r ↦ Reads (val := SpongeStateVal F) r
        (ws.foldl (fun (s : Poseidon.Triple F) w ↦
          Poseidon.blockCipher p (Poseidon.RandomOracle.addBlock s w)) v)⦄ := by
  intro bs
  induction bs with
  | nil =>
    intro ws st v
    cases ws with
    | nil =>
      simp only [List.foldlM_nil, List.foldl_nil]
      vcgen
      all_goals prover_assert
    | cons w ws =>
      simp only [All₂, inf_bot_eq]
      exact ⟨fun _ h ↦ h.elim⟩
  | cons b bs ih =>
    intro ws st v
    cases ws with
    | nil =>
      simp only [All₂, inf_bot_eq]
      exact ⟨fun _ h ↦ h.elim⟩
    | cons w ws =>
      have hs := Prover.updateBlock_spec p hsize st b v w
      have ht := fun st' ↦ ih ws st' (Poseidon.blockCipher p (Poseidon.RandomOracle.addBlock v w))
      simp only [List.foldlM_cons, List.foldl_cons, All₂]
      vcgen [hs, ht]
      all_goals prover_assert

/-- `update`'s completeness: the output state reads `Poseidon.RandomOracle.update` of the state's
and the inputs' readings. -/
theorem Prover.update_spec [Field F] [DecidableEq F] (p : Poseidon.Params F)
    (hsize : p.roundConstants.size = Poseidon.fullRounds) (st : SpongeState F)
    (xs : List (FVar F)) (v : SpongeStateVal F) (vs : List F) :
    ⦃Reads st v ⊓ All₂ Reads xs vs⦄ update (c := Prover (KimchiConstraint F)) p st xs
    ⦃fun r ↦ Reads (val := SpongeStateVal F) r (Poseidon.RandomOracle.update p v vs)⦄ := by
  have hf := Prover.foldBlocks_spec p hsize (toBlocksVar xs)
    (Poseidon.RandomOracle.toBlocks vs) st v
  have hb := (Pred.le_iff _ _).mp (Prover.toBlocksVar_reads xs vs)
  unfold update
  simp only [Poseidon.RandomOracle.update]
  vcgen [hf]
  all_goals prover_assert

/-- `hash2`'s completeness: the digest reads `Poseidon.RandomOracle.hash` of the two operands'
readings. -/
theorem Prover.hash2_spec [Field F] [DecidableEq F] (p : Poseidon.Params F)
    (hsize : p.roundConstants.size = Poseidon.fullRounds) (a b : FVar F) (u w : F) :
    ⦃Reads a u ⊓ Reads b w⦄ hash2 (c := Prover (KimchiConstraint F)) p a b
    ⦃fun r ↦ Reads r (Poseidon.RandomOracle.hash p [u, w])⦄ := by
  have hu := Prover.updateBlock_spec p hsize initState (a, b)
    Poseidon.RandomOracle.initialState (u, w)
  unfold hash2
  vcgen [hu]
  all_goals prover_assert with
    (intros; simp_all [Prover.reads_spongeState_apply, Reads.prod_apply, Reads.fvar_apply,
      initState, Poseidon.RandomOracle.hash, Poseidon.RandomOracle.update,
      Poseidon.RandomOracle.toBlocks, Poseidon.RandomOracle.chunk,
      Poseidon.RandomOracle.digest, Poseidon.RandomOracle.initialState, CVar.val])

/-- `hashVec`'s completeness: the digest reads `Poseidon.RandomOracle.hash` of the inputs'
readings. -/
theorem Prover.hashVec_spec [Field F] [DecidableEq F] (p : Poseidon.Params F)
    (hsize : p.roundConstants.size = Poseidon.fullRounds) (xs : List (FVar F)) (vs : List F) :
    ⦃All₂ Reads xs vs⦄ hashVec (c := Prover (KimchiConstraint F)) p xs
    ⦃fun r ↦ Reads r (Poseidon.RandomOracle.hash p vs)⦄ := by
  have hu := Prover.update_spec p hsize initState xs Poseidon.RandomOracle.initialState vs
  unfold hashVec
  vcgen [hu]
  all_goals prover_assert with
    (intros; simp_all [Prover.reads_spongeState_apply, Reads.fvar_apply, initState,
      Poseidon.RandomOracle.hash, Poseidon.RandomOracle.digest,
      Poseidon.RandomOracle.initialState, CVar.val])

end ProverReading

end RandomOracle

end Snarky.Kimchi
