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

/-- The fresh state is in scope and reads as the value fresh state, at any table. -/
private theorem initState_readsAs [Field F] (st : ProverState F) :
    CircuitType.ReadsAs (val := SpongeStateVal F) st (initState (F := F))
      Poseidon.RandomOracle.initialState :=
  ⟨scoped_spongeState.mpr ⟨trivial, trivial, trivial⟩,
   by simp [initState, Poseidon.RandomOracle.initialState, CVar.val]⟩

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

open Std.Do in
/-- **Soundness** (`updateBlock`): the output state reads as one value block step —
`blockCipher` of `addBlock` at the state and block readings. -/
@[spec] private theorem updateBlock_spec {V : Valuation F} [Field F] [DecidableEq F]
    (p : Poseidon.Params F) (hsize : p.roundConstants.size = Poseidon.fullRounds)
    (st : SpongeState F) (b : FVar F × FVar F) :
    ⦃⌜True⌝⦄
    updateBlock (c := Builder V (KimchiConstraint F)) p st b
    ⦃⇓ r _ => ⌜CircuitType.readVal (val := SpongeStateVal F) V r
      = Poseidon.blockCipher p (Poseidon.RandomOracle.addBlock
          (CircuitType.readVal (val := SpongeStateVal F) V st)
          (CircuitType.readVal (val := F × F) V b))⌝⦄ := by
  obtain ⟨b0, b1⟩ := b
  simp only [updateBlock]
  have pspec := Poseidon.poseidon_spec (V := V) p hsize
  mvcgen [pspec] <;>
    simp_all [addBlockVar, Poseidon.RandomOracle.addBlock, CVar.val_add_]

open Std.Do in
/-- `updateBlock`'s state-relative completeness: the output state reads one value block step
at the entry readings. -/
private theorem Prover.updateBlock_spec [Field F] [DecidableEq F] (p : Poseidon.Params F)
    (hsize : p.roundConstants.size = Poseidon.fullRounds) (st : SpongeState F)
    (b : FVar F × FVar F) (st₀ : ProverState F) :
    ⦃fun s => ⌜s = st₀ ∧ CircuitType.Scoped (val := SpongeStateVal F) st₀ st ∧
      CircuitType.Scoped (val := F × F) st₀ b⌝⦄
    updateBlock (c := Prover (KimchiConstraint F)) p st b
    ⦃⇓ r s' => ⌜CircuitType.ReadsAs (val := SpongeStateVal F) s' r
        (Poseidon.blockCipher p (Poseidon.RandomOracle.addBlock
          (CircuitType.readVal (val := SpongeStateVal F) st₀.env.get st)
          (CircuitType.readVal (val := F × F) st₀.env.get b))) ∧ st₀ ≤ s'⌝⦄ := by
  obtain ⟨b0, b1⟩ := b
  unfold updateBlock
  mvcgen
  case vc1 =>
    rename_i _ h
    obtain ⟨rfl, hs, hb⟩ := h
    simp only [addBlockVar, scoped_spongeState, CircuitType.scoped_prod,
      CircuitType.scoped_fvar] at hs hb ⊢
    exact ⟨trivial, CVar.Scoped.add_ hs.1 hb.1, CVar.Scoped.add_ hs.2.1 hb.2, hs.2.2⟩
  case vc2 =>
    rename_i s₀ h₀ r s₁
    obtain ⟨rfl, -, -⟩ := h₀
    intro h
    obtain ⟨hr, hle⟩ := Prover.Reg.iff.mp h
    have hv : CircuitType.readVal (val := SpongeStateVal F) s₀.env.get (addBlockVar st (b0, b1))
        = Poseidon.RandomOracle.addBlock
          (CircuitType.readVal (val := SpongeStateVal F) s₀.env.get st)
          (CircuitType.readVal (val := F × F) s₀.env.get (b0, b1)) := by
      simp [addBlockVar, Poseidon.RandomOracle.addBlock, CVar.val_add_]
    exact ⟨by rwa [hv] at hr, hle⟩
  case vc3 => exact fun _ _ _ _ => hsize

attribute [irreducible] addBlockVar updateBlock

/-! ## The block fold -/

/-- Fold the input into the state block by block. -/
def update [Field F] [BasicSystem F c] [ConstraintHolds F c]
    [KimchiSystem F c] (p : Poseidon.Params F)
    (st : SpongeState F) (xs : List (FVar F)) :
    CircuitM F c (SpongeState F) :=
  (toBlocksVar xs).foldlM (updateBlock p) st

open Std.Do in
/-- The block fold is sound, generalized over the block list: the output state reads as
the value fold of the block readings. -/
private theorem foldBlocks_spec {V : Valuation F} [Field F] [DecidableEq F]
    (p : Poseidon.Params F) (hsize : p.roundConstants.size = Poseidon.fullRounds)
    (bs : List (FVar F × FVar F)) (st : SpongeState F) :
    ⦃⌜True⌝⦄
    bs.foldlM (updateBlock (c := Builder V (KimchiConstraint F)) p) st
    ⦃⇓ r _ => ⌜CircuitType.readVal (val := SpongeStateVal F) V r
      = (bs.map (CircuitType.readVal (val := F × F) V)).foldl
          (fun s b => Poseidon.blockCipher p (Poseidon.RandomOracle.addBlock s b))
          (CircuitType.readVal (val := SpongeStateVal F) V st)⌝⦄ := by
  have ub := updateBlock_spec (V := V) p hsize
  mvcgen [ub]
  case inv1 =>
    exact ⇓ q _ => ⌜CircuitType.readVal (val := SpongeStateVal F) V q.2
      = (q.1.prefix.map (CircuitType.readVal (val := F × F) V)).foldl
          (fun s b => Poseidon.blockCipher p (Poseidon.RandomOracle.addBlock s b))
          (CircuitType.readVal (val := SpongeStateVal F) V st)⌝
  all_goals simp_all

open Std.Do in
/-- **Soundness** (`update`): the output state reads as `Poseidon.RandomOracle.update`
of the state and input readings. -/
@[spec] theorem update_spec {V : Valuation F} [Field F] [DecidableEq F]
    (p : Poseidon.Params F) (hsize : p.roundConstants.size = Poseidon.fullRounds)
    (st : SpongeState F) (xs : List (FVar F)) :
    ⦃⌜True⌝⦄
    update (c := Builder V (KimchiConstraint F)) p st xs
    ⦃⇓ r _ => ⌜CircuitType.readVal (val := SpongeStateVal F) V r
      = Poseidon.RandomOracle.update p
          (CircuitType.readVal (val := SpongeStateVal F) V st)
          (xs.map (fun x => x.val V))⌝⦄ := by
  have h := foldBlocks_spec (V := V) p hsize (toBlocksVar xs) st
  rw [toBlocksVar_readVal] at h
  simpa only [update, Poseidon.RandomOracle.update] using h

open Std.Do in
/-- `update`'s state-relative completeness: the output state reads
`Poseidon.RandomOracle.update` of the entry readings, block by block. -/
theorem Prover.update_spec [Field F] [DecidableEq F] (p : Poseidon.Params F)
    (hsize : p.roundConstants.size = Poseidon.fullRounds) (st : SpongeState F)
    (xs : List (FVar F)) (st₀ : ProverState F) :
    ⦃fun s => ⌜s = st₀ ∧ CircuitType.Scoped (val := SpongeStateVal F) st₀ st ∧
      ∀ x ∈ xs, x.Scoped st₀⌝⦄
    update (c := Prover (KimchiConstraint F)) p st xs
    ⦃⇓ r s' => ⌜CircuitType.ReadsAs (val := SpongeStateVal F) s' r
        (Poseidon.RandomOracle.update p
          (CircuitType.readVal (val := SpongeStateVal F) st₀.env.get st) (xs.map st₀.read)) ∧
      st₀ ≤ s'⌝⦄ := by
  have hu := fun t b => Prover.register (Prover.updateBlock_spec p hsize t b)
  -- the blocks are in scope with the inputs: their readings are `toBlocksVar_readsAs`'s
  have hblocks : (∀ x ∈ xs, x.Scoped st₀) → ∀ b ∈ toBlocksVar xs,
      CircuitType.Scoped (val := F × F) st₀ b := fun hxs b hb =>
    ((List.forall₂_and_left _ _).mp (toBlocksVar_readsAs (st := st₀)
      (List.forall₂_map_right_iff.mpr (List.forall₂_same.mpr fun x hx =>
        ⟨CircuitType.scoped_fvar.mpr (hxs x hx), CircuitType.reads_fvar.mpr rfl⟩)))).1 b hb
  unfold update
  mvcgen [hu]
  case inv1 =>
    exact ⇓ q s => ⌜CircuitType.ReadsAs (val := SpongeStateVal F) s q.2
        ((q.1.prefix.map (CircuitType.readVal (val := F × F) st₀.env.get)).foldl
          (fun t b => Poseidon.blockCipher p (Poseidon.RandomOracle.addBlock t b))
          (CircuitType.readVal (val := SpongeStateVal F) st₀.env.get st)) ∧ st₀ ≤ s⌝
  case vc1 =>
    rename_i _ h
    obtain ⟨rfl, hs, -⟩ := h
    simp only [SPred.down_pure, List.map_nil, List.foldl_nil]
    exact ⟨⟨hs, reads_spongeState.mpr ⟨rfl, rfl, rfl⟩⟩, le_rfl⟩
  case vc2 =>
    rename_i _ _ r s
    intro h
    simp only [SPred.down_pure] at h
    obtain ⟨hr, hle⟩ := h
    rw [toBlocksVar_readVal] at hr
    exact ⟨by simpa only [Poseidon.RandomOracle.update] using hr, hle⟩
  case vc3 => simp
  case vc4 =>
    rename_i s₀ h₀ pref cur suff hbs b s hinv
    obtain ⟨rfl, -, hxs⟩ := h₀
    simp only [SPred.down_pure] at hinv
    obtain ⟨hb, hle⟩ := hinv
    exact ⟨trivial, hb.1, CircuitType.Scoped.mono (ProverState.nv_le_of_le hle)
      (hblocks hxs cur (by simp [hbs]))⟩
  -- one block: the fold's next step, at the block's reading carried from the entry table
  case vc5 =>
    rename_i s₀ h₀ pref cur suff hbs b s hinv r
    intro s' hpost
    simp only [SPred.down_pure] at hinv ⊢
    obtain ⟨rfl, -, hxs⟩ := h₀
    obtain ⟨hb, hle⟩ := hinv
    obtain ⟨hr, hle'⟩ := Prover.Reg.iff.mp hpost
    have hcur := hblocks hxs cur (by simp [hbs])
    obtain ⟨c0, c1⟩ := cur
    obtain ⟨h0, h1⟩ := CircuitType.scoped_prod.mp hcur
    have hcv : CircuitType.readVal (val := F × F) s.env.get (c0, c1)
        = CircuitType.readVal (val := F × F) s₀.env.get (c0, c1) := by
      simp only [CircuitType.readVal_prod, CircuitType.readVal_fvar,
        CVar.val_of_le hle (CircuitType.scoped_fvar.mp h0),
        CVar.val_of_le hle (CircuitType.scoped_fvar.mp h1)]
    rw [(CircuitType.reads_iff.mp hb.2).2, hcv] at hr
    refine ⟨?_, hle.trans hle'⟩
    simpa only [List.map_append, List.map_cons, List.map_nil, List.foldl_append,
      List.foldl_cons, List.foldl_nil] using hr

attribute [irreducible] update

/-! ## Hashing two elements -/

/-- Hash exactly two elements: one block, one permutation. -/
def hash2 [Field F] [BasicSystem F c] [ConstraintHolds F c]
    [KimchiSystem F c] (p : Poseidon.Params F)
    (a b : FVar F) : CircuitM F c (FVar F) := do
  let st ← updateBlock p initState (a, b)
  pure st.s0

open Std.Do in
/-- **Soundness** (`hash2`): the digest reads as the value `hash` of the two
readings. -/
@[spec] theorem hash2_spec {V : Valuation F} [Field F] [DecidableEq F]
    (p : Poseidon.Params F) (hsize : p.roundConstants.size = Poseidon.fullRounds)
    (a b : FVar F) :
    ⦃⌜True⌝⦄
    hash2 (c := Builder V (KimchiConstraint F)) p a b
    ⦃⇓ r _ => ⌜r.val V = Poseidon.RandomOracle.hash p [a.val V, b.val V]⌝⦄ := by
  simp only [hash2]
  have ub := updateBlock_spec (V := V) p hsize
  mvcgen [ub]
  rename_i r _ h
  have h1 := congrArg Prod.fst h
  simpa [Poseidon.RandomOracle.hash, Poseidon.RandomOracle.update,
    Poseidon.RandomOracle.toBlocks, Poseidon.RandomOracle.chunk,
    Poseidon.RandomOracle.digest, Poseidon.RandomOracle.initialState, initState,
    CVar.val] using h1

open Std.Do in
/-- `hash2`'s state-relative completeness: the digest reads `Poseidon.RandomOracle.hash` of
the two entry readings. -/
theorem Prover.hash2_spec [Field F] [DecidableEq F] (p : Poseidon.Params F)
    (hsize : p.roundConstants.size = Poseidon.fullRounds) (a b : FVar F)
    (st₀ : ProverState F) :
    ⦃fun s => ⌜s = st₀ ∧ a.Scoped st₀ ∧ b.Scoped st₀⌝⦄
    hash2 (c := Prover (KimchiConstraint F)) p a b
    ⦃⇓ r s' => ⌜r.Scoped s' ∧
      s'.read r = Poseidon.RandomOracle.hash p [st₀.read a, st₀.read b] ∧ st₀ ≤ s'⌝⦄ := by
  have hu := fun t c => Prover.register (Prover.updateBlock_spec p hsize t c)
  unfold hash2
  mvcgen [hu]
  case vc1 =>
    rename_i _ h
    obtain ⟨rfl, ha, hb⟩ := h
    exact ⟨trivial, (initState_readsAs _).1,
      CircuitType.scoped_prod.mpr ⟨CircuitType.scoped_fvar.mpr ha, CircuitType.scoped_fvar.mpr hb⟩⟩
  case vc2 =>
    rename_i s₀ h₀ r s₁ h₁
    obtain ⟨rfl, -, -⟩ := h₀
    obtain ⟨hr, hle⟩ := Prover.Reg.iff.mp h₁
    simp only [CircuitType.ReadsAs, scoped_spongeState, reads_spongeState] at hr
    refine ⟨hr.1.1, ?_, hle⟩
    rw [ProverState.read, hr.2.1]
    simp [Poseidon.RandomOracle.hash, Poseidon.RandomOracle.update,
      Poseidon.RandomOracle.toBlocks, Poseidon.RandomOracle.chunk,
      Poseidon.RandomOracle.digest, Poseidon.RandomOracle.initialState, initState, CVar.val]

attribute [irreducible] hash2

/-! ## Hashing a list -/

/-- Hash a list: `update` the fresh state, read slot 0. -/
def hashVec [Field F] [BasicSystem F c] [ConstraintHolds F c]
    [KimchiSystem F c] (p : Poseidon.Params F)
    (xs : List (FVar F)) : CircuitM F c (FVar F) := do
  let st ← update p initState xs
  pure st.s0

open Std.Do in
/-- **Soundness** (`hashVec`): the digest reads as the value `hash` of the input
readings. -/
@[spec] theorem hashVec_spec {V : Valuation F} [Field F] [DecidableEq F]
    (p : Poseidon.Params F) (hsize : p.roundConstants.size = Poseidon.fullRounds)
    (xs : List (FVar F)) :
    ⦃⌜True⌝⦄
    hashVec (c := Builder V (KimchiConstraint F)) p xs
    ⦃⇓ r _ => ⌜r.val V = Poseidon.RandomOracle.hash p (xs.map (fun x => x.val V))⌝⦄ := by
  simp only [hashVec]
  have uspec := update_spec (V := V) p hsize
  mvcgen [uspec]
  rename_i r _ h
  have h1 := congrArg Prod.fst h
  simpa [Poseidon.RandomOracle.hash, Poseidon.RandomOracle.digest,
    Poseidon.RandomOracle.initialState, initState, CVar.val] using h1

open Std.Do in
/-- `hashVec`'s state-relative completeness: the digest reads `Poseidon.RandomOracle.hash` of
the entry readings. -/
theorem Prover.hashVec_spec [Field F] [DecidableEq F] (p : Poseidon.Params F)
    (hsize : p.roundConstants.size = Poseidon.fullRounds) (xs : List (FVar F))
    (st₀ : ProverState F) :
    ⦃fun s => ⌜s = st₀ ∧ ∀ x ∈ xs, x.Scoped st₀⌝⦄
    hashVec (c := Prover (KimchiConstraint F)) p xs
    ⦃⇓ r s' => ⌜r.Scoped s' ∧
      s'.read r = Poseidon.RandomOracle.hash p (xs.map st₀.read) ∧ st₀ ≤ s'⌝⦄ := by
  have hu := fun t ys => Prover.register (Prover.update_spec p hsize t ys)
  unfold hashVec
  mvcgen [hu]
  case vc1 =>
    rename_i _ h
    obtain ⟨rfl, hxs⟩ := h
    exact ⟨trivial, (initState_readsAs _).1, hxs⟩
  case vc2 =>
    rename_i s₀ h₀ r s₁ h₁
    obtain ⟨rfl, -⟩ := h₀
    obtain ⟨hr, hle⟩ := Prover.Reg.iff.mp h₁
    have hinit : CircuitType.readVal (val := SpongeStateVal F) s₀.env.get (initState (F := F))
        = Poseidon.RandomOracle.initialState :=
      (CircuitType.reads_iff.mp (initState_readsAs s₀).2).2
    rw [hinit] at hr
    simp only [CircuitType.ReadsAs, scoped_spongeState, reads_spongeState] at hr
    refine ⟨hr.1.1, ?_, hle⟩
    rw [ProverState.read, hr.2.1]
    simp [Poseidon.RandomOracle.hash, Poseidon.RandomOracle.digest]

attribute [irreducible] hashVec

end RandomOracle

end Snarky.Kimchi
