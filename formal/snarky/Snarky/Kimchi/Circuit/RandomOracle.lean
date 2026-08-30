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
`toBlocks`/`chunk`/`addBlock`. The state is the gadget's `SpongeState` and blocks are
pairs, both read by their `CircuitType` instances; a list of operands is read entrywise
by `List.Forall₂`.

Deviations from the PS original:
- PS's ambient `PoseidonField` class arrives as the explicit `p : Poseidon.Params F`.
- PS's width-3 / width-2 `Vector`s render as `SpongeState` and the pair; PS `Array`
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

/-! ## The block decomposition

Metadata: no rows. Each piece is aligned with its `Poseidon.RandomOracle` counterpart
twice — at the total reading, which soundness quotes, and at `CircuitType.ReadsAs`,
which completeness carries. -/

/-- The fresh state (PS `initialState`, unexported there): constant-zero cells. -/
private def initState [Zero F] : SpongeState F :=
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
private def addBlockVar [Add F] (st : SpongeState F) (b : FVar F × FVar F) :
    SpongeState F :=
  ⟨CVar.add_ st.s0 b.1, CVar.add_ st.s1 b.2, st.s2⟩

/-- The fresh state is in scope and reads as the value fresh state, at any table. -/
private theorem initState_readsAs [Field F] (st : ProverState F) :
    CircuitType.ReadsAs (val := Poseidon.Triple F) st (initState (F := F))
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

/-- Read inputs chunk to read blocks: the constant pads read as the value pads. -/
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

/-- Absorb one block (PS `updateBlock`): add into the rate slots, permute. -/
private def updateBlock [Field F] [BasicSystem F c] [KimchiSystem F c]
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
    ⦃⇓ r _ => ⌜CircuitType.readVal (val := Poseidon.Triple F) V r
      = Poseidon.blockCipher p (Poseidon.RandomOracle.addBlock
          (CircuitType.readVal (val := Poseidon.Triple F) V st)
          (CircuitType.readVal (val := F × F) V b))⌝⦄ := by
  obtain ⟨b0, b1⟩ := b
  simp only [updateBlock]
  have pspec := Poseidon.poseidon_spec (V := V) p hsize
  mvcgen [pspec] <;>
    simp_all [addBlockVar, Poseidon.RandomOracle.addBlock, CVar.val_add_]

/-- **Completeness** (`updateBlock`): the honest run accepts on a read state and block,
and the output reads back the value block step. -/
private theorem updateBlock_complete [Field F] [DecidableEq F] (p : Poseidon.Params F)
    (hsize : p.roundConstants.size = Poseidon.fullRounds) (st : SpongeState F)
    (b : FVar F × FVar F) (sv : Poseidon.Triple F) (bv : F × F) :
    Complete (F := F) (c := KimchiConstraint F)
      (fun s => CircuitType.ReadsAs (val := Poseidon.Triple F) s st sv ∧
        CircuitType.ReadsAs (val := F × F) s b bv)
      (updateBlock (c := KimchiConstraint F) p st b)
      (fun r s' => CircuitType.ReadsAs (val := Poseidon.Triple F) s' r
        (Poseidon.blockCipher p (Poseidon.RandomOracle.addBlock sv bv))) := by
  obtain ⟨b0, b1⟩ := b
  obtain ⟨bv0, bv1⟩ := bv
  refine Complete.imp (fun _ h => ?_) (fun _ _ h => h)
    (Poseidon.poseidon_complete p hsize (addBlockVar st (b0, b1))
      (Poseidon.RandomOracle.addBlock sv (bv0, bv1)))
  obtain ⟨hst, hb⟩ := h
  simp only [CircuitType.ReadsAs, scoped_spongeState, reads_spongeState,
    CircuitType.scoped_prod, CircuitType.reads_prod, CircuitType.scoped_fvar,
    CircuitType.reads_fvar] at hst hb
  obtain ⟨⟨hs0, hs1, hs2⟩, hv0, hv1, hv2⟩ := hst
  obtain ⟨⟨hb0, hb1⟩, hbv0, hbv1⟩ := hb
  refine ⟨?_, ?_⟩
  · refine scoped_spongeState.mpr ⟨CVar.ScopedBy.add_ hs0 hb0,
      CVar.ScopedBy.add_ hs1 hb1, hs2⟩
  · refine reads_spongeState.mpr ⟨?_, ?_, hv2⟩
    · simp only [addBlockVar, CVar.val_add_, hv0, hbv0]; rfl
    · simp only [addBlockVar, CVar.val_add_, hv1, hbv1]; rfl

attribute [irreducible] addBlockVar updateBlock

/-! ## The block fold -/

/-- Fold the input into the state block by block (PS `update`). -/
def update [Field F] [BasicSystem F c] [KimchiSystem F c] (p : Poseidon.Params F)
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
    ⦃⇓ r _ => ⌜CircuitType.readVal (val := Poseidon.Triple F) V r
      = (bs.map (CircuitType.readVal (val := F × F) V)).foldl
          (fun s b => Poseidon.blockCipher p (Poseidon.RandomOracle.addBlock s b))
          (CircuitType.readVal (val := Poseidon.Triple F) V st)⌝⦄ := by
  have ub := updateBlock_spec (V := V) p hsize
  mvcgen [ub]
  case inv1 =>
    exact ⇓ q _ => ⌜CircuitType.readVal (val := Poseidon.Triple F) V q.2
      = (q.1.prefix.map (CircuitType.readVal (val := F × F) V)).foldl
          (fun s b => Poseidon.blockCipher p (Poseidon.RandomOracle.addBlock s b))
          (CircuitType.readVal (val := Poseidon.Triple F) V st)⌝
  all_goals simp_all

/-- The block fold is complete, generalized over the block list: the honest run accepts
on a read state and read blocks, and the output reads back the value fold. -/
private theorem foldBlocks_complete [Field F] [DecidableEq F] (p : Poseidon.Params F)
    (hsize : p.roundConstants.size = Poseidon.fullRounds) :
    ∀ (bs : List (FVar F × FVar F)) (bvs : List (F × F)) (st : SpongeState F)
      (sv : Poseidon.Triple F),
      Complete (F := F) (c := KimchiConstraint F)
        (fun s => CircuitType.ReadsAs (val := Poseidon.Triple F) s st sv ∧
          List.Forall₂ (CircuitType.ReadsAs (val := F × F) s) bs bvs)
        (bs.foldlM (updateBlock (c := KimchiConstraint F) p) st)
        (fun r s' => CircuitType.ReadsAs (val := Poseidon.Triple F) s' r
          (bvs.foldl (fun t b => Poseidon.blockCipher p
            (Poseidon.RandomOracle.addBlock t b)) sv))
  | [], bvs, st, sv => by
    simp only [List.foldlM_nil]
    cases bvs with
    | nil =>
      exact Complete.imp (fun _ h => h.1) (fun _ _ h => h) (Complete.pure_of fun _ h => h)
    | cons _ _ => exact Complete.of_false fun _ h => by simp at h
  | b :: bs, bvs, st, sv => by
    simp only [List.foldlM_cons]
    cases bvs with
    | nil => exact Complete.of_false fun _ h => by simp at h
    | cons bv bvs =>
      simp only [List.foldl_cons]
      exact Complete.bind
        (Complete.imp (fun _ h => ⟨⟨h.1, (List.forall₂_cons.mp h.2).1⟩,
            (List.forall₂_cons.mp h.2).2⟩) (fun _ _ h => h)
          (Complete.frame Mono.forall₂ (updateBlock_complete p hsize st b sv bv)))
        fun r => foldBlocks_complete p hsize bs bvs r _

open Std.Do in
/-- **Soundness** (`update`): the output state reads as `Poseidon.RandomOracle.update`
of the state and input readings. -/
@[spec] theorem update_spec {V : Valuation F} [Field F] [DecidableEq F]
    (p : Poseidon.Params F) (hsize : p.roundConstants.size = Poseidon.fullRounds)
    (st : SpongeState F) (xs : List (FVar F)) :
    ⦃⌜True⌝⦄
    update (c := Builder V (KimchiConstraint F)) p st xs
    ⦃⇓ r _ => ⌜CircuitType.readVal (val := Poseidon.Triple F) V r
      = Poseidon.RandomOracle.update p
          (CircuitType.readVal (val := Poseidon.Triple F) V st)
          (xs.map (fun x => x.val V))⌝⦄ := by
  have h := foldBlocks_spec (V := V) p hsize (toBlocksVar xs) st
  rw [toBlocksVar_readVal] at h
  simpa only [update, Poseidon.RandomOracle.update] using h

/-- **Completeness** (`update`): the honest run accepts on a read state and read
inputs, and the output reads back `Poseidon.RandomOracle.update` of their values. -/
theorem update_complete [Field F] [DecidableEq F] (p : Poseidon.Params F)
    (hsize : p.roundConstants.size = Poseidon.fullRounds) (st : SpongeState F)
    (xs : List (FVar F)) (sv : Poseidon.Triple F) (vs : List F) :
    Complete (F := F) (c := KimchiConstraint F)
      (fun s => CircuitType.ReadsAs (val := Poseidon.Triple F) s st sv ∧
        List.Forall₂ (CircuitType.ReadsAs (val := F) s) xs vs)
      (update (c := KimchiConstraint F) p st xs)
      (fun r s' => CircuitType.ReadsAs (val := Poseidon.Triple F) s' r
        (Poseidon.RandomOracle.update p sv vs)) := by
  simp only [update, Poseidon.RandomOracle.update]
  exact Complete.imp (fun _ h => ⟨h.1, toBlocksVar_readsAs h.2⟩) (fun _ _ h => h)
    (foldBlocks_complete p hsize (toBlocksVar xs) _ st sv)

attribute [irreducible] update

/-! ## Hashing two elements -/

/-- Hash exactly two elements (PS `hash2`): one block, one permutation. -/
def hash2 [Field F] [BasicSystem F c] [KimchiSystem F c] (p : Poseidon.Params F)
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

/-- **Completeness** (`hash2`): the honest run accepts on read operands, and the digest
reads back the value `hash` of their values. -/
theorem hash2_complete [Field F] [DecidableEq F] (p : Poseidon.Params F)
    (hsize : p.roundConstants.size = Poseidon.fullRounds) (a b : FVar F) (av bv : F) :
    Complete (F := F) (c := KimchiConstraint F)
      (fun s => CircuitType.ReadsAs (val := F) s a av ∧
        CircuitType.ReadsAs (val := F) s b bv)
      (hash2 (c := KimchiConstraint F) p a b)
      (fun r s' => CircuitType.ReadsAs (val := F) s' r
        (Poseidon.RandomOracle.hash p [av, bv])) := by
  refine Complete.bind
    (Complete.imp (fun s h => ⟨initState_readsAs s,
        ⟨CircuitType.scoped_prod.mpr ⟨h.1.1, h.2.1⟩,
          CircuitType.reads_prod.mpr ⟨h.1.2, h.2.2⟩⟩⟩) (fun _ _ h => h)
      (updateBlock_complete p hsize initState (a, b) Poseidon.RandomOracle.initialState
        (av, bv)))
    fun r => Complete.pure_of fun _ hR => ?_
  simp only [CircuitType.ReadsAs, scoped_spongeState, reads_spongeState] at hR
  refine ⟨CircuitType.scoped_fvar.mpr hR.1.1, CircuitType.reads_fvar.mpr ?_⟩
  simpa [Poseidon.RandomOracle.hash, Poseidon.RandomOracle.update,
    Poseidon.RandomOracle.toBlocks, Poseidon.RandomOracle.chunk,
    Poseidon.RandomOracle.digest] using hR.2.1

attribute [irreducible] hash2

/-! ## Hashing a list -/

/-- Hash a list of elements (PS `hashVec`): update the fresh state, read slot 0. -/
def hashVec [Field F] [BasicSystem F c] [KimchiSystem F c] (p : Poseidon.Params F)
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

/-- **Completeness** (`hashVec`): the honest run accepts on read inputs, and the digest
reads back the value `hash` of their values. -/
theorem hashVec_complete [Field F] [DecidableEq F] (p : Poseidon.Params F)
    (hsize : p.roundConstants.size = Poseidon.fullRounds) (xs : List (FVar F))
    (vs : List F) :
    Complete (F := F) (c := KimchiConstraint F)
      (fun s => List.Forall₂ (CircuitType.ReadsAs (val := F) s) xs vs)
      (hashVec (c := KimchiConstraint F) p xs)
      (fun r s' => CircuitType.ReadsAs (val := F) s' r
        (Poseidon.RandomOracle.hash p vs)) := by
  refine Complete.bind
    (Complete.imp (fun s h => ⟨initState_readsAs s, h⟩) (fun _ _ h => h)
      (update_complete p hsize initState xs Poseidon.RandomOracle.initialState vs))
    fun r => Complete.pure_of fun _ hR => ?_
  simp only [CircuitType.ReadsAs, scoped_spongeState, reads_spongeState] at hR
  refine ⟨CircuitType.scoped_fvar.mpr hR.1.1, CircuitType.reads_fvar.mpr ?_⟩
  simpa [Poseidon.RandomOracle.hash, Poseidon.RandomOracle.digest] using hR.2.1

attribute [irreducible] hashVec

end RandomOracle

end Snarky.Kimchi
