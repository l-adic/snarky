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
`toBlocks`/`chunk`/`addBlock`.

Deviations from the PS original:
- PS's ambient `PoseidonField` class arrives as the explicit `p : Poseidon.Params F`.
- PS's width-3 / width-2 `Vector`s render as the triple and the pair; PS `Array`
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
private def initState [Zero F] : FVar F × FVar F × FVar F :=
  (.const 0, .const 0, .const 0)

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
private def addBlockVar [Add F] (st : FVar F × FVar F × FVar F) (b : FVar F × FVar F) :
    FVar F × FVar F × FVar F :=
  (CVar.add_ st.1 b.1, CVar.add_ st.2.1 b.2, st.2.2)

/-- Absorb one block (PS `updateBlock`): add into the rate slots, permute. -/
private def updateBlock [Field F] [KimchiSystem F c]
    (p : Poseidon.Params F) (st : FVar F × FVar F × FVar F) (b : FVar F × FVar F) :
    CircuitM F c (FVar F × FVar F × FVar F) :=
  poseidon p (addBlockVar st b)

/-- Fold the input into the state block by block (PS `update`). -/
def update [Field F] [KimchiSystem F c] (p : Poseidon.Params F)
    (st : FVar F × FVar F × FVar F) (xs : List (FVar F)) :
    CircuitM F c (FVar F × FVar F × FVar F) :=
  (toBlocksVar xs).foldlM (updateBlock p) st

/-- Hash exactly two elements (PS `hash2`): one block, one permutation. -/
def hash2 [Field F] [KimchiSystem F c] (p : Poseidon.Params F) (a b : FVar F) :
    CircuitM F c (FVar F) := do
  let st ← updateBlock p initState (a, b)
  pure st.1

/-- Hash a list of elements (PS `hashVec`): update the fresh state, read slot 0. -/
def hashVec [Field F] [KimchiSystem F c] (p : Poseidon.Params F)
    (xs : List (FVar F)) : CircuitM F c (FVar F) := do
  let st ← update p initState xs
  pure st.1

/-! ## The laws

Each op reads as its `Poseidon.RandomOracle` value counterpart: `update` as the block
fold, `hash2`/`hashVec` as `hash`. The block fold is walked once, generalized over the
block list; the public laws instantiate it at the chunking, bridged by the pure
chunk-alignment lemmas. -/

open Std.Do

/-- The circuit chunking reads as the value chunking. -/
private theorem chunkVar_map_val [Field F] (V : Valuation F) :
    ∀ xs : List (FVar F),
      (chunkVar xs).map (fun b => (b.1.val V, b.2.val V))
        = Poseidon.RandomOracle.chunk (xs.map (fun x => x.val V))
  | [] => rfl
  | [_] => rfl
  | x :: y :: rest => by
    simp only [chunkVar, Poseidon.RandomOracle.chunk, List.map_cons,
      chunkVar_map_val V rest]

/-- The circuit block decomposition reads as the value block decomposition. -/
private theorem toBlocksVar_map_val [Field F] (V : Valuation F) :
    ∀ xs : List (FVar F),
      (toBlocksVar xs).map (fun b => (b.1.val V, b.2.val V))
        = Poseidon.RandomOracle.toBlocks (xs.map (fun x => x.val V))
  | [] => rfl
  | [x] => chunkVar_map_val V [x]
  | x :: y :: rest => chunkVar_map_val V (x :: y :: rest)

/-- `updateBlock` is sound: the output cells read as one value block step —
`blockCipher` of `addBlock` at the cell readings. -/
@[spec] private theorem updateBlock_spec [Field F] [DecidableEq F]
    (p : Poseidon.Params F) (hsize : p.roundConstants.size = 5 * 11)
    (st : FVar F × FVar F × FVar F) (b : FVar F × FVar F)
    (Q : PostCond (FVar F × FVar F × FVar F) (.arg (BuilderState F) .pure)) :
    ⦃Sound (fun V (r : FVar F × FVar F × FVar F) =>
        (r.1.val V, r.2.1.val V, r.2.2.val V)
          = Poseidon.blockCipher p
              (Poseidon.RandomOracle.addBlock
                (st.1.val V, st.2.1.val V, st.2.2.val V) (b.1.val V, b.2.val V))) Q⦄
    (updateBlock (c := KimchiConstraint F) p st b)
    ⦃Q⦄ := by
  simp only [updateBlock]
  intro s hpre
  refine Poseidon.poseidon_spec p hsize _ Q s ?_
  intro r nv hpos
  refine hpre _ _ ?_
  exact hpos.trans (by
    simp [addBlockVar, Poseidon.RandomOracle.addBlock, CVar.val_add_])

/-- `updateBlock` is complete: the honest run accepts on readable cells and block, and
the output cells read back as the value block step. -/
@[spec] private theorem updateBlock_complete_spec [Field F] [DecidableEq F]
    (p : Poseidon.Params F) (hsize : p.roundConstants.size = 5 * 11)
    (st : FVar F × FVar F × FVar F) (b : FVar F × FVar F)
    (Q : PostCond (FVar F × FVar F × FVar F)
      (.arg (ProverState F) (.except EvalError .pure))) :
    ⦃Complete
        (fun env => (st.1.eval env).isOk ∧ (st.2.1.eval env).isOk ∧
          (st.2.2.eval env).isOk ∧ (b.1.eval env).isOk ∧ (b.2.eval env).isOk)
        (fun env (r : FVar F × FVar F × FVar F) env' =>
          ∀ a₁ a₂ a₃ v₁ v₂, st.1.eval env = .ok a₁ → st.2.1.eval env = .ok a₂ →
            st.2.2.eval env = .ok a₃ → b.1.eval env = .ok v₁ → b.2.eval env = .ok v₂ →
            r.1.eval env' = .ok (Poseidon.blockCipher p
              (Poseidon.RandomOracle.addBlock (a₁, a₂, a₃) (v₁, v₂))).1 ∧
            r.2.1.eval env' = .ok (Poseidon.blockCipher p
              (Poseidon.RandomOracle.addBlock (a₁, a₂, a₃) (v₁, v₂))).2.1 ∧
            r.2.2.eval env' = .ok (Poseidon.blockCipher p
              (Poseidon.RandomOracle.addBlock (a₁, a₂, a₃) (v₁, v₂))).2.2)
        Q⦄
    (updateBlock (c := KimchiProverC F) p st b)
    ⦃Q⦄ := by
  simp only [updateBlock]
  intro s hpre
  obtain ⟨⟨h₁, h₂, h₃, h₄, h₅⟩, hk⟩ := hpre
  obtain ⟨a₁, h₁⟩ := CVar.evalOk h₁
  obtain ⟨a₂, h₂⟩ := CVar.evalOk h₂
  obtain ⟨a₃, h₃⟩ := CVar.evalOk h₃
  obtain ⟨v₁, h₄⟩ := CVar.evalOk h₄
  obtain ⟨v₂, h₅⟩ := CVar.evalOk h₅
  refine Poseidon.poseidon_complete_spec p hsize _ Q s
    ⟨⟨isOk_of_eq (CVar.eval_add_ h₁ h₄), isOk_of_eq (CVar.eval_add_ h₂ h₅),
      isOk_of_eq h₃⟩, fun r st₁ hpos hle => ?_⟩
  have hpos := hpos _ _ _ (CVar.eval_add_ h₁ h₄) (CVar.eval_add_ h₂ h₅) h₃
  refine hk _ _ (fun a₁' a₂' a₃' v₁' v₂' h₁' h₂' h₃' h₄' h₅' => ?_) hle
  rw [h₁] at h₁'; rw [h₂] at h₂'; rw [h₃] at h₃'; rw [h₄] at h₄'; rw [h₅] at h₅'
  injection h₁' with h₁'; injection h₂' with h₂'; injection h₃' with h₃'
  injection h₄' with h₄'; injection h₅' with h₅'
  subst h₁' h₂' h₃' h₄' h₅'
  exact hpos

/-- The block fold is sound, generalized over the block list: the output cells read as
the value fold of the block readings. -/
private theorem foldBlocks_spec [Field F] [DecidableEq F]
    (p : Poseidon.Params F) (hsize : p.roundConstants.size = 5 * 11) :
    ∀ (bs : List (FVar F × FVar F)) (st : FVar F × FVar F × FVar F)
      (Q : PostCond (FVar F × FVar F × FVar F) (.arg (BuilderState F) .pure)),
      ⦃Sound (fun V (r : FVar F × FVar F × FVar F) =>
          (r.1.val V, r.2.1.val V, r.2.2.val V)
            = (bs.map fun b => (b.1.val V, b.2.val V)).foldl
                (fun s b =>
                  Poseidon.blockCipher p (Poseidon.RandomOracle.addBlock s b))
                (st.1.val V, st.2.1.val V, st.2.2.val V)) Q⦄
      (bs.foldlM (updateBlock (c := KimchiConstraint F) p) st)
      ⦃Q⦄
  | [], st, Q => by
    simp only [List.foldlM_nil]
    mvcgen
    rename_i s hpre
    exact hpre _ _ (by simp)
  | b :: bs, st, Q => by
    simp only [List.foldlM_cons]
    have ih := foldBlocks_spec p hsize bs
    intro s hpre
    simp only [WPMonad.wp_bind, PredTrans.apply_Bind_bind]
    refine updateBlock_spec p hsize st b _ s ?_
    intro r₁ nv₁ h₁
    refine ih r₁ _ ⟨s.V, nv₁⟩ ?_
    intro r₂ nv₂ h₂
    refine hpre _ _ ?_
    simp only [List.map_cons, List.foldl_cons, ← h₁]
    exact h₂

/-- The complete-side reading of an input list — element-wise pinned evaluations, in
the order given, as `List.Forall₂`. The vocabulary of
`update_complete_spec`/`hashVec_complete_spec`. -/
def ReadsAll [Field F] (env : Assignments F) (xs : List (FVar F)) (vs : List F) :
    Prop :=
  List.Forall₂ (fun (x : FVar F) v => x.eval env = .ok v) xs vs

/-- The reading survives table extension. -/
theorem ReadsAll.le [Field F] {env env' : Assignments F} (hle : env.Le env')
    {xs : List (FVar F)} {vs : List F} (h : ReadsAll env xs vs) :
    ReadsAll env' xs vs :=
  List.Forall₂.imp (fun _ _ hx => CVar.eval_le hle hx) h

/-- Evaluable inputs read as SOME value list — names the list the complete laws'
`ReadsAll` hypotheses quantify over, for use inside a proof. -/
theorem exists_readsAll [Field F] {env : Assignments F} :
    ∀ {xs : List (FVar F)}, (∀ x ∈ xs, (x.eval env).isOk) → ∃ vs, ReadsAll env xs vs
  | [], _ => ⟨[], .nil⟩
  | x :: xs, h => by
    obtain ⟨v, hv⟩ := CVar.evalOk (h x (by simp))
    obtain ⟨vs, hvs⟩ := exists_readsAll (xs := xs) fun y hy => h y (by simp [hy])
    exact ⟨v :: vs, .cons hv hvs⟩

/-- The complete-side reading of a block list — `ReadsAll`'s shape, componentwise on
the pairs. -/
private def ReadsBlocks [Field F] (env : Assignments F)
    (bs : List (FVar F × FVar F)) (vs : List (F × F)) : Prop :=
  List.Forall₂ (fun (b : FVar F × FVar F) (v : F × F) =>
    b.1.eval env = .ok v.1 ∧ b.2.eval env = .ok v.2) bs vs

/-- The reading survives table extension. -/
private theorem ReadsBlocks.le [Field F] {env env' : Assignments F}
    (hle : env.Le env') {bs : List (FVar F × FVar F)} {vs : List (F × F)}
    (h : ReadsBlocks env bs vs) : ReadsBlocks env' bs vs :=
  List.Forall₂.imp (fun _ _ hb => ⟨CVar.eval_le hle hb.1, CVar.eval_le hle hb.2⟩) h

/-- Pinned inputs chunk to pinned blocks (the constant pads read as the value pads). -/
private theorem readsBlocks_chunkVar [Field F] {env : Assignments F} :
    ∀ {xs : List (FVar F)} {vs : List F}, ReadsAll env xs vs →
      ReadsBlocks env (chunkVar xs) (Poseidon.RandomOracle.chunk vs)
  | [], _, h => by cases h; exact .nil
  | [x], _, h => by
    cases h with
    | cons hx hrest => cases hrest; exact .cons ⟨hx, rfl⟩ .nil
  | x :: y :: rest, _, h => by
    cases h with
    | cons hx h2 =>
      cases h2 with
      | cons hy hrest => exact .cons ⟨hx, hy⟩ (readsBlocks_chunkVar hrest)

/-- Pinned inputs decompose to pinned blocks. -/
private theorem readsBlocks_toBlocksVar [Field F] {env : Assignments F}
    {xs : List (FVar F)} {vs : List F} (h : ReadsAll env xs vs) :
    ReadsBlocks env (toBlocksVar xs) (Poseidon.RandomOracle.toBlocks vs) := by
  cases h with
  | nil => exact .cons ⟨rfl, rfl⟩ .nil
  | @cons x v xs' vs' hx hrest =>
    show ReadsBlocks env (chunkVar (x :: xs'))
      (Poseidon.RandomOracle.chunk (v :: vs'))
    exact readsBlocks_chunkVar (.cons hx hrest)

/-- Evaluable inputs chunk to evaluable blocks. -/
private theorem chunkVar_ok [Field F] {env : Assignments F} :
    ∀ xs : List (FVar F), (∀ x ∈ xs, (x.eval env).isOk) →
      ∀ b ∈ chunkVar xs, (b.1.eval env).isOk ∧ (b.2.eval env).isOk
  | [], _ => by simp [chunkVar]
  | [x], h => by
    simp only [chunkVar, List.mem_singleton, forall_eq]
    exact ⟨h x (by simp), isOk_of_eq rfl⟩
  | x :: y :: rest, h => by
    simp only [chunkVar, List.mem_cons, forall_eq_or_imp]
    refine ⟨⟨h x (by simp), h y (by simp)⟩, ?_⟩
    exact fun b hb =>
      chunkVar_ok rest (fun z hz => h z (by simp [hz])) b hb

/-- Evaluable inputs decompose to evaluable blocks. -/
private theorem toBlocksVar_ok [Field F] {env : Assignments F} :
    ∀ xs : List (FVar F), (∀ x ∈ xs, (x.eval env).isOk) →
      ∀ b ∈ toBlocksVar xs, (b.1.eval env).isOk ∧ (b.2.eval env).isOk
  | [], _ => by
    simp only [toBlocksVar, List.mem_singleton, forall_eq]
    exact ⟨isOk_of_eq rfl, isOk_of_eq rfl⟩
  | [x], h => chunkVar_ok [x] h
  | x :: y :: rest, h => chunkVar_ok (x :: y :: rest) h

/-- The block fold is complete, generalized over the block list: the honest run
accepts on readable cells and blocks, and the output cells read back as the value
fold. -/
private theorem foldBlocks_complete_spec [Field F] [DecidableEq F]
    (p : Poseidon.Params F) (hsize : p.roundConstants.size = 5 * 11) :
    ∀ (bs : List (FVar F × FVar F)) (st : FVar F × FVar F × FVar F)
      (Q : PostCond (FVar F × FVar F × FVar F)
        (.arg (ProverState F) (.except EvalError .pure))),
      ⦃Complete
          (fun env => ((st.1.eval env).isOk ∧ (st.2.1.eval env).isOk ∧
            (st.2.2.eval env).isOk) ∧
            ∀ b ∈ bs, (b.1.eval env).isOk ∧ (b.2.eval env).isOk)
          (fun env (r : FVar F × FVar F × FVar F) env' =>
            ∀ a₁ a₂ a₃ vs, st.1.eval env = .ok a₁ → st.2.1.eval env = .ok a₂ →
              st.2.2.eval env = .ok a₃ → ReadsBlocks env bs vs →
              r.1.eval env' = .ok (vs.foldl
                (fun s b =>
                  Poseidon.blockCipher p (Poseidon.RandomOracle.addBlock s b))
                (a₁, a₂, a₃)).1 ∧
              r.2.1.eval env' = .ok (vs.foldl
                (fun s b =>
                  Poseidon.blockCipher p (Poseidon.RandomOracle.addBlock s b))
                (a₁, a₂, a₃)).2.1 ∧
              r.2.2.eval env' = .ok (vs.foldl
                (fun s b =>
                  Poseidon.blockCipher p (Poseidon.RandomOracle.addBlock s b))
                (a₁, a₂, a₃)).2.2)
          Q⦄
      (bs.foldlM (updateBlock (c := KimchiProverC F) p) st)
      ⦃Q⦄
  | [], st, Q => by
    simp only [List.foldlM_nil]
    mvcgen
    rename_i s hpre
    obtain ⟨⟨hcells, _⟩, hk⟩ := hpre
    refine hk _ s (fun a₁ a₂ a₃ vs h₁ h₂ h₃ hr => ?_) (Assignments.Le.refl _)
    cases hr
    exact ⟨h₁, h₂, h₃⟩
  | b :: bs, st, Q => by
    simp only [List.foldlM_cons]
    have ih := foldBlocks_complete_spec p hsize bs
    intro s hpre
    obtain ⟨⟨⟨h₁, h₂, h₃⟩, hblocks⟩, hk⟩ := hpre
    obtain ⟨a₁, h₁⟩ := CVar.evalOk h₁
    obtain ⟨a₂, h₂⟩ := CVar.evalOk h₂
    obtain ⟨a₃, h₃⟩ := CVar.evalOk h₃
    obtain ⟨hb₁, hb₂⟩ := hblocks b (by simp)
    obtain ⟨v₁, hb₁⟩ := CVar.evalOk hb₁
    obtain ⟨v₂, hb₂⟩ := CVar.evalOk hb₂
    simp only [WPMonad.wp_bind, PredTrans.apply_Bind_bind]
    refine updateBlock_complete_spec p hsize st b _ s
      ⟨⟨isOk_of_eq h₁, isOk_of_eq h₂, isOk_of_eq h₃, isOk_of_eq hb₁,
        isOk_of_eq hb₂⟩, fun r₁ st₁ hout hle₁ => ?_⟩
    have houtv := hout _ _ _ _ _ h₁ h₂ h₃ hb₁ hb₂
    refine ih r₁ _ st₁
      ⟨⟨⟨isOk_of_eq houtv.1, isOk_of_eq houtv.2.1, isOk_of_eq houtv.2.2⟩,
        fun b' hb' => ?_⟩, fun r₂ st₂ hrest hle₂ => ?_⟩
    · obtain ⟨hx, hy⟩ := hblocks b' (by simp [hb'])
      obtain ⟨x, hx⟩ := CVar.evalOk hx
      obtain ⟨y, hy⟩ := CVar.evalOk hy
      exact ⟨isOk_of_eq (CVar.eval_le hle₁ hx), isOk_of_eq (CVar.eval_le hle₁ hy)⟩
    · refine hk _ _ (fun a₁' a₂' a₃' vs h₁' h₂' h₃' hr => ?_) (hle₁.trans hle₂)
      rw [h₁] at h₁'; rw [h₂] at h₂'; rw [h₃] at h₃'
      injection h₁' with h₁'; injection h₂' with h₂'; injection h₃' with h₃'
      subst h₁' h₂' h₃'
      cases hr with
      | cons hv hr' =>
        obtain ⟨hv₁, hv₂⟩ := hv
        rw [hb₁] at hv₁; rw [hb₂] at hv₂
        injection hv₁ with hv₁; injection hv₂ with hv₂
        subst hv₁ hv₂
        simp only [List.foldl_cons]
        exact hrest _ _ _ _ houtv.1 houtv.2.1 houtv.2.2 (ReadsBlocks.le hle₁ hr')

/-- `update` is sound: the output cells read as `Poseidon.RandomOracle.update` of the
cell and input readings. -/
@[spec] theorem update_spec [Field F] [DecidableEq F] (p : Poseidon.Params F)
    (hsize : p.roundConstants.size = 5 * 11) (st : FVar F × FVar F × FVar F)
    (xs : List (FVar F))
    (Q : PostCond (FVar F × FVar F × FVar F) (.arg (BuilderState F) .pure)) :
    ⦃Sound (fun V (r : FVar F × FVar F × FVar F) =>
        (r.1.val V, r.2.1.val V, r.2.2.val V)
          = Poseidon.RandomOracle.update p
              (st.1.val V, st.2.1.val V, st.2.2.val V)
              (xs.map (fun x => x.val V))) Q⦄
    (update (c := KimchiConstraint F) p st xs)
    ⦃Q⦄ := by
  simp only [update]
  intro s hpre
  refine foldBlocks_spec p hsize (toBlocksVar xs) st _ s ?_
  intro r nv h
  refine hpre _ _ ?_
  simp only [Poseidon.RandomOracle.update]
  rw [← toBlocksVar_map_val]
  exact h

/-- `update` is complete: the honest run accepts on readable cells and inputs, and the
output cells read back as `Poseidon.RandomOracle.update` of the values. -/
@[spec] theorem update_complete_spec [Field F] [DecidableEq F] (p : Poseidon.Params F)
    (hsize : p.roundConstants.size = 5 * 11) (st : FVar F × FVar F × FVar F)
    (xs : List (FVar F))
    (Q : PostCond (FVar F × FVar F × FVar F)
      (.arg (ProverState F) (.except EvalError .pure))) :
    ⦃Complete
        (fun env => ((st.1.eval env).isOk ∧ (st.2.1.eval env).isOk ∧
          (st.2.2.eval env).isOk) ∧ ∀ x ∈ xs, (x.eval env).isOk)
        (fun env (r : FVar F × FVar F × FVar F) env' =>
          ∀ a₁ a₂ a₃ vs, st.1.eval env = .ok a₁ → st.2.1.eval env = .ok a₂ →
            st.2.2.eval env = .ok a₃ → ReadsAll env xs vs →
            r.1.eval env' = .ok (Poseidon.RandomOracle.update p (a₁, a₂, a₃) vs).1 ∧
            r.2.1.eval env'
              = .ok (Poseidon.RandomOracle.update p (a₁, a₂, a₃) vs).2.1 ∧
            r.2.2.eval env'
              = .ok (Poseidon.RandomOracle.update p (a₁, a₂, a₃) vs).2.2)
        Q⦄
    (update (c := KimchiProverC F) p st xs)
    ⦃Q⦄ := by
  simp only [update]
  intro s hpre
  obtain ⟨⟨hcells, hxs⟩, hk⟩ := hpre
  refine foldBlocks_complete_spec p hsize (toBlocksVar xs) st _ s
    ⟨⟨hcells, toBlocksVar_ok xs hxs⟩, fun r st' hout hle => ?_⟩
  refine hk _ _ (fun a₁ a₂ a₃ vs h₁ h₂ h₃ hr => ?_) hle
  exact hout a₁ a₂ a₃ (Poseidon.RandomOracle.toBlocks vs) h₁ h₂ h₃
    (readsBlocks_toBlocksVar hr)

/-- `hash2` is sound: the digest reads as the value `hash` of the two readings. -/
@[spec] theorem hash2_spec [Field F] [DecidableEq F] (p : Poseidon.Params F)
    (hsize : p.roundConstants.size = 5 * 11) (a b : FVar F)
    (Q : PostCond (FVar F) (.arg (BuilderState F) .pure)) :
    ⦃Sound (fun V (r : FVar F) =>
        r.val V = Poseidon.RandomOracle.hash p [a.val V, b.val V]) Q⦄
    (hash2 (c := KimchiConstraint F) p a b)
    ⦃Q⦄ := by
  simp only [hash2]
  have u := updateBlock_spec p hsize
  mvcgen [u]
  rename_i s hpre
  intro r nv h
  mvcgen
  refine hpre _ _ ?_
  have h1 := congrArg Prod.fst h
  simpa [Poseidon.RandomOracle.hash, Poseidon.RandomOracle.update,
    Poseidon.RandomOracle.toBlocks, Poseidon.RandomOracle.chunk,
    Poseidon.RandomOracle.digest, Poseidon.RandomOracle.initialState,
    initState] using h1

/-- `hash2` is complete: the honest run accepts on readable operands, and the digest
reads back as the value `hash` of their values. -/
@[spec] theorem hash2_complete_spec [Field F] [DecidableEq F] (p : Poseidon.Params F)
    (hsize : p.roundConstants.size = 5 * 11) (a b : FVar F)
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
  refine ⟨⟨isOk_of_eq rfl, isOk_of_eq rfl, isOk_of_eq rfl, isOk_of_eq ha,
    isOk_of_eq hb⟩, fun r₁ st₁ hout hle₁ => ?_⟩
  have hout := hout _ _ _ _ _ rfl rfl rfl ha hb
  simp only [wp, PredTrans.apply, prove]
  intro hf
  refine hk _ ⟨st₁.nv, st₁.env, hf⟩ (fun av' bv' ha' hb' => ?_) hle₁
  rw [ha] at ha'; rw [hb] at hb'
  injection ha' with ha'; injection hb' with hb'
  subst ha' hb'
  simpa [Poseidon.RandomOracle.hash, Poseidon.RandomOracle.update,
    Poseidon.RandomOracle.toBlocks, Poseidon.RandomOracle.chunk,
    Poseidon.RandomOracle.digest, Poseidon.RandomOracle.initialState] using hout.1

/-- `hashVec` is sound: the digest reads as the value `hash` of the input readings. -/
@[spec] theorem hashVec_spec [Field F] [DecidableEq F] (p : Poseidon.Params F)
    (hsize : p.roundConstants.size = 5 * 11) (xs : List (FVar F))
    (Q : PostCond (FVar F) (.arg (BuilderState F) .pure)) :
    ⦃Sound (fun V (r : FVar F) =>
        r.val V = Poseidon.RandomOracle.hash p (xs.map (fun x => x.val V))) Q⦄
    (hashVec (c := KimchiConstraint F) p xs)
    ⦃Q⦄ := by
  simp only [hashVec]
  have u := update_spec p hsize
  mvcgen [u]
  rename_i s hpre
  intro r nv h
  mvcgen
  refine hpre _ _ ?_
  have h1 := congrArg Prod.fst h
  simpa [Poseidon.RandomOracle.hash, Poseidon.RandomOracle.digest,
    Poseidon.RandomOracle.initialState, initState] using h1

/-- `hashVec` is complete: the honest run accepts on readable inputs, and the digest
reads back as the value `hash` of their values. -/
@[spec] theorem hashVec_complete_spec [Field F] [DecidableEq F]
    (p : Poseidon.Params F) (hsize : p.roundConstants.size = 5 * 11)
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
  refine ⟨⟨⟨isOk_of_eq rfl, isOk_of_eq rfl, isOk_of_eq rfl⟩, hxs⟩,
    fun r₁ st₁ hout hle₁ => ?_⟩
  simp only [wp, PredTrans.apply, prove]
  intro hf
  refine hk _ ⟨st₁.nv, st₁.env, hf⟩ (fun vs hr => ?_) hle₁
  have hout := hout 0 0 0 vs rfl rfl rfl hr
  simpa [Poseidon.RandomOracle.hash, Poseidon.RandomOracle.digest,
    Poseidon.RandomOracle.initialState] using hout.1

end RandomOracle

end Snarky.Kimchi
