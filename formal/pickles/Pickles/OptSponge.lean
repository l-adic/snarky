import Snarky.DSL.Boolean
import Snarky.Kimchi.Circuit.Poseidon
import Snarky.Kimchi.Circuit.Sponge

set_option mvcgen.warning false

/-!
# The conditional sponge

Port of the PureScript `Pickles.OptSponge` (OCaml `opt_sponge.ml`): a sponge absorbing a
data-dependent subset of its inputs, each guarded by a bit, in a fixed number of
permutations. The position within the rate block is a circuit bit; inputs are consumed in
pairs, each pair adding its kept entries at the tracked positions and permuting where a
block fills, with the last unpaired entry and the final permutation handled after.

## Main definitions

* `OptSponge.squeeze`: consume the guarded inputs from a fresh sponge and read slot `0`
  after the final permutation.

## Main results

* `OptSponge.squeeze_spec`: the output reads as the first squeeze of the value sponge that
  absorbed exactly the kept inputs, in order.

## Implementation notes

The value model `optAbsorb1` absorbs one kept element at the tracked position and permutes
eagerly when the block fills; `Poseidon.absorb1` permutes lazily on the next absorb. The
two agree on every squeeze, which the invariant `Rel` records: at position `1` the states
coincide, at position `0` the conditional sponge holds either the fresh block or the
permutation of the value sponge's full block.
-/

namespace Pickles

open Std.Do Snarky Snarky.Kimchi

variable {F c : Type} [Field F] [DecidableEq F] [BasicSystem F c] [KimchiSystem F c]

namespace OptSponge

/-- Add `x` into the rate slot the bit `pos` selects, by one `r1cs` row per slot. -/
private def addIn (st : SpongeState F) (pos : BoolVar F) (x : FVar F) :
    CircuitM F c (SpongeState F) := do
  let flag0 := Snarky.not pos
  let s0' ← witness (val := F) (advice st.s0 (↑flag0) x)
  addConstraint (BasicSystem.r1cs x (↑flag0) (CVar.sub_ s0' st.s0))
  let s1' ← witness (val := F) (advice st.s1 (↑pos) x)
  addConstraint (BasicSystem.r1cs x (↑pos) (CVar.sub_ s1' st.s1))
  pure ⟨s0', s1', st.s2⟩
where
  /-- The advice: the slot plus `x` where the flag is set, the slot otherwise. -/
  advice (s flag x : FVar F) : AsProver F F := do
    let sv ← AsProver.readCVar s
    let fv ← AsProver.readCVar flag
    let xv ← AsProver.readCVar x
    pure (if fv = 1 then sv + xv else sv)

/-- Permute where the bit is set: the permutation, then one selection per slot. -/
private def condPermute (p : Poseidon.Params F) (permute : BoolVar F) (st : SpongeState F) :
    CircuitM F c (SpongeState F) := do
  let permuted ← poseidon p st
  let s0 ← selectField permute permuted.s0 st.s0
  let s1 ← selectField permute permuted.s1 st.s1
  let s2 ← selectField permute permuted.s2 st.s2
  pure ⟨s0, s1, s2⟩

/-- Consume one pair of guarded inputs (OCaml `consume_pairs`' fold body). -/
private def consumePair (p : Poseidon.Params F) (st : SpongeState F) (pos : BoolVar F)
    (e₁ e₂ : BoolVar F × FVar F) : CircuitM F c (SpongeState F × BoolVar F) := do
  let (b, x) := e₁
  let (b', y) := e₂
  let p' ← Snarky.xor pos b
  let posAfter ← Snarky.xor p' b'
  let yMasked ← mul y (↑b')
  let addInYAfter ← Snarky.all [b, b', pos]
  let addInYBefore := Snarky.not addInYAfter
  let xb ← mul x (↑b)
  let state1 ← addIn st pos xb
  let yBefore ← mul yMasked (↑addInYBefore)
  let state2 ← addIn state1 p' yBefore
  let bOrB' ← Snarky.or b b'
  let pAndBOrB' ← Snarky.and pos bOrB'
  let bAndB' ← Snarky.and b b'
  let permute ← Snarky.or bAndB' pAndBOrB'
  let state3 ← condPermute p permute state2
  let yAfter ← mul yMasked (↑addInYAfter)
  let state4 ← addIn state3 p' yAfter
  pure (state4, posAfter)

/-- Consume the pairs in order. -/
private def consumePairs (p : Poseidon.Params F) :
    SpongeState F → BoolVar F → List ((BoolVar F × FVar F) × (BoolVar F × FVar F)) →
    CircuitM F c (SpongeState F × BoolVar F)
  | st, pos, [] => pure (st, pos)
  | st, pos, (e₁, e₂) :: rest => do
    let (st', pos') ← consumePair p st pos e₁ e₂
    consumePairs p st' pos' rest

/-- Consecutive pairs, and the unpaired last entry. -/
private def pairUp {α : Type} : List α → List (α × α) × Option α
  | [] => ([], none)
  | [a] => ([], some a)
  | a :: b :: rest => ((a, b) :: (pairUp rest).1, (pairUp rest).2)

/-- The fresh state. -/
private def initState : SpongeState F := ⟨.const 0, .const 0, .const 0⟩

/-- Consume the guarded inputs from a fresh sponge and read slot `0` after the final
permutation (PS `squeeze create`, so the start position is `0` and an empty absorb still
permutes): the pairs, then the unpaired entry if any, then a permutation where the block is
non-empty or nothing at all was kept. -/
def squeeze (p : Poseidon.Params F) (input : List (BoolVar F × FVar F)) :
    CircuitM F c (FVar F) := do
  let (pairs, leftover) := pairUp input
  let (st, pos) ← consumePairs p initState false_ pairs
  let anyKept ← Snarky.any (input.map (·.1))
  let emptyInput := Snarky.not anyKept
  let final ← match leftover with
    | none => do
      let shouldPermute ← Snarky.or emptyInput pos
      condPermute p shouldPermute st
    | some (b, x) => do
      let _ ← Snarky.xor pos b
      let xb ← mul x (↑b)
      let st' ← addIn st pos xb
      let shouldPermute ← Snarky.any [pos, b, emptyInput]
      condPermute p shouldPermute st'
  pure final.s0

/-! ## The value model -/

/-- One guarded absorb at the tracked position: a kept element is added at slot `pos`, and
the block is permuted at once when it fills; a dropped element changes nothing. -/
private def optAbsorb1 (p : Poseidon.Params F) (os : Poseidon.Triple F × Bool) (e : Bool × F) :
    Poseidon.Triple F × Bool :=
  if e.1 then
    if os.2 then (Poseidon.blockCipher p (Poseidon.addSlot os.1 1 e.2), false)
    else (Poseidon.addSlot os.1 0 e.2, true)
  else os

/-- The final read: permute where the block is non-empty or nothing at all was kept, then
slot `0`. -/
private def optFinal (p : Poseidon.Params F) (os : Poseidon.Triple F × Bool) (empty : Bool) :
    F :=
  (if empty || os.2 then Poseidon.blockCipher p os.1 else os.1).1

/-- The conditional sponge implements the value sponge: at position `1` the states agree and
the value sponge has one element in its block; at position `0` either both are at a fresh
block, or the value sponge's block is full and the conditional sponge holds its
permutation. -/
private def Rel (p : Poseidon.Params F) (os : Poseidon.Triple F × Bool) (ps : Poseidon.State F) :
    Prop :=
  if os.2 then ps.mode = .absorbed 1 ∧ os.1 = ps.state
  else (ps.mode = .absorbed 0 ∧ os.1 = ps.state)
    ∨ (ps.mode = .absorbed 2 ∧ os.1 = Poseidon.blockCipher p ps.state)

omit [DecidableEq F] in
private theorem rel_init (p : Poseidon.Params F) : Rel p ((0, 0, 0), false) Poseidon.init :=
  Or.inl ⟨rfl, rfl⟩

omit [DecidableEq F] in
/-- One step preserves the invariant: a kept element is absorbed on both sides, a dropped
one on neither. -/
private theorem rel_step (p : Poseidon.Params F) {os : Poseidon.Triple F × Bool}
    {ps : Poseidon.State F} (h : Rel p os ps) (e : Bool × F) :
    Rel p (optAbsorb1 p os e) (if e.1 then Poseidon.absorb1 p ps e.2 else ps) := by
  obtain ⟨st, pos⟩ := os
  obtain ⟨b, x⟩ := e
  cases b
  · simpa [optAbsorb1] using h
  · cases pos
    · simp only [Rel, Bool.false_eq_true, ite_false] at h
      rcases h with ⟨hm, hs⟩ | ⟨hm, hs⟩
      · simp [optAbsorb1, Rel, Poseidon.absorb1, hm, hs]
      · simp [optAbsorb1, Rel, Poseidon.absorb1, hm, hs]
    · simp only [Rel, ite_true] at h
      obtain ⟨hm, hs⟩ := h
      simp [optAbsorb1, Rel, Poseidon.absorb1, hm, hs]

omit [DecidableEq F] in
/-- The invariant along a whole input: the conditional fold against the value absorb of the
kept elements. -/
private theorem rel_fold (p : Poseidon.Params F) :
    ∀ (xs : List (Bool × F)) {os : Poseidon.Triple F × Bool} {ps : Poseidon.State F},
      Rel p os ps →
      Rel p (xs.foldl (optAbsorb1 p) os) (Poseidon.absorb p ps ((xs.filter (·.1)).map (·.2)))
  | [], _, _, h => h
  | e :: xs, os, ps, h => by
    have := rel_fold p xs (rel_step p h e)
    obtain ⟨b, x⟩ := e
    cases b <;> simpa [Poseidon.absorb, List.filter_cons] using this

omit [DecidableEq F] in
/-- An absorb never leaves the block empty. -/
private theorem absorb1_mode_ne (p : Poseidon.Params F) (sp : Poseidon.State F) (x : F) :
    (Poseidon.absorb1 p sp x).mode ≠ .absorbed 0 := by
  obtain ⟨st, mode⟩ := sp
  cases mode with
  | absorbed n =>
    fin_cases n
    all_goals simp [Poseidon.absorb1]
  | squeezed n => exact fun h => absurd (Poseidon.SpongeMode.absorbed.inj h) (by decide)

omit [DecidableEq F] in
/-- Absorbing a non-empty list never leaves the block empty. -/
private theorem absorb_mode_ne (p : Poseidon.Params F) (sp : Poseidon.State F) :
    ∀ ys : List F, ys ≠ [] → (Poseidon.absorb p sp ys).mode ≠ .absorbed 0
  | [], h => absurd rfl h
  | [y], _ => by simpa [Poseidon.absorb] using absorb1_mode_ne p sp y
  | y :: z :: zs, _ => absorb_mode_ne p (Poseidon.absorb1 p sp y) (z :: zs) (by simp)

omit [DecidableEq F] in
/-- The block is empty exactly when nothing was absorbed. -/
private theorem absorb_mode_eq_zero_iff (p : Poseidon.Params F) :
    ∀ xs : List F, (Poseidon.absorb p Poseidon.init xs).mode = .absorbed 0 ↔ xs = []
  | [] => by simp [Poseidon.absorb, Poseidon.init]
  | x :: xs => iff_of_false (absorb_mode_ne p _ _ (List.cons_ne_nil x xs)) (List.cons_ne_nil x xs)

omit [DecidableEq F] in
/-- The final read agrees with the value sponge's squeeze. -/
private theorem optFinal_eq_squeeze (p : Poseidon.Params F) {os : Poseidon.Triple F × Bool}
    {ps : Poseidon.State F} (h : Rel p os ps) (empty : Bool)
    (he : empty = true ↔ ps.mode = .absorbed 0) :
    optFinal p os empty = (Poseidon.squeeze p ps).1 := by
  obtain ⟨st, pos⟩ := os
  obtain ⟨pst, mode⟩ := ps
  cases pos
  · simp only [Rel, Bool.false_eq_true, ite_false] at h
    rcases h with ⟨hm, hs⟩ | ⟨hm, hs⟩
    · subst hm hs
      have : empty = true := he.mpr rfl
      subst this
      simp [optFinal, Poseidon.squeeze, Poseidon.slot]
    · subst hm hs
      have : empty = false := by
        cases empty with
        | true => exact absurd (he.mp rfl) (by simp)
        | false => rfl
      subst this
      simp [optFinal, Poseidon.squeeze, Poseidon.slot]
  · simp only [Rel, ite_true] at h
    obtain ⟨hm, hs⟩ := h
    subst hm hs
    simp [optFinal, Poseidon.squeeze, Poseidon.slot]

/-! ## Soundness -/

variable {V : Valuation F}

/-- `addIn` reads as `addSlot` at the slot the position bit selects. -/
private theorem addIn_spec (st : SpongeState F) (pos : BoolVar F) (x : FVar F) :
    ⦃⌜True⌝⦄ addIn (c := Builder V (KimchiConstraint F)) st pos x
    ⦃⇓ r _ => ⌜∀ pb : Bool, (↑pos : CVar F).val V = bit pb →
      CircuitType.readVal (val := Poseidon.Triple F) V r
      = Poseidon.addSlot (CircuitType.readVal (val := Poseidon.Triple F) V st)
          (if pb then 1 else 0) (x.val V)⌝⦄ := by
  simp only [addIn]
  mvcgen
  intro pb hp
  rename_i _ s0' _ _ _ _ h0 s1' _ _ _ _ h1
  rw [LawfulBasicSystem.holds_r1cs] at h0 h1
  rw [CVar.val_sub_, not_val hp] at h0
  rw [CVar.val_sub_, hp] at h1
  cases pb
  · simp only [bit, Bool.not_false, Bool.false_eq_true, ite_true, ite_false, mul_one,
      mul_zero] at h0 h1
    simp only [readVal_spongeState, Poseidon.addSlot, Bool.false_eq_true, ite_false]
    refine Prod.ext ?_ (Prod.ext ?_ rfl)
    · simp only; linear_combination -h0
    · simp only; linear_combination -h1
  · simp only [bit, Bool.not_true, Bool.false_eq_true, ite_true, ite_false, mul_one,
      mul_zero] at h0 h1
    simp only [readVal_spongeState, Poseidon.addSlot, ite_true]
    refine Prod.ext ?_ (Prod.ext ?_ rfl)
    · simp only; linear_combination -h0
    · simp only; linear_combination -h1

/-- `condPermute` reads as the permutation where the bit is set. -/
private theorem condPermute_spec (p : Poseidon.Params F)
    (hsize : p.roundConstants.size = Poseidon.fullRounds) (permute : BoolVar F)
    (st : SpongeState F) :
    ⦃⌜True⌝⦄ condPermute (c := Builder V (KimchiConstraint F)) p permute st
    ⦃⇓ r _ => ⌜∀ pb : Bool, (↑permute : CVar F).val V = bit pb →
      CircuitType.readVal (val := Poseidon.Triple F) V r
      = if pb then Poseidon.blockCipher p (CircuitType.readVal (val := Poseidon.Triple F) V st)
        else CircuitType.readVal (val := Poseidon.Triple F) V st⌝⦄ := by
  simp only [condPermute]
  have hpose := Poseidon.poseidon_spec (V := V) p hsize st
  mvcgen [hpose]
  intro pb hp
  rename_i _ permuted _ hP s0 _ h0 s1 _ h1 s2 _ h2
  simp only [readVal_spongeState] at hP ⊢
  rw [h0 pb hp, h1 pb hp, h2 pb hp]
  cases pb <;> simp [hP]

/-- Two guarded absorbs, as the pair step computes them. -/
private def optAbsorb2 (p : Poseidon.Params F) (os : Poseidon.Triple F × Bool)
    (e : (Bool × F) × (Bool × F)) : Poseidon.Triple F × Bool :=
  optAbsorb1 p (optAbsorb1 p os e.1) e.2

/-- One pair reads as two guarded absorbs. -/
private theorem consumePair_spec (p : Poseidon.Params F)
    (hsize : p.roundConstants.size = Poseidon.fullRounds)
    (hall : ∀ j k : ℕ, j ≤ 3 → k ≤ 3 → (j : F) = k → j = k)
    (st : SpongeState F) (pos : BoolVar F) (e₁ e₂ : BoolVar F × FVar F)
    (v₁ v₂ : Bool × F) (h1 : CircuitType.Reads V e₁ v₁)
    (h2 : CircuitType.Reads V e₂ v₂) :
    ⦃⌜True⌝⦄ consumePair (c := Builder V (KimchiConstraint F)) p st pos e₁ e₂
    ⦃⇓ r _ => ⌜∀ pb : Bool, (↑pos : CVar F).val V = bit pb →
      CircuitType.readVal (val := Poseidon.Triple F) V r.1
        = (optAbsorb2 p (CircuitType.readVal (val := Poseidon.Triple F) V st, pb) (v₁, v₂)).1
      ∧ (↑r.2 : CVar F).val V
        = bit (optAbsorb2 p (CircuitType.readVal (val := Poseidon.Triple F) V st, pb)
            (v₁, v₂)).2⌝⦄ := by
  obtain ⟨b, x⟩ := e₁
  obtain ⟨b', y⟩ := e₂
  obtain ⟨b₁, xv⟩ := v₁
  obtain ⟨b₂, yv⟩ := v₂
  obtain ⟨hb, hx⟩ := CircuitType.reads_prod.mp h1
  obtain ⟨hb', hy⟩ := CircuitType.reads_prod.mp h2
  rw [CircuitType.reads_boolVar] at hb hb'
  rw [CircuitType.reads_fvar] at hx hy
  simp only [consumePair]
  have hallS := Snarky.all_spec (V := V) (c := KimchiConstraint F) [b, b', pos]
    (by simpa using hall)
  have hcp := condPermute_spec (V := V) p hsize
  mvcgen [hallS, addIn_spec, hcp]
  rename_i _ p' _ hp' posAfter _ hpa yM _ hyM aYA _ haYA xb _ hxb st1 _ hst1 yB _ hyB st2 _ hst2
    bob _ hbob pbob _ hpbob bab _ hbab perm _ hperm st3 _ hst3 yA _ hyA st4 _ hst4
  intro pb hp
  have bit01 : ∀ bb : Bool, (bit bb : F) = 0 ∨ (bit bb : F) = 1 := fun bb => by
    cases bb <;> simp [bit]
  have hbool : ∀ q ∈ [b, b', pos], (↑q : CVar F).val V = 0 ∨ (↑q : CVar F).val V = 1 := by
    intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · rw [hb]; exact bit01 _
    · rw [hb']; exact bit01 _
    · rw [hp]; exact bit01 _
  have HaYA : (↑aYA : CVar F).val V = bit (b₁ && b₂ && pb) := by
    rw [haYA hbool]
    cases pb <;> cases b₁ <;> cases b₂ <;> simp [bit, hb, hb', hp]
  have Hp' := hp' pb b₁ hp hb
  have Hpa := hpa (pb ^^ b₁) b₂ Hp' hb'
  have Hbob := hbob b₁ b₂ hb hb'
  have Hpbob := hpbob pb (b₁ || b₂) hp Hbob
  have Hbab := hbab b₁ b₂ hb hb'
  have Hperm := hperm (b₁ && b₂) (pb && (b₁ || b₂)) Hbab Hpbob
  rw [not_val HaYA, hyM, hb', hy] at hyB
  rw [hyM, hb', HaYA, hy] at hyA
  rw [hb, hx] at hxb
  have Hst1 := hst1 pb hp
  have Hst2 := hst2 (pb ^^ b₁) Hp'
  have Hst3 := hst3 ((b₁ && b₂) || (pb && (b₁ || b₂))) Hperm
  have Hst4 := hst4 (pb ^^ b₁) Hp'
  rw [hxb] at Hst1
  rw [hyB, Hst1] at Hst2
  rw [Hst2] at Hst3
  rw [Hst3, hyA] at Hst4
  rw [Hst4, Hpa]
  simp only [readVal_spongeState]
  cases pb <;> cases b₁ <;> cases b₂ <;> simp [optAbsorb2, optAbsorb1, bit, Poseidon.addSlot]

/-- The pair fold reads as the guarded absorbs of all its entries. -/
private theorem consumePairs_spec (p : Poseidon.Params F)
    (hsize : p.roundConstants.size = Poseidon.fullRounds)
    (hall : ∀ j k : ℕ, j ≤ 3 → k ≤ 3 → (j : F) = k → j = k) :
    ∀ (pairs : List ((BoolVar F × FVar F) × (BoolVar F × FVar F)))
      (vs : List ((Bool × F) × (Bool × F))) (st : SpongeState F) (pos : BoolVar F),
      List.Forall₂ (CircuitType.Reads V) pairs vs →
      ⦃⌜True⌝⦄ consumePairs (c := Builder V (KimchiConstraint F)) p st pos pairs
      ⦃⇓ r _ => ⌜∀ pb : Bool, (↑pos : CVar F).val V = bit pb →
        CircuitType.readVal (val := Poseidon.Triple F) V r.1
          = (vs.foldl (optAbsorb2 p) (CircuitType.readVal (val := Poseidon.Triple F) V st, pb)).1
        ∧ (↑r.2 : CVar F).val V
          = bit (vs.foldl (optAbsorb2 p)
              (CircuitType.readVal (val := Poseidon.Triple F) V st, pb)).2⌝⦄
  | [], [], st, pos, _ => by
    simp only [consumePairs]
    mvcgen
    intro pb hp
    exact ⟨rfl, hp⟩
  | [], _ :: _, _, _, h => nomatch h
  | _ :: _, [], _, _, h => nomatch h
  | (e₁, e₂) :: rest, v :: vs, st, pos, h => by
    obtain ⟨hv, hrest⟩ := List.forall₂_cons.mp h
    obtain ⟨v₁, v₂⟩ := v
    obtain ⟨h1, h2⟩ := CircuitType.reads_prod.mp hv
    simp only [consumePairs]
    have hstep := consumePair_spec (V := V) p hsize hall st pos e₁ e₂ v₁ v₂ h1 h2
    have hih := fun st' pos' => consumePairs_spec p hsize hall rest vs st' pos' hrest
    mvcgen [hstep, hih]
    rename_i _ r₁ _ hS r₂ _
    intro hI pb hp
    obtain ⟨hs, hpos⟩ := hS pb hp
    obtain ⟨h1', h2'⟩ := hI _ hpos
    rw [h1', h2', hs, List.foldl_cons]
    exact ⟨rfl, rfl⟩

omit [DecidableEq F] in
/-- The pair fold followed by the unpaired entry is the fold over all entries. -/
private theorem foldl_pairUp (p : Poseidon.Params F) :
    ∀ (xs : List (Bool × F)) (os : Poseidon.Triple F × Bool),
      (match (pairUp xs).2 with
        | none => (pairUp xs).1.foldl (optAbsorb2 p) os
        | some v => optAbsorb1 p ((pairUp xs).1.foldl (optAbsorb2 p) os) v)
        = xs.foldl (optAbsorb1 p) os
  | [], os => rfl
  | [a], os => rfl
  | a :: b :: rest, os => by
    have := foldl_pairUp p rest (optAbsorb1 p (optAbsorb1 p os a) b)
    simpa [pairUp, optAbsorb2] using this

omit [DecidableEq F] in
/-- The unpaired entry is an entry. -/
private theorem pairUp_snd_mem {α : Type} :
    ∀ (xs : List α) (v : α), (pairUp xs).2 = some v → v ∈ xs
  | [], _, h => nomatch h
  | [a], v, h => by simp [pairUp] at h; simp [h]
  | _ :: _ :: rest, v, h =>
    List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (pairUp_snd_mem rest v h))

/-- Readings pair up alongside the entries. -/
private theorem pairUp_forall₂ :
    ∀ (l : List (BoolVar F × FVar F)) (xs : List (Bool × F)),
      List.Forall₂ (CircuitType.Reads V) l xs →
      List.Forall₂ (CircuitType.Reads V) (pairUp l).1 (pairUp xs).1
        ∧ Option.Rel (CircuitType.Reads V) (pairUp l).2 (pairUp xs).2
  | [], [], _ => ⟨.nil, .none⟩
  | [e], [v], h => ⟨.nil, .some (List.forall₂_cons.mp h).1⟩
  | e₁ :: e₂ :: l, v₁ :: v₂ :: xs, h => by
    obtain ⟨h1, h'⟩ := List.forall₂_cons.mp h
    obtain ⟨h2, hl⟩ := List.forall₂_cons.mp h'
    obtain ⟨ih1, ih2⟩ := pairUp_forall₂ l xs hl
    exact ⟨.cons (CircuitType.reads_prod.mpr ⟨h1, h2⟩) ih1, ih2⟩
  | [], _ :: _, h => nomatch h
  | _ :: _, [], h => nomatch h
  | [_], _ :: _ :: _, h => nomatch (List.forall₂_cons.mp h).2
  | _ :: _ :: _, [_], h => nomatch (List.forall₂_cons.mp h).2

omit [DecidableEq F] in
/-- The unpaired entry's absorb and final permutation, as the circuit computes them: the
entry is added at the tracked position and the block permuted where the position, the
guard, or emptiness demands. A kept entry rules out emptiness. -/
private theorem optFinal_leftover (p : Poseidon.Params F) (stv : Poseidon.Triple F)
    (posb bb e : Bool) (xv : F) (hbe : bb = true → e = false) :
    (if posb || bb || e then
        Poseidon.blockCipher p (Poseidon.addSlot stv (if posb then 1 else 0) (xv * bit bb))
      else Poseidon.addSlot stv (if posb then 1 else 0) (xv * bit bb)).1
      = optFinal p (optAbsorb1 p (stv, posb) (bb, xv)) e := by
  cases bb
  · cases posb <;> simp [optFinal, optAbsorb1, Poseidon.addSlot, bit]
  · have := hbe rfl
    subst this
    cases posb <;> simp [optFinal, optAbsorb1, Poseidon.addSlot, bit]

/-- Some guard reads as `1` exactly when some entry is kept. -/
private theorem exists_guard_iff :
    ∀ (l : List (BoolVar F × FVar F)) (ys : List (Bool × F)),
      List.Forall₂ (CircuitType.Reads V) l ys →
      ((∃ q : BoolVar F, q ∈ l.map (·.1) ∧ (↑q : CVar F).val V = 1)
        ↔ ∃ v ∈ ys, v.1 = true)
  | [], [], _ => by simp
  | e :: l, v :: ys, h => by
    obtain ⟨hev, hrest⟩ := List.forall₂_cons.mp h
    have hb := CircuitType.reads_boolVar.mp (CircuitType.reads_prod.mp hev).1
    obtain ⟨bv, xv⟩ := v
    simp only [List.map_cons, List.mem_cons, exists_eq_or_imp, exists_guard_iff l ys hrest, hb]
    cases bv <;> simp [bit]
  | [], _ :: _, h => nomatch h
  | _ :: _, [], h => nomatch h

/-- Every guard reads as a bit. -/
private theorem guard_bit :
    ∀ (l : List (BoolVar F × FVar F)) (ys : List (Bool × F)),
      List.Forall₂ (CircuitType.Reads V) l ys →
      ∀ q : BoolVar F, q ∈ l.map (·.1) →
        (↑q : CVar F).val V = 0 ∨ (↑q : CVar F).val V = 1
  | [], [], _, _, h => nomatch h
  | e :: l, v :: ys, h, q, hq => by
    obtain ⟨hev, hrest⟩ := List.forall₂_cons.mp h
    rcases List.mem_cons.mp hq with rfl | hq'
    · rw [CircuitType.reads_boolVar.mp (CircuitType.reads_prod.mp hev).1]
      cases v.1 <;> simp [bit]
    · exact guard_bit l ys hrest q hq'
  | [], _ :: _, h, _, _ => nomatch h
  | _ :: _, [], h, _, _ => nomatch h

/-- Under any valuation the squeeze reads as the first squeeze of the value sponge that
absorbed exactly the kept inputs: with the `i`-th guarded input reading as `(bᵢ, xᵢ)`, the
output is `squeeze(absorb(init, [xᵢ | bᵢ = 1]))₀`. -/
theorem squeeze_spec (p : Poseidon.Params F)
    (hsize : p.roundConstants.size = Poseidon.fullRounds)
    (hall : ∀ j k : ℕ, j ≤ 3 → k ≤ 3 → (j : F) = k → j = k)
    (input : List (BoolVar F × FVar F)) (xs : List (Bool × F))
    (hx : List.Forall₂ (CircuitType.Reads V) input xs)
    (hchar : ∀ k : ℕ, k ≤ input.length → (k : F) = 0 → k = 0) :
    ⦃⌜True⌝⦄ squeeze (c := Builder V (KimchiConstraint F)) p input
    ⦃⇓ d _ => ⌜d.val V = (Poseidon.squeeze p
      (Poseidon.absorb p Poseidon.init ((xs.filter (·.1)).map (·.2)))).1⌝⦄ := by
  have hbool := guard_bit input xs hx
  have hex := exists_guard_iff input xs hx
  have hany := Snarky.any_spec (V := V) (c := KimchiConstraint F) (input.map (·.1))
    (by simpa using hchar)
  have hpairs := consumePairs_spec (V := V) p hsize hall
  have hcp := condPermute_spec (V := V) p hsize
  have hany3 := Snarky.any_spec (V := V) (c := KimchiConstraint F)
  obtain ⟨hpF, hlF⟩ := pairUp_forall₂ input xs hx
  have hfold := foldl_pairUp p xs ((0, 0, 0), false)
  have hrel := rel_fold p xs (rel_init p)
  have hmode := absorb_mode_eq_zero_iff p ((xs.filter (·.1)).map (·.2))
  have hmem := pairUp_snd_mem xs
  rcases hpu : pairUp input with ⟨pairs, leftover⟩
  rcases hpx : pairUp xs with ⟨vpairs, vleft⟩
  rw [hpu] at hpF hlF
  rw [hpx] at hpF hlF hfold hmem
  have hP := hpairs pairs vpairs initState false_ hpF
  have hf : (↑(false_ : BoolVar F) : CVar F).val V = bit false := by simp [false_, bit]
  have hinit : CircuitType.readVal (val := Poseidon.Triple F) V initState = (0, 0, 0) := by
    simp [initState, readVal_spongeState]
  have hanyChar : ∀ k ≤ (input.map (·.1)).length, (k : F) = 0 → k = 0 := by simpa using hchar
  have hchar3 : ∀ l : List (BoolVar F), l.length = 3 →
      ∀ k ≤ l.length, (k : F) = 0 → k = 0 := by
    intro l hl k hk h0
    exact hall k 0 (hl ▸ hk) (by omega) (by simpa using h0)
  have bit01 : ∀ bb : Bool, (bit bb : F) = 0 ∨ (bit bb : F) = 1 := fun bb => by
    cases bb <;> simp [bit]
  have hempty : ((!xs.any (·.1)) = true) ↔
      (Poseidon.absorb p Poseidon.init ((xs.filter (·.1)).map (·.2))).mode = .absorbed 0 := by
    rw [hmode]
    simp [List.any_eq_false, List.filter_eq_nil_iff]
  simp only [squeeze, hpu]
  cases leftover with
  | none =>
    cases hlF
    simp only at hfold
    mvcgen [hP, hany, hcp]
    rename_i _ acc _ hAcc anyK _ hAny sp _ hOr fin _ hFin
    obtain ⟨hst, hpos⟩ := hAcc false hf
    rw [hinit] at hst hpos
    have hAnyV : (↑anyK : CVar F).val V = bit (xs.any (·.1)) := by
      rw [hAny hbool]
      by_cases h : ∃ v ∈ xs, v.1 = true
      · rw [if_pos (hex.mpr h)]; simp [bit, List.any_eq_true, h]
      · rw [if_neg (fun h' => h (hex.mp h'))]; simp [bit, List.any_eq_true, h]
    have hE := not_val hAnyV
    have hSp := hOr _ _ hE hpos
    have hF := hFin _ hSp
    have hs0 : fin.s0.val V = (CircuitType.readVal (val := Poseidon.Triple F) V fin).1 := by
      simp [readVal_spongeState]
    rw [hs0, hF, hst]
    show optFinal p (List.foldl (optAbsorb2 p) ((0, 0, 0), false) vpairs) (!xs.any (·.1)) = _
    rw [hfold]
    exact optFinal_eq_squeeze p hrel _ hempty
  | some e =>
    obtain ⟨b, x⟩ := e
    cases hlF with
    | some hv =>
    rename_i v
    obtain ⟨bb, xv⟩ := v
    have hb := CircuitType.reads_boolVar.mp (CircuitType.reads_prod.mp hv).1
    have hxv := CircuitType.reads_fvar.mp (CircuitType.reads_prod.mp hv).2
    simp only at hfold
    have hbe : bb = true → (!xs.any (·.1)) = false := fun h => by
      simp only [Bool.not_eq_false', List.any_eq_true]
      exact ⟨(bb, xv), hmem _ rfl, h⟩
    mvcgen [hP, hany, hcp, addIn_spec]
    all_goals first | exact hchar3 _ rfl | skip
    rename_i _ acc _ hAcc anyK _ hAny _ _ _ xb _ hxb st' _ hSt sp _ hAny3 fin _ hFin
    obtain ⟨hst, hpos⟩ := hAcc false hf
    rw [hinit] at hst hpos
    have hAnyV : (↑anyK : CVar F).val V = bit (xs.any (·.1)) := by
      rw [hAny hbool]
      by_cases h : ∃ v ∈ xs, v.1 = true
      · rw [if_pos (hex.mpr h)]; simp [bit, List.any_eq_true, h]
      · rw [if_neg (fun h' => h (hex.mp h'))]; simp [bit, List.any_eq_true, h]
    have hE := not_val hAnyV
    rw [hb, hxv] at hxb
    have hS := hSt _ hpos
    rw [hst, hxb] at hS
    have hSp : (↑sp : CVar F).val V
        = bit ((List.foldl (optAbsorb2 p) ((0, 0, 0), false) vpairs).2 || bb
            || !xs.any (·.1)) := by
      rw [hAny3 ?_]
      · generalize (List.foldl (optAbsorb2 p) ((0, 0, 0), false) vpairs).2 = fp at hpos ⊢
        simp only [List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp, exists_eq_left,
          hpos, hb, hE]
        cases fp <;> cases bb <;> cases xs.any (·.1) <;> simp [bit]
      · intro q hq
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl | rfl
        · rw [hpos]; exact bit01 _
        · rw [hb]; exact bit01 _
        · rw [hE]; exact bit01 _
    have hF := hFin _ hSp
    have hs0 : fin.s0.val V = (CircuitType.readVal (val := Poseidon.Triple F) V fin).1 := by
      simp [readVal_spongeState]
    rw [hs0, hF, hS]
    generalize List.foldl (optAbsorb2 p) ((0, 0, 0), false) vpairs = fd at hfold ⊢
    obtain ⟨fst, fpos⟩ := fd
    rw [optFinal_leftover p fst fpos bb (!xs.any (·.1)) xv hbe, hfold]
    exact optFinal_eq_squeeze p hrel _ hempty

end OptSponge

end Pickles
