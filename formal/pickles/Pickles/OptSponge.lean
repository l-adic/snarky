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

/-- Consume the guarded inputs from the state `st` at position `pos` (OCaml `consume`, PS
`consume`): the pairs, then the unpaired entry if any, then a permutation where the block is
non-empty or — where `needsFinalPermuteIfEmpty` — nothing at all was kept. -/
def consume (p : Poseidon.Params F) (st : SpongeState F) (pos : BoolVar F)
    (needsFinalPermuteIfEmpty : Bool) (input : List (BoolVar F × FVar F)) :
    CircuitM F c (SpongeState F) := do
  let (pairs, leftover) := pairUp input
  let (st, pos) ← consumePairs p st pos pairs
  let anyKept ← Snarky.any (input.map (·.1))
  let emptyInput := Snarky.not anyKept
  match leftover with
  | none => do
    let shouldPermute ←
      if needsFinalPermuteIfEmpty then Snarky.or emptyInput pos else pure pos
    condPermute p shouldPermute st
  | some (b, x) => do
    let _ ← Snarky.xor pos b
    let xb ← mul x (↑b)
    let st' ← addIn st pos xb
    let shouldPermute ←
      if needsFinalPermuteIfEmpty then Snarky.any [pos, b, emptyInput] else Snarky.any [pos, b]
    condPermute p shouldPermute st'

/-- Consume the guarded inputs from a fresh sponge and read slot `0` after the final
permutation (PS `squeeze create`, so the start position is `0` and an empty absorb still
permutes). -/
def squeeze (p : Poseidon.Params F) (input : List (BoolVar F × FVar F)) :
    CircuitM F c (FVar F) := do
  let final ← consume p initState false_ true input
  pure final.s0


/-! ## The phase machine -/

/-- The conditional sponge's phase (PS `OptSpongePhase`, OCaml `Opt_sponge.sponge_state`):
absorbing, with the pending guarded inputs most recent first and the position the block
restarts at; or squeezed, at the next slot to read. -/
inductive Phase (F : Type)
  /-- Accumulating guarded inputs, consumed at the next squeeze. -/
  | absorbing (nextIndex : BoolVar F) (pending : List (BoolVar F × FVar F))
  /-- Squeezing, at the next slot to read. -/
  | squeezed (n : Fin 3)

/-- The conditional sponge with its phase (PS `OptSpongeState`, OCaml `Opt_sponge.t`). -/
structure OptSpongeVar (F : Type) where
  /-- The width-3 state. -/
  state : SpongeState F
  /-- The phase. -/
  phase : Phase F
  /-- Whether the next consume permutes an empty block (OCaml
  `needs_final_permute_if_empty`). -/
  needsFinalPermuteIfEmpty : Bool

omit [DecidableEq F] in
/-- The fresh conditional sponge (OCaml `create`, PS `runOptSpongeM`'s start). -/
def create : OptSpongeVar F := ⟨initState, .absorbing false_ [], true⟩

omit [DecidableEq F] in
/-- Absorb a guarded input (PS `optAbsorb`, OCaml `absorb`): onto the pending list, or a new
block at position `0` after a squeeze. No rows. -/
def optAbsorb (ov : OptSpongeVar F) (e : BoolVar F × FVar F) : OptSpongeVar F :=
  match ov.phase with
  | .absorbing i xs => { ov with phase := .absorbing i (e :: xs) }
  | .squeezed _ => { ov with phase := .absorbing false_ [e] }

/-- Read slot `n`. Emits nothing. -/
private def slotVar (st : SpongeState F) : Fin 3 → FVar F
  | ⟨0, _⟩ => st.s0
  | ⟨1, _⟩ => st.s1
  | ⟨_ + 2, _⟩ => st.s2

/-- Squeeze (PS `optSqueeze`, OCaml `squeeze`): squeezed, the next slot, permuting first when
the block is exhausted; absorbing, consume the pending inputs oldest first, then slot `0`,
now squeezed at slot `1` with the empty-block permute re-armed. -/
def optSqueeze (p : Poseidon.Params F) (ov : OptSpongeVar F) :
    CircuitM F c (FVar F × OptSpongeVar F) :=
  match ov.phase with
  | .squeezed n =>
    if n.val = 2 then do
      let st ← poseidon p ov.state
      pure (st.s0, ⟨st, .squeezed 1, ov.needsFinalPermuteIfEmpty⟩)
    else pure (slotVar ov.state n, { ov with phase := .squeezed (n + 1) })
  | .absorbing i xs => do
    let st ← consume p ov.state i ov.needsFinalPermuteIfEmpty xs.reverse
    pure (st.s0, ⟨st, .squeezed 1, true⟩)

/-- Hand the sponge to the plain sponge (PS `toRegularSponge`, wrap_verifier.ml's `S.make`):
squeezed at its slot; absorbing, at a fresh block. -/
def toRegularSponge (ov : OptSpongeVar F) : SpongeVar F :=
  match ov.phase with
  | .squeezed n => ⟨ov.state, .squeezed n⟩
  | .absorbing _ _ => ⟨ov.state, .absorbed 0⟩

/-! ## The value model -/

/-- One guarded absorb at the tracked position: a kept element is added at slot `pos`, and
the block is permuted at once when it fills; a dropped element changes nothing. -/
private def optAbsorb1 (p : Poseidon.Params F) (os : Poseidon.Triple F × Bool) (e : Bool × F) :
    Poseidon.Triple F × Bool :=
  if e.1 then
    if os.2 then (Poseidon.blockCipher p (Poseidon.addSlot os.1 1 e.2), false)
    else (Poseidon.addSlot os.1 0 e.2, true)
  else os

/-- The final state: permute where the block is non-empty or nothing at all was kept. -/
private def optFinalState (p : Poseidon.Params F) (os : Poseidon.Triple F × Bool)
    (empty : Bool) : Poseidon.Triple F :=
  if empty || os.2 then Poseidon.blockCipher p os.1 else os.1

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

/-- A start for `consume`: the invariant, or a sponge just squeezed — at position `0`, the
states equal — whose next kept element restarts the block at slot `0`
(`Poseidon.absorb1`'s `.squeezed` branch) exactly as the invariant's fresh block does. -/
private def RelStart (p : Poseidon.Params F) (os : Poseidon.Triple F × Bool)
    (ps : Poseidon.State F) : Prop :=
  Rel p os ps ∨ (os.2 = false ∧ (∃ n, ps.mode = .squeezed n) ∧ os.1 = ps.state)

omit [DecidableEq F] in
/-- A start whose sponge is not squeezed is the invariant. -/
private theorem rel_of_relStart (p : Poseidon.Params F) {os : Poseidon.Triple F × Bool}
    {ps : Poseidon.State F} (h : RelStart p os ps) (hm : ∀ n, ps.mode ≠ .squeezed n) :
    Rel p os ps := by
  rcases h with h | ⟨-, ⟨n, hn⟩, -⟩
  · exact h
  · exact absurd hn (hm n)

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
/-- One step from a start: a kept element lands in the invariant, a dropped one keeps the
start. -/
private theorem relStart_step (p : Poseidon.Params F) {os : Poseidon.Triple F × Bool}
    {ps : Poseidon.State F} (h : RelStart p os ps) (e : Bool × F) :
    RelStart p (optAbsorb1 p os e) (if e.1 then Poseidon.absorb1 p ps e.2 else ps) := by
  rcases h with h | ⟨hpos, ⟨n, hn⟩, hs⟩
  · exact Or.inl (rel_step p h e)
  · obtain ⟨st, pos⟩ := os
    obtain ⟨b, x⟩ := e
    simp only at hpos hs
    subst hpos hs
    cases b
    · exact Or.inr ⟨rfl, ⟨n, hn⟩, rfl⟩
    · exact Or.inl (by simp [optAbsorb1, Rel, Poseidon.absorb1, hn])

omit [DecidableEq F] in
/-- The start along a whole input. -/
private theorem relStart_fold (p : Poseidon.Params F) :
    ∀ (xs : List (Bool × F)) {os : Poseidon.Triple F × Bool} {ps : Poseidon.State F},
      RelStart p os ps →
      RelStart p (xs.foldl (optAbsorb1 p) os)
        (Poseidon.absorb p ps ((xs.filter (·.1)).map (·.2)))
  | [], _, _, h => h
  | e :: xs, os, ps, h => by
    have := relStart_fold p xs (relStart_step p h e)
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
/-- An absorb leaves the sponge absorbing. -/
private theorem absorb1_mode_ne_squeezed (p : Poseidon.Params F) (sp : Poseidon.State F)
    (x : F) (n : Fin 3) : (Poseidon.absorb1 p sp x).mode ≠ .squeezed n := by
  obtain ⟨st, mode⟩ := sp
  cases mode with
  | absorbed m =>
    by_cases hm : m.val = 2 <;> simp [Poseidon.absorb1, hm]
  | squeezed m => simp [Poseidon.absorb1]

omit [DecidableEq F] in
/-- Absorbing a non-empty list leaves the sponge absorbing. -/
private theorem absorb_mode_ne_squeezed (p : Poseidon.Params F) (sp : Poseidon.State F) :
    ∀ ys : List F, ys ≠ [] → ∀ n, (Poseidon.absorb p sp ys).mode ≠ .squeezed n
  | [], h => absurd rfl h
  | [y], _ => by simpa [Poseidon.absorb] using absorb1_mode_ne_squeezed p sp y
  | y :: z :: zs, _ =>
    absorb_mode_ne_squeezed p (Poseidon.absorb1 p sp y) (z :: zs) (by simp)

omit [DecidableEq F] in
/-- From an empty block, the block is empty exactly when nothing was absorbed. -/
private theorem absorb_mode_eq_zero_iff (p : Poseidon.Params F) (sp : Poseidon.State F)
    (h0 : sp.mode = .absorbed 0) :
    ∀ xs : List F, (Poseidon.absorb p sp xs).mode = .absorbed 0 ↔ xs = []
  | [] => by simp [Poseidon.absorb, h0]
  | x :: xs => iff_of_false (absorb_mode_ne p _ _ (List.cons_ne_nil x xs)) (List.cons_ne_nil x xs)

omit [DecidableEq F] in
/-- The final state agrees with the value sponge's state after its squeeze. -/
private theorem optFinalState_eq_squeeze (p : Poseidon.Params F)
    {os : Poseidon.Triple F × Bool} {ps : Poseidon.State F} (h : Rel p os ps) (empty : Bool)
    (he : empty = true ↔ ps.mode = .absorbed 0) :
    optFinalState p os empty = (Poseidon.squeeze p ps).2.state := by
  obtain ⟨st, pos⟩ := os
  obtain ⟨pst, mode⟩ := ps
  cases pos
  · simp only [Rel, Bool.false_eq_true, ite_false] at h
    rcases h with ⟨hm, hs⟩ | ⟨hm, hs⟩
    · subst hm hs
      have : empty = true := he.mpr rfl
      subst this
      simp [optFinalState, Poseidon.squeeze]
    · subst hm hs
      have : empty = false := by
        cases empty with
        | true => exact absurd (he.mp rfl) (by simp)
        | false => rfl
      subst this
      simp [optFinalState, Poseidon.squeeze]
  · simp only [Rel, ite_true] at h
    obtain ⟨hm, hs⟩ := h
    subst hm hs
    simp [optFinalState, Poseidon.squeeze]

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
private theorem optFinalState_leftover (p : Poseidon.Params F) (stv : Poseidon.Triple F)
    (posb bb e : Bool) (xv : F) (hbe : bb = true → e = false) :
    (if posb || bb || e then
        Poseidon.blockCipher p (Poseidon.addSlot stv (if posb then 1 else 0) (xv * bit bb))
      else Poseidon.addSlot stv (if posb then 1 else 0) (xv * bit bb))
      = optFinalState p (optAbsorb1 p (stv, posb) (bb, xv)) e := by
  cases bb
  · cases posb <;> simp [optFinalState, optAbsorb1, Poseidon.addSlot, bit]
  · have := hbe rfl
    subst this
    cases posb <;> simp [optFinalState, optAbsorb1, Poseidon.addSlot, bit]

omit [DecidableEq F] in
/-- Absorbing from an absorbing sponge leaves it absorbing. -/
private theorem absorb_mode_absorbed (p : Poseidon.Params F) :
    ∀ (xs : List F) (sp : Poseidon.State F), (∃ m, sp.mode = .absorbed m) →
      ∃ m, (Poseidon.absorb p sp xs).mode = .absorbed m
  | [], sp, h => h
  | x :: xs, sp, _ => by
    refine absorb_mode_absorbed p xs (Poseidon.absorb1 p sp x) ?_
    obtain ⟨st, mode⟩ := sp
    cases mode with
    | absorbed m => by_cases hm : m.val = 2 <;> simp [Poseidon.absorb1, hm]
    | squeezed m => simp [Poseidon.absorb1]

omit [DecidableEq F] in
/-- An absorbing sponge's squeeze reads slot `0` of its squeezed state. -/
private theorem squeeze_fst_of_absorbed (p : Poseidon.Params F) (sp : Poseidon.State F)
    (h : ∃ m, sp.mode = .absorbed m) :
    (Poseidon.squeeze p sp).1 = (Poseidon.squeeze p sp).2.state.1 := by
  obtain ⟨m, hm⟩ := h
  obtain ⟨st, mode⟩ := sp
  simp only at hm
  subst hm
  simp [Poseidon.squeeze, Poseidon.slot]

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

/-- Under any valuation satisfying the emitted constraints, `consume` from a start reading as
`RelStart` at the position bit's reading, with the `i`-th guarded input reading as `(bᵢ, xᵢ)`
and either some input kept or the start at an empty block, ends in the state the value
sponge that absorbed exactly the kept inputs has after its squeeze:
`squeeze(absorb(ps, [xᵢ | bᵢ = 1]))`'s state. Stated at `needsFinalPermuteIfEmpty = true`, the
only flag the verifiers use. -/
theorem consume_spec (p : Poseidon.Params F)
    (hsize : p.roundConstants.size = Poseidon.fullRounds)
    (hall : ∀ j k : ℕ, j ≤ 3 → k ≤ 3 → (j : F) = k → j = k)
    (st : SpongeState F) (pos : BoolVar F) (input : List (BoolVar F × FVar F))
    (xs : List (Bool × F)) (hx : List.Forall₂ (CircuitType.Reads V) input xs)
    (hchar : ∀ k : ℕ, k ≤ input.length → (k : F) = 0 → k = 0) :
    ⦃⌜True⌝⦄ consume (c := Builder V (KimchiConstraint F)) p st pos true input
    ⦃⇓ r _ => ⌜∀ (pb : Bool) (ps : Poseidon.State F), (↑pos : CVar F).val V = bit pb →
      RelStart p (CircuitType.readVal (val := Poseidon.Triple F) V st, pb) ps →
      ((∃ v ∈ xs, v.1 = true) ∨ ps.mode = .absorbed 0) →
      CircuitType.readVal (val := Poseidon.Triple F) V r
        = (Poseidon.squeeze p (Poseidon.absorb p ps ((xs.filter (·.1)).map (·.2)))).2.state⌝⦄ := by
  have hbool := guard_bit input xs hx
  have hex := exists_guard_iff input xs hx
  have hany := Snarky.any_spec (V := V) (c := KimchiConstraint F) (input.map (·.1))
    (by simpa using hchar)
  have hpairs := consumePairs_spec (V := V) p hsize hall
  have hcp := condPermute_spec (V := V) p hsize
  have hany3 := Snarky.any_spec (V := V) (c := KimchiConstraint F)
  obtain ⟨hpF, hlF⟩ := pairUp_forall₂ input xs hx
  have hmem := pairUp_snd_mem xs
  rcases hpu : pairUp input with ⟨pairs, leftover⟩
  rcases hpx : pairUp xs with ⟨vpairs, vleft⟩
  rw [hpu] at hpF hlF
  rw [hpx] at hpF hlF hmem
  have hP := hpairs pairs vpairs st pos hpF
  have hchar3 : ∀ l : List (BoolVar F), l.length = 3 →
      ∀ k ≤ l.length, (k : F) = 0 → k = 0 := by
    intro l hl k hk h0
    exact hall k 0 (hl ▸ hk) (by omega) (by simpa using h0)
  have bit01 : ∀ bb : Bool, (bit bb : F) = 0 ∨ (bit bb : F) = 1 := fun bb => by
    cases bb <;> simp [bit]
  have hanyChar : ∀ k ≤ (input.map (·.1)).length, (k : F) = 0 → k = 0 := by simpa using hchar
  -- the fold's invariant and the emptiness reading, at the start the caller provides
  have hend : ∀ (pb : Bool) (ps : Poseidon.State F),
      RelStart p (CircuitType.readVal (val := Poseidon.Triple F) V st, pb) ps →
      ((∃ v ∈ xs, v.1 = true) ∨ ps.mode = .absorbed 0) →
      Rel p (xs.foldl (optAbsorb1 p) (CircuitType.readVal (val := Poseidon.Triple F) V st, pb))
          (Poseidon.absorb p ps ((xs.filter (·.1)).map (·.2))) ∧
        ((!xs.any (·.1)) = true ↔
          (Poseidon.absorb p ps ((xs.filter (·.1)).map (·.2))).mode = .absorbed 0) := by
    intro pb ps hstart hne
    have hrel0 := relStart_fold p xs hstart
    have hne' : (∃ v ∈ xs, v.1 = true) ↔ (xs.filter (·.1)).map (·.2) ≠ [] := by
      simp [List.filter_eq_nil_iff]
    rcases hne with hne | h0
    · have hk := hne'.mp hne
      refine ⟨rel_of_relStart p hrel0 (absorb_mode_ne_squeezed p ps _ hk), ?_⟩
      have := absorb_mode_ne p ps _ hk
      simp only [Bool.not_eq_true', List.any_eq_false, this, iff_false]
      simp only [not_forall, not_not]
      obtain ⟨v, hv, h⟩ := hne
      exact ⟨v, hv, h⟩
    · refine ⟨rel_of_relStart p hrel0 fun n hn => ?_, ?_⟩
      · by_cases hk : (xs.filter (·.1)).map (·.2) = []
        · rw [hk] at hn
          simp [Poseidon.absorb, h0] at hn
        · exact absorb_mode_ne_squeezed p ps _ hk n hn
      · rw [absorb_mode_eq_zero_iff p ps h0]
        simp [List.any_eq_false, List.filter_eq_nil_iff]
  simp only [consume, hpu]
  cases leftover with
  | none =>
    cases hlF
    have hfold := foldl_pairUp p xs
    rw [hpx] at hfold
    simp only at hfold
    mvcgen [hP, hany, hcp]
    rename_i _ acc _ hAcc anyK _ _ hAny sp _ hOr fin _
    intro hFin pb ps hp hstart hne
    obtain ⟨hst, hpos⟩ := hAcc pb hp
    obtain ⟨hrel, hempty⟩ := hend pb ps hstart hne
    have hAnyV : (↑anyK : CVar F).val V = bit (xs.any (·.1)) := by
      rw [hAny hbool]
      by_cases h : ∃ v ∈ xs, v.1 = true
      · rw [if_pos (hex.mpr h)]; simp [bit, List.any_eq_true, h]
      · rw [if_neg (fun h' => h (hex.mp h'))]; simp [bit, List.any_eq_true, h]
    have hE := not_val hAnyV
    have hSp := hOr _ _ hE hpos
    have hF := hFin _ hSp
    rw [hF, hst]
    show optFinalState p (List.foldl (optAbsorb2 p)
      (CircuitType.readVal (val := Poseidon.Triple F) V st, pb) vpairs) (!xs.any (·.1)) = _
    rw [hfold _]
    exact optFinalState_eq_squeeze p hrel _ hempty
  | some e =>
    obtain ⟨b, x⟩ := e
    cases hlF with
    | some hv =>
    rename_i v
    obtain ⟨bb, xv⟩ := v
    have hb := CircuitType.reads_boolVar.mp (CircuitType.reads_prod.mp hv).1
    have hxv := CircuitType.reads_fvar.mp (CircuitType.reads_prod.mp hv).2
    have hfold := foldl_pairUp p xs
    rw [hpx] at hfold
    simp only at hfold
    have hbe : bb = true → (!xs.any (·.1)) = false := fun h => by
      simp only [Bool.not_eq_false', List.any_eq_true]
      exact ⟨(bb, xv), hmem _ rfl, h⟩
    mvcgen [hP, hany, hcp, addIn_spec]
    all_goals first | exact hchar3 _ rfl | exact hanyChar | skip
    rename_i _ acc _ hAcc anyK _ hAny _ _ _ xb _ hxb st' _ _ hSt sp _ hAny3 fin _
    intro hFin pb ps hp hstart hne
    obtain ⟨hst, hpos⟩ := hAcc pb hp
    obtain ⟨hrel, hempty⟩ := hend pb ps hstart hne
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
        = bit ((List.foldl (optAbsorb2 p)
            (CircuitType.readVal (val := Poseidon.Triple F) V st, pb) vpairs).2 || bb
            || !xs.any (·.1)) := by
      rw [hAny3 ?_]
      · generalize (List.foldl (optAbsorb2 p)
          (CircuitType.readVal (val := Poseidon.Triple F) V st, pb) vpairs).2 = fp at hpos ⊢
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
    rw [hF, hS]
    have hfold' := hfold (CircuitType.readVal (val := Poseidon.Triple F) V st, pb)
    generalize List.foldl (optAbsorb2 p)
      (CircuitType.readVal (val := Poseidon.Triple F) V st, pb) vpairs = fd at hfold' ⊢
    obtain ⟨fst, fpos⟩ := fd
    rw [optFinalState_leftover p fst fpos bb (!xs.any (·.1)) xv hbe, hfold']
    exact optFinalState_eq_squeeze p hrel _ hempty

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
  have hc := consume_spec (V := V) p hsize hall initState false_ input xs hx hchar
  simp only [squeeze]
  mvcgen [hc]
  rename_i _ fin _ hfin
  have hf : (↑(false_ : BoolVar F) : CVar F).val V = bit false := by simp [false_, bit]
  have hinit : CircuitType.readVal (val := Poseidon.Triple F) V initState = (0, 0, 0) := by
    simp [initState, readVal_spongeState]
  have hF := hfin false Poseidon.init hf (by rw [hinit]; exact Or.inl (rel_init p)) (Or.inr rfl)
  have hs0 : fin.s0.val V = (CircuitType.readVal (val := Poseidon.Triple F) V fin).1 := by
    simp [readVal_spongeState]
  rw [hs0, hF]
  exact (squeeze_fst_of_absorbed p _ (absorb_mode_absorbed p _ _ ⟨0, rfl⟩)).symm


/-! ## The phase machine's readings -/

omit [DecidableEq F] in
/-- A squeezed conditional sponge reads as a value sponge: the states agree, the slot is the
mode's, and the empty-block permute is armed. -/
def SqueezedReads (V : Valuation F) (ov : OptSpongeVar F) (ps : Poseidon.State F) : Prop :=
  ∃ n, ov.phase = .squeezed n ∧
    CircuitType.readVal (val := Poseidon.Triple F) V ov.state = ps.state ∧
    ps.mode = .squeezed n ∧ ov.needsFinalPermuteIfEmpty = true

omit [DecidableEq F] in
/-- An absorbing conditional sponge reads as a start `ps₀` at the position bit's reading
`ib`, its pending inputs (oldest first) reading as `pend`, the empty-block permute armed. -/
def AbsorbingReads (p : Poseidon.Params F) (V : Valuation F) (ov : OptSpongeVar F) (ib : Bool)
    (ps₀ : Poseidon.State F) (pend : List (Bool × F)) : Prop :=
  ∃ i xs, ov.phase = .absorbing i xs ∧ (↑i : CVar F).val V = bit ib ∧
    RelStart p (CircuitType.readVal (val := Poseidon.Triple F) V ov.state, ib) ps₀ ∧
    List.Forall₂ (CircuitType.Reads V) xs.reverse pend ∧ ov.needsFinalPermuteIfEmpty = true

omit [BasicSystem F c] [KimchiSystem F c] in
/-- The fresh conditional sponge reads as the fresh value sponge with nothing pending. -/
theorem create_reads (p : Poseidon.Params F) :
    AbsorbingReads p V (create (F := F)) false Poseidon.init [] :=
  ⟨false_, [], rfl, by simp [false_, bit],
    by simpa [create, initState, readVal_spongeState] using Or.inl (rel_init p), .nil, rfl⟩

omit [BasicSystem F c] [KimchiSystem F c] in
/-- Absorbing while absorbing appends to the pending readings. -/
theorem optAbsorb_reads_absorbing {p : Poseidon.Params F} {ov : OptSpongeVar F} {ib : Bool}
    {ps₀ : Poseidon.State F} {pend : List (Bool × F)}
    (h : AbsorbingReads p V ov ib ps₀ pend) {e : BoolVar F × FVar F} {v : Bool × F}
    (he : CircuitType.Reads V e v) :
    AbsorbingReads p V (optAbsorb ov e) ib ps₀ (pend ++ [v]) := by
  obtain ⟨i, xs, hph, hi, hrel, hxs, hnf⟩ := h
  refine ⟨i, e :: xs, by simp [optAbsorb, hph], hi, by simpa [optAbsorb, hph] using hrel, ?_,
    by simpa [optAbsorb, hph] using hnf⟩
  simp only [List.reverse_cons]
  exact List.rel_append hxs (.cons he .nil)

omit [BasicSystem F c] [KimchiSystem F c] in
/-- Absorbing after a squeeze starts a block at position `0` from the squeezed sponge. -/
theorem optAbsorb_reads_squeezed (p : Poseidon.Params F) {ov : OptSpongeVar F}
    {ps : Poseidon.State F} (h : SqueezedReads V ov ps) {e : BoolVar F × FVar F} {v : Bool × F}
    (he : CircuitType.Reads V e v) :
    AbsorbingReads p V (optAbsorb ov e) false ps [v] := by
  obtain ⟨n, hph, hst, hm, hnf⟩ := h
  refine ⟨false_, [e], by simp [optAbsorb, hph], by simp [false_, bit], ?_, .cons he .nil,
    by simpa [optAbsorb, hph] using hnf⟩
  simp only [optAbsorb, hph]
  exact Or.inr ⟨rfl, ⟨n, hm⟩, hst⟩

omit [DecidableEq F] [BasicSystem F c] [KimchiSystem F c] in
/-- `slotVar` reads the value slot. -/
private theorem slotVar_val (st : SpongeState F) (n : Fin 3) :
    (slotVar st n).val V
      = Poseidon.slot (CircuitType.readVal (val := Poseidon.Triple F) V st) n := by
  fin_cases n <;> simp [slotVar, Poseidon.slot, readVal_spongeState]

omit [DecidableEq F] in
/-- A non-empty absorb leaves the sponge absorbing, from any start. -/
private theorem absorb_mode_absorbed_of_ne_nil (p : Poseidon.Params F) (sp : Poseidon.State F)
    (ys : List F) (h : ys ≠ []) : ∃ m, (Poseidon.absorb p sp ys).mode = .absorbed m := by
  cases hm : (Poseidon.absorb p sp ys).mode with
  | absorbed m => exact ⟨m, rfl⟩
  | squeezed n => exact absurd hm (absorb_mode_ne_squeezed p sp ys h n)

omit [DecidableEq F] in
/-- An absorbing sponge's squeeze permutes and lands at slot `1`. -/
private theorem squeeze_mode_of_absorbed (p : Poseidon.Params F) (sp : Poseidon.State F)
    (h : ∃ m, sp.mode = .absorbed m) : (Poseidon.squeeze p sp).2.mode = .squeezed 1 := by
  obtain ⟨m, hm⟩ := h
  obtain ⟨st, mode⟩ := sp
  simp only at hm
  subst hm
  simp [Poseidon.squeeze]

/-- Squeezing a squeezed sponge reads as the value squeeze. -/
private theorem optSqueeze_spec_squeezed (p : Poseidon.Params F)
    (hsize : p.roundConstants.size = Poseidon.fullRounds) (ov : OptSpongeVar F)
    (ps : Poseidon.State F) (h : SqueezedReads V ov ps) :
    ⦃⌜True⌝⦄ optSqueeze (c := Builder V (KimchiConstraint F)) p ov
    ⦃⇓ r _ => ⌜r.1.val V = (Poseidon.squeeze p ps).1 ∧
      SqueezedReads V r.2 (Poseidon.squeeze p ps).2⌝⦄ := by
  obtain ⟨n, hph, hst, hm, hnf⟩ := h
  obtain ⟨st, phase, nf⟩ := ov
  simp only at hph hst hnf
  subst hph hnf
  obtain ⟨pst, pmode⟩ := ps
  simp only at hst hm
  subst hst hm
  simp only [optSqueeze]
  by_cases hn : n.val = 2
  · rw [if_pos hn]
    have hp := Poseidon.poseidon_spec (V := V) p hsize st
    mvcgen [hp]
    rename_i st' _ hst'
    refine ⟨?_, 1, rfl, ?_, ?_, rfl⟩
    · have h0 := congrArg Prod.fst hst'
      simp only [readVal_spongeState] at h0
      simpa [Poseidon.squeeze, hn, Poseidon.slot, readVal_spongeState] using h0
    · simp [Poseidon.squeeze, hn, hst']
    · simp [Poseidon.squeeze, hn]
  · rw [if_neg hn]
    mvcgen
    refine ⟨?_, n + 1, rfl, ?_, ?_, rfl⟩
    · simp [Poseidon.squeeze, hn, slotVar_val]
    · simp [Poseidon.squeeze, hn]
    · simp [Poseidon.squeeze, hn]

/-- Squeezing an absorbing sponge consumes the pending inputs and reads as the value squeeze
of the start after absorbing the kept ones, given some kept input or a start at an empty
block. -/
private theorem optSqueeze_spec_absorbing (p : Poseidon.Params F)
    (hsize : p.roundConstants.size = Poseidon.fullRounds)
    (hall : ∀ j k : ℕ, j ≤ 3 → k ≤ 3 → (j : F) = k → j = k) (ov : OptSpongeVar F) (ib : Bool)
    (ps₀ : Poseidon.State F) (pend : List (Bool × F)) (h : AbsorbingReads p V ov ib ps₀ pend)
    (hne : (∃ v ∈ pend, v.1 = true) ∨ ps₀.mode = .absorbed 0)
    (hchar : ∀ k : ℕ, k ≤ pend.length → (k : F) = 0 → k = 0) :
    ⦃⌜True⌝⦄ optSqueeze (c := Builder V (KimchiConstraint F)) p ov
    ⦃⇓ r _ => ⌜r.1.val V
        = (Poseidon.squeeze p (Poseidon.absorb p ps₀ ((pend.filter (·.1)).map (·.2)))).1 ∧
      SqueezedReads V r.2
        (Poseidon.squeeze p (Poseidon.absorb p ps₀ ((pend.filter (·.1)).map (·.2)))).2⌝⦄ := by
  obtain ⟨i, xs, hph, hi, hrel, hxs, hnf⟩ := h
  obtain ⟨st, phase, nf⟩ := ov
  simp only at hph hrel hnf
  subst hph hnf
  have hlen : xs.reverse.length = pend.length := List.Forall₂.length_eq hxs
  have hc := consume_spec (V := V) p hsize hall st i xs.reverse pend hxs (by rwa [hlen])
  have habs : ∃ m, (Poseidon.absorb p ps₀ ((pend.filter (·.1)).map (·.2))).mode = .absorbed m := by
    rcases hne with hne | h0
    · exact absorb_mode_absorbed_of_ne_nil p ps₀ _ (by
        simp only [ne_eq, List.map_eq_nil_iff, List.filter_eq_nil_iff, not_forall, not_not]
        obtain ⟨v, hv, hb⟩ := hne
        exact ⟨v, hv, hb⟩)
    · exact absorb_mode_absorbed p _ ps₀ ⟨0, h0⟩
  simp only [optSqueeze]
  mvcgen [hc]
  rename_i st' _ hst'
  have hS := hst' ib ps₀ hi hrel hne
  refine ⟨?_, 1, rfl, hS, squeeze_mode_of_absorbed p _ habs, rfl⟩
  rw [squeeze_fst_of_absorbed p _ habs, ← hS]
  simp [readVal_spongeState]


/-- Under any valuation satisfying the emitted constraints, a squeeze reads by phase: from a
sponge reading as squeezed at `ps`, as the value squeeze of `ps`; from one reading as
absorbing from `ps₀` with `pend` pending, as the value squeeze of `ps₀` after absorbing the
kept inputs, given some kept input or a start at an empty block and a characteristic above
the pending count. -/
theorem optSqueeze_spec (p : Poseidon.Params F)
    (hsize : p.roundConstants.size = Poseidon.fullRounds)
    (hall : ∀ j k : ℕ, j ≤ 3 → k ≤ 3 → (j : F) = k → j = k) (ov : OptSpongeVar F) :
    ⦃⌜True⌝⦄ optSqueeze (c := Builder V (KimchiConstraint F)) p ov
    ⦃⇓ r _ => ⌜(∀ ps : Poseidon.State F, SqueezedReads V ov ps →
        r.1.val V = (Poseidon.squeeze p ps).1 ∧ SqueezedReads V r.2 (Poseidon.squeeze p ps).2) ∧
      (∀ (ib : Bool) (ps₀ : Poseidon.State F) (pend : List (Bool × F)),
        AbsorbingReads p V ov ib ps₀ pend →
        ((∃ v ∈ pend, v.1 = true) ∨ ps₀.mode = .absorbed 0) →
        (∀ k : ℕ, k ≤ pend.length → (k : F) = 0 → k = 0) →
        r.1.val V
          = (Poseidon.squeeze p (Poseidon.absorb p ps₀ ((pend.filter (·.1)).map (·.2)))).1 ∧
        SqueezedReads V r.2
          (Poseidon.squeeze p (Poseidon.absorb p ps₀ ((pend.filter (·.1)).map (·.2)))).2)⌝⦄ := by
  rw [builder_spec_iff]
  intro nv hsat
  exact ⟨fun ps h => (builder_spec_iff _ _).mp (optSqueeze_spec_squeezed p hsize ov ps h) nv hsat,
    fun ib ps₀ pend h hne hchar => (builder_spec_iff _ _).mp
      (optSqueeze_spec_absorbing p hsize hall ov ib ps₀ pend h hne hchar) nv hsat⟩

omit [DecidableEq F] [BasicSystem F c] [KimchiSystem F c] in
/-- The plain sponge a squeezed conditional sponge hands over reads as the same value
sponge. -/
theorem toRegularSponge_reads {ov : OptSpongeVar F} {ps : Poseidon.State F}
    (h : SqueezedReads V ov ps) : SpongeVar.ReadsAt V (toRegularSponge ov) ps := by
  obtain ⟨n, hph, hst, hm, -⟩ := h
  exact ⟨by simpa [toRegularSponge, hph] using hst, by simp [toRegularSponge, hph, hm]⟩

end OptSponge

end Pickles
