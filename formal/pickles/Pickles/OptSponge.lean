import Snarky.DSL.Boolean
import Snarky.Kimchi.Circuit.Poseidon
import Snarky.Kimchi.Circuit.Sponge

set_option mvcgen.warning false

/-!
# The conditional sponge

Transcribes `OptSponge.purs` (OCaml `opt_sponge.ml`): a sponge absorbing a data-dependent
subset of its inputs, each guarded by a bit, in a fixed number of permutations. The position
within the rate block is a circuit bit; inputs are consumed in pairs, each pair permuting at
most once, with the last unpaired entry and the final permutation handled after.

## Main definitions

* `OptSponge.squeeze`: consume the guarded inputs from a fresh sponge and read slot `0`.
* `OptSponge.OptSpongeVar`, `OptSponge.optSqueeze`: the same sponge with a phase, for
  interleaved absorbs and squeezes.

## Main results

* `OptSponge.squeeze_spec`: the output reads as the first squeeze of the value sponge that
  absorbed exactly the kept inputs, in order.
* `OptSponge.optSqueeze_spec`: each squeeze reads as the value sponge's, by phase.
* `OptSponge.optSqueeze_absorbing_spec`, `OptSponge.ofSponge_spec`: a squeeze after a
  plain sponge's handover reads as the plain sponge's squeeze of the kept inputs.

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

/-- Add `x` into the rate slot the bit `pos` selects, by one `r1cs` constraint per slot. -/
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

/-- Consume one pair of guarded inputs at position `pos`, permuting at most once; returns the
state and the next position. -/
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

/-- The final permutation's bit with no unpaired entry: the position, or, under
`needsFinalPermuteIfEmpty`, an empty input. -/
private def finalBit (nf : Bool) (emptyInput pos : BoolVar F) : CircuitM F c (BoolVar F) :=
  if nf then Snarky.or emptyInput pos else pure pos

/-- The final permutation's bit after the unpaired entry `b`: the position or `b`, or, under
`needsFinalPermuteIfEmpty`, an empty input. -/
private def finalBitLeftover (nf : Bool) (emptyInput pos b : BoolVar F) :
    CircuitM F c (BoolVar F) :=
  if nf then Snarky.any [pos, b, emptyInput] else Snarky.any [pos, b]

/-- Consume the guarded inputs from `st` at position `pos`: the pairs, then the unpaired entry
if any, then a permutation where the block is non-empty or, under `needsFinalPermuteIfEmpty`,
nothing was kept. -/
def consume (p : Poseidon.Params F) (st : SpongeState F) (pos : BoolVar F)
    (needsFinalPermuteIfEmpty : Bool) (input : List (BoolVar F × FVar F)) :
    CircuitM F c (SpongeState F) := do
  let (pairs, leftover) := pairUp input
  let (st, pos) ← consumePairs p st pos pairs
  let anyKept ← Snarky.any (input.map (·.1))
  let emptyInput := Snarky.not anyKept
  match leftover with
  | none => do
    let shouldPermute ← finalBit needsFinalPermuteIfEmpty emptyInput pos
    condPermute p shouldPermute st
  | some (b, x) => do
    let _ ← Snarky.xor pos b
    let xb ← mul x (↑b)
    let st' ← addIn st pos xb
    let shouldPermute ← finalBitLeftover needsFinalPermuteIfEmpty emptyInput pos b
    condPermute p shouldPermute st'

/-- Consume the guarded inputs from a fresh sponge at position `0`, permuting even when
nothing was kept, and read slot `0`. -/
def squeeze (p : Poseidon.Params F) (input : List (BoolVar F × FVar F)) :
    CircuitM F c (FVar F) := do
  let final ← consume p initState false_ true input
  pure final.s0


/-! ## The phase machine -/

/-- The conditional sponge's phase. -/
inductive Phase (F : Type)
  /-- Accumulating guarded inputs, most recent first, to be consumed from position `nextIndex`
  at the next squeeze. -/
  | absorbing (nextIndex : BoolVar F) (pending : List (BoolVar F × FVar F))
  /-- Squeezing, at the next slot to read. -/
  | squeezed (n : Fin 3)

/-- The conditional sponge with its phase. -/
structure OptSpongeVar (F : Type) where
  /-- The width-3 state. -/
  state : SpongeState F
  /-- The phase. -/
  phase : Phase F
  /-- Whether the next consume permutes when no input was kept. -/
  needsFinalPermuteIfEmpty : Bool

omit [DecidableEq F] in
/-- The fresh conditional sponge: zero state, absorbing from position `0`, permuting even when
nothing is kept. -/
def create : OptSpongeVar F := ⟨initState, .absorbing false_ [], true⟩

/-- A plain sponge as the conditional sponge on the same state: squeezed at the same slot;
absorbed at position `0` or `1`, absorbing from there; with both rate slots filled, permuted
first, which alone clears the empty-input permute. -/
def ofSponge (p : Poseidon.Params F) (sv : SpongeVar F) : CircuitM F c (OptSpongeVar F) :=
  match sv.mode with
  | .squeezed n => pure ⟨sv.state, .squeezed n, true⟩
  | .absorbed ⟨0, _⟩ => pure ⟨sv.state, .absorbing false_ [], true⟩
  | .absorbed ⟨1, _⟩ => pure ⟨sv.state, .absorbing true_ [], true⟩
  | .absorbed ⟨_ + 2, _⟩ => do
    let st ← poseidon p sv.state
    pure ⟨st, .absorbing false_ [], false⟩

omit [DecidableEq F] in
/-- Absorb a guarded input: onto the pending list, or a new block at position `0` after a
squeeze. -/
def optAbsorb (ov : OptSpongeVar F) (e : BoolVar F × FVar F) : OptSpongeVar F :=
  match ov.phase with
  | .absorbing i xs => { ov with phase := .absorbing i (e :: xs) }
  | .squeezed _ => { ov with phase := .absorbing false_ [e] }

/-- The slot of `st` at an index. -/
private def slotVar (st : SpongeState F) : Fin 3 → FVar F
  | ⟨0, _⟩ => st.s0
  | ⟨1, _⟩ => st.s1
  | ⟨_ + 2, _⟩ => st.s2

/-- Squeeze: when squeezed, the next slot, permuting first when the block is exhausted; when
absorbing, consume the pending inputs oldest first and read slot `0`, now squeezed at slot `1`
with the empty-input permute set. -/
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

/-- The plain sponge on the same state: squeezed at its slot; absorbing, at a fresh block,
dropping any pending inputs. -/
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

/-- The invariant tying the conditional sponge to the value sponge: at position `1` the states
agree and the value block holds one element; at position `0` either both are at a fresh
block, or the value block is full and the conditional sponge holds its permutation. -/
private def Rel (p : Poseidon.Params F) (os : Poseidon.Triple F × Bool) (ps : Poseidon.State F) :
    Prop :=
  if os.2 then ps.mode = .absorbed 1 ∧ os.1 = ps.state
  else (ps.mode = .absorbed 0 ∧ os.1 = ps.state)
    ∨ (ps.mode = .absorbed 2 ∧ os.1 = Poseidon.blockCipher p ps.state)

omit [DecidableEq F] in
private theorem rel_init (p : Poseidon.Params F) : Rel p ((0, 0, 0), false) Poseidon.init :=
  Or.inl ⟨rfl, rfl⟩

/-- A start for `consume`: the invariant, or position `0` against a just-squeezed value sponge
with equal states. `Poseidon.absorb1` restarts a squeezed sponge's block at slot `0`, as the
invariant's fresh block does. -/
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
/-- `RelStart` survives a whole input. -/
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
/-- The final state agrees with the value sponge's state after its squeeze. -/
private theorem optFinalState_eq_squeeze (p : Poseidon.Params F)
    {os : Poseidon.Triple F × Bool} {ps : Poseidon.State F} (h : Rel p os ps) (empty : Bool)
    (he : os.2 = false → (empty = true ↔ ps.mode = .absorbed 0)) :
    optFinalState p os empty = (Poseidon.squeeze p ps).2.state := by
  obtain ⟨st, pos⟩ := os
  obtain ⟨pst, mode⟩ := ps
  cases pos
  · replace he := he rfl
    simp only [Rel, Bool.false_eq_true, ite_false] at h
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

/-- `finalBit` reads as the position, or an empty input under the flag. -/
private theorem finalBit_spec (nf : Bool) (e pos : BoolVar F) :
    ⦃⌜True⌝⦄ finalBit (c := Builder V (KimchiConstraint F)) nf e pos
    ⦃⇓ r _ => ⌜∀ eb pb : Bool, (↑e : CVar F).val V = bit eb → (↑pos : CVar F).val V = bit pb →
      (↑r : CVar F).val V = bit ((eb && nf) || pb)⌝⦄ := by
  cases nf
  · simp only [finalBit]
    mvcgen
    intro eb pb _ hp
    simpa using hp
  · simp only [finalBit, if_true]
    have ho := Snarky.or_spec (V := V) (c := KimchiConstraint F) e pos
    mvcgen [ho]
    intro h eb pb he hp
    simpa using h eb pb he hp

/-- `finalBitLeftover` reads as the position or the entry's bit, or an empty input under the
flag. -/
private theorem finalBitLeftover_spec (hall : ∀ j k : ℕ, j ≤ 3 → k ≤ 3 → (j : F) = k → j = k)
    (nf : Bool) (e pos b : BoolVar F) :
    ⦃⌜True⌝⦄ finalBitLeftover (c := Builder V (KimchiConstraint F)) nf e pos b
    ⦃⇓ r _ => ⌜∀ eb pb bb : Bool, (↑e : CVar F).val V = bit eb →
      (↑pos : CVar F).val V = bit pb → (↑b : CVar F).val V = bit bb →
      (↑r : CVar F).val V = bit (pb || bb || (eb && nf))⌝⦄ := by
  have hchar : ∀ l : List (BoolVar F), l.length ≤ 3 → ∀ k ≤ l.length, (k : F) = 0 → k = 0 :=
    fun l hl k hk h0 => hall k 0 (le_trans hk hl) (by omega) (by simpa using h0)
  have bit01 : ∀ bb : Bool, (bit bb : F) = 0 ∨ (bit bb : F) = 1 := fun bb => by
    cases bb <;> simp [bit]
  cases nf
  · simp only [finalBitLeftover]
    have ha := Snarky.any_spec (V := V) (c := KimchiConstraint F) [pos, b]
      (hchar _ (by simp))
    mvcgen [ha]
    all_goals first | (intro _; exact hchar _ (by simp)) | skip
    intro h eb pb bb _ hp hb
    rw [h (by
      intro q hq
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl
      · rw [hp]; exact bit01 _
      · rw [hb]; exact bit01 _)]
    simp only [List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp, exists_eq_left,
      hp, hb]
    cases pb <;> cases bb <;> simp [bit]
  · simp only [finalBitLeftover, if_true]
    have ha := Snarky.any_spec (V := V) (c := KimchiConstraint F) [pos, b, e]
      (hchar _ (by simp))
    mvcgen [ha]
    all_goals first | (intro _; exact hchar _ (by simp)) | skip
    intro h eb pb bb he hp hb
    rw [h (by
      intro q hq
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl
      · rw [hp]; exact bit01 _
      · rw [hb]; exact bit01 _
      · rw [he]; exact bit01 _)]
    simp only [List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp, exists_eq_left,
      hp, hb, he]
    cases pb <;> cases bb <;> cases eb <;> simp [bit]

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
/-- The unpaired entry's absorb and final permutation, as the circuit computes them, is
`optFinalState` after `optAbsorb1`, given that a kept entry rules out emptiness. -/
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
theorem absorb_mode_absorbed (p : Poseidon.Params F) :
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

omit [DecidableEq F] in
/-- Dropped inputs leave the value model where it was. -/
private theorem foldl_optAbsorb1_dropped (p : Poseidon.Params F) :
    ∀ (xs : List (Bool × F)) (os : Poseidon.Triple F × Bool), (∀ v ∈ xs, v.1 = false) →
      xs.foldl (optAbsorb1 p) os = os
  | [], _, _ => rfl
  | e :: xs, os, h => by
    have he : e.1 = false := h e (List.mem_cons_self ..)
    simp only [List.foldl_cons, optAbsorb1, he, Bool.false_eq_true, ite_false]
    exact foldl_optAbsorb1_dropped p xs os fun v hv => h v (List.mem_cons_of_mem _ hv)

/-- Under any valuation satisfying the emitted constraints, `consume` from a start in `RelStart`
with `ps`, with the `i`-th guarded input reading as `(bᵢ, xᵢ)`, ends in the state of
`squeeze(absorb(ps, [xᵢ | bᵢ = 1]))`, given some input kept or, with none kept, `ps` absorbing
and, at position `0`, the empty-input permute `nf` on exactly when `ps` is at an empty
block. -/
theorem consume_spec (p : Poseidon.Params F)
    (hsize : p.roundConstants.size = Poseidon.fullRounds)
    (hall : ∀ j k : ℕ, j ≤ 3 → k ≤ 3 → (j : F) = k → j = k)
    (st : SpongeState F) (pos : BoolVar F) (nf : Bool) (input : List (BoolVar F × FVar F))
    (xs : List (Bool × F)) (hx : List.Forall₂ (CircuitType.Reads V) input xs)
    (hchar : ∀ k : ℕ, k ≤ input.length → (k : F) = 0 → k = 0) :
    ⦃⌜True⌝⦄ consume (c := Builder V (KimchiConstraint F)) p st pos nf input
    ⦃⇓ r _ => ⌜∀ (pb : Bool) (ps : Poseidon.State F), (↑pos : CVar F).val V = bit pb →
      RelStart p (CircuitType.readVal (val := Poseidon.Triple F) V st, pb) ps →
      ((∃ v ∈ xs, v.1 = true) ∨ ((∀ n, ps.mode ≠ .squeezed n) ∧
        (pb = false → (nf = true ↔ ps.mode = .absorbed 0)))) →
      CircuitType.readVal (val := Poseidon.Triple F) V r
        = (Poseidon.squeeze p (Poseidon.absorb p ps ((xs.filter (·.1)).map (·.2)))).2.state⌝⦄ := by
  have hbool := guard_bit input xs hx
  have hex := exists_guard_iff input xs hx
  have hany := Snarky.any_spec (V := V) (c := KimchiConstraint F) (input.map (·.1))
    (by simpa using hchar)
  have hpairs := consumePairs_spec (V := V) p hsize hall
  have hcp := condPermute_spec (V := V) p hsize
  have hfb := finalBit_spec (V := V) nf
  have hfbl := finalBitLeftover_spec (V := V) hall nf
  obtain ⟨hpF, hlF⟩ := pairUp_forall₂ input xs hx
  have hmem := pairUp_snd_mem xs
  rcases hpu : pairUp input with ⟨pairs, leftover⟩
  rcases hpx : pairUp xs with ⟨vpairs, vleft⟩
  rw [hpu] at hpF hlF
  rw [hpx] at hpF hlF hmem
  have hP := hpairs pairs vpairs st pos hpF
  have hanyChar : ∀ k ≤ (input.map (·.1)).length, (k : F) = 0 → k = 0 := by simpa using hchar
  -- the fold's invariant and the emptiness reading, at the start the caller provides
  have hend : ∀ (pb : Bool) (ps : Poseidon.State F),
      RelStart p (CircuitType.readVal (val := Poseidon.Triple F) V st, pb) ps →
      ((∃ v ∈ xs, v.1 = true) ∨ ((∀ n, ps.mode ≠ .squeezed n) ∧
        (pb = false → (nf = true ↔ ps.mode = .absorbed 0)))) →
      Rel p (xs.foldl (optAbsorb1 p) (CircuitType.readVal (val := Poseidon.Triple F) V st, pb))
          (Poseidon.absorb p ps ((xs.filter (·.1)).map (·.2))) ∧
        ((xs.foldl (optAbsorb1 p) (CircuitType.readVal (val := Poseidon.Triple F) V st, pb)).2
            = false →
          (((!xs.any (·.1)) && nf) = true ↔
            (Poseidon.absorb p ps ((xs.filter (·.1)).map (·.2))).mode = .absorbed 0)) := by
    intro pb ps hstart hne
    have hrel0 := relStart_fold p xs hstart
    have hne' : (∃ v ∈ xs, v.1 = true) ↔ (xs.filter (·.1)).map (·.2) ≠ [] := by
      simp [List.filter_eq_nil_iff]
    by_cases hk : ∃ v ∈ xs, v.1 = true
    · have hk' := hne'.mp hk
      refine ⟨rel_of_relStart p hrel0 (absorb_mode_ne_squeezed p ps _ hk'), fun _ => ?_⟩
      have := absorb_mode_ne p ps _ hk'
      have hany : xs.any (·.1) = true := by
        obtain ⟨v, hv, h⟩ := hk
        exact List.any_eq_true.mpr ⟨v, hv, h⟩
      simp only [hany, Bool.not_true, Bool.false_and, Bool.false_eq_true, this]
    · have hdrop : ∀ v ∈ xs, v.1 = false := fun v hv => by
        cases h : v.1
        · rfl
        · exact absurd ⟨v, hv, h⟩ hk
      have hnil : (xs.filter (·.1)).map (·.2) = [] := by
        by_contra h; exact hk (hne'.mpr h)
      obtain ⟨hsq, hpos0⟩ := hne.resolve_left hk
      have hfold := foldl_optAbsorb1_dropped p xs
        (CircuitType.readVal (val := Poseidon.Triple F) V st, pb) hdrop
      rw [hnil] at hrel0 ⊢
      simp only [Poseidon.absorb, List.foldl_nil] at hrel0 ⊢
      refine ⟨rel_of_relStart p hrel0 hsq, fun hp => ?_⟩
      rw [hfold] at hp
      have hany : xs.any (·.1) = false := List.any_eq_false.mpr fun v hv => by
        simp [hdrop v hv]
      simp only [hany, Bool.not_false, Bool.true_and]
      exact hpos0 hp
  have hAnyV : ∀ anyK : BoolVar F, ((∀ b ∈ input.map (fun q : BoolVar F × FVar F => q.1),
      (↑b : CVar F).val V = 0 ∨ (↑b : CVar F).val V = 1) →
      (↑anyK : CVar F).val V = if ∃ b ∈ input.map (fun q : BoolVar F × FVar F => q.1),
        (↑b : CVar F).val V = 1 then 1 else 0) →
      (↑anyK : CVar F).val V = bit (xs.any (·.1)) := by
    intro anyK hAny
    rw [hAny hbool]
    by_cases h : ∃ v ∈ xs, v.1 = true
    · rw [if_pos (hex.mpr h)]; simp [bit, List.any_eq_true, h]
    · rw [if_neg (fun h' => h (hex.mp h'))]; simp [bit, List.any_eq_true, h]
  simp only [consume, hpu]
  cases leftover with
  | none =>
    cases hlF
    have hfold := foldl_pairUp p xs
    rw [hpx] at hfold
    simp only at hfold
    mvcgen [hP, hany, hcp, hfb]
    rename_i _ acc _ hAcc anyK _ hAny sp _ hOr fin _
    intro hFin pb ps hp hstart hne
    obtain ⟨hst, hpos⟩ := hAcc pb hp
    obtain ⟨hrel, hempty⟩ := hend pb ps hstart hne
    have hE := not_val (hAnyV anyK hAny)
    have hSp := hOr _ _ hE hpos
    have hF := hFin _ hSp
    rw [hF, hst]
    show optFinalState p (List.foldl (optAbsorb2 p)
      (CircuitType.readVal (val := Poseidon.Triple F) V st, pb) vpairs)
        ((!xs.any (·.1)) && nf) = _
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
    have hbe : bb = true → ((!xs.any (·.1)) && nf) = false := fun h => by
      have : xs.any (·.1) = true := List.any_eq_true.mpr ⟨(bb, xv), hmem _ rfl, h⟩
      simp [this]
    mvcgen [hP, hany, hcp, addIn_spec, hfbl]
    rename_i _ acc _ hAcc anyK _ hAny _ _ _ xb _ hxb st' _ hSt sp _ hAny3 fin _
    intro hFin pb ps hp hstart hne
    obtain ⟨hst, hpos⟩ := hAcc pb hp
    obtain ⟨hrel, hempty⟩ := hend pb ps hstart hne
    have hE := not_val (hAnyV anyK hAny)
    rw [hb, hxv] at hxb
    have hS := hSt _ hpos
    rw [hst, hxb] at hS
    have hSp := hAny3 _ _ _ hE hpos hb
    have hF := hFin _ hSp
    rw [hF, hS]
    have hfold' := hfold (CircuitType.readVal (val := Poseidon.Triple F) V st, pb)
    generalize List.foldl (optAbsorb2 p)
      (CircuitType.readVal (val := Poseidon.Triple F) V st, pb) vpairs = fd at hfold' ⊢
    obtain ⟨fst, fpos⟩ := fd
    rw [optFinalState_leftover p fst fpos bb ((!xs.any (·.1)) && nf) xv hbe, hfold']
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
  have hc := consume_spec (V := V) p hsize hall initState false_ true input xs hx hchar
  simp only [squeeze]
  mvcgen [hc]
  rename_i _ fin _ hfin
  have hf : (↑(false_ : BoolVar F) : CVar F).val V = bit false := by simp [false_, bit]
  have hinit : CircuitType.readVal (val := Poseidon.Triple F) V initState = (0, 0, 0) := by
    simp [initState, readVal_spongeState]
  have hF := hfin false Poseidon.init hf (by rw [hinit]; exact Or.inl (rel_init p))
    (Or.inr ⟨fun n h => (nomatch h), fun _ => iff_of_true trivial rfl⟩)
  have hs0 : fin.s0.val V = (CircuitType.readVal (val := Poseidon.Triple F) V fin).1 := by
    simp [readVal_spongeState]
  rw [hs0, hF]
  exact (squeeze_fst_of_absorbed p _ (absorb_mode_absorbed p _ _ ⟨0, rfl⟩)).symm


/-! ## The phase machine's readings -/

omit [DecidableEq F] in
/-- A squeezed conditional sponge reads as a value sponge: the states agree, the slot is the
mode's, and the empty-input permute is on. -/
def SqueezedReads (V : Valuation F) (ov : OptSpongeVar F) (ps : Poseidon.State F) : Prop :=
  ∃ n, ov.phase = .squeezed n ∧
    CircuitType.readVal (val := Poseidon.Triple F) V ov.state = ps.state ∧
    ps.mode = .squeezed n ∧ ov.needsFinalPermuteIfEmpty = true

omit [DecidableEq F] in
/-- An absorbing conditional sponge reads as a start `ps₀` at the position bit's reading
`ib`, its pending inputs (oldest first) reading as `pend`, the empty-input permute `nf` (on
unless given). -/
def AbsorbingReads (p : Poseidon.Params F) (V : Valuation F) (ov : OptSpongeVar F) (ib : Bool)
    (ps₀ : Poseidon.State F) (pend : List (Bool × F)) (nf : Bool := true) : Prop :=
  ∃ i xs, ov.phase = .absorbing i xs ∧ (↑i : CVar F).val V = bit ib ∧
    RelStart p (CircuitType.readVal (val := Poseidon.Triple F) V ov.state, ib) ps₀ ∧
    List.Forall₂ (CircuitType.Reads V) xs.reverse pend ∧ ov.needsFinalPermuteIfEmpty = nf

omit [BasicSystem F c] [KimchiSystem F c] in
/-- The fresh conditional sponge reads as the fresh value sponge with nothing pending. -/
theorem create_reads (p : Poseidon.Params F) :
    AbsorbingReads p V (create (F := F)) false Poseidon.init [] :=
  ⟨false_, [], rfl, by simp [false_, bit],
    by simpa [create, initState, readVal_spongeState] using Or.inl (rel_init p), .nil, rfl⟩

omit [BasicSystem F c] [KimchiSystem F c] in
/-- Absorbing while absorbing appends to the pending readings. -/
theorem optAbsorb_reads_absorbing {p : Poseidon.Params F} {ov : OptSpongeVar F} {ib : Bool}
    {ps₀ : Poseidon.State F} {pend : List (Bool × F)} {nf : Bool}
    (h : AbsorbingReads p V ov ib ps₀ pend nf) {e : BoolVar F × FVar F} {v : Bool × F}
    (he : CircuitType.Reads V e v) :
    AbsorbingReads p V (optAbsorb ov e) ib ps₀ (pend ++ [v]) nf := by
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

/-- Under any valuation satisfying the emitted constraints, squeezing an absorbing sponge
consumes the pending inputs and reads as the value squeeze of the start after absorbing the
kept ones, given some kept input or, with none kept, a start that is absorbing and, at
position `0`, has the empty-input permute on exactly at an empty block. -/
theorem optSqueeze_absorbing_spec (p : Poseidon.Params F)
    (hsize : p.roundConstants.size = Poseidon.fullRounds)
    (hall : ∀ j k : ℕ, j ≤ 3 → k ≤ 3 → (j : F) = k → j = k) (ov : OptSpongeVar F) (ib : Bool)
    (ps₀ : Poseidon.State F) (pend : List (Bool × F)) (nf : Bool)
    (h : AbsorbingReads p V ov ib ps₀ pend nf)
    (hne : (∃ v ∈ pend, v.1 = true) ∨ ((∀ n, ps₀.mode ≠ .squeezed n) ∧
      (ib = false → (nf = true ↔ ps₀.mode = .absorbed 0))))
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
  have hc := consume_spec (V := V) p hsize hall st i nf xs.reverse pend hxs (by rwa [hlen])
  have habs : ∃ m, (Poseidon.absorb p ps₀ ((pend.filter (·.1)).map (·.2))).mode = .absorbed m := by
    rcases hne with hne | ⟨hsq, -⟩
    · exact absorb_mode_absorbed_of_ne_nil p ps₀ _ (by
        simp only [ne_eq, List.map_eq_nil_iff, List.filter_eq_nil_iff, not_forall, not_not]
        obtain ⟨v, hv, hb⟩ := hne
        exact ⟨v, hv, hb⟩)
    · refine absorb_mode_absorbed p _ ps₀ ?_
      cases hm : ps₀.mode with
      | absorbed m => exact ⟨m, rfl⟩
      | squeezed n => exact absurd hm (hsq n)
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
      (optSqueeze_absorbing_spec p hsize hall ov ib ps₀ pend true h
        (hne.imp_right fun h0 => ⟨fun n hn => by simp [h0] at hn, fun _ => by simp [h0]⟩)
        hchar) nv hsat⟩

omit [DecidableEq F] [BasicSystem F c] [KimchiSystem F c] in
/-- The plain sponge a squeezed conditional sponge hands over reads as the same value
sponge. -/
theorem toRegularSponge_reads {ov : OptSpongeVar F} {ps : Poseidon.State F}
    (h : SqueezedReads V ov ps) : SpongeVar.ReadsAt V (toRegularSponge ov) ps := by
  obtain ⟨n, hph, hst, hm, -⟩ := h
  exact ⟨by simpa [toRegularSponge, hph] using hst, by simp [toRegularSponge, hph, hm]⟩

/-- Under any valuation satisfying the emitted constraints, the conditional sponge `ofSponge`
builds from an absorbing plain sponge reads as absorbing from the same value sponge with
nothing pending, its empty-input permute on at an empty block. -/
theorem ofSponge_spec (p : Poseidon.Params F)
    (hsize : p.roundConstants.size = Poseidon.fullRounds) (sv : SpongeVar F) :
    ⦃⌜True⌝⦄ ofSponge (c := Builder V (KimchiConstraint F)) p sv
    ⦃⇓ ov _ => ⌜∀ s : Poseidon.State F, SpongeVar.ReadsAt V sv s →
      (∀ n, s.mode ≠ .squeezed n) → ∃ ib nf, AbsorbingReads p V ov ib s [] nf ∧
        (ib = false → (nf = true ↔ s.mode = .absorbed 0))⌝⦄ := by
  obtain ⟨st, mode⟩ := sv
  cases mode with
  | squeezed n =>
    simp only [ofSponge]
    mvcgen
    intro s hs hsq
    exact absurd hs.2.symm (hsq n)
  | absorbed m =>
    match m with
    | ⟨0, _⟩ =>
      simp only [ofSponge]
      mvcgen
      intro s hs _
      obtain ⟨hst, hm⟩ := hs
      refine ⟨false, true, ⟨false_, [], rfl, by simp [false_, bit], ?_, .nil, rfl⟩,
        fun _ => iff_of_true rfl hm.symm⟩
      exact Or.inl (by simp [Rel, ← hm, hst])
    | ⟨1, _⟩ =>
      simp only [ofSponge]
      mvcgen
      intro s hs _
      obtain ⟨hst, hm⟩ := hs
      refine ⟨true, true, ⟨true_, [], rfl, by simp [true_, bit], ?_, .nil, rfl⟩,
        fun h => absurd h (by simp)⟩
      exact Or.inl (by simp [Rel, ← hm, hst])
    | ⟨2, _⟩ =>
      simp only [ofSponge]
      have hp := Poseidon.poseidon_spec (V := V) p hsize st
      mvcgen [hp]
      rename_i st' _ hst'
      intro s hs _
      obtain ⟨hst, hm⟩ := hs
      refine ⟨false, false, ⟨false_, [], rfl, by simp [false_, bit], ?_, .nil, rfl⟩,
        fun _ => ⟨fun h => absurd h (by simp), fun h => absurd (hm.trans h) (by simp)⟩⟩
      exact Or.inl (by simp [Rel, ← hm, hst', hst])

/-! The gadgets are sealed after their specs: a consumer composes `squeeze_spec` and
`optSqueeze_spec`, never the bodies. -/
attribute [irreducible] addIn condPermute consumePair consumePairs consume squeeze optSqueeze

end OptSponge

end Pickles
