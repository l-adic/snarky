import Snarky.DSL.Utils
import Snarky.Tactic
import Snarky.Kimchi.Circuit.Poseidon

/-!
# The in-circuit duplex sponge

Port of `Snarky.Circuit.RandomOracle.Sponge`
(packages/random-oracle/src/Snarky/Circuit/RandomOracle/Sponge.purs): the absorb/squeeze
automaton of `Poseidon/Basic.lean` with the width-3 state as circuit variables, the
permutation as the `poseidon` gadget, and every absorption sealed (OCaml `add_assign`:
`state.(i) <- seal (state.(i) + x)`).

The state cells are the only circuit data; the duplex mode (`Poseidon.SpongeMode`) is
metadata steering which constraints are emitted — one `poseidon` block per permutation,
one seal per absorb, and squeeze reads are free.

Name map: `absorb`/`squeeze` keep their names on `SpongeVar`; PS `initialState` is
`SpongeVar.init`, PS `spongeFromConstants` is `SpongeVar.ofConstants`; the private slot
helpers mirror `Poseidon.slot`/`Poseidon.addSlot`.

One section per gadget: the definition, its soundness spec, its completeness law, and
then the definition is sealed `irreducible`. The sponge's own reading relations come
first, since every law is stated in them.

Deviations from the PS original:
- PS's width-3 `Vector` state renders as the gadget's `SpongeState`, reading as the
  value sponge's `Poseidon.Triple` through its `CircuitType` instance.
- PS's ambient `PoseidonField` class arrives as the explicit `p : Poseidon.Params F`
  (the Poseidon gadget's deviation, inherited).
- The rate-boundary tests are spelled `n.val = 2` as in `Poseidon.absorb1`/`squeeze`
  (PS: `n == rate` at `rate = 2`), so the laws' branch analyses align with the value
  sponge's.
- No oracle-corpus circuit exercises the sponge in isolation (the corpus covers the raw
  permutation gadget); byte-parity with PS is deferred until a sponge-bearing circuit
  is transcribed. The laws below pin the semantics to the fixture-validated value
  automaton.
-/

namespace Snarky.Kimchi

open Snarky

variable {F c : Type}

/-- An in-circuit duplex sponge (PS `Sponge (FVar f)`): the width-3 state as circuit
variables, plus the direction/position mode shared with the value sponge. -/
structure SpongeVar (F : Type) where
  /-- The width-3 Poseidon state, as circuit variables. -/
  state : SpongeState F
  /-- The automaton direction and intra-block position — metadata, not circuit data. -/
  mode : Poseidon.SpongeMode

namespace SpongeVar

/-- The fresh sponge (PS `initialState`): constant-zero state, `absorbed 0`. -/
def init [Zero F] : SpongeVar F :=
  ⟨⟨.const 0, .const 0, .const 0⟩, .absorbed 0⟩

/-- Seed a sponge from a value-level state (PS `spongeFromConstants`): the cells as
constants, the same mode. -/
def ofConstants (s : Poseidon.State F) : SpongeVar F :=
  ⟨⟨.const s.state.1, .const s.state.2.1, .const s.state.2.2⟩, s.mode⟩

/-! ## Reading a sponge

A circuit sponge implements a value sponge when its cells read that sponge's cells and
the modes agree — the mode is metadata, so it must match on the nose. `ReadsAt` is the
soundness side (a valuation), `Reads` the completeness side (scope and reading together,
transported by `Reads.mono`); the pair mirrors `OnCurveAt`/`OnCurveAs`. -/

/-- The sponge's reading under a valuation: cells and mode. -/
def ReadsAt [Add F] [Mul F] [Zero F] (V : Valuation F) (sv : SpongeVar F)
    (s : Poseidon.State F) : Prop :=
  CircuitType.readVal (val := Poseidon.Triple F) V sv.state = s.state ∧ sv.mode = s.mode

/-- The sponge's reading at a table: in scope, and reading this value sponge. -/
def Reads [Add F] [Mul F] [Zero F] (st : ProverState F) (sv : SpongeVar F)
    (s : Poseidon.State F) : Prop :=
  CircuitType.ReadsAs (val := Poseidon.Triple F) st sv.state s.state ∧ sv.mode = s.mode

/-- A sponge's reading survives the table's growth. -/
theorem Reads.mono [Add F] [Mul F] [Zero F] {st st' : ProverState F} {sv : SpongeVar F}
    {s : Poseidon.State F} (hnv : st.nv ≤ st'.nv) (hle : st.env.Le st'.env)
    (h : Reads st sv s) : Reads st' sv s :=
  ⟨CircuitType.ReadsAs.mono hnv hle h.1, h.2⟩

/-- A sponge's reading is monotone — `Reads.mono`, as walker vocabulary. -/
@[complete_mono] theorem Mono.spongeReads [Add F] [Mul F] [Zero F] {sv : SpongeVar F}
    {s : Poseidon.State F} : Snarky.Mono (F := F) fun st => Reads st sv s :=
  fun _ _ hnv hle h => h.mono hnv hle

/-- A sponge's state component reads the value sponge's. -/
@[complete_reads_fwd] theorem Reads.state [Add F] [Mul F] [Zero F] {st : ProverState F}
    {sv : SpongeVar F} {s : Poseidon.State F} (h : Reads st sv s) :
    CircuitType.ReadsAs (val := Poseidon.Triple F) st sv.state s.state := h.1

/-- A table reading is a valuation reading at that table. -/
theorem Reads.readsAt [Add F] [Mul F] [Zero F] {st : ProverState F} {sv : SpongeVar F}
    {s : Poseidon.State F} (h : Reads st sv s) : ReadsAt st.env.get sv s :=
  ⟨(CircuitType.reads_iff.mp h.1.2).2, h.2⟩

/-! ## The rate slot -/

/-- Seal `x` into rate slot `n` — `Poseidon.addSlot` over circuit variables, the PS
operand order (`seal (add_ x state[i])`) kept. -/
private def addSlotVar [Field F] [DecidableEq F] [BasicSystem F c]
    (s : SpongeState F) (n : Fin 3) (x : FVar F) :
    CircuitM F c (SpongeState F) :=
  match n with
  | 0 => do
    let cell ← sealVar (CVar.add_ x s.s0)
    pure ⟨cell, s.s1, s.s2⟩
  | 1 => do
    let cell ← sealVar (CVar.add_ x s.s1)
    pure ⟨s.s0, cell, s.s2⟩
  | _ => do
    let cell ← sealVar (CVar.add_ x s.s2)
    pure ⟨s.s0, s.s1, cell⟩

open Std.Do in
/-- **Soundness** (`addSlotVar`): the output state reads as `Poseidon.addSlot` of the
input state's reading — the seal reads as the sum, in either operand order. -/
@[spec] private theorem addSlotVar_spec {V : Valuation F} [Field F] [DecidableEq F]
    [BasicSystem F c] [ConstraintHolds F c] [LawfulBasicSystem F c]
    (s : SpongeState F) (n : Fin 3) (x : FVar F) :
    ⦃⌜True⌝⦄
    addSlotVar (c := Builder V c) s n x
    ⦃⇓ r _ => ⌜CircuitType.readVal (val := Poseidon.Triple F) V r
      = Poseidon.addSlot (CircuitType.readVal (val := Poseidon.Triple F) V s) n
          (x.val V)⌝⦄ := by
  match n with
  | 0 =>
    simp only [addSlotVar]
    mvcgen
    simp_all [Poseidon.addSlot, CVar.val_add_, add_comm]
  | 1 =>
    simp only [addSlotVar]
    mvcgen
    simp_all [Poseidon.addSlot, CVar.val_add_, add_comm]
  | 2 =>
    simp only [addSlotVar]
    mvcgen
    simp_all [Poseidon.addSlot, CVar.val_add_, add_comm]

/-- **Completeness** (`addSlotVar`): the honest run accepts on a read state and element,
and the output reads `Poseidon.addSlot` of their values. -/
@[complete_law]
private theorem addSlotVar_complete [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] [LawfulBasicSystem F c] (s : SpongeState F) (n : Fin 3)
    (x : FVar F) (sv : Poseidon.Triple F) (xv : F) :
    Complete (F := F) (c := c)
      (fun st => CircuitType.ReadsAs (val := Poseidon.Triple F) st s sv ∧
        CircuitType.ReadsAs (val := F) st x xv)
      (addSlotVar (c := c) s n x)
      (fun r st' => CircuitType.ReadsAs (val := Poseidon.Triple F) st' r
        (Poseidon.addSlot sv n xv)) := by
  match n with
  | 0 =>
    simp only [addSlotVar]
    have hsum : ∀ {st : ProverState F},
        CircuitType.ReadsAs (val := Poseidon.Triple F) st s sv →
        CircuitType.ReadsAs (val := F) st x xv →
        CircuitType.ReadsAs (val := F) st (CVar.add_ x s.s0) (xv + sv.1) :=
      fun hs hx => ⟨CircuitType.scoped_fvar.mpr
          (CVar.Scoped.add_ (CircuitType.scoped_fvar.mp hx.1)
            (scoped_spongeState.mp hs.1).1),
        CircuitType.reads_fvar.mpr (by
          rw [CVar.val_add_, CircuitType.reads_fvar.mp hx.2,
            (reads_spongeState.mp hs.2).1])⟩
    complete_walk
    refine Complete.pure_of fun st h => ?_
    refine ⟨scoped_spongeState.mpr ⟨CircuitType.scoped_fvar.mp h.2.1,
        (scoped_spongeState.mp h.1.1.1).2.1, (scoped_spongeState.mp h.1.1.1).2.2⟩,
      reads_spongeState.mpr ⟨?_, ?_, ?_⟩⟩
    · rw [show (Poseidon.addSlot sv 0 xv).1 = sv.1 + xv from rfl,
        CircuitType.reads_fvar.mp h.2.2, add_comm]
    · rw [show (Poseidon.addSlot sv 0 xv).2.1 = sv.2.1 from rfl,
        (reads_spongeState.mp h.1.1.2).2.1]
    · rw [show (Poseidon.addSlot sv 0 xv).2.2 = sv.2.2 from rfl,
        (reads_spongeState.mp h.1.1.2).2.2]
  | 1 =>
    simp only [addSlotVar]
    have hsum : ∀ {st : ProverState F},
        CircuitType.ReadsAs (val := Poseidon.Triple F) st s sv →
        CircuitType.ReadsAs (val := F) st x xv →
        CircuitType.ReadsAs (val := F) st (CVar.add_ x s.s1) (xv + sv.2.1) :=
      fun hs hx => ⟨CircuitType.scoped_fvar.mpr
          (CVar.Scoped.add_ (CircuitType.scoped_fvar.mp hx.1)
            (scoped_spongeState.mp hs.1).2.1),
        CircuitType.reads_fvar.mpr (by
          rw [CVar.val_add_, CircuitType.reads_fvar.mp hx.2,
            (reads_spongeState.mp hs.2).2.1])⟩
    complete_walk
    refine Complete.pure_of fun st h => ?_
    refine ⟨scoped_spongeState.mpr ⟨(scoped_spongeState.mp h.1.1.1).1,
        CircuitType.scoped_fvar.mp h.2.1, (scoped_spongeState.mp h.1.1.1).2.2⟩,
      reads_spongeState.mpr ⟨?_, ?_, ?_⟩⟩
    · rw [show (Poseidon.addSlot sv 1 xv).1 = sv.1 from rfl,
        (reads_spongeState.mp h.1.1.2).1]
    · rw [show (Poseidon.addSlot sv 1 xv).2.1 = sv.2.1 + xv from rfl,
        CircuitType.reads_fvar.mp h.2.2, add_comm]
    · rw [show (Poseidon.addSlot sv 1 xv).2.2 = sv.2.2 from rfl,
        (reads_spongeState.mp h.1.1.2).2.2]
  | 2 =>
    simp only [addSlotVar]
    have hsum : ∀ {st : ProverState F},
        CircuitType.ReadsAs (val := Poseidon.Triple F) st s sv →
        CircuitType.ReadsAs (val := F) st x xv →
        CircuitType.ReadsAs (val := F) st (CVar.add_ x s.s2) (xv + sv.2.2) :=
      fun hs hx => ⟨CircuitType.scoped_fvar.mpr
          (CVar.Scoped.add_ (CircuitType.scoped_fvar.mp hx.1)
            (scoped_spongeState.mp hs.1).2.2),
        CircuitType.reads_fvar.mpr (by
          rw [CVar.val_add_, CircuitType.reads_fvar.mp hx.2,
            (reads_spongeState.mp hs.2).2.2])⟩
    complete_walk
    refine Complete.pure_of fun st h => ?_
    refine ⟨scoped_spongeState.mpr ⟨(scoped_spongeState.mp h.1.1.1).1,
        (scoped_spongeState.mp h.1.1.1).2.1, CircuitType.scoped_fvar.mp h.2.1⟩,
      reads_spongeState.mpr ⟨?_, ?_, ?_⟩⟩
    · rw [show (Poseidon.addSlot sv 2 xv).1 = sv.1 from rfl,
        (reads_spongeState.mp h.1.1.2).1]
    · rw [show (Poseidon.addSlot sv 2 xv).2.1 = sv.2.1 from rfl,
        (reads_spongeState.mp h.1.1.2).2.1]
    · rw [show (Poseidon.addSlot sv 2 xv).2.2 = sv.2.2 + xv from rfl,
        CircuitType.reads_fvar.mp h.2.2, add_comm]

attribute [irreducible] addSlotVar

/-! ## Absorb -/

/-- Absorb one element (PS `absorb`): seal into the next rate slot, permuting first
when the rate is full; absorbing after a squeeze restarts at slot 0. Mirrors
`Poseidon.absorb1` branch for branch. -/
def absorb [Field F] [DecidableEq F] [BasicSystem F c] [KimchiSystem F c]
    (p : Poseidon.Params F) (sv : SpongeVar F) (x : FVar F) :
    CircuitM F c (SpongeVar F) :=
  match sv.mode with
  | .absorbed n =>
    if n.val = 2 then do
      let st ← poseidon p sv.state
      let st' ← addSlotVar st 0 x
      pure ⟨st', .absorbed 1⟩
    else do
      let st' ← addSlotVar sv.state n x
      pure ⟨st', .absorbed (n + 1)⟩
  | .squeezed _ => do
    let st' ← addSlotVar sv.state 0 x
    pure ⟨st', .absorbed 1⟩

open Std.Do in
/-- **Soundness** (`absorb`): the output sponge reads as the value single-element absorb
`Poseidon.absorb1` of whatever sponge the input reads as. -/
@[spec] theorem absorb_spec {V : Valuation F} [Field F] [DecidableEq F]
    (p : Poseidon.Params F) (hsize : p.roundConstants.size = Poseidon.fullRounds)
    (sv : SpongeVar F) (x : FVar F) :
    ⦃⌜True⌝⦄
    absorb (c := Builder V (KimchiConstraint F)) p sv x
    ⦃⇓ r _ => ⌜∀ s, ReadsAt V sv s → ReadsAt V r (Poseidon.absorb1 p s (x.val V))⌝⦄ := by
  obtain ⟨stv, mode⟩ := sv
  have pspec := Poseidon.poseidon_spec (V := V) p hsize
  cases mode with
  | absorbed n =>
    by_cases hn : n.val = 2
    · simp only [absorb, if_pos hn]
      mvcgen [pspec]
      rename_i _ _ hpos _ _ hslot
      rintro ⟨sst, smode⟩ ⟨hst, hm⟩
      simp only at hm
      subst hm
      rw [hst] at hpos
      rw [hpos] at hslot
      simp only [Poseidon.absorb1, if_pos hn]
      exact ⟨hslot, rfl⟩
    · simp only [absorb, if_neg hn]
      mvcgen
      rename_i _ _ hslot
      rintro ⟨sst, smode⟩ ⟨hst, hm⟩
      simp only at hm
      subst hm
      rw [hst] at hslot
      simp only [Poseidon.absorb1, if_neg hn]
      exact ⟨hslot, rfl⟩
  | squeezed n =>
    simp only [absorb]
    mvcgen
    rename_i _ _ hslot
    rintro ⟨sst, smode⟩ ⟨hst, hm⟩
    simp only at hm
    subst hm
    rw [hst] at hslot
    simp only [Poseidon.absorb1]
    exact ⟨hslot, rfl⟩

/-- **Completeness** (`absorb`): the honest run accepts on a read sponge and element, and
the output reads `Poseidon.absorb1` of their values. -/
theorem absorb_complete [Field F] [DecidableEq F] (p : Poseidon.Params F)
    (hsize : p.roundConstants.size = Poseidon.fullRounds) (sv : SpongeVar F) (x : FVar F)
    (s : Poseidon.State F) (xv : F) :
    Complete (F := F) (c := KimchiConstraint F)
      (fun st => Reads st sv s ∧ CircuitType.ReadsAs (val := F) st x xv)
      (absorb (c := KimchiConstraint F) p sv x)
      (fun r st' => Reads st' r (Poseidon.absorb1 p s xv)) := by
  obtain ⟨stv, mode⟩ := sv
  obtain ⟨sst, smode⟩ := s
  -- the modes agree — metadata, so `instantiate` names the identification
  refine Complete.instantiate (ι := PLift (mode = smode))
    (P := fun _ st => Reads st ⟨stv, mode⟩ ⟨sst, smode⟩ ∧
      CircuitType.ReadsAs (val := F) st x xv)
    (fun st h => ⟨⟨h.1.2⟩, h⟩) fun hm => ?_
  obtain ⟨hm⟩ := hm
  subst hm
  -- the state's reading, off the sponge's — the walk's way into the `Reads` bundle
  have hstate : ∀ {st : ProverState F}, Reads st ⟨stv, mode⟩ ⟨sst, mode⟩ →
      CircuitType.ReadsAs (val := Poseidon.Triple F) st stv sst := fun h => h.1
  cases mode with
  | absorbed n =>
    by_cases hn : n.val = 2
    · simp only [absorb, if_pos hn]
      complete_walk
      exact Complete.pure_of fun _ h =>
        ⟨by simp only [Poseidon.absorb1, if_pos hn]; exact h.2,
          by simp only [Poseidon.absorb1, if_pos hn]⟩
    · simp only [absorb, if_neg hn]
      complete_walk
      exact Complete.pure_of fun _ h =>
        ⟨by simp only [Poseidon.absorb1, if_neg hn]; exact h.2,
          by simp only [Poseidon.absorb1, if_neg hn]⟩
  | squeezed n =>
    simp only [absorb]
    complete_walk
    exact Complete.pure_of fun _ h =>
      ⟨by simp only [Poseidon.absorb1]; exact h.2, by simp only [Poseidon.absorb1]⟩

attribute [irreducible] absorb

/-! ## Squeeze -/

/-- Read rate slot `n` — `Poseidon.slot` over circuit variables. Emits nothing. -/
private def slotVar (s : SpongeState F) : Fin 3 → FVar F
  | 0 => s.s0
  | 1 => s.s1
  | _ => s.s2

/-- `slotVar` reads the value sponge's slot. -/
private theorem slotVar_val [Field F] {V : Valuation F} {s : SpongeState F}
    {v : Poseidon.Triple F} (h : CircuitType.readVal (val := Poseidon.Triple F) V s = v) :
    ∀ n : Fin 3, (slotVar s n).val V = Poseidon.slot v n := by
  intro n
  subst h
  match n with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl

/-- `slotVar` is one of the state's cells, so it is in scope when the state is. -/
private theorem slotVar_scoped [Field F] {st : ProverState F} {s : SpongeState F}
    (h : CircuitType.Scoped (val := Poseidon.Triple F) st s) :
    ∀ n : Fin 3, (slotVar s n).Scoped st := by
  rw [scoped_spongeState] at h
  intro n
  match n with
  | 0 => exact h.1
  | 1 => exact h.2.1
  | 2 => exact h.2.2

/-- Squeeze one element (PS `squeeze`): read the next rate slot, permuting first when
entering squeeze mode or when the block is exhausted. Mirrors `Poseidon.squeeze`
branch for branch; reads emit no constraints. -/
def squeeze [Field F] [DecidableEq F] [BasicSystem F c] [KimchiSystem F c]
    (p : Poseidon.Params F) (sv : SpongeVar F) :
    CircuitM F c (FVar F × SpongeVar F) :=
  match sv.mode with
  | .squeezed n =>
    if n.val = 2 then do
      let st ← poseidon p sv.state
      pure (slotVar st 0, ⟨st, .squeezed 1⟩)
    else
      pure (slotVar sv.state n, ⟨sv.state, .squeezed (n + 1)⟩)
  | .absorbed _ => do
    let st ← poseidon p sv.state
    pure (slotVar st 0, ⟨st, .squeezed 1⟩)

open Std.Do in
/-- **Soundness** (`squeeze`): the returned element reads as the value squeeze's element
and the output sponge as its state, at whatever sponge the input reads as. -/
@[spec] theorem squeeze_spec {V : Valuation F} [Field F] [DecidableEq F]
    (p : Poseidon.Params F) (hsize : p.roundConstants.size = Poseidon.fullRounds)
    (sv : SpongeVar F) :
    ⦃⌜True⌝⦄
    squeeze (c := Builder V (KimchiConstraint F)) p sv
    ⦃⇓ r _ => ⌜∀ s, ReadsAt V sv s →
      r.1.val V = (Poseidon.squeeze p s).1 ∧
        ReadsAt V r.2 (Poseidon.squeeze p s).2⌝⦄ := by
  obtain ⟨stv, mode⟩ := sv
  have pspec := Poseidon.poseidon_spec (V := V) p hsize
  cases mode with
  | squeezed n =>
    by_cases hn : n.val = 2
    · simp only [squeeze, if_pos hn]
      mvcgen [pspec]
      rename_i r₁ _ hpos
      rintro ⟨sst, smode⟩ ⟨hst, hm⟩
      simp only at hm
      subst hm
      rw [hst] at hpos
      simp only [Poseidon.squeeze, if_pos hn]
      exact ⟨slotVar_val hpos 0, hpos, rfl⟩
    · simp only [squeeze, if_neg hn]
      mvcgen
      rintro ⟨sst, smode⟩ ⟨hst, hm⟩
      simp only at hm
      subst hm
      simp only [Poseidon.squeeze, if_neg hn]
      exact ⟨slotVar_val hst n, hst, rfl⟩
  | absorbed n =>
    simp only [squeeze]
    mvcgen [pspec]
    rename_i r₁ _ hpos
    rintro ⟨sst, smode⟩ ⟨hst, hm⟩
    simp only at hm
    subst hm
    rw [hst] at hpos
    simp only [Poseidon.squeeze]
    exact ⟨slotVar_val hpos 0, hpos, rfl⟩

/-- **Completeness** (`squeeze`): the honest run accepts on a read sponge; the element
reads the value squeeze's element and the output sponge its state. -/
theorem squeeze_complete [Field F] [DecidableEq F] (p : Poseidon.Params F)
    (hsize : p.roundConstants.size = Poseidon.fullRounds) (sv : SpongeVar F)
    (s : Poseidon.State F) :
    Complete (F := F) (c := KimchiConstraint F)
      (fun st => Reads st sv s)
      (squeeze (c := KimchiConstraint F) p sv)
      (fun r st' => CircuitType.ReadsAs (val := F) st' r.1 (Poseidon.squeeze p s).1 ∧
        Reads st' r.2 (Poseidon.squeeze p s).2) := by
  obtain ⟨stv, mode⟩ := sv
  obtain ⟨sst, smode⟩ := s
  have hslot : ∀ (stk : ProverState F) (t : SpongeState F) (v : Poseidon.Triple F),
      CircuitType.ReadsAs (val := Poseidon.Triple F) stk t v → ∀ k : Fin 3,
        CircuitType.ReadsAs (val := F) stk (slotVar t k) (Poseidon.slot v k) := by
    intro stk t v h k
    exact ⟨CircuitType.scoped_fvar.mpr (slotVar_scoped h.1 k),
      CircuitType.reads_fvar.mpr (slotVar_val (CircuitType.reads_iff.mp h.2).2 k)⟩
  -- the modes agree — metadata, so `instantiate` names the identification
  refine Complete.instantiate (ι := PLift (mode = smode))
    (P := fun _ st => Reads st ⟨stv, mode⟩ ⟨sst, smode⟩)
    (fun st h => ⟨⟨h.2⟩, h⟩) fun hm => ?_
  obtain ⟨hm⟩ := hm
  subst hm
  -- the state's reading, off the sponge's — the walk's way into the `Reads` bundle
  have hstate : ∀ {st : ProverState F}, Reads st ⟨stv, mode⟩ ⟨sst, mode⟩ →
      CircuitType.ReadsAs (val := Poseidon.Triple F) st stv sst := fun h => h.1
  cases mode with
  | squeezed n =>
    by_cases hn : n.val = 2
    · simp only [squeeze, if_pos hn]
      complete_walk
      refine Complete.pure_of fun stk h => ?_
      refine ⟨?_, ?_, ?_⟩
      · simpa only [Poseidon.squeeze, if_pos hn] using hslot stk st _ h.2 0
      · simpa only [Poseidon.squeeze, if_pos hn] using h.2
      · simp only [Poseidon.squeeze, if_pos hn]
    · simp only [squeeze, if_neg hn]
      refine Complete.pure_of fun st h => ?_
      refine ⟨?_, ?_, ?_⟩
      · simpa only [Poseidon.squeeze, if_neg hn] using hslot st stv _ h.1 n
      · simpa only [Poseidon.squeeze, if_neg hn] using h.1
      · simp only [Poseidon.squeeze, if_neg hn]
  | absorbed n =>
    simp only [squeeze]
    complete_walk
    refine Complete.pure_of fun stk h => ?_
    refine ⟨?_, ?_, ?_⟩
    · simpa only [Poseidon.squeeze] using hslot stk st _ h.2 0
    · simpa only [Poseidon.squeeze] using h.2
    · simp only [Poseidon.squeeze]

attribute [irreducible] slotVar squeeze

end SpongeVar

end Snarky.Kimchi
