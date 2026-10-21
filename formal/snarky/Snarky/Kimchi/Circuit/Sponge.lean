import Snarky.DSL.Utils
import Snarky.Kimchi.Circuit.Poseidon

/-!
# The in-circuit duplex sponge

Transcribes packages/random-oracle/src/Snarky/Circuit/RandomOracle/Sponge.purs: the
absorb/squeeze automaton of `Poseidon.absorb1`/`Poseidon.squeeze` with the state as
circuit variables (a `SpongeState`, reading as a `SpongeStateVal`), the permutation as
the `poseidon` gadget, and every absorption sealed by `sealVar`.

The state cells are the only circuit data; the mode (`Poseidon.SpongeMode`) is metadata
steering which constraints are emitted: one `poseidon` block per permutation, one seal
per absorb, and free squeeze reads.

One section per gadget: the definition and its soundness spec, then the definition sealed
`irreducible`; the completeness laws, at the prover's reading, close the file. The reading
relations come first, since every law is stated in them. The rate-boundary tests are spelled
`n.val = 2`, as in the value sponge, so each law's case split matches the value automaton's.
-/

namespace Snarky.Kimchi

open Snarky

variable {F c : Type}

/-- An in-circuit duplex sponge: the state as circuit variables, plus the mode shared
with the value sponge. -/
structure SpongeVar (F : Type) where
  /-- The width-3 Poseidon state, as circuit variables. -/
  state : SpongeState F
  /-- The automaton direction and intra-block position — metadata, not circuit data. -/
  mode : Poseidon.SpongeMode

namespace SpongeVar

/-- The fresh sponge: constant-zero state, `absorbed 0`. -/
def init [Zero F] : SpongeVar F :=
  ⟨⟨.const 0, .const 0, .const 0⟩, .absorbed 0⟩

/-- Seed a sponge from a value-level state: the cells as constants, the same mode. -/
def ofConstants (s : Poseidon.State F) : SpongeVar F :=
  ⟨⟨.const s.state.1, .const s.state.2.1, .const s.state.2.2⟩, s.mode⟩

/-! ## Reading a sponge

A circuit sponge implements a value sponge when its cells read that sponge's cells and
the modes agree; the mode is metadata, so it must match exactly. `ReadsAt` is the
soundness side (a valuation), `Reads` the completeness side (an assertion over prover tables:
scope and reading). -/

/-- The sponge's reading under a valuation: cells and mode. -/
def ReadsAt [Add F] [Mul F] [Zero F] (V : Valuation F) (sv : SpongeVar F)
    (s : Poseidon.State F) : Prop :=
  CircuitType.readVal (val := SpongeStateVal F) V sv.state = s.state ∧ sv.mode = s.mode

/-- The fresh circuit sponge reads as the fresh value sponge. -/
theorem ReadsAt.init [Field F] {V : Valuation F} :
    ReadsAt V (SpongeVar.init (F := F)) (Poseidon.init (F := F)) :=
  ⟨rfl, rfl⟩

/-- A sponge seeded from constants reads as its value-level state. -/
theorem ReadsAt.ofConstants [Field F] {V : Valuation F} (s : Poseidon.State F) :
    ReadsAt V (SpongeVar.ofConstants s) s :=
  ⟨rfl, rfl⟩

/-- The sponge's reading at the prover's tables: its state reads this value sponge's state,
and the modes agree. -/
def Reads [Add F] [Mul F] [Zero F] (sv : SpongeVar F) (s : Poseidon.State F) :
    Prover.Pred F :=
  Prover.Reads (val := SpongeStateVal F) sv.state s.state ⊓ Prover.Pred.ofProp (sv.mode = s.mode)

/-! ## The rate slot -/

/-- Seal `x` into rate slot `n`: `Poseidon.addSlot` over circuit variables, with `x` as
the left addend. -/
private def addSlotVar [Field F] [DecidableEq F] [BasicSystem F c] [ConstraintHolds F c]
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

open Std.WP in
/-- **Soundness** (`addSlotVar`): the output state reads as `Poseidon.addSlot` of the
input state's reading — the seal reads as the sum, in either operand order. -/
@[spec] private theorem addSlotVar_spec {V : Valuation F} [Field F] [DecidableEq F]
    [BasicSystem F c] [ConstraintHolds F c] [LawfulBasicSystem F c]
    (s : SpongeState F) (n : Fin 3) (x : FVar F) :
    ⦃fun _ => True⦄
    addSlotVar (c := Builder V c) s n x
    ⦃fun r _ => CircuitType.readVal (val := SpongeStateVal F) V r
      = Poseidon.addSlot (CircuitType.readVal (val := SpongeStateVal F) V s) n
          (x.val V)⦄ := by
  match n with
  | 0 =>
    simp only [addSlotVar]
    vcgen
    simp_all [Poseidon.addSlot, CVar.val_add_, add_comm]
  | 1 =>
    simp only [addSlotVar]
    vcgen
    simp_all [Poseidon.addSlot, CVar.val_add_, add_comm]
  | 2 =>
    simp only [addSlotVar]
    vcgen
    simp_all [Poseidon.addSlot, CVar.val_add_, add_comm]

attribute [irreducible] addSlotVar

/-! ## Absorb -/

/-- Absorb one element: seal into the next rate slot, permuting first when the rate is
full; absorbing after a squeeze restarts at slot 0. Mirrors `Poseidon.absorb1` branch
for branch. -/
def absorb [Field F] [DecidableEq F] [BasicSystem F c] [ConstraintHolds F c] [KimchiSystem F c]
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

open Std.WP in
/-- **Soundness** (`absorb`): the output sponge reads as the value single-element absorb
`Poseidon.absorb1` of whatever sponge the input reads as. -/
@[spec] theorem absorb_spec {V : Valuation F} [Field F] [DecidableEq F]
    (p : Poseidon.Params F) (hsize : p.roundConstants.size = Poseidon.fullRounds)
    (sv : SpongeVar F) (x : FVar F) :
    ⦃fun _ => True⦄
    absorb (c := Builder V (KimchiConstraint F)) p sv x
    ⦃fun r _ => ∀ s, ReadsAt V sv s → ReadsAt V r (Poseidon.absorb1 p s (x.val V))⦄ := by
  obtain ⟨stv, mode⟩ := sv
  have pspec := Poseidon.poseidon_spec (V := V) p hsize
  cases mode with
  | absorbed n =>
    by_cases hn : n.val = 2
    · simp only [absorb, ite_eq_left hn]
      vcgen [pspec]
      rename_i hpos _ hslot st₀ hr
      obtain ⟨sst, smode⟩ := st₀
      obtain ⟨hst, hm⟩ := hr
      simp only at hm
      subst hm
      rw [hst] at hpos
      rw [hpos] at hslot
      simp only [Poseidon.absorb1, ite_eq_left hn]
      exact ⟨hslot, rfl⟩
    · simp only [absorb, ite_eq_right hn]
      vcgen
      rename_i hslot st₀ hr
      obtain ⟨sst, smode⟩ := st₀
      obtain ⟨hst, hm⟩ := hr
      simp only at hm
      subst hm
      rw [hst] at hslot
      simp only [Poseidon.absorb1, ite_eq_right hn]
      exact ⟨hslot, rfl⟩
  | squeezed n =>
    simp only [absorb]
    vcgen
    rename_i hslot st₀ hr
    obtain ⟨sst, smode⟩ := st₀
    obtain ⟨hst, hm⟩ := hr
    simp only at hm
    subst hm
    rw [hst] at hslot
    simp only [Poseidon.absorb1]
    exact ⟨hslot, rfl⟩

attribute [irreducible] absorb

/-! ## Squeeze -/

/-- Read rate slot `n` — `Poseidon.slot` over circuit variables. Emits nothing. -/
private def slotVar (s : SpongeState F) : Fin 3 → FVar F
  | 0 => s.s0
  | 1 => s.s1
  | _ => s.s2

/-- `slotVar` reads the value sponge's slot. -/
private theorem slotVar_val [Field F] {V : Valuation F} {s : SpongeState F}
    {v : Poseidon.Triple F} (h : CircuitType.readVal (val := SpongeStateVal F) V s = v) :
    ∀ n : Fin 3, (slotVar s n).val V = Poseidon.slot v n := by
  intro n
  subst h
  match n with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl

/-- `slotVar` is one of the state's cells, so it is in scope when the state is. -/
private theorem slotVar_scoped [Field F] {st : ProverState F} {s : SpongeState F}
    (h : CircuitType.Scoped (val := SpongeStateVal F) st s) :
    ∀ n : Fin 3, (slotVar s n).Scoped st := by
  rw [scoped_spongeState] at h
  intro n
  match n with
  | 0 => exact h.1
  | 1 => exact h.2.1
  | 2 => exact h.2.2

/-- Squeeze one element: read the next rate slot, permuting first when entering squeeze
mode or when the block is exhausted. Mirrors `Poseidon.squeeze` branch for branch. -/
def squeeze [Field F] [DecidableEq F] [BasicSystem F c] [ConstraintHolds F c] [KimchiSystem F c]
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

open Std.WP in
/-- **Soundness** (`squeeze`): the returned element reads as the value squeeze's element
and the output sponge as its state, at whatever sponge the input reads as. -/
@[spec] theorem squeeze_spec {V : Valuation F} [Field F] [DecidableEq F]
    (p : Poseidon.Params F) (hsize : p.roundConstants.size = Poseidon.fullRounds)
    (sv : SpongeVar F) :
    ⦃fun _ => True⦄
    squeeze (c := Builder V (KimchiConstraint F)) p sv
    ⦃fun r _ => ∀ s, ReadsAt V sv s →
      r.1.val V = (Poseidon.squeeze p s).1 ∧
        ReadsAt V r.2 (Poseidon.squeeze p s).2⦄ := by
  obtain ⟨stv, mode⟩ := sv
  have pspec := Poseidon.poseidon_spec (V := V) p hsize
  cases mode with
  | squeezed n =>
    by_cases hn : n.val = 2
    · simp only [squeeze, ite_eq_left hn]
      vcgen [pspec]
      rename_i hpos st₀ hr
      obtain ⟨sst, smode⟩ := st₀
      obtain ⟨hst, hm⟩ := hr
      simp only at hm
      subst hm
      rw [hst] at hpos
      simp only [Poseidon.squeeze, ite_eq_left hn]
      exact ⟨slotVar_val hpos 0, hpos, rfl⟩
    · simp only [squeeze, ite_eq_right hn]
      vcgen
      rename_i st₀ hr
      obtain ⟨sst, smode⟩ := st₀
      obtain ⟨hst, hm⟩ := hr
      simp only at hm
      subst hm
      simp only [Poseidon.squeeze, ite_eq_right hn]
      exact ⟨slotVar_val hst n, hst, rfl⟩
  | absorbed n =>
    simp only [squeeze]
    vcgen [pspec]
    rename_i hpos st₀ hr
    obtain ⟨sst, smode⟩ := st₀
    obtain ⟨hst, hm⟩ := hr
    simp only at hm
    subst hm
    rw [hst] at hpos
    simp only [Poseidon.squeeze]
    exact ⟨slotVar_val hpos 0, hpos, rfl⟩

/-! ## At the prover's reading

Each law at the prover's reading (`Snarky.Prover.VCGen`): the sponge's and the element's readings
in, the value automaton's step at those readings out. The permutation is
`Poseidon.Prover.poseidon_spec` and the seal `Prover.sealVar_spec`, cited at the gadget's
parameters. -/

section ProverReading

open Snarky.Prover Std.WP

/-- A state reads a triple exactly when its cells are in scope and read the components. -/
private theorem Prover.reads_spongeState_apply [Field F] (s : SpongeState F)
    (v : SpongeStateVal F) (st : ProverState F) :
    Prover.Reads s v st ↔ s.s0.Scoped st ∧ s.s1.Scoped st ∧ s.s2.Scoped st ∧
      s.s0.val st.env.get = v.1 ∧ s.s1.val st.env.get = v.2.1 ∧
        s.s2.val st.env.get = v.2.2 := by
  change CircuitType.ReadsAs st s v ↔ _
  simp only [CircuitType.ReadsAs, scoped_spongeState, reads_spongeState, and_assoc]

/-- A sponge reads a value sponge exactly when its state reads the value state and the modes
agree. -/
private theorem Prover.reads_spongeVar_apply [Field F] (sv : SpongeVar F)
    (s : Poseidon.State F) (st : ProverState F) :
    Reads sv s st ↔ Prover.Reads (val := SpongeStateVal F) sv.state s.state st ∧
      sv.mode = s.mode :=
  Iff.rfl

/-- `addSlotVar`'s completeness: the output state reads `Poseidon.addSlot` of the input state's
and the element's readings. -/
private theorem Prover.addSlotVar_spec [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] [LawfulBasicSystem F c] (s : SpongeState F) (n : Fin 3) (x : FVar F)
    (v : SpongeStateVal F) (a : F) :
    ⦃Prover.Reads s v ⊓ Prover.Reads x a⦄ addSlotVar (c := Prover c) s n x
    ⦃fun r ↦ Prover.Reads (val := SpongeStateVal F) r (Poseidon.addSlot v n a)⦄ := by
  have h0 := Prover.sealVar_spec (c := c) (CVar.add_ x s.s0) (a + v.1)
  have h1 := Prover.sealVar_spec (c := c) (CVar.add_ x s.s1) (a + v.2.1)
  have h2 := Prover.sealVar_spec (c := c) (CVar.add_ x s.s2) (a + v.2.2)
  match n with
  | 0 | 1 | 2 =>
    simp only [addSlotVar]
    vcgen [h0, h1, h2]
    all_goals prover_assert with
      (intros; simp_all [Prover.reads_spongeState_apply, Reads.fvar_apply, Poseidon.addSlot,
        CVar.val_add_, CVar.Scoped.add_, add_comm])

/-- `absorb`'s completeness: the output sponge reads `Poseidon.absorb1` of the input sponge's
and the element's readings. -/
theorem Prover.absorb_spec [Field F] [DecidableEq F] (p : Poseidon.Params F)
    (hsize : p.roundConstants.size = Poseidon.fullRounds) (sv : SpongeVar F) (x : FVar F)
    (s : Poseidon.State F) (a : F) :
    ⦃Reads sv s ⊓ Prover.Reads x a⦄ absorb (c := Prover (KimchiConstraint F)) p sv x
    ⦃fun r ↦ Reads r (Poseidon.absorb1 p s a)⦄ := by
  obtain ⟨stv, mode⟩ := sv
  obtain ⟨v, smode⟩ := s
  by_cases hm : mode = smode
  swap
  · rw [triple_iff]
    intro st h
    exact absurd ((Prover.reads_spongeVar_apply _ _ st).mp ((Pred.inf_apply _ _ st).mp h).1).2 hm
  subst hm
  have hp := Poseidon.Prover.poseidon_spec p hsize stv v
  have hb := fun t : SpongeState F ↦ Prover.addSlotVar_spec (c := KimchiConstraint F) t 0 x
    (Poseidon.blockCipher p v) a
  have ha := fun n : Fin 3 ↦ Prover.addSlotVar_spec (c := KimchiConstraint F) stv n x v a
  cases mode with
  | absorbed n =>
    by_cases hn : n.val = 2
    · simp only [absorb, ite_eq_left hn]
      vcgen [hp, hb]
      all_goals prover_assert with
        (intros; simp_all [Prover.reads_spongeVar_apply, Poseidon.absorb1])
    · simp only [absorb, ite_eq_right hn]
      vcgen [ha]
      all_goals prover_assert with
        (intros; simp_all [Prover.reads_spongeVar_apply, Poseidon.absorb1])
  | squeezed n =>
    simp only [absorb]
    vcgen [ha]
    all_goals prover_assert with
      (intros; simp_all [Prover.reads_spongeVar_apply, Poseidon.absorb1])

/-- `squeeze`'s completeness: the element reads the value squeeze's element and the output
sponge its state, at the input sponge's reading. -/
theorem Prover.squeeze_spec [Field F] [DecidableEq F] (p : Poseidon.Params F)
    (hsize : p.roundConstants.size = Poseidon.fullRounds) (sv : SpongeVar F)
    (s : Poseidon.State F) :
    ⦃Reads sv s⦄ squeeze (c := Prover (KimchiConstraint F)) p sv
    ⦃fun r ↦ Prover.Reads r.1 (Poseidon.squeeze p s).1 ⊓
      Reads r.2 (Poseidon.squeeze p s).2⦄ := by
  obtain ⟨stv, mode⟩ := sv
  obtain ⟨v, smode⟩ := s
  by_cases hm : mode = smode
  swap
  · rw [triple_iff]
    intro st h
    exact absurd ((Prover.reads_spongeVar_apply _ _ st).mp h).2 hm
  subst hm
  have hp := Poseidon.Prover.poseidon_spec p hsize stv v
  cases mode with
  | squeezed n =>
    by_cases hn : n.val = 2
    · simp only [squeeze, ite_eq_left hn]
      vcgen [hp]
      all_goals prover_assert with
        (intros; simp_all [Prover.reads_spongeVar_apply, Prover.reads_spongeState_apply,
          Reads.fvar_apply, Poseidon.squeeze, slotVar, Poseidon.slot])
    · simp only [squeeze, ite_eq_right hn]
      vcgen
      all_goals prover_assert with
        simp_all [Prover.reads_spongeVar_apply, Prover.reads_spongeState_apply,
          Reads.fvar_apply, Poseidon.squeeze, slotVar_scoped, slotVar_val]
  | absorbed n =>
    simp only [squeeze]
    vcgen [hp]
    all_goals prover_assert with
      (intros; simp_all [Prover.reads_spongeVar_apply, Prover.reads_spongeState_apply,
        Reads.fvar_apply, Poseidon.squeeze, slotVar, Poseidon.slot])

end ProverReading

attribute [irreducible] slotVar squeeze

end SpongeVar

end Snarky.Kimchi
