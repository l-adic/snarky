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
soundness side (a valuation), `Reads` the completeness side (scope and reading at a table),
as with `OnCurveAt`/`OnCurveAs`. -/

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

/-- The sponge's reading at a table: in scope, and reading this value sponge. -/
def Reads [Add F] [Mul F] [Zero F] (st : ProverState F) (sv : SpongeVar F)
    (s : Poseidon.State F) : Prop :=
  CircuitType.ReadsAs (val := SpongeStateVal F) st sv.state s.state ∧ sv.mode = s.mode

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

Each law is state-relative: the output reads the value automaton's step at the entry table's
readings. The permutation is `Poseidon.Prover.poseidon_spec`, cited at the gadget's parameters. -/

open Std.Do in
/-- `addSlotVar`'s state-relative completeness: the output state reads `Poseidon.addSlot` of
the input state's and the element's readings. -/
private theorem Prover.addSlotVar_spec [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] [LawfulBasicSystem F c] (s : SpongeState F) (n : Fin 3) (x : FVar F)
    (st₀ : ProverState F) :
    ⦃fun st => ⌜st = st₀ ∧ CircuitType.Scoped (val := SpongeStateVal F) st₀ s ∧ x.Scoped st₀⌝⦄
    addSlotVar (c := Prover c) s n x
    ⦃⇓ r st' => ⌜CircuitType.ReadsAs (val := SpongeStateVal F) st' r
        (Poseidon.addSlot (CircuitType.readVal (val := SpongeStateVal F) st₀.env.get s) n
          (st₀.read x)) ∧ st₀ ≤ st'⌝⦄ := by
  match n with
  | 0 | 1 | 2 =>
    simp only [addSlotVar]
    mvcgen
    case vc1 =>
      rename_i _ h
      obtain ⟨rfl, hs, hx⟩ := h
      obtain ⟨h0, h1, h2⟩ := scoped_spongeState.mp hs
      exact ⟨trivial, CVar.Scoped.add_ hx ‹_›⟩
    case vc2 =>
      rename_i s₀ h₀ r s₁ h₁
      obtain ⟨rfl, hs, hx⟩ := h₀
      obtain ⟨hr, hrv, hle⟩ := Prover.Reg.iff.mp h₁
      obtain ⟨h0, h1, h2⟩ := scoped_spongeState.mp hs
      simp only [ProverState.read, CVar.val_add_] at hrv
      refine ⟨⟨scoped_spongeState.mpr ⟨?_, ?_, ?_⟩, reads_spongeState.mpr ⟨?_, ?_, ?_⟩⟩, hle⟩
      all_goals first
        | exact hr
        | exact CVar.Scoped.of_le hle ‹_›
        | simp [readVal_spongeState, Poseidon.addSlot, ProverState.read, hrv,
            CVar.val_of_le hle h0, CVar.val_of_le hle h1, CVar.val_of_le hle h2, add_comm]

open Std.Do in
/-- `absorb`'s state-relative completeness: from a sponge whose state is in scope and an element
in scope, the output sponge reads `Poseidon.absorb1` of the input's readings. -/
theorem Prover.absorb_spec [Field F] [DecidableEq F] (p : Poseidon.Params F)
    (hsize : p.roundConstants.size = Poseidon.fullRounds) (sv : SpongeVar F) (x : FVar F)
    (st₀ : ProverState F) :
    ⦃fun st => ⌜st = st₀ ∧ CircuitType.Scoped (val := SpongeStateVal F) st₀ sv.state ∧
      x.Scoped st₀⌝⦄
    absorb (c := Prover (KimchiConstraint F)) p sv x
    ⦃⇓ r st' => ⌜Reads st' r (Poseidon.absorb1 p
        ⟨CircuitType.readVal (val := SpongeStateVal F) st₀.env.get sv.state, sv.mode⟩
        (st₀.read x)) ∧ st₀ ≤ st'⌝⦄ := by
  have hp := fun t => Prover.register (Poseidon.Prover.poseidon_spec p hsize t)
  have ha := fun t n y => Prover.register
    (Prover.addSlotVar_spec (F := F) (c := KimchiConstraint F) t n y)
  obtain ⟨stv, mode⟩ := sv
  cases mode with
  | absorbed n =>
    by_cases hn : n.val = 2
    · simp only [absorb, ite_eq_left hn]
      mvcgen [hp, ha]
      case vc2 =>
        rename_i _ h
        obtain ⟨rfl, hs, -⟩ := h
        exact ⟨trivial, hs⟩
      case vc3 =>
        rename_i s₀ h₀ r s₁ h₁
        obtain ⟨rfl, -, hx⟩ := h₀
        obtain ⟨hr, hle⟩ := Prover.Reg.iff.mp h₁
        exact ⟨trivial, hr.1, hx.of_le hle⟩
      case vc4 =>
        rename_i s₀ h₀ r s₁ h₁ r' s₂ h₂
        obtain ⟨rfl, -, hx⟩ := h₀
        obtain ⟨hr, hle₁⟩ := Prover.Reg.iff.mp h₁
        obtain ⟨hr', hle₂⟩ := Prover.Reg.iff.mp h₂
        rw [(CircuitType.reads_iff.mp hr.2).2, ProverState.read_of_le hle₁ hx] at hr'
        refine ⟨⟨?_, ?_⟩, hle₁.trans hle₂⟩
        · simpa only [Poseidon.absorb1, ite_eq_left hn] using hr'
        · simp only [Poseidon.absorb1, ite_eq_left hn]
    · simp only [absorb, ite_eq_right hn]
      mvcgen [hp, ha]
      case vc1 =>
        rename_i _ h
        obtain ⟨rfl, hs, hx⟩ := h
        exact ⟨trivial, hs, hx⟩
      case vc2 =>
        rename_i s₀ h₀ r s₁ h₁
        obtain ⟨rfl, -, -⟩ := h₀
        obtain ⟨hr, hle⟩ := Prover.Reg.iff.mp h₁
        refine ⟨⟨?_, ?_⟩, hle⟩
        · simpa only [Poseidon.absorb1, ite_eq_right hn] using hr
        · simp only [Poseidon.absorb1, ite_eq_right hn]
  | squeezed n =>
    simp only [absorb]
    mvcgen [hp, ha]
    case vc1 =>
      rename_i _ h
      obtain ⟨rfl, hs, hx⟩ := h
      exact ⟨trivial, hs, hx⟩
    case vc2 =>
      rename_i s₀ h₀ r s₁ h₁
      obtain ⟨rfl, -, -⟩ := h₀
      obtain ⟨hr, hle⟩ := Prover.Reg.iff.mp h₁
      refine ⟨⟨?_, ?_⟩, hle⟩
      · simpa only [Poseidon.absorb1] using hr
      · simp only [Poseidon.absorb1]

open Std.Do in
/-- `squeeze`'s state-relative completeness: from a sponge whose state is in scope, the element
reads the value squeeze's element and the output sponge its state, at the input's readings. -/
theorem Prover.squeeze_spec [Field F] [DecidableEq F] (p : Poseidon.Params F)
    (hsize : p.roundConstants.size = Poseidon.fullRounds) (sv : SpongeVar F)
    (st₀ : ProverState F) :
    ⦃fun st => ⌜st = st₀ ∧ CircuitType.Scoped (val := SpongeStateVal F) st₀ sv.state⌝⦄
    squeeze (c := Prover (KimchiConstraint F)) p sv
    ⦃⇓ r st' => ⌜r.1.Scoped st' ∧ st'.read r.1 = (Poseidon.squeeze p
        ⟨CircuitType.readVal (val := SpongeStateVal F) st₀.env.get sv.state, sv.mode⟩).1 ∧
      Reads st' r.2 (Poseidon.squeeze p
        ⟨CircuitType.readVal (val := SpongeStateVal F) st₀.env.get sv.state, sv.mode⟩).2 ∧
      st₀ ≤ st'⌝⦄ := by
  have hp := fun t => Prover.register (Poseidon.Prover.poseidon_spec p hsize t)
  obtain ⟨stv, mode⟩ := sv
  cases mode with
  | squeezed n =>
    by_cases hn : n.val = 2
    · simp only [squeeze, ite_eq_left hn]
      mvcgen [hp]
      case vc2 =>
        rename_i _ h
        obtain ⟨rfl, hs⟩ := h
        exact ⟨trivial, hs⟩
      case vc3 =>
        rename_i s₀ h₀ r s₁ h₁
        obtain ⟨rfl, -⟩ := h₀
        obtain ⟨hr, hle⟩ := Prover.Reg.iff.mp h₁
        refine ⟨slotVar_scoped hr.1 0, ?_, ⟨?_, ?_⟩, hle⟩
        · simp only [Poseidon.squeeze, ite_eq_left hn]
          exact slotVar_val (CircuitType.reads_iff.mp hr.2).2 0
        · simpa only [Poseidon.squeeze, ite_eq_left hn] using hr
        · simp only [Poseidon.squeeze, ite_eq_left hn]
    · simp only [squeeze, ite_eq_right hn]
      mvcgen
      case vc1 =>
        rename_i _ h
        obtain ⟨rfl, hs⟩ := h
        refine ⟨slotVar_scoped hs n, ?_, ⟨?_, ?_⟩, le_rfl⟩
        · simp only [Poseidon.squeeze, ite_eq_right hn]
          exact slotVar_val rfl n
        · simp only [Poseidon.squeeze, ite_eq_right hn]
          exact ⟨hs, reads_spongeState.mpr ⟨rfl, rfl, rfl⟩⟩
        · simp only [Poseidon.squeeze, ite_eq_right hn]
  | absorbed n =>
    simp only [squeeze]
    mvcgen [hp]
    case vc2 =>
      rename_i _ h
      obtain ⟨rfl, hs⟩ := h
      exact ⟨trivial, hs⟩
    case vc3 =>
      rename_i s₀ h₀ r s₁ h₁
      obtain ⟨rfl, -⟩ := h₀
      obtain ⟨hr, hle⟩ := Prover.Reg.iff.mp h₁
      refine ⟨slotVar_scoped hr.1 0, ?_, ⟨?_, ?_⟩, hle⟩
      · simp only [Poseidon.squeeze]
        exact slotVar_val (CircuitType.reads_iff.mp hr.2).2 0
      · simpa only [Poseidon.squeeze] using hr
      · simp only [Poseidon.squeeze]

attribute [irreducible] slotVar squeeze

end SpongeVar

end Snarky.Kimchi
