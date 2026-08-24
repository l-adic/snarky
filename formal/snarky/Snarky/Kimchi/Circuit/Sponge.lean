import Snarky.Circuit.DSL.Utils
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

Deviations from the PS original:
- PS's width-3 `Vector` state is `Poseidon.Triple (FVar F)` — the value sponge's carrier
  at circuit variables; its reading is the product instance's.
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
  state : Poseidon.Triple (FVar F)
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

/-- Read rate slot `n` — `Poseidon.slot` over circuit variables. Emits nothing. -/
private def slotVar (s : Poseidon.Triple (FVar F)) : Fin 3 → FVar F
  | 0 => s.s0
  | 1 => s.s1
  | _ => s.s2

/-- Seal `x` into rate slot `n` — `Poseidon.addSlot` over circuit variables, the PS
operand order (`seal (add_ x state[i])`) kept. -/
private def addSlotVar [Field F] [DecidableEq F] [BasicSystem F c]
    (s : Poseidon.Triple (FVar F)) (n : Fin 3) (x : FVar F) :
    CircuitM F c (Poseidon.Triple (FVar F)) :=
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

/-- Squeeze one element (PS `squeeze`): read the next rate slot, permuting first when
entering squeeze mode or when the block is exhausted. Mirrors `Poseidon.squeeze`
branch for branch; reads emit no constraints. -/
def squeeze [Field F] [KimchiSystem F c] (p : Poseidon.Params F) (sv : SpongeVar F) :
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

/-! ## The reads-as relations

The laws relate an in-circuit sponge to the value-level `Poseidon.State` it
implements: the generic state reading `readVal` at a valuation plus mode agreement —
one relation, read at a soundness valuation or at the prover table's total reading. A
transcript threads it from the `vals_init` (or `ofConstants`) entry point through the
op laws below — any absorb/squeeze schedule lands on the value automaton with no
per-transcript lemma; an op's `Grants` carries the reading across the table extension
of the op, and `readVal_of_le` across any gadgets interleaved between sponge ops. -/

open Std.Do

/-- Sound-side reads-as: the cells read under `V` as the value sponge's cells, and the
modes agree. -/
def Vals [Add F] [Mul F] (V : Valuation F) (sv : SpongeVar F)
    (s : Poseidon.State F) : Prop :=
  readVal V sv.state = s.state ∧ sv.mode = s.mode

/-- The fresh circuit sponge reads as the fresh value sponge. -/
theorem vals_init [Field F] (V : Valuation F) :
    Vals V (init (F := F)) Poseidon.init := by
  refine ⟨?_, rfl⟩
  simp only [init, readVal_prod, readVal_fvar]
  rfl

/-- A constant-seeded sponge reads as the state it was seeded from. -/
theorem vals_ofConstants [Field F] (V : Valuation F) (s : Poseidon.State F) :
    Vals V (ofConstants s) s := by
  refine ⟨?_, rfl⟩
  simp only [ofConstants, readVal_prod, readVal_fvar]
  rfl

/-- What a sponge op's run grants: the table grew, the output state is in scope there,
and the sponge reads there as the value sponge. -/
def Grants [Field F] (st : ProverState F) (r : ProverState F × SpongeVar F)
    (s : Poseidon.State F) : Prop :=
  st.env.Le r.1.env ∧ CircuitType.Scoped (Poseidon.Triple F) r.1 r.2.state ∧
    Vals r.1.env.toValuation r.2 s

/-! ## The slot helpers' laws -/

/-- `slotVar` reads as `Poseidon.slot` of the state reading. -/
private theorem slotVar_val [Add F] [Mul F] (s : Poseidon.Triple (FVar F)) (V : Valuation F) :
    ∀ n : Fin 3, (slotVar s n).val V = Poseidon.slot (readVal V s) n := by
  intro n
  simp only [readVal_prod, readVal_fvar]
  match n with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl

/-- `slotVar` is in scope when the state is. -/
private theorem slotVar_scoped {st : ProverState F} {s : Poseidon.Triple (FVar F)}
    (h : CircuitType.Scoped (Poseidon.Triple F) st s) : ∀ n : Fin 3, (slotVar s n).Scoped st := by
  intro n
  simp only [scoped_prod_iff, scoped_fvar_iff] at h
  obtain ⟨h1, h2, h3⟩ := h
  match n with
  | 0 => exact h1
  | 1 => exact h2
  | 2 => exact h3

/-- `addSlotVar` is sound: the output state reads as `Poseidon.addSlot` of the input
state's reading (the seal reads as the sum, in either operand order). -/
@[spec] private theorem addSlotVar_spec {V : Valuation F} [Field F] [DecidableEq F]
    (s : Poseidon.Triple (FVar F)) (n : Fin 3) (x : FVar F) :
    ⦃⌜True⌝⦄
    (addSlotVar (c := Builder V (KimchiConstraint F)) s n x)
    ⦃⇓ r _ => ⌜readVal V r = Poseidon.addSlot (readVal V s) n (x.val V)⌝⦄ := by
  match n with
  | 0 =>
    simp only [addSlotVar]
    mvcgen
    simp_all [Poseidon.addSlot, CVar.val_add_, add_comm, readVal_prod, readVal_fvar]
  | 1 =>
    simp only [addSlotVar]
    mvcgen
    simp_all [Poseidon.addSlot, CVar.val_add_, add_comm, readVal_prod, readVal_fvar]
  | 2 =>
    simp only [addSlotVar]
    mvcgen
    simp_all [Poseidon.addSlot, CVar.val_add_, add_comm, readVal_prod, readVal_fvar]

/-- The state and result of `addSlotVar`'s honest run: the slot sum's seal. -/
private def addSlotRun [Field F] [DecidableEq F] (st : ProverState F)
    (s : Poseidon.Triple (FVar F)) (n : Fin 3) (x : FVar F) :
    ProverState F × Poseidon.Triple (FVar F) :=
  match n with
  | 0 => let r := sealRun st (CVar.add_ x s.s0); (r.1, (r.2, s.s1, s.s2))
  | 1 => let r := sealRun st (CVar.add_ x s.s1); (r.1, (s.s0, r.2, s.s2))
  | _ => let r := sealRun st (CVar.add_ x s.s2); (r.1, (s.s0, s.s1, r.2))

/-- `addSlotVar`'s honest run on an in-scope state and element lands at `addSlotRun`. -/
private theorem addSlotVar_run [Field F] [DecidableEq F] {s : Poseidon.Triple (FVar F)}
    (n : Fin 3) {x : FVar F} (st : ProverState F)
    (hs : CircuitType.Scoped (Poseidon.Triple F) st s) (hx : x.Scoped st) :
    prove (Checker.holds (F := F) (c := KimchiConstraint F))
      (addSlotVar (c := KimchiConstraint F) s n x) st.nv st.env
      = .ok ((addSlotRun st s n x).1.out (addSlotRun st s n x).2) := by
  simp only [scoped_prod_iff, scoped_fvar_iff] at hs
  obtain ⟨h0, h1, h2⟩ := hs
  match n with
  | 0 =>
    simp only [addSlotVar, addSlotRun, prove_bind, sealVar_run st (hx.add_ h0), Except.bind]
    rfl
  | 1 =>
    simp only [addSlotVar, addSlotRun, prove_bind, sealVar_run st (hx.add_ h1), Except.bind]
    rfl
  | 2 =>
    simp only [addSlotVar, addSlotRun, prove_bind, sealVar_run st (hx.add_ h2), Except.bind]
    rfl

/-- `addSlotRun` reads as `Poseidon.addSlot` of the input readings. -/
private theorem addSlotRun_grants [Field F] [DecidableEq F] {st : ProverState F}
    {s : Poseidon.Triple (FVar F)} (n : Fin 3) {x : FVar F}
    (hs : CircuitType.Scoped (Poseidon.Triple F) st s) (hx : x.Scoped st) :
    Snarky.Grants (Poseidon.Triple F) st (addSlotRun st s n x)
      (Poseidon.addSlot (readVal st.env.toValuation s) n (x.val st.env.toValuation)) := by
  simp only [scoped_prod_iff, scoped_fvar_iff] at hs
  obtain ⟨h0, h1, h2⟩ := hs
  match n with
  | 0 =>
    have h := sealRun_grants (st := st) (hx.add_ h0)
    refine ⟨h.le, ?_, ?_⟩
    · simp only [addSlotRun, scoped_prod_iff, scoped_fvar_iff]
      exact ⟨h.fvar_scoped, h1.of_le h.le, h2.of_le h.le⟩
    · simp only [addSlotRun, readVal_prod, readVal_fvar, Poseidon.addSlot]
      rw [h.fvar_val, CVar.val_add_, CVar.val_of_le h.le h1, CVar.val_of_le h.le h2, add_comm]
  | 1 =>
    have h := sealRun_grants (st := st) (hx.add_ h1)
    refine ⟨h.le, ?_, ?_⟩
    · simp only [addSlotRun, scoped_prod_iff, scoped_fvar_iff]
      exact ⟨h0.of_le h.le, h.fvar_scoped, h2.of_le h.le⟩
    · simp only [addSlotRun, readVal_prod, readVal_fvar, Poseidon.addSlot]
      rw [h.fvar_val, CVar.val_add_, CVar.val_of_le h.le h0, CVar.val_of_le h.le h2, add_comm]
  | 2 =>
    have h := sealRun_grants (st := st) (hx.add_ h2)
    refine ⟨h.le, ?_, ?_⟩
    · simp only [addSlotRun, scoped_prod_iff, scoped_fvar_iff]
      exact ⟨h0.of_le h.le, h1.of_le h.le, h.fvar_scoped⟩
    · simp only [addSlotRun, readVal_prod, readVal_fvar, Poseidon.addSlot]
      rw [h.fvar_val, CVar.val_add_, CVar.val_of_le h.le h0, CVar.val_of_le h.le h1, add_comm]

/-! ## The op laws -/

/-- `absorb` is sound: the output sponge reads as the value single-element absorb
`Poseidon.absorb1` of whatever state the input sponge reads as. -/
@[spec] theorem absorb_spec {V : Valuation F} [Field F] [DecidableEq F] (p : Poseidon.Params F)
    (hsize : p.roundConstants.size = Poseidon.fullRounds) (sv : SpongeVar F)
    (x : FVar F) :
    ⦃⌜True⌝⦄
    (absorb (c := Builder V (KimchiConstraint F)) p sv x)
    ⦃⇓ r _ => ⌜∀ s, Vals V sv s →
        Vals V r (Poseidon.absorb1 p s (x.val V))⌝⦄ := by
  obtain ⟨stv, mode⟩ := sv
  have pspec := Poseidon.poseidon_spec (F := F) (V := V) p hsize
  cases mode with
  | absorbed n =>
    by_cases hn : n.val = 2
    · simp only [absorb, if_pos hn]
      mvcgen [pspec]
      rename_i r₁ _ hpos r₂ _ hslot
      rintro ⟨sst, smode⟩ ⟨hst, hm⟩
      simp only at hm
      subst hm
      rw [hst] at hpos
      rw [hpos] at hslot
      simp only [Poseidon.absorb1, if_pos hn]
      exact ⟨hslot, rfl⟩
    · simp only [absorb, if_neg hn]
      mvcgen
      rename_i r₂ _ hslot
      rintro ⟨sst, smode⟩ ⟨hst, hm⟩
      simp only at hm
      subst hm
      rw [hst] at hslot
      simp only [Poseidon.absorb1, if_neg hn]
      exact ⟨hslot, rfl⟩
  | squeezed n =>
    simp only [absorb]
    mvcgen
    rename_i r₂ _ hslot
    rintro ⟨sst, smode⟩ ⟨hst, hm⟩
    simp only at hm
    subst hm
    rw [hst] at hslot
    simp only [Poseidon.absorb1]
    exact ⟨hslot, rfl⟩

/-- `squeeze` is sound: the returned element reads as the value squeeze's element, and
the output sponge as its state, at whatever state the input sponge reads as. -/
@[spec] theorem squeeze_spec {V : Valuation F} [Field F] [DecidableEq F] (p : Poseidon.Params F)
    (hsize : p.roundConstants.size = Poseidon.fullRounds) (sv : SpongeVar F) :
    ⦃⌜True⌝⦄
    (squeeze (c := Builder V (KimchiConstraint F)) p sv)
    ⦃⇓ r _ => ⌜∀ s, Vals V sv s →
        r.1.val V = (Poseidon.squeeze p s).1 ∧
          Vals V r.2 (Poseidon.squeeze p s).2⌝⦄ := by
  obtain ⟨stv, mode⟩ := sv
  have pspec := Poseidon.poseidon_spec (F := F) (V := V) p hsize
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
      exact ⟨(slotVar_val r₁ V 0).trans (by rw [hpos]), hpos, rfl⟩
    · simp only [squeeze, if_neg hn]
      mvcgen
      rintro ⟨sst, smode⟩ ⟨hst, hm⟩
      simp only at hm
      subst hm
      simp only [Poseidon.squeeze, if_neg hn]
      exact ⟨(slotVar_val stv V n).trans (by rw [hst]), hst, rfl⟩
  | absorbed n =>
    simp only [squeeze]
    mvcgen [pspec]
    rename_i r₁ _ hpos
    rintro ⟨sst, smode⟩ ⟨hst, hm⟩
    simp only at hm
    subst hm
    rw [hst] at hpos
    simp only [Poseidon.squeeze]
    exact ⟨(slotVar_val r₁ V 0).trans (by rw [hpos]), hpos, rfl⟩

/-- The state and result of `absorb`'s honest run: `absorb`'s branches over
`poseidonRun` and `addSlotRun`. -/
def absorbRun [Field F] [DecidableEq F] (p : Poseidon.Params F) (st : ProverState F)
    (sv : SpongeVar F) (x : FVar F) : ProverState F × SpongeVar F :=
  match sv.mode with
  | .absorbed n =>
    if n.val = 2 then
      let r := Poseidon.poseidonRun p st sv.state
      let r' := addSlotRun r.1 r.2 0 x
      (r'.1, ⟨r'.2, .absorbed 1⟩)
    else
      let r' := addSlotRun st sv.state n x
      (r'.1, ⟨r'.2, .absorbed (n + 1)⟩)
  | .squeezed _ =>
    let r' := addSlotRun st sv.state 0 x
    (r'.1, ⟨r'.2, .absorbed 1⟩)

/-- `absorb`'s honest run on an in-scope sponge and element lands at `absorbRun`. -/
theorem absorb_run [Field F] [DecidableEq F] (p : Poseidon.Params F) {sv : SpongeVar F}
    {x : FVar F} (st : ProverState F) (hsv : CircuitType.Scoped (Poseidon.Triple F) st sv.state)
    (hx : x.Scoped st) :
    prove (Checker.holds (F := F) (c := KimchiConstraint F))
      (absorb (c := KimchiConstraint F) p sv x) st.nv st.env
      = .ok ((absorbRun p st sv x).1.out (absorbRun p st sv x).2) := by
  obtain ⟨stv, mode⟩ := sv
  cases mode with
  | absorbed n =>
    by_cases hn : n.val = 2
    · have hp := Poseidon.poseidonRun_scope p st stv
      simp only [absorb, absorbRun, if_pos hn, prove_bind, Poseidon.poseidon_run p st hsv,
        Except.bind, addSlotVar_run 0 _ hp.2 (hx.of_le hp.1)]
      rfl
    · simp only [absorb, absorbRun, if_neg hn, prove_bind, addSlotVar_run n st hsv hx,
        Except.bind]
      rfl
  | squeezed n =>
    simp only [absorb, absorbRun, prove_bind, addSlotVar_run 0 st hsv hx, Except.bind]
    rfl

/-- `absorbRun` reads as `Poseidon.absorb1` of the input readings. -/
theorem absorbRun_grants [Field F] [DecidableEq F] (p : Poseidon.Params F)
    (hsize : p.roundConstants.size = Poseidon.fullRounds) {st : ProverState F}
    {sv : SpongeVar F} {x : FVar F} (hsv : CircuitType.Scoped (Poseidon.Triple F) st sv.state)
    (hx : x.Scoped st) {s : Poseidon.State F} (hvals : Vals st.env.toValuation sv s) :
    Grants st (absorbRun p st sv x) (Poseidon.absorb1 p s (x.val st.env.toValuation)) := by
  obtain ⟨stv, mode⟩ := sv
  obtain ⟨sst, smode⟩ := s
  obtain ⟨hst, hm⟩ := hvals
  simp only at hm hst
  subst hm
  cases mode with
  | absorbed n =>
    by_cases hn : n.val = 2
    · have hp := Poseidon.poseidonRun_grants p hsize st stv
      simp only [absorbRun, if_pos hn, Poseidon.absorb1]
      generalize Poseidon.poseidonRun p st stv = r at hp ⊢
      have ha := addSlotRun_grants 0 hp.scope (hx.of_le hp.le)
      refine ⟨hp.le.trans ha.le, ha.scope, ?_, rfl⟩
      rw [ha.read, hp.read, CVar.val_of_le hp.le hx, hst]
    · have ha := addSlotRun_grants n hsv hx
      simp only [absorbRun, if_neg hn, Poseidon.absorb1]
      refine ⟨ha.le, ha.scope, ?_, rfl⟩
      rw [ha.read, hst]
  | squeezed n =>
    have ha := addSlotRun_grants 0 hsv hx
    simp only [absorbRun, Poseidon.absorb1]
    refine ⟨ha.le, ha.scope, ?_, rfl⟩
    rw [ha.read, hst]

/-- The state and result of `squeeze`'s honest run: `squeeze`'s branches over
`poseidonRun`; the reads allocate nothing. -/
def squeezeRun [Field F] (p : Poseidon.Params F) (st : ProverState F) (sv : SpongeVar F) :
    ProverState F × (FVar F × SpongeVar F) :=
  match sv.mode with
  | .squeezed n =>
    if n.val = 2 then
      let r := Poseidon.poseidonRun p st sv.state
      (r.1, (slotVar r.2 0, ⟨r.2, .squeezed 1⟩))
    else
      (st, (slotVar sv.state n, ⟨sv.state, .squeezed (n + 1)⟩))
  | .absorbed _ =>
    let r := Poseidon.poseidonRun p st sv.state
    (r.1, (slotVar r.2 0, ⟨r.2, .squeezed 1⟩))

/-- `squeeze`'s honest run on an in-scope sponge lands at `squeezeRun`. -/
theorem squeeze_run [Field F] [DecidableEq F] (p : Poseidon.Params F) {sv : SpongeVar F}
    (st : ProverState F) (hsv : CircuitType.Scoped (Poseidon.Triple F) st sv.state) :
    prove (Checker.holds (F := F) (c := KimchiConstraint F))
      (squeeze (c := KimchiConstraint F) p sv) st.nv st.env
      = .ok ((squeezeRun p st sv).1.out (squeezeRun p st sv).2) := by
  obtain ⟨stv, mode⟩ := sv
  cases mode with
  | squeezed n =>
    by_cases hn : n.val = 2
    · simp only [squeeze, squeezeRun, if_pos hn, prove_bind, Poseidon.poseidon_run p st hsv,
        Except.bind]
      rfl
    · simp only [squeeze, squeezeRun, if_neg hn]
      rfl
  | absorbed n =>
    simp only [squeeze, squeezeRun, prove_bind, Poseidon.poseidon_run p st hsv, Except.bind]
    rfl

/-- `squeezeRun` reads as `Poseidon.squeeze` of the input reading: the element, and
the sponge. -/
theorem squeezeRun_grants [Field F] [DecidableEq F] (p : Poseidon.Params F)
    (hsize : p.roundConstants.size = Poseidon.fullRounds) {st : ProverState F}
    {sv : SpongeVar F} (hsv : CircuitType.Scoped (Poseidon.Triple F) st sv.state)
    {s : Poseidon.State F} (hvals : Vals st.env.toValuation sv s) :
    Snarky.Grants F st ((squeezeRun p st sv).1, (squeezeRun p st sv).2.1)
        (Poseidon.squeeze p s).1 ∧
      Grants st ((squeezeRun p st sv).1, (squeezeRun p st sv).2.2) (Poseidon.squeeze p s).2 := by
  obtain ⟨stv, mode⟩ := sv
  obtain ⟨sst, smode⟩ := s
  obtain ⟨hst, hm⟩ := hvals
  simp only at hm hst
  subst hm
  cases mode with
  | squeezed n =>
    by_cases hn : n.val = 2
    · have hp := Poseidon.poseidonRun_grants p hsize st stv
      simp only [squeezeRun, if_pos hn, Poseidon.squeeze]
      generalize Poseidon.poseidonRun p st stv = r at hp ⊢
      refine ⟨Snarky.Grants.fvar hp.le (slotVar_scoped hp.scope 0) ?_, hp.le, hp.scope, ?_, rfl⟩
      · rw [slotVar_val, hp.read, hst]
      · rw [hp.read, hst]
    · simp only [squeezeRun, if_neg hn, Poseidon.squeeze]
      refine ⟨Snarky.Grants.fvar (Assignments.Le.refl _) (slotVar_scoped hsv n) ?_,
        Assignments.Le.refl _, hsv, hst, rfl⟩
      rw [slotVar_val, hst]
  | absorbed n =>
    have hp := Poseidon.poseidonRun_grants p hsize st stv
    simp only [squeezeRun, Poseidon.squeeze]
    generalize Poseidon.poseidonRun p st stv = r at hp ⊢
    refine ⟨Snarky.Grants.fvar hp.le (slotVar_scoped hp.scope 0) ?_, hp.le, hp.scope, ?_, rfl⟩
    · rw [slotVar_val, hp.read, hst]
    · rw [hp.read, hst]

end SpongeVar

end Snarky.Kimchi
