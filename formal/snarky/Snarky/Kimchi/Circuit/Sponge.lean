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
- PS's width-3 `Vector` state renders as the triple, matching the gadget and the value
  sponge's `Triple`.
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
  state : FVar F × FVar F × FVar F
  /-- The automaton direction and intra-block position — metadata, not circuit data. -/
  mode : Poseidon.SpongeMode

namespace SpongeVar

/-- The fresh sponge (PS `initialState`): constant-zero state, `absorbed 0`. -/
def init [Zero F] : SpongeVar F :=
  ⟨(.const 0, .const 0, .const 0), .absorbed 0⟩

/-- Seed a sponge from a value-level state (PS `spongeFromConstants`): the cells as
constants, the same mode. -/
def ofConstants (s : Poseidon.State F) : SpongeVar F :=
  ⟨(.const s.state.1, .const s.state.2.1, .const s.state.2.2), s.mode⟩

/-- Read rate slot `n` — `Poseidon.slot` over circuit variables. Emits nothing. -/
private def slotVar (s : FVar F × FVar F × FVar F) : Fin 3 → FVar F
  | 0 => s.1
  | 1 => s.2.1
  | _ => s.2.2

/-- Seal `x` into rate slot `n` — `Poseidon.addSlot` over circuit variables, the PS
operand order (`seal (add_ x state[i])`) kept. -/
private def addSlotVar [Field F] [DecidableEq F] [BasicSystem F c]
    (s : FVar F × FVar F × FVar F) (n : Fin 3) (x : FVar F) :
    CircuitM F c (FVar F × FVar F × FVar F) :=
  match n with
  | 0 => do
    let cell ← sealVar (CVar.add_ x s.1)
    pure (cell, s.2.1, s.2.2)
  | 1 => do
    let cell ← sealVar (CVar.add_ x s.2.1)
    pure (s.1, cell, s.2.2)
  | _ => do
    let cell ← sealVar (CVar.add_ x s.2.2)
    pure (s.1, s.2.1, cell)

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
implements: `Vals` under a soundness valuation, `Reads` under a prover table. Both pin
the three cells and the mode. A transcript threads them from the `vals_init` /
`reads_init` (or `ofConstants`) entry points through the op laws below — any
absorb/squeeze schedule lands on the value automaton with no per-transcript lemma. -/

open Std.Do

/-- Sound-side reads-as: the cells read under `V` as the value sponge's cells, and the
modes agree. -/
def Vals [Add F] [Mul F] (V : Valuation F) (sv : SpongeVar F)
    (s : Poseidon.State F) : Prop :=
  sv.state.1.val V = s.state.1 ∧ sv.state.2.1.val V = s.state.2.1 ∧
    sv.state.2.2.val V = s.state.2.2 ∧ sv.mode = s.mode

/-- Complete-side reads-as: the cells evaluate on the prover table to the value
sponge's cells, and the modes agree. -/
def Reads [Add F] [Mul F] (env : Assignments F) (sv : SpongeVar F)
    (s : Poseidon.State F) : Prop :=
  sv.state.1.eval env = .ok s.state.1 ∧ sv.state.2.1.eval env = .ok s.state.2.1 ∧
    sv.state.2.2.eval env = .ok s.state.2.2 ∧ sv.mode = s.mode

/-- The fresh circuit sponge reads as the fresh value sponge. -/
theorem vals_init [Field F] (V : Valuation F) :
    Vals V (init (F := F)) Poseidon.init :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- A constant-seeded sponge reads as the state it was seeded from. -/
theorem vals_ofConstants [Field F] (V : Valuation F) (s : Poseidon.State F) :
    Vals V (ofConstants s) s :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- The fresh circuit sponge reads as the fresh value sponge, prover side. -/
theorem reads_init [Field F] (env : Assignments F) :
    Reads env (init (F := F)) Poseidon.init :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- A constant-seeded sponge reads as the state it was seeded from, prover side. -/
theorem reads_ofConstants [Field F] (env : Assignments F) (s : Poseidon.State F) :
    Reads env (ofConstants s) s :=
  ⟨rfl, rfl, rfl, rfl⟩

/-! ## The slot helpers' laws -/

/-- `slotVar` reads as `Poseidon.slot` of the cell readings. -/
private theorem slotVar_val [Add F] [Mul F] (s : FVar F × FVar F × FVar F)
    (V : Valuation F) :
    ∀ n : Fin 3,
      (slotVar s n).val V = Poseidon.slot (s.1.val V, s.2.1.val V, s.2.2.val V) n
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl

/-- `slotVar` evaluates to `Poseidon.slot` of the cell values, prover side. -/
private theorem slotVar_eval [Add F] [Mul F] {env : Assignments F}
    {s : FVar F × FVar F × FVar F} {a b c : F} (ha : s.1.eval env = .ok a)
    (hb : s.2.1.eval env = .ok b) (hc : s.2.2.eval env = .ok c) :
    ∀ n : Fin 3, (slotVar s n).eval env = .ok (Poseidon.slot (a, b, c) n)
  | 0 => ha
  | 1 => hb
  | 2 => hc

/-- `addSlotVar` is sound: the output cells read as `Poseidon.addSlot` of the input
cell readings (the seal reads as the sum, in either operand order). -/
@[spec] private theorem addSlotVar_spec [Field F] [DecidableEq F]
    (s : FVar F × FVar F × FVar F) (n : Fin 3) (x : FVar F)
    (Q : PostCond (FVar F × FVar F × FVar F) (.arg (BuilderState F) .pure)) :
    ⦃Sound (fun V (r : FVar F × FVar F × FVar F) =>
        (r.1.val V, r.2.1.val V, r.2.2.val V)
          = Poseidon.addSlot (s.1.val V, s.2.1.val V, s.2.2.val V) n (x.val V)) Q⦄
    (addSlotVar (c := KimchiConstraint F) s n x)
    ⦃Q⦄ := by
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

/-- A pinned evaluation is a successful one. -/
private theorem isOk_of_eq {α : Type} {x : Except EvalError α} {v : α}
    (h : x = .ok v) : x.isOk := by rw [h]; rfl

/-- `addSlotVar` is complete: the honest run accepts on readable cells, and the output
cells read back as `Poseidon.addSlot` of the input values. -/
@[spec] private theorem addSlotVar_complete_spec [Field F] [DecidableEq F]
    (s : FVar F × FVar F × FVar F) (n : Fin 3) (x : FVar F)
    (Q : PostCond (FVar F × FVar F × FVar F)
      (.arg (ProverState F) (.except EvalError .pure))) :
    ⦃Complete
        (fun env => (s.1.eval env).isOk ∧ (s.2.1.eval env).isOk ∧
          (s.2.2.eval env).isOk ∧ (x.eval env).isOk)
        (fun env (r : FVar F × FVar F × FVar F) env' =>
          ∀ a b c xv, s.1.eval env = .ok a → s.2.1.eval env = .ok b →
            s.2.2.eval env = .ok c → x.eval env = .ok xv →
            r.1.eval env' = .ok (Poseidon.addSlot (a, b, c) n xv).1 ∧
            r.2.1.eval env' = .ok (Poseidon.addSlot (a, b, c) n xv).2.1 ∧
            r.2.2.eval env' = .ok (Poseidon.addSlot (a, b, c) n xv).2.2)
        Q⦄
    (addSlotVar (c := KimchiProverC F) s n x)
    ⦃Q⦄ := by
  match n with
  | 0 =>
    simp only [addSlotVar]
    mvcgen
    rename_i st hpre
    obtain ⟨⟨ha, hb, hc, hx⟩, hk⟩ := hpre
    obtain ⟨av, ha⟩ := CVar.evalOk ha
    obtain ⟨bv, hb⟩ := CVar.evalOk hb
    obtain ⟨cv, hc⟩ := CVar.evalOk hc
    obtain ⟨xv, hx⟩ := CVar.evalOk hx
    refine ⟨isOk_of_eq (CVar.eval_add_ hx ha), fun r st' hr hle => ?_⟩
    simp only [wp, PredTrans.apply, prove]
    intro hf
    refine hk _ ⟨st'.nv, st'.env, hf⟩ (fun a' b' c' xv' ha' hb' hc' hx' => ?_) hle
    rw [ha] at ha'; rw [hb] at hb'; rw [hc] at hc'; rw [hx] at hx'
    injection ha' with ha'; injection hb' with hb'
    injection hc' with hc'; injection hx' with hx'
    subst ha' hb' hc' hx'
    refine ⟨?_, CVar.eval_le hle hb, CVar.eval_le hle hc⟩
    simpa [Poseidon.addSlot, add_comm] using hr _ (CVar.eval_add_ hx ha)
  | 1 =>
    simp only [addSlotVar]
    mvcgen
    rename_i st hpre
    obtain ⟨⟨ha, hb, hc, hx⟩, hk⟩ := hpre
    obtain ⟨av, ha⟩ := CVar.evalOk ha
    obtain ⟨bv, hb⟩ := CVar.evalOk hb
    obtain ⟨cv, hc⟩ := CVar.evalOk hc
    obtain ⟨xv, hx⟩ := CVar.evalOk hx
    refine ⟨isOk_of_eq (CVar.eval_add_ hx hb), fun r st' hr hle => ?_⟩
    simp only [wp, PredTrans.apply, prove]
    intro hf
    refine hk _ ⟨st'.nv, st'.env, hf⟩ (fun a' b' c' xv' ha' hb' hc' hx' => ?_) hle
    rw [ha] at ha'; rw [hb] at hb'; rw [hc] at hc'; rw [hx] at hx'
    injection ha' with ha'; injection hb' with hb'
    injection hc' with hc'; injection hx' with hx'
    subst ha' hb' hc' hx'
    refine ⟨CVar.eval_le hle ha, ?_, CVar.eval_le hle hc⟩
    simpa [Poseidon.addSlot, add_comm] using hr _ (CVar.eval_add_ hx hb)
  | 2 =>
    simp only [addSlotVar]
    mvcgen
    rename_i st hpre
    obtain ⟨⟨ha, hb, hc, hx⟩, hk⟩ := hpre
    obtain ⟨av, ha⟩ := CVar.evalOk ha
    obtain ⟨bv, hb⟩ := CVar.evalOk hb
    obtain ⟨cv, hc⟩ := CVar.evalOk hc
    obtain ⟨xv, hx⟩ := CVar.evalOk hx
    refine ⟨isOk_of_eq (CVar.eval_add_ hx hc), fun r st' hr hle => ?_⟩
    simp only [wp, PredTrans.apply, prove]
    intro hf
    refine hk _ ⟨st'.nv, st'.env, hf⟩ (fun a' b' c' xv' ha' hb' hc' hx' => ?_) hle
    rw [ha] at ha'; rw [hb] at hb'; rw [hc] at hc'; rw [hx] at hx'
    injection ha' with ha'; injection hb' with hb'
    injection hc' with hc'; injection hx' with hx'
    subst ha' hb' hc' hx'
    refine ⟨CVar.eval_le hle ha, CVar.eval_le hle hb, ?_⟩
    simpa [Poseidon.addSlot, add_comm] using hr _ (CVar.eval_add_ hx hc)

/-! ## The op laws -/

/-- `absorb` is sound: the output sponge reads as the value single-element absorb
`Poseidon.absorb1` of whatever state the input sponge reads as. -/
@[spec] theorem absorb_spec [Field F] [DecidableEq F] (p : Poseidon.Params F)
    (hsize : p.roundConstants.size = 5 * 11) (sv : SpongeVar F) (x : FVar F)
    (Q : PostCond (SpongeVar F) (.arg (BuilderState F) .pure)) :
    ⦃Sound (fun V (r : SpongeVar F) => ∀ s, Vals V sv s →
        Vals V r (Poseidon.absorb1 p s (x.val V))) Q⦄
    (absorb (c := KimchiConstraint F) p sv x)
    ⦃Q⦄ := by
  obtain ⟨stv, mode⟩ := sv
  have pspec := Poseidon.poseidon_spec (F := F) p hsize
  cases mode with
  | absorbed n =>
    by_cases hn : n.val = 2
    · simp only [absorb, if_pos hn]
      mvcgen [pspec]
      rename_i st hpre
      intro r₁ nv₁ hpos
      mvcgen
      intro r₂ nv₂ hslot
      mvcgen
      refine hpre _ _ ?_
      rintro ⟨sst, smode⟩ ⟨h1, h2, h3, hm⟩
      simp only at hm
      subst hm
      rw [h1, h2, h3] at hpos
      rw [hpos] at hslot
      obtain ⟨e1, e23⟩ := Prod.ext_iff.mp hslot
      obtain ⟨e2, e3⟩ := Prod.ext_iff.mp e23
      simp only [Poseidon.absorb1, if_pos hn]
      exact ⟨e1, e2, e3, rfl⟩
    · simp only [absorb, if_neg hn]
      mvcgen
      rename_i st hpre
      intro r₂ nv₂ hslot
      mvcgen
      refine hpre _ _ ?_
      rintro ⟨sst, smode⟩ ⟨h1, h2, h3, hm⟩
      simp only at hm
      subst hm
      rw [h1, h2, h3] at hslot
      obtain ⟨e1, e23⟩ := Prod.ext_iff.mp hslot
      obtain ⟨e2, e3⟩ := Prod.ext_iff.mp e23
      simp only [Poseidon.absorb1, if_neg hn]
      exact ⟨e1, e2, e3, rfl⟩
  | squeezed n =>
    simp only [absorb]
    mvcgen
    rename_i st hpre
    intro r₂ nv₂ hslot
    mvcgen
    refine hpre _ _ ?_
    rintro ⟨sst, smode⟩ ⟨h1, h2, h3, hm⟩
    simp only at hm
    subst hm
    rw [h1, h2, h3] at hslot
    obtain ⟨e1, e23⟩ := Prod.ext_iff.mp hslot
    obtain ⟨e2, e3⟩ := Prod.ext_iff.mp e23
    simp only [Poseidon.absorb1]
    exact ⟨e1, e2, e3, rfl⟩

/-- `squeeze` is sound: the returned element reads as the value squeeze's element, and
the output sponge as its state, at whatever state the input sponge reads as. -/
@[spec] theorem squeeze_spec [Field F] [DecidableEq F] (p : Poseidon.Params F)
    (hsize : p.roundConstants.size = 5 * 11) (sv : SpongeVar F)
    (Q : PostCond (FVar F × SpongeVar F) (.arg (BuilderState F) .pure)) :
    ⦃Sound (fun V (r : FVar F × SpongeVar F) => ∀ s, Vals V sv s →
        r.1.val V = (Poseidon.squeeze p s).1 ∧
          Vals V r.2 (Poseidon.squeeze p s).2) Q⦄
    (squeeze (c := KimchiConstraint F) p sv)
    ⦃Q⦄ := by
  obtain ⟨stv, mode⟩ := sv
  have pspec := Poseidon.poseidon_spec (F := F) p hsize
  cases mode with
  | squeezed n =>
    by_cases hn : n.val = 2
    · simp only [squeeze, if_pos hn]
      mvcgen [pspec]
      rename_i st hpre
      intro r₁ nv₁ hpos
      mvcgen
      refine hpre _ _ ?_
      rintro ⟨sst, smode⟩ ⟨h1, h2, h3, hm⟩
      simp only at hm
      subst hm
      rw [h1, h2, h3] at hpos
      obtain ⟨e1, e23⟩ := Prod.ext_iff.mp hpos
      obtain ⟨e2, e3⟩ := Prod.ext_iff.mp e23
      simp only [Poseidon.squeeze, if_pos hn]
      exact ⟨by simpa [slotVar, Poseidon.slot] using e1, e1, e2, e3, rfl⟩
    · simp only [squeeze, if_neg hn]
      mvcgen
      rename_i st hpre
      refine hpre _ _ ?_
      rintro ⟨sst, smode⟩ ⟨h1, h2, h3, hm⟩
      simp only at hm
      subst hm
      simp only [Poseidon.squeeze, if_neg hn]
      exact ⟨(slotVar_val stv st.V n).trans (by rw [h1, h2, h3]), h1, h2, h3, rfl⟩
  | absorbed n =>
    simp only [squeeze]
    mvcgen [pspec]
    rename_i st hpre
    intro r₁ nv₁ hpos
    mvcgen
    refine hpre _ _ ?_
    rintro ⟨sst, smode⟩ ⟨h1, h2, h3, hm⟩
    simp only at hm
    subst hm
    rw [h1, h2, h3] at hpos
    obtain ⟨e1, e23⟩ := Prod.ext_iff.mp hpos
    obtain ⟨e2, e3⟩ := Prod.ext_iff.mp e23
    simp only [Poseidon.squeeze]
    exact ⟨by simpa [slotVar, Poseidon.slot] using e1, e1, e2, e3, rfl⟩

/-- `absorb` is complete: the honest run accepts on readable cells and element, and
the output sponge reads back as `Poseidon.absorb1` of whatever state the input sponge
reads as. -/
@[spec] theorem absorb_complete_spec [Field F] [DecidableEq F] (p : Poseidon.Params F)
    (hsize : p.roundConstants.size = 5 * 11) (sv : SpongeVar F) (x : FVar F)
    (Q : PostCond (SpongeVar F) (.arg (ProverState F) (.except EvalError .pure))) :
    ⦃Complete
        (fun env => (sv.state.1.eval env).isOk ∧ (sv.state.2.1.eval env).isOk ∧
          (sv.state.2.2.eval env).isOk ∧ (x.eval env).isOk)
        (fun env (r : SpongeVar F) env' => ∀ s xv, Reads env sv s →
          x.eval env = .ok xv → Reads env' r (Poseidon.absorb1 p s xv))
        Q⦄
    (absorb (c := KimchiProverC F) p sv x)
    ⦃Q⦄ := by
  obtain ⟨stv, mode⟩ := sv
  have pspec := Poseidon.poseidon_complete_spec (F := F) p hsize
  cases mode with
  | absorbed n =>
    by_cases hn : n.val = 2
    · simp only [absorb, if_pos hn]
      mvcgen [pspec]
      rename_i st hpre
      obtain ⟨⟨ha, hb, hc, hx⟩, hk⟩ := hpre
      obtain ⟨av, ha⟩ := CVar.evalOk ha
      obtain ⟨bv, hb⟩ := CVar.evalOk hb
      obtain ⟨cv, hc⟩ := CVar.evalOk hc
      obtain ⟨xv, hx⟩ := CVar.evalOk hx
      refine ⟨⟨isOk_of_eq ha, isOk_of_eq hb, isOk_of_eq hc⟩,
        fun r₁ st₁ hpos hle₁ => ?_⟩
      have hpos := hpos av bv cv ha hb hc
      mvcgen
      refine ⟨⟨isOk_of_eq hpos.1, isOk_of_eq hpos.2.1, isOk_of_eq hpos.2.2,
        isOk_of_eq (CVar.eval_le hle₁ hx)⟩, fun r₂ st₂ hslot hle₂ => ?_⟩
      have hslot := hslot _ _ _ _ hpos.1 hpos.2.1 hpos.2.2 (CVar.eval_le hle₁ hx)
      simp only [wp, PredTrans.apply, prove]
      intro hf
      refine hk _ ⟨st₂.nv, st₂.env, hf⟩ (fun s xv' hs hx' => ?_) (hle₁.trans hle₂)
      obtain ⟨sst, smode⟩ := s
      obtain ⟨h1, h2, h3, hm⟩ := hs
      simp only at hm
      subst hm
      rw [ha] at h1; rw [hb] at h2; rw [hc] at h3; rw [hx] at hx'
      injection h1 with h1; injection h2 with h2
      injection h3 with h3; injection hx' with hx'
      subst h1 h2 h3 hx'
      simp only [Poseidon.absorb1, if_pos hn]
      exact ⟨hslot.1, hslot.2.1, hslot.2.2, rfl⟩
    · simp only [absorb, if_neg hn]
      mvcgen
      rename_i st hpre
      obtain ⟨⟨ha, hb, hc, hx⟩, hk⟩ := hpre
      obtain ⟨av, ha⟩ := CVar.evalOk ha
      obtain ⟨bv, hb⟩ := CVar.evalOk hb
      obtain ⟨cv, hc⟩ := CVar.evalOk hc
      obtain ⟨xv, hx⟩ := CVar.evalOk hx
      refine ⟨⟨isOk_of_eq ha, isOk_of_eq hb, isOk_of_eq hc, isOk_of_eq hx⟩,
        fun r₂ st₂ hslot hle₂ => ?_⟩
      have hslot := hslot _ _ _ _ ha hb hc hx
      simp only [wp, PredTrans.apply, prove]
      intro hf
      refine hk _ ⟨st₂.nv, st₂.env, hf⟩ (fun s xv' hs hx' => ?_) hle₂
      obtain ⟨sst, smode⟩ := s
      obtain ⟨h1, h2, h3, hm⟩ := hs
      simp only at hm
      subst hm
      rw [ha] at h1; rw [hb] at h2; rw [hc] at h3; rw [hx] at hx'
      injection h1 with h1; injection h2 with h2
      injection h3 with h3; injection hx' with hx'
      subst h1 h2 h3 hx'
      simp only [Poseidon.absorb1, if_neg hn]
      exact ⟨hslot.1, hslot.2.1, hslot.2.2, rfl⟩
  | squeezed n =>
    simp only [absorb]
    mvcgen
    rename_i st hpre
    obtain ⟨⟨ha, hb, hc, hx⟩, hk⟩ := hpre
    obtain ⟨av, ha⟩ := CVar.evalOk ha
    obtain ⟨bv, hb⟩ := CVar.evalOk hb
    obtain ⟨cv, hc⟩ := CVar.evalOk hc
    obtain ⟨xv, hx⟩ := CVar.evalOk hx
    refine ⟨⟨isOk_of_eq ha, isOk_of_eq hb, isOk_of_eq hc, isOk_of_eq hx⟩,
      fun r₂ st₂ hslot hle₂ => ?_⟩
    have hslot := hslot _ _ _ _ ha hb hc hx
    simp only [wp, PredTrans.apply, prove]
    intro hf
    refine hk _ ⟨st₂.nv, st₂.env, hf⟩ (fun s xv' hs hx' => ?_) hle₂
    obtain ⟨sst, smode⟩ := s
    obtain ⟨h1, h2, h3, hm⟩ := hs
    simp only at hm
    subst hm
    rw [ha] at h1; rw [hb] at h2; rw [hc] at h3; rw [hx] at hx'
    injection h1 with h1; injection h2 with h2
    injection h3 with h3; injection hx' with hx'
    subst h1 h2 h3 hx'
    simp only [Poseidon.absorb1]
    exact ⟨hslot.1, hslot.2.1, hslot.2.2, rfl⟩

/-- `squeeze` is complete: the honest run accepts on readable cells; the returned
element reads back as the value squeeze's element and the output sponge as its
state. -/
@[spec] theorem squeeze_complete_spec [Field F] [DecidableEq F]
    (p : Poseidon.Params F) (hsize : p.roundConstants.size = 5 * 11)
    (sv : SpongeVar F)
    (Q : PostCond (FVar F × SpongeVar F)
      (.arg (ProverState F) (.except EvalError .pure))) :
    ⦃Complete
        (fun env => (sv.state.1.eval env).isOk ∧ (sv.state.2.1.eval env).isOk ∧
          (sv.state.2.2.eval env).isOk)
        (fun env (r : FVar F × SpongeVar F) env' => ∀ s, Reads env sv s →
          r.1.eval env' = .ok (Poseidon.squeeze p s).1 ∧
            Reads env' r.2 (Poseidon.squeeze p s).2)
        Q⦄
    (squeeze (c := KimchiProverC F) p sv)
    ⦃Q⦄ := by
  obtain ⟨stv, mode⟩ := sv
  have pspec := Poseidon.poseidon_complete_spec (F := F) p hsize
  cases mode with
  | squeezed n =>
    by_cases hn : n.val = 2
    · simp only [squeeze, if_pos hn]
      mvcgen [pspec]
      rename_i st hpre
      obtain ⟨⟨ha, hb, hc⟩, hk⟩ := hpre
      obtain ⟨av, ha⟩ := CVar.evalOk ha
      obtain ⟨bv, hb⟩ := CVar.evalOk hb
      obtain ⟨cv, hc⟩ := CVar.evalOk hc
      refine ⟨⟨isOk_of_eq ha, isOk_of_eq hb, isOk_of_eq hc⟩,
        fun r₁ st₁ hpos hle₁ => ?_⟩
      have hpos := hpos av bv cv ha hb hc
      simp only [wp, PredTrans.apply, prove]
      intro hf
      refine hk _ ⟨st₁.nv, st₁.env, hf⟩ (fun s hs => ?_) hle₁
      obtain ⟨sst, smode⟩ := s
      obtain ⟨h1, h2, h3, hm⟩ := hs
      simp only at hm
      subst hm
      rw [ha] at h1; rw [hb] at h2; rw [hc] at h3
      injection h1 with h1; injection h2 with h2; injection h3 with h3
      subst h1 h2 h3
      simp only [Poseidon.squeeze, if_pos hn]
      exact ⟨slotVar_eval hpos.1 hpos.2.1 hpos.2.2 0, hpos.1, hpos.2.1, hpos.2.2, rfl⟩
    · simp only [squeeze, if_neg hn]
      mvcgen
      rename_i st hpre
      obtain ⟨⟨ha, hb, hc⟩, hk⟩ := hpre
      obtain ⟨av, ha⟩ := CVar.evalOk ha
      obtain ⟨bv, hb⟩ := CVar.evalOk hb
      obtain ⟨cv, hc⟩ := CVar.evalOk hc
      refine hk _ st (fun s hs => ?_) (Assignments.Le.refl _)
      obtain ⟨sst, smode⟩ := s
      obtain ⟨h1, h2, h3, hm⟩ := hs
      simp only at hm
      subst hm
      rw [ha] at h1; rw [hb] at h2; rw [hc] at h3
      injection h1 with h1; injection h2 with h2; injection h3 with h3
      subst h1 h2 h3
      simp only [Poseidon.squeeze, if_neg hn]
      exact ⟨slotVar_eval ha hb hc n, ha, hb, hc, rfl⟩
  | absorbed n =>
    simp only [squeeze]
    mvcgen [pspec]
    rename_i st hpre
    obtain ⟨⟨ha, hb, hc⟩, hk⟩ := hpre
    obtain ⟨av, ha⟩ := CVar.evalOk ha
    obtain ⟨bv, hb⟩ := CVar.evalOk hb
    obtain ⟨cv, hc⟩ := CVar.evalOk hc
    refine ⟨⟨isOk_of_eq ha, isOk_of_eq hb, isOk_of_eq hc⟩,
      fun r₁ st₁ hpos hle₁ => ?_⟩
    have hpos := hpos av bv cv ha hb hc
    simp only [wp, PredTrans.apply, prove]
    intro hf
    refine hk _ ⟨st₁.nv, st₁.env, hf⟩ (fun s hs => ?_) hle₁
    obtain ⟨sst, smode⟩ := s
    obtain ⟨h1, h2, h3, hm⟩ := hs
    simp only at hm
    subst hm
    rw [ha] at h1; rw [hb] at h2; rw [hc] at h3
    injection h1 with h1; injection h2 with h2; injection h3 with h3
    subst h1 h2 h3
    simp only [Poseidon.squeeze]
    exact ⟨slotVar_eval hpos.1 hpos.2.1 hpos.2.2 0, hpos.1, hpos.2.1, hpos.2.2, rfl⟩

end SpongeVar

end Snarky.Kimchi
