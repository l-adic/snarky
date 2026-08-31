import Snarky.Witness
import Snarky.Prover
import Snarky.Kimchi.Semantics
import Poseidon.Basic
import Kimchi.Gate.Semantics.Poseidon

/-!
# The Poseidon gadget

Port of `Snarky.Circuit.Kimchi.Poseidon`
(packages/snarky-kimchi/src/Snarky/Circuit/Kimchi/Poseidon.purs): witness the 55 round
outputs of the permutation in ONE bulk `exists` — the traversal lives inside the
witness computation, so the circuit itself is three binds — emit the block constraint
over the 56 chained states, and return the output state.

Name map: `poseidon` keeps its name; the `exists` body's `scanl` of the production
round renders as the gate's canonical iterate `Kimchi.Gate.Poseidon.rounds` — the
same field values (`round_eq_fullRound`), and the form the gate's chain lemmas
certify — with output `i` the `(i + 1)`-round prefix.

Deviations from the PS original (per `formal/docs/snarky-kimchi-alignment.md`):
- PS's ambient `PoseidonField` class arrives as the explicit parameter
  `p : Poseidon.Params F`, whose data the emitted payload carries (the payload-data
  deviation in `Constraint/Poseidon.lean`).
- PS's width-3 `Vector` states render as the nominal `SpongeState` (cells `s0`/`s1`/
  `s2`), reading as the value side's `Poseidon.Triple`; the constraint payload's rows
  stay bare triples (`SpongeState.cells`).
- The PS `label "poseidon"` wrapper is dropped (labels are not threaded —
  `Kimchi/Constraint.lean`'s deviation ledger).
-/

namespace Snarky.Kimchi

open Snarky

variable {F c : Type}

/-- The width-3 Poseidon state as circuit variables (PS `Vector 3 (FVar f)`). Reads
as the value side's `Poseidon.Triple` through its `CircuitType` instance. -/
structure SpongeState (F : Type) where
  /-- Rate slot 0. -/
  s0 : FVar F
  /-- Rate slot 1. -/
  s1 : FVar F
  /-- The capacity slot. -/
  s2 : FVar F

/-- The state's cells as a constraint-row triple — the payload rendering
(`PoseidonConstraint`'s rows are bare tuples). -/
def SpongeState.cells (st : SpongeState F) : FVar F × FVar F × FVar F :=
  (st.s0, st.s1, st.s2)

/-- A width-3 value state encodes as its three slots, read back as a `SpongeState`. -/
instance instCircuitTypeSpongeState :
    CircuitType F (Poseidon.Triple F) (SpongeState F) where
  size := 3
  valueToFields v := #v[v.1, v.2.1, v.2.2]
  fieldsToValue fs := (fs[0], fs[1], fs[2])
  varToFields st := #v[st.s0, st.s1, st.s2]
  fieldsToVar fs := ⟨fs[0], fs[1], fs[2]⟩
  value_roundTrip _ := rfl
  var_roundTrip cvs := by
    ext i hi
    match i, hi with
    | 0, _ => rfl
    | 1, _ => rfl
    | 2, _ => rfl

/-- The state's reading, one cell at a time — the instance's defining equation. -/
@[simp] theorem readVal_spongeState [Add F] [Mul F] [Zero F] (V : Valuation F)
    (s : SpongeState F) :
    CircuitType.readVal (val := Poseidon.Triple F) V s
      = (s.s0.val V, s.s1.val V, s.s2.val V) := rfl

/-- The state is in scope when its three cells are. -/
@[simp] theorem scoped_spongeState [Add F] [Mul F] [Zero F] {st : ProverState F}
    {s : SpongeState F} :
    CircuitType.Scoped (val := Poseidon.Triple F) st s ↔
      s.s0.Scoped st ∧ s.s1.Scoped st ∧ s.s2.Scoped st := by
  show (∀ cv ∈ [s.s0, s.s1, s.s2], cv.Scoped st) ↔ _
  simp

/-- The state reads a triple exactly when its cells read the components. -/
@[simp] theorem reads_spongeState [Add F] [Mul F] [Zero F] {V : Valuation F}
    {s : SpongeState F} {v : Poseidon.Triple F} :
    CircuitType.Reads V s v ↔
      s.s0.val V = v.1 ∧ s.s1.val V = v.2.1 ∧ s.s2.val V = v.2.2 := by
  constructor
  · intro h
    refine ⟨congrArg (fun w : Vector F 3 => w[0]) h, congrArg (fun w : Vector F 3 => w[1]) h,
      congrArg (fun w : Vector F 3 => w[2]) h⟩
  · rintro ⟨h0, h1, h2⟩
    show (#v[s.s0.val V, s.s1.val V, s.s2.val V] : Vector F 3) = #v[v.1, v.2.1, v.2.2]
    rw [h0, h1, h2]

/-- The state cells carry no well-formedness constraint (plain field variables). -/
instance instCheckedTypeSpongeState [Add F] [Mul F] [Zero F] [One F] [BasicSystem F c] :
    CheckedType F c (Poseidon.Triple F) (SpongeState F) where
  check _ := pure PUnit.unit
  post _ _ := True
  check_sound _ _ _ _ := trivial
  check_complete _ _ _ := Complete.pure

/-- A state triple carries no admissibility condition. -/
@[simp] theorem valid_spongeState [Add F] [Mul F] [Zero F] [One F] [BasicSystem F c]
    {v : Poseidon.Triple F} :
    CheckedType.Valid (F := F) (c := c) (var := SpongeState F) v := fun _ _ _ => trivial

/-- The Poseidon permutation gadget (PS `poseidon`): one bulk witness of the round
outputs, one block constraint over the 56 chained states at `p`'s data, the last
state returned. -/
def poseidon [Field F] [BasicSystem F c] [KimchiSystem F c] (p : Poseidon.Params F)
    (initialState : SpongeState F) : CircuitM F c (SpongeState F) := do
  let roundOutputs ← witness (val := Vector (Poseidon.Triple F) 55) (advice p initialState)
  addConstraint (KimchiSystem.poseidon
    { mds := p.mds, rc := p.roundConstants.toList,
      state := initialState.cells :: (roundOutputs.map SpongeState.cells).toList })
  pure roundOutputs[54]
where
  /-- The advice: the 55 round outputs, oldest first — the traversal lives here, so
  the circuit itself is one witness and one row. -/
  advice (p : Poseidon.Params F) (s : SpongeState F) :
      AsProver F (Vector (Poseidon.Triple F) 55) := do
    let s0 ← AsProver.readCVar s.s0
    let s1 ← AsProver.readCVar s.s1
    let s2 ← AsProver.readCVar s.s2
    pure (Vector.ofFn fun i => Kimchi.Gate.Poseidon.rounds
      (Kimchi.Gate.Poseidon.mdsOfParams p) (Kimchi.Gate.Poseidon.paramsRc p)
      (i.1 + 1) (s0, s1, s2))

/-! ## Soundness -/

namespace Poseidon

open Std.Do

private theorem chainHolds_window [Field F] {M : Kimchi.Gate.Poseidon.Mds F}
    {rc : List (F × F × F)} :
    ∀ (i k0 : ℕ) (l : List (F × F × F)), chainHolds M rc k0 l →
      5 * i + 5 < l.length →
      Kimchi.Gate.Poseidon.Holds M (rcRow rc (k0 + i))
        ⟨l.getD (5 * i) (0, 0, 0), l.getD (5 * i + 1) (0, 0, 0),
         l.getD (5 * i + 2) (0, 0, 0), l.getD (5 * i + 3) (0, 0, 0),
         l.getD (5 * i + 4) (0, 0, 0), l.getD (5 * i + 5) (0, 0, 0)⟩
  | 0, k0, s0 :: s1 :: s2 :: s3 :: s4 :: s5 :: rest, h, _ => by
    simp only [chainHolds] at h
    simpa using h.1
  | i + 1, k0, s0 :: s1 :: s2 :: s3 :: s4 :: s5 :: rest, h, hlen => by
    simp only [chainHolds] at h
    have ih := chainHolds_window i (k0 + 1) (s5 :: rest) h.2
      (by simp at hlen ⊢; omega)
    rw [show k0 + 1 + i = k0 + (i + 1) by omega] at ih
    simpa [show ∀ j, 5 * (i + 1) + j = (5 * i + j) + 5 from fun j => by omega,
      List.getD] using ih
  | _, _, [], h, hlen => by simp at hlen
  | _, _, [_], h, hlen => by
    simp only [List.length_cons, List.length_nil] at hlen
    omega
  | _, _, [_, _], h, hlen => by
    simp only [List.length_cons, List.length_nil] at hlen
    omega
  | _, _, [_, _, _], h, hlen => by
    simp only [List.length_cons, List.length_nil] at hlen
    omega
  | _, _, [_, _, _, _], h, hlen => by
    simp only [List.length_cons, List.length_nil] at hlen
    omega
  | _, _, [_, _, _, _, _], h, hlen => by
    simp only [List.length_cons, List.length_nil] at hlen
    omega

open Std.Do in
/-- **The gadget is sound**: under any satisfying valuation, at a full-size constant
table, the returned state reads as `Poseidon.blockCipher` of the input state's
reading — the fixture-validated production permutation. The row carries the whole
chain, so the proof assembles its five-apart windows into the gate tower's `Chain`
and applies `chain_blockCipher`. -/
@[spec] theorem poseidon_spec {V : Valuation F} [Field F] [DecidableEq F]
    (p : Poseidon.Params F) (hsize : p.roundConstants.size = Poseidon.fullRounds)
    (s : SpongeState F) :
    ⦃⌜True⌝⦄
    poseidon (c := Builder V (KimchiConstraint F)) p s
    ⦃⇓ r _ => ⌜CircuitType.readVal (val := Poseidon.Triple F) V r
        = Poseidon.blockCipher p (CircuitType.readVal (val := Poseidon.Triple F) V s)⌝⦄ := by
  simp only [poseidon]
  mvcgen
  rename_i outs _ _ _ _ hpay
  show (outs[54].s0.val V, outs[54].s1.val V, outs[54].s2.val V)
    = Poseidon.blockCipher p (s.s0.val V, s.s1.val V, s.s2.val V)
  have hchain : chainHolds (mdsOf p.mds) p.roundConstants.toList 0
      (read V ⟨p.mds, p.roundConstants.toList,
        s.cells :: (outs.map SpongeState.cells).toList⟩) := hpay
  let vs : List (F × F × F) :=
    read V ⟨p.mds, p.roundConstants.toList,
      s.cells :: (outs.map SpongeState.cells).toList⟩
  have hlen : vs.length = 56 := by simp [vs, read]
  let w : ℕ → Kimchi.Gate.Poseidon.Witness F := fun k =>
    ⟨vs.getD (5 * k) (0, 0, 0), vs.getD (5 * k + 1) (0, 0, 0),
     vs.getD (5 * k + 2) (0, 0, 0), vs.getD (5 * k + 3) (0, 0, 0),
     vs.getD (5 * k + 4) (0, 0, 0), vs.getD (5 * k + 5) (0, 0, 0)⟩
  have hch : Kimchi.Gate.Poseidon.Chain (Kimchi.Gate.Poseidon.mdsOfParams p)
      (fun i => p.roundConstants.toList.getD i (0, 0, 0)) w 11 := by
    refine ⟨fun i hi => ?_, fun i _ => rfl⟩
    have hw := chainHolds_window i 0 vs hchain (by omega)
    rw [Nat.zero_add] at hw
    exact hw
  have hrc : ∀ i < 5 * 11, (fun i => p.roundConstants.toList.getD i (0, 0, 0)) i
      = Kimchi.Gate.Poseidon.paramsRc p i := by
    intro i _
    simp [Kimchi.Gate.Poseidon.paramsRc, List.getD_eq_getElem?_getD,
      Array.getD_eq_getD_getElem?]
  have hbc := Kimchi.Gate.Poseidon.chain_blockCipher p
    (fun i => p.roundConstants.toList.getD i (0, 0, 0)) w 11 hch (by omega) hsize hrc
  have h0 : (w 0).s0 = (s.s0.val V, s.s1.val V, s.s2.val V) := rfl
  have h55 : (w 10).s5
      = (outs[54].s0.val V, outs[54].s1.val V, outs[54].s2.val V) := by
    show vs.getD 55 (0, 0, 0) = _
    rw [List.getD_eq_getElem vs (0, 0, 0) (by omega)]
    simp [vs, read, Vector.getElem_toList, SpongeState.cells]
  rw [h0, h55] at hbc
  exact hbc

end Poseidon

/-! ## Completeness -/

namespace Poseidon

open Kimchi.Gate.Poseidon (rounds mdsOfParams paramsRc)

private theorem chainHolds_of_succ [Field F] {M : Kimchi.Gate.Poseidon.Mds F}
    {rc : List (F × F × F)} :
    ∀ (k : ℕ) (l : List (F × F × F)),
      (∀ j (hj1 : j + 1 < l.length) (hj0 : j < l.length),
        l[j + 1] = Kimchi.Gate.Poseidon.round M l[j]
          (rc.getD (5 * k + j) (0, 0, 0))) →
      chainHolds M rc k l
  | k, s0 :: s1 :: s2 :: s3 :: s4 :: s5 :: rest, hsucc => by
    simp only [chainHolds]
    refine ⟨?_, ?_⟩
    · have e0 := hsucc 0 (by simp) (by simp)
      have e1 := hsucc 1 (by simp) (by simp)
      have e2 := hsucc 2 (by simp) (by simp)
      have e3 := hsucc 3 (by simp) (by simp)
      have e4 := hsucc 4 (by simp) (by simp)
      simp only [List.getElem_cons_zero, List.getElem_cons_succ] at e0 e1 e2 e3 e4
      have hwin : (⟨s0, s1, s2, s3, s4, s5⟩ : Kimchi.Gate.Poseidon.Witness F)
          = Kimchi.Gate.Poseidon.build M s0 (rcRow rc k) := by
        simp [Kimchi.Gate.Poseidon.build, rcRow, e0, e1, e2, e3, e4]
      rw [hwin]
      exact Kimchi.Gate.Poseidon.complete M s0 (rcRow rc k)
    · refine chainHolds_of_succ (k + 1) (s5 :: rest) ?_
      intro j hj1 hj0
      have hs := hsucc (j + 5) (by simp at hj1 ⊢; omega) (by simp at hj1 ⊢; omega)
      simp only [List.getElem_cons_succ] at hs ⊢
      rw [show 5 * (k + 1) + j = 5 * k + (j + 5) by omega]
      exact hs
  | k, [], _ => by simp [chainHolds]
  | k, [_], _ => by simp [chainHolds]
  | k, [_, _], _ => by simp [chainHolds]
  | k, [_, _, _], _ => by simp [chainHolds]
  | k, [_, _, _, _], _ => by simp [chainHolds]
  | k, [_, _, _, _, _], _ => by simp [chainHolds]

/-- The rounds trajectory checks: a state list whose entries are the round
function's iterates satisfies the checker's window fold. The fold speaks
window-indexed `getD` cells; the trajectory speaks the round function — this is the
honest witness's face of the checker, converted once. -/
private theorem chainHolds_rounds [Field F] [DecidableEq F] (p : Poseidon.Params F)
    (s0 : F × F × F) :
    chainHolds (mdsOf p.mds) p.roundConstants.toList 0
      (s0 :: (List.ofFn fun i : Fin 55 =>
        rounds (mdsOfParams p) (paramsRc p) (i.1 + 1) s0)) := by
  refine chainHolds_of_succ 0 _ ?_
  intro j hj1 hj0
  have hgetD : ∀ (m : ℕ) (hm : m < 56),
      (s0 :: (List.ofFn fun i : Fin 55 =>
          rounds (mdsOfParams p) (paramsRc p) (i.1 + 1) s0))[m]'(by simp; omega)
        = rounds (mdsOfParams p) (paramsRc p) m s0 := by
    intro m hm
    cases m with
    | zero => rfl
    | succ i => simp only [List.getElem_cons_succ, List.getElem_ofFn]
  simp only [List.length_cons, List.length_ofFn] at hj1
  rw [hgetD (j + 1) (by omega), hgetD j (by omega)]
  rw [show (5 * 0 + j) = j by omega]
  have hgd : p.roundConstants.toList.getD j (0, 0, 0)
      = Kimchi.Gate.Poseidon.paramsRc p j := by
    simp [Kimchi.Gate.Poseidon.paramsRc, List.getD_eq_getElem?_getD,
      Array.getD_eq_getD_getElem?]
  rw [hgd]
  rfl


/-- **The gadget is complete**: from a scoped input state that reads `sv`, the run
succeeds — no domain conditions — its row holds at every extension of the final
table, and the output reads back as `Poseidon.blockCipher p sv`.

The advice is the gate's canonical iterate, so the emitted chain is
`chainHolds_rounds` — the gate's own `complete`, applied window by window. -/
@[complete_law]
theorem poseidon_complete [Field F] [DecidableEq F] (p : Poseidon.Params F)
    (hsize : p.roundConstants.size = Poseidon.fullRounds)
    (s : SpongeState F) (sv : Poseidon.Triple F) :
    Complete (F := F) (c := KimchiConstraint F)
      (fun st => CircuitType.ReadsAs (val := Poseidon.Triple F) st s sv)
      (poseidon (c := KimchiConstraint F) p s)
      (fun r st' => CircuitType.ReadsAs (val := Poseidon.Triple F) st' r
        (Poseidon.blockCipher p sv)) := by
  -- the operand's three cells, in scope and reading
  have hcell : ∀ {st : ProverState F} {t : SpongeState F} {v : Poseidon.Triple F},
      CircuitType.ReadsAs (val := Poseidon.Triple F) st t v →
        (t.s0.Scoped st ∧ t.s1.Scoped st ∧ t.s2.Scoped st) ∧
          t.s0.val st.env.get = v.1 ∧ t.s1.val st.env.get = v.2.1 ∧
            t.s2.val st.env.get = v.2.2 := by
    intro st t v h
    rw [CircuitType.ReadsAs, scoped_spongeState, reads_spongeState] at h
    exact ⟨⟨h.1.1, h.1.2.1, h.1.2.2⟩, h.2.1, h.2.2.1, h.2.2.2⟩
  refine Complete.bind
    (Complete.imp (fun st h => ⟨?_, h⟩) (fun _ _ h => h)
      (Complete.frame Mono.readsAs
        (Complete.witness (poseidon.advice p s)
          (Vector.ofFn fun i : Fin 55 => rounds (mdsOfParams p) (paramsRc p) (i.1 + 1) sv)
          (by simp))))
    (fun outs => Complete.bind (Complete.addConstraint ?_)
      fun _ => Complete.pure_of fun _ h => ?_)
  -- the advice runs: the operand's cells through the round chain
  · obtain ⟨⟨hsc0, hsc1, hsc2⟩, hs0, hs1, hs2⟩ := hcell h
    simp only [poseidon.advice, AsProver.bind_eq, AsProver.run_bind,
      AsProver.readCVar_run hsc0, AsProver.readCVar_run hsc1,
      AsProver.readCVar_run hsc2, hs0, hs1, hs2]
    rfl
  -- the chain row, at every extension of the table the run lands in
  · rintro st ⟨hO, hs⟩ stf hle
    obtain ⟨⟨hsc0, hsc1, hsc2⟩, hs0, hs1, hs2⟩ := hcell hs
    have hscO := CircuitType.scoped_vector.mp hO.1
    have hrdO := CircuitType.reads_vector.mp hO.2
    show chainHolds (mdsOf p.mds) p.roundConstants.toList 0
      (read stf.env.get ⟨p.mds, p.roundConstants.toList,
        s.cells :: (outs.map SpongeState.cells).toList⟩)
    have hlist : read stf.env.get ⟨p.mds, p.roundConstants.toList,
        s.cells :: (outs.map SpongeState.cells).toList⟩
        = sv :: (List.ofFn fun i : Fin 55 =>
            rounds (mdsOfParams p) (paramsRc p) (i.1 + 1) sv) := by
      simp only [read, List.map_cons, SpongeState.cells]
      refine congrArg₂ List.cons ?_ ?_
      · rw [CVar.val_of_le hle hsc0, CVar.val_of_le hle hsc1, CVar.val_of_le hle hsc2,
          hs0, hs1, hs2]
      · refine List.ext_getElem (by simp) fun i h1 h2 => ?_
        simp only [List.getElem_map, Vector.getElem_toList, List.getElem_ofFn]
        have hi : i < 55 := by simpa using h2
        have hread := (hrdO i hi).of_le (hscO i hi) hle
        have h0 : outs[i].s0.val stf.env.get = (rounds (mdsOfParams p) (paramsRc p)
            (i + 1) sv).1 := by
          simpa using congrArg (fun w : Vector F 3 => w[0]'(by omega)) hread
        have h1' : outs[i].s1.val stf.env.get = (rounds (mdsOfParams p) (paramsRc p)
            (i + 1) sv).2.1 := by
          simpa using congrArg (fun w : Vector F 3 => w[1]'(by omega)) hread
        have h2' : outs[i].s2.val stf.env.get = (rounds (mdsOfParams p) (paramsRc p)
            (i + 1) sv).2.2 := by
          simpa using congrArg (fun w : Vector F 3 => w[2]'(by omega)) hread
        simp only [Vector.getElem_map, SpongeState.cells]
        rw [h0, h1', h2']
    rw [hlist]
    exact chainHolds_rounds p sv
  -- the result: the last round's state
  · refine ⟨(CircuitType.scoped_vector.mp h.1.1) 54 (by omega), ?_⟩
    have hread := (CircuitType.reads_vector.mp h.1.2) 54 (by omega)
    rw [Kimchi.Gate.Poseidon.blockCipher_eq_rounds, hsize]
    simpa using hread

end Poseidon

attribute [irreducible] poseidon

end Snarky.Kimchi
