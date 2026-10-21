import Snarky.Witness
import Snarky.Prover
import Snarky.Prover.VCGen
import Snarky.Kimchi.Semantics
import Poseidon.Basic
import Kimchi.Gate.Semantics.Poseidon

/-!
# The Poseidon gadget

Transcribes packages/snarky-kimchi/src/Snarky/Circuit/Kimchi/Poseidon.purs: witness the
55 round outputs of the permutation in one bulk witness step (the traversal lives inside
the witness computation, so the circuit itself is three binds), emit the block constraint
over the 56 chained states, and return the output state.

## Implementation notes

- The round outputs are the gate's iterate `Kimchi.Gate.Poseidon.rounds`, with output `i`
  the `(i + 1)`-round prefix; `round_eq_fullRound` identifies it with the sponge's round.
- The parameters arrive as an explicit `p : Poseidon.Params F`, whose data the emitted
  payload carries.
- The states are the nominal `SpongeState` (cells `s0`/`s1`/`s2`), reading as
  `SpongeStateVal`, a `Poseidon.Triple` under its own name; the constraint payload's rows stay
  bare triples (`SpongeState.cells`).
- Labels are not threaded.
-/

namespace Snarky.Kimchi

open Snarky

variable {F c : Type}

/-- The width-3 Poseidon state as circuit variables. Reads as the value side's
`SpongeStateVal` through its `CircuitType` instance. -/
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

/-- The width-3 Poseidon state's values, the value side of `SpongeState`: a
`Poseidon.Triple` under its own name. A `def`, not an `abbrev`, so instance resolution does not
see through it: the sponge state's `CircuitType` instance matches this type only, never another
triple of cells, whose variables are three plain cells. -/
@[implicit_reducible] def SpongeStateVal (F : Type) : Type := Poseidon.Triple F

/-- A width-3 value state encodes as its three slots, read back as a `SpongeState`. -/
instance instCircuitTypeSpongeState :
    CircuitType F (SpongeStateVal F) (SpongeState F) where
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
    CircuitType.readVal (val := SpongeStateVal F) V s
      = (s.s0.val V, s.s1.val V, s.s2.val V) := rfl

/-- The instance's variable encoding. -/
@[simp] theorem varToFields_spongeState (s : SpongeState F) :
    CircuitType.varToFields (val := SpongeStateVal F) s = #v[s.s0, s.s1, s.s2] := rfl

/-- The instance's value encoding. -/
@[simp] theorem valueToFields_spongeState (v : SpongeStateVal F) :
    CircuitType.valueToFields (F := F) (var := SpongeState F) v = #v[v.1, v.2.1, v.2.2] := rfl

/-- The state is in scope when its three cells are. -/
@[simp] theorem scoped_spongeState [Add F] [Mul F] [Zero F] {st : ProverState F}
    {s : SpongeState F} :
    CircuitType.Scoped (val := SpongeStateVal F) st s ↔
      s.s0.Scoped st ∧ s.s1.Scoped st ∧ s.s2.Scoped st := by
  show (∀ cv ∈ [s.s0, s.s1, s.s2], cv.Scoped st) ↔ _
  simp

/-- The state reads a triple exactly when its cells read the components. -/
@[simp] theorem reads_spongeState [Add F] [Mul F] [Zero F] {V : Valuation F}
    {s : SpongeState F} {v : SpongeStateVal F} :
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
instance instCheckedTypeSpongeState [Field F] [BasicSystem F c] [ConstraintHolds F c] :
    CheckedType F c (SpongeStateVal F) (SpongeState F) where
  check _ := pure PUnit.unit
  post _ _ := True
  check_sound _ _ _ _ := trivial

open Std.WP in
/-- The state cells' check keeps their reading. -/
instance instCheckSpecSpongeState [Field F] [BasicSystem F c] [ConstraintHolds F c] :
    Prover.CheckSpec F c (SpongeStateVal F) (SpongeState F) where
  check r v _ := by
    show ⦃Prover.Reads r v⦄ (pure PUnit.unit : CircuitM F (Prover c) PUnit)
      ⦃fun _ ↦ Prover.Reads r v⦄
    vcgen

/-- The Poseidon permutation gadget: one bulk witness of the round outputs, one block
constraint over the 56 chained states at `p`'s data, the last state returned. -/
def poseidon [Field F] [BasicSystem F c] [ConstraintHolds F c]
    [KimchiSystem F c] (p : Poseidon.Params F)
    (initialState : SpongeState F) : CircuitM F c (SpongeState F) := do
  let roundOutputs ← witness (val := Vector (SpongeStateVal F) 55) (advice p initialState)
  addConstraint (KimchiSystem.poseidon
    { mds := p.mds, rc := p.roundConstants.toList,
      state := initialState.cells :: (roundOutputs.map SpongeState.cells).toList })
  pure roundOutputs[54]
where
  /-- The advice: the 55 round outputs, oldest first — the traversal lives here, so
  the circuit itself is one witness and one constraint. -/
  advice (p : Poseidon.Params F) (s : SpongeState F) :
      AsProver F (Vector (SpongeStateVal F) 55) := do
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
      show 5 * (i + 1) = 5 * i + 5 from by omega, List.getD] using ih
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

open Std.WP in
/-- **The gadget is sound**: under any satisfying valuation, at a full-size constant
table, the returned state reads as `Poseidon.blockCipher` of the input state's
reading — the fixture-validated production permutation. The constraint carries the
whole chain, so the proof assembles its five-apart windows into the gate tower's
`Chain` and applies `chain_blockCipher`. -/
@[spec] theorem poseidon_spec {V : Valuation F} [Field F] [DecidableEq F]
    (p : Poseidon.Params F) (hsize : p.roundConstants.size = Poseidon.fullRounds)
    (s : SpongeState F) :
    ⦃fun _ => True⦄
    poseidon (c := Builder V (KimchiConstraint F)) p s
    ⦃fun (r : SpongeState F) _ => CircuitType.readVal (val := SpongeStateVal F) V r
        = Poseidon.blockCipher p (CircuitType.readVal (val := SpongeStateVal F) V s)⦄ := by
  simp only [poseidon]
  vcgen
  rename_i _ hpay
  show (roundOutputs[54].s0.val V, roundOutputs[54].s1.val V, roundOutputs[54].s2.val V)
    = Poseidon.blockCipher p (s.s0.val V, s.s1.val V, s.s2.val V)
  have hchain : chainHolds (mdsOf p.mds) p.roundConstants.toList 0
      (read V ⟨p.mds, p.roundConstants.toList,
        s.cells :: (roundOutputs.map SpongeState.cells).toList⟩) := hpay
  let vs : List (F × F × F) :=
    read V ⟨p.mds, p.roundConstants.toList,
      s.cells :: (roundOutputs.map SpongeState.cells).toList⟩
  have hlen : vs.length = 56 := by simp [vs, read]
  let w : ℕ → Kimchi.Gate.Poseidon.Witness F := fun k =>
    ⟨vs.getD (5 * k) (0, 0, 0), vs.getD (5 * k + 1) (0, 0, 0),
     vs.getD (5 * k + 2) (0, 0, 0), vs.getD (5 * k + 3) (0, 0, 0),
     vs.getD (5 * k + 4) (0, 0, 0), vs.getD (5 * k + 5) (0, 0, 0)⟩
  have hholds : ∀ i < 11, Kimchi.Gate.Poseidon.Holds (Kimchi.Gate.Poseidon.mdsOfParams p)
      (fun j : Fin 5 => p.roundConstants.toList.getD (5 * i + (j : ℕ)) (0, 0, 0)) (w i) := by
    intro i hi
    have hw := chainHolds_window i 0 vs hchain (by omega)
    rw [Nat.zero_add] at hw
    exact hw
  have hrc : ∀ i < 5 * 11, (fun i => p.roundConstants.toList.getD i (0, 0, 0)) i
      = Kimchi.Gate.Poseidon.paramsRc p i := by
    intro i _
    simp [Kimchi.Gate.Poseidon.paramsRc, List.getD_eq_getElem?_getD,
      Array.getD_eq_getD_getElem?]
  have hbc := Kimchi.Gate.Poseidon.chain_blockCipher p
    (fun i => p.roundConstants.toList.getD i (0, 0, 0)) w 11 hholds (fun _ _ => rfl) (by omega)
    hsize hrc
  have h0 : (w 0).s0 = (s.s0.val V, s.s1.val V, s.s2.val V) := rfl
  have h55 : (w 10).s5
      = (roundOutputs[54].s0.val V, roundOutputs[54].s1.val V, roundOutputs[54].s2.val V) := by
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
window-indexed cells; the trajectory speaks the round function — this is the
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

/-! ### At the prover's reading

The permutation's law at the prover's reading (`Snarky.Prover.VCGen`): the input state's reading
in, the block cipher of that reading out. -/

section ProverReading

open Snarky.Prover Std.WP

/-- A state reads a triple exactly when its cells are in scope and read the components. -/
private theorem Prover.reads_spongeState_apply [Field F] (s : SpongeState F)
    (v : SpongeStateVal F) (st : ProverState F) :
    Reads s v st ↔ s.s0.Scoped st ∧ s.s1.Scoped st ∧ s.s2.Scoped st ∧
      s.s0.val st.env.get = v.1 ∧ s.s1.val st.env.get = v.2.1 ∧
        s.s2.val st.env.get = v.2.2 := by
  change CircuitType.ReadsAs st s v ↔ _
  simp only [CircuitType.ReadsAs, scoped_spongeState, reads_spongeState, and_assoc]

/-- `poseidon.advice` returns the round trace of the input state's reading. -/
private theorem Prover.poseidon_advice_run [Field F] (p : Poseidon.Params F)
    {s : SpongeState F} {st : ProverState F} (h0 : s.s0.Scoped st) (h1 : s.s1.Scoped st)
    (h2 : s.s2.Scoped st) :
    (poseidon.advice p s).run st.env = .ok (Vector.ofFn fun i : Fin 55 =>
      rounds (mdsOfParams p) (paramsRc p) (i.1 + 1)
        (s.s0.val st.env.get, s.s1.val st.env.get, s.s2.val st.env.get)) := by
  simp [poseidon.advice, AsProver.readCVar_run h0, AsProver.readCVar_run h1,
    AsProver.readCVar_run h2]

/-- The block row is checked wherever the input state reads `v` and the outputs read the round
trace from `v`. -/
private theorem Prover.poseidon_row_checked [Field F] [DecidableEq F] (p : Poseidon.Params F)
    (s : SpongeState F) (v : SpongeStateVal F) (outs : Vector (SpongeState F) 55) :
    Reads s v ⊓ Reads (val := Vector (SpongeStateVal F) 55) outs (Vector.ofFn fun i : Fin 55 =>
        rounds (mdsOfParams p) (paramsRc p) (i.1 + 1) v) ≤
      Checked (F := F) (KimchiConstraint.poseidon
        { mds := p.mds, rc := p.roundConstants.toList,
          state := s.cells :: (outs.map SpongeState.cells).toList }) := by
  rw [Pred.le_iff]
  intro st hst
  obtain ⟨hs, ho⟩ := (Pred.inf_apply _ _ st).mp hst
  obtain ⟨hs0, hs1, hs2, hv0, hv1, hv2⟩ := (Prover.reads_spongeState_apply s v st).mp hs
  rw [Reads.vector_eq, Pred.iInf_apply] at ho
  have ho' : ∀ (i : ℕ) (hi : i < 55), outs[i].s0.Scoped st ∧ outs[i].s1.Scoped st ∧
      outs[i].s2.Scoped st ∧
      outs[i].s0.val st.env.get = (rounds (mdsOfParams p) (paramsRc p) (i + 1) v).1 ∧
      outs[i].s1.val st.env.get = (rounds (mdsOfParams p) (paramsRc p) (i + 1) v).2.1 ∧
      outs[i].s2.val st.env.get = (rounds (mdsOfParams p) (paramsRc p) (i + 1) v).2.2 :=
    fun i hi ↦ by simpa [Prover.reads_spongeState_apply] using ho ⟨i, hi⟩
  rw [Checked.apply]
  refine ⟨?_, ?_⟩
  · change chainHolds (mdsOf p.mds) p.roundConstants.toList 0
      (read st.env.get ⟨p.mds, p.roundConstants.toList,
        s.cells :: (outs.map SpongeState.cells).toList⟩)
    have hlist : read st.env.get ⟨p.mds, p.roundConstants.toList,
        s.cells :: (outs.map SpongeState.cells).toList⟩
        = v :: List.ofFn fun i : Fin 55 => rounds (mdsOfParams p) (paramsRc p) (i.1 + 1) v := by
      simp only [read, List.map_cons, SpongeState.cells]
      refine congrArg₂ List.cons (by simp [hv0, hv1, hv2]) ?_
      refine List.ext_getElem (by simp) fun i h1 h2 ↦ ?_
      have hi : i < 55 := by simpa using h2
      obtain ⟨-, -, -, e0, e1, e2⟩ := ho' i hi
      rw [List.getElem_map, Vector.getElem_toList, List.getElem_ofFn]
      simp only [Vector.getElem_map, SpongeState.cells]
      rw [e0, e1, e2]
    rw [hlist]
    exact chainHolds_rounds p v
  · intro y hy
    change y ∈ (s.cells :: (outs.map SpongeState.cells).toList).flatMap
      (fun t ↦ [t.1, t.2.1, t.2.2]) at hy
    rw [List.flatMap_cons, List.mem_append] at hy
    rcases hy with hy | hy
    · simp only [SpongeState.cells, List.mem_cons, List.mem_nil_iff, or_false] at hy
      rcases hy with rfl | rfl | rfl <;> assumption
    · obtain ⟨t, ht, hy⟩ := List.mem_flatMap.mp hy
      rw [Vector.toList_map, List.mem_map] at ht
      obtain ⟨o, ho, rfl⟩ := ht
      obtain ⟨i, hi, rfl⟩ := Vector.mem_iff_getElem.mp (Vector.mem_toList_iff.mp ho)
      obtain ⟨c0, c1, c2, -⟩ := ho' i hi
      simp only [SpongeState.cells, List.mem_cons, List.mem_nil_iff, or_false] at hy
      rcases hy with rfl | rfl | rfl <;> assumption

/-- At a full-size constant table, the round trace's last entry is the block cipher. -/
private theorem Prover.poseidon_trace_last [Field F] (p : Poseidon.Params F)
    (hsize : p.roundConstants.size = Poseidon.fullRounds) (v : SpongeStateVal F)
    (outs : Vector (SpongeState F) 55) :
    Reads (F := F) (val := Vector (SpongeStateVal F) 55) outs (Vector.ofFn fun i : Fin 55 =>
        rounds (mdsOfParams p) (paramsRc p) (i.1 + 1) v) ≤
      Reads (val := SpongeStateVal F) outs[54] (Poseidon.blockCipher p v) := by
  rw [Kimchi.Gate.Poseidon.blockCipher_eq_rounds, hsize, Reads.vector_eq]
  exact iInf_le_of_le 54 (by simp)

/-- The permutation's completeness: from an input state reading `v`, at a full-size constant
table, the output reads `Poseidon.blockCipher p v`. The advice's value is the gate's round trace
from `v`, and the row is `chainHolds_rounds` at it. -/
theorem Prover.poseidon_spec [Field F] [DecidableEq F] (p : Poseidon.Params F)
    (hsize : p.roundConstants.size = Poseidon.fullRounds) (s : SpongeState F)
    (v : SpongeStateVal F) :
    ⦃Reads s v⦄ poseidon (c := Prover (KimchiConstraint F)) p s
    ⦃fun r ↦ Reads (val := SpongeStateVal F) r (Poseidon.blockCipher p v)⦄ := by
  have hw := Spec.witness (c := KimchiConstraint F) (poseidon.advice p s)
    (Vector.ofFn fun i : Fin 55 => rounds (mdsOfParams p) (paramsRc p) (i.1 + 1) v)
    (valid_vector.mpr fun _ _ _ _ _ ↦ trivial)
  have hrow := Prover.poseidon_row_checked p s v
  have hlast := Prover.poseidon_trace_last p hsize v
  unfold poseidon
  vcgen [hw]
  all_goals prover_assert with
    (intros; first
      | exact (Pred.le_iff _ _).mp (hrow _) _ ((Pred.inf_apply _ _ _).mpr ⟨‹_›, ‹_›⟩)
      | simp_all [Prover.reads_spongeState_apply, Prover.poseidon_advice_run])

end ProverReading

end Poseidon

attribute [irreducible] poseidon

end Snarky.Kimchi
