import Snarky.Circuit.DSL.Monad
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

Name map: `poseidon` keeps its name; the `exists` body's `scanl` renders as the
indexed prefix map `roundsUpTo` (same values, and output `i` is the `(i + 1)`-round
prefix by definition).

Deviations from the PS original (per `formal/docs/snarky-kimchi-alignment.md`):
- PS's ambient `PoseidonField` class arrives as the explicit parameter
  `p : Poseidon.Params F`, whose data the emitted payload carries (the payload-data
  deviation in `Constraint/Poseidon.lean`).
- PS's width-3 `Vector` states render as triples, matching the payload.
- The PS `label "poseidon"` wrapper is dropped (labels are not threaded —
  `Kimchi/Constraint.lean`'s deviation ledger).
-/

namespace Snarky.Kimchi

open Snarky

variable {F c : Type}

/-- The state after rounds `0 … k − 1` (the `k`-prefix of the `blockCipher` fold;
`getD` never fires at the deployed 55-entry table). -/
private def roundsUpTo [Field F] (p : Poseidon.Params F) :
    ℕ → F × F × F → F × F × F
  | 0, s => s
  | k + 1, s =>
    Poseidon.fullRound p.mds (p.roundConstants.getD k (0, 0, 0)) (roundsUpTo p k s)

/-- The bulk witness: read the input state, return all 55 round outputs, oldest
first (the PS `exists` body's `scanl`). -/
private def roundOutputsWit [Field F] (p : Poseidon.Params F)
    (s : FVar F × FVar F × FVar F) : AsProver F (Vector (F × F × F) 55) := do
  let s0 ← AsProver.readCVar s.1
  let s1 ← AsProver.readCVar s.2.1
  let s2 ← AsProver.readCVar s.2.2
  pure (Vector.ofFn fun i => roundsUpTo p (i.1 + 1) (s0, s1, s2))

/-- The Poseidon permutation gadget (PS `poseidon`): one bulk witness of the round
outputs, one block constraint over the 56 chained states at `p`'s data, the last
state returned. -/
def poseidon [Field F] [KimchiSystem F c] (p : Poseidon.Params F)
    (initialState : FVar F × FVar F × FVar F) :
    CircuitM F c (FVar F × FVar F × FVar F) := do
  let roundOutputs ← witness (val := Vector (F × F × F) 55)
    (roundOutputsWit p initialState)
  addConstraint (KimchiSystem.poseidon
    { mds := p.mds, rc := p.roundConstants.toList,
      state := initialState :: roundOutputs.toList })
  pure roundOutputs[54]

/-! ## Soundness

`Poseidon.poseidon_spec`: any satisfying valuation reads the returned state as
`Poseidon.blockCipher` of the input state — the fixture-validated production
permutation. The walk is three nodes (the bulk witness promises nothing, the
constraint carries the whole chain), and the finish assembles the payload's
`chainHolds` windows into the gate tower's `Chain` and applies
`chain_blockCipher`. -/

namespace Poseidon

open Std.Do

/-- Window `i` of a satisfied chain, read off the list by index: `chainHolds` from
position `k0` puts the gate's `Holds` on every five-apart window, at the constant
table's row `k0 + i`. -/
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

/-- The gadget is sound: under any satisfying valuation, at a full-size constant
table, the returned state's values are `Poseidon.blockCipher` of the input state's
values. -/
theorem poseidon_spec [Field F] [DecidableEq F] (p : Poseidon.Params F)
    (hsize : p.roundConstants.size = 5 * 11) (s : FVar F × FVar F × FVar F)
    (Q : PostCond (FVar F × FVar F × FVar F) (.arg (BuilderState F) .pure)) :
    ⦃Sound (fun V (r : FVar F × FVar F × FVar F) =>
        (r.1.val V, r.2.1.val V, r.2.2.val V)
          = Poseidon.blockCipher p (s.1.val V, s.2.1.val V, s.2.2.val V)) Q⦄
    (poseidon (c := KimchiConstraint F) p s)
    ⦃Q⦄ := by
  simp only [poseidon]
  mvcgen
  rename_i st hpre
  intro outs _
  mvcgen
  intro u _ hpay
  mvcgen
  refine hpre _ _ ?_
  have hchain : chainHolds (mdsOf p.mds) p.roundConstants.toList 0
      (read st.V ⟨p.mds, p.roundConstants.toList, s :: outs.toList⟩) := hpay
  let vs : List (F × F × F) :=
    read st.V ⟨p.mds, p.roundConstants.toList, s :: outs.toList⟩
  have hlen : vs.length = 56 := by
    simp [vs, read]
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
  have h0 : (w 0).s0 = (s.1.val st.V, s.2.1.val st.V, s.2.2.val st.V) := rfl
  have h55 : (w 10).s5
      = (outs[54].1.val st.V, outs[54].2.1.val st.V, outs[54].2.2.val st.V) := by
    show vs.getD 55 (0, 0, 0) = _
    rw [List.getD_eq_getElem vs (0, 0, 0) (by omega)]
    simp [vs, read, Vector.getElem_toList]
  rw [h0, h55] at hbc
  exact hbc

end Poseidon

/-! ## Completeness

`Poseidon.poseidon_complete_spec`: the honest `KimchiProverC` run accepts on any
readable input state — no domain conditions — and the output reads back as
`Poseidon.blockCipher` of the inputs. The witness values are `roundsUpTo` prefixes,
so each window's five equations hold by the recursion itself, read through
`round_eq_fullRound`. -/

namespace Poseidon

/-- The prefix map is the gate tower's iterate at the parameter family. -/
private theorem roundsUpTo_eq_rounds [Field F] (p : Poseidon.Params F) :
    ∀ (k : ℕ) (s : F × F × F),
      roundsUpTo p k s
        = Kimchi.Gate.Poseidon.rounds (Kimchi.Gate.Poseidon.mdsOfParams p)
            (Kimchi.Gate.Poseidon.paramsRc p) k s
  | 0, _ => rfl
  | k + 1, s => by
    rw [show roundsUpTo p (k + 1) s
        = Poseidon.fullRound p.mds (p.roundConstants.getD k (0, 0, 0))
            (roundsUpTo p k s) from rfl,
      Kimchi.Gate.Poseidon.rounds, roundsUpTo_eq_rounds p k s,
      Kimchi.Gate.Poseidon.round_eq_fullRound]
    rfl

/-- The decidable chain check reflects the chain reading (the gate's `ok_iff`,
windowed). -/
private theorem chainOk_iff [Field F] [DecidableEq F]
    {M : Kimchi.Gate.Poseidon.Mds F} {rc : List (F × F × F)} :
    ∀ (k : ℕ) (l : List (F × F × F)), chainOk M rc k l = true ↔ chainHolds M rc k l
  | k, [] => by simp [chainOk, chainHolds]
  | k, [_] => by simp [chainOk, chainHolds]
  | k, [_, _] => by simp [chainOk, chainHolds]
  | k, [_, _, _] => by simp [chainOk, chainHolds]
  | k, [_, _, _, _] => by simp [chainOk, chainHolds]
  | k, s0 :: s1 :: s2 :: s3 :: s4 :: [] => by simp [chainOk, chainHolds]
  | k, s0 :: s1 :: s2 :: s3 :: s4 :: s5 :: rest => by
    simp only [chainOk, chainHolds, Bool.and_eq_true,
      Kimchi.Gate.Poseidon.ok_iff, chainOk_iff (k + 1) (s5 :: rest)]

/-- A list whose successive entries are the gate's round images satisfies the chain
reading: each window's fifteen constraint expressions vanish by the adjacency
equations alone. -/
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
      intro e he
      simp only [Kimchi.Gate.Poseidon.constraints, rcRow, List.mem_cons,
        List.not_mem_nil, or_false] at he
      rcases he with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
        (subst h; simp [e0, e1, e2, e3, e4])
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

/-- Element reads assemble into the state-list evaluation. -/
private theorem evalStates_ok [Field F] [DecidableEq F] {env : Assignments F} :
    ∀ (ts : List (FVar F × FVar F × FVar F)) (vs : List (F × F × F)),
      (∀ j (hj : j < ts.length) (hj' : j < vs.length),
        ts[j].1.eval env = .ok vs[j].1 ∧
        ts[j].2.1.eval env = .ok vs[j].2.1 ∧
        ts[j].2.2.eval env = .ok vs[j].2.2) →
      ts.length = vs.length →
      evalStates env ts = .ok vs
  | [], [], _, _ => rfl
  | [], _ :: _, _, hlen => by simp at hlen
  | _ :: _, [], _, hlen => by simp at hlen
  | t :: ts, v :: vs, hread, hlen => by
    obtain ⟨h1, h2, h3⟩ := hread 0 (by simp) (by simp)
    simp only [List.getElem_cons_zero] at h1 h2 h3
    have ih := evalStates_ok ts vs
      (fun j hj hj' => by
        have := hread (j + 1) (by simpa using hj) (by simpa using hj')
        simpa only [List.getElem_cons_succ] using this)
      (by simpa using hlen)
    simp [evalStates, h1, h2, h3, ih, Bind.bind, Except.bind, Pure.pure, Except.pure]

open Std.Do in
/-- The gadget is complete: the honest prover run accepts on any readable input
state — no domain conditions — and the output state reads back as
`Poseidon.blockCipher` of the input values. -/
theorem poseidon_complete_spec [Field F] [DecidableEq F] (p : Poseidon.Params F)
    (hsize : p.roundConstants.size = 5 * 11) (s : FVar F × FVar F × FVar F)
    (Q : PostCond (FVar F × FVar F × FVar F)
      (.arg (ProverState F) (.except EvalError .pure))) :
    ⦃Complete
        (fun env =>
          (s.1.eval env).isOk ∧ (s.2.1.eval env).isOk ∧ (s.2.2.eval env).isOk)
        (fun env (r : FVar F × FVar F × FVar F) env' =>
          ∀ a b c, s.1.eval env = .ok a → s.2.1.eval env = .ok b →
            s.2.2.eval env = .ok c →
            r.1.eval env' = .ok (Poseidon.blockCipher p (a, b, c)).1 ∧
            r.2.1.eval env' = .ok (Poseidon.blockCipher p (a, b, c)).2.1 ∧
            r.2.2.eval env' = .ok (Poseidon.blockCipher p (a, b, c)).2.2)
        Q⦄
    (poseidon (c := KimchiProverC F) p s)
    ⦃Q⦄ := by
  simp only [poseidon]
  mvcgen
  rename_i st hpre
  obtain ⟨⟨haok, hbok, hcok⟩, hk⟩ := hpre
  obtain ⟨av, ha⟩ := CVar.evalOk haok
  obtain ⟨bv, hb⟩ := CVar.evalOk hbok
  obtain ⟨cv, hc⟩ := CVar.evalOk hcok
  have hwit : roundOutputsWit p s st.env
      = .ok (Vector.ofFn fun i => roundsUpTo p (i.1 + 1) (av, bv, cv)) := by
    simp [roundOutputsWit, AsProver.readCVar, ha, hb, hc, Bind.bind, ReaderT.bind,
      Except.bind, Pure.pure, ReaderT.pure, Except.pure]
  refine ⟨by rw [hwit]; rfl, fun outs st₁ hgrant hle₁ => ?_⟩
  have hread := hgrant _ hwit
  have helem : ∀ (i : ℕ) (hi : i < 55),
      outs[i].1.eval st₁.env = .ok (roundsUpTo p (i + 1) (av, bv, cv)).1 ∧
      outs[i].2.1.eval st₁.env = .ok (roundsUpTo p (i + 1) (av, bv, cv)).2.1 ∧
      outs[i].2.2.eval st₁.env = .ok (roundsUpTo p (i + 1) (av, bv, cv)).2.2 := by
    intro i hi
    have h := hread i hi
    simpa only [Vector.getElem_ofFn] using h
  mvcgen
  refine addConstraint_complete_spec (c := KimchiConstraint F)
    (KimchiSystem.poseidon ⟨p.mds, p.roundConstants.toList, s :: outs.toList⟩)
    (fun a => wp⟦pure outs[54]⟧ Q, Q.2) st₁ ⟨?_, fun u st₂ _ hle₂ => ?_⟩
  · show KimchiConstraint.check
      (.poseidon ⟨p.mds, p.roundConstants.toList, s :: outs.toList⟩) st₁.env = true
    have hstates : evalStates st₁.env (s :: outs.toList)
        = .ok ((av, bv, cv) ::
            (List.ofFn fun i : Fin 55 => roundsUpTo p (i.1 + 1) (av, bv, cv))) := by
      refine evalStates_ok _ _ ?_ (by simp)
      intro j hj hj'
      cases j with
      | zero =>
        exact ⟨CVar.eval_le hle₁ ha, CVar.eval_le hle₁ hb, CVar.eval_le hle₁ hc⟩
      | succ i =>
        simp only [List.length_cons, Vector.length_toList] at hj
        have h := helem i (by omega)
        simp only [List.getElem_cons_succ, Vector.getElem_toList, List.getElem_ofFn]
        exact h
    have hchain : chainHolds (mdsOf p.mds) p.roundConstants.toList 0
        ((av, bv, cv) ::
          (List.ofFn fun i : Fin 55 => roundsUpTo p (i.1 + 1) (av, bv, cv))) := by
      refine chainHolds_of_succ 0 _ ?_
      intro j hj1 hj0
      have hgetD : ∀ (m : ℕ) (hm : m < 56),
          ((av, bv, cv) ::
            (List.ofFn fun i : Fin 55 => roundsUpTo p (i.1 + 1) (av, bv, cv)))[m]'(
              by simp; omega)
            = roundsUpTo p m (av, bv, cv) := by
        intro m hm
        cases m with
        | zero => rfl
        | succ i => simp only [List.getElem_cons_succ, List.getElem_ofFn]
      simp only [List.length_cons, List.length_ofFn] at hj1
      rw [hgetD (j + 1) (by omega), hgetD j (by omega)]
      rw [show (5 * 0 + j) = j by omega]
      rw [show roundsUpTo p (j + 1) (av, bv, cv)
          = Poseidon.fullRound p.mds (p.roundConstants.getD j (0, 0, 0))
              (roundsUpTo p j (av, bv, cv)) from rfl,
        ← Kimchi.Gate.Poseidon.round_eq_fullRound]
      have hgd : p.roundConstants.toList.getD j (0, 0, 0)
          = p.roundConstants.getD j (0, 0, 0) := by
        simp [List.getD_eq_getElem?_getD, Array.getD_eq_getD_getElem?]
      rw [hgd]
      rfl
    simp only [KimchiConstraint.check, hstates]
    exact (chainOk_iff 0 _).mpr hchain
  · simp only [wp, PredTrans.apply, prove]
    intro hf
    refine hk _ ⟨st₂.nv, st₂.env, hf⟩ (fun a b c ha' hb' hc' => ?_) (hle₁.trans hle₂)
    rw [ha] at ha'
    rw [hb] at hb'
    rw [hc] at hc'
    injection ha' with ha'
    injection hb' with hb'
    injection hc' with hc'
    subst ha' hb' hc'
    have h54 := helem 54 (by omega)
    have hbc : Poseidon.blockCipher p (av, bv, cv)
        = roundsUpTo p 55 (av, bv, cv) := by
      rw [roundsUpTo_eq_rounds,
        show (55 : ℕ) = p.roundConstants.size by rw [hsize]]
      exact Kimchi.Gate.Poseidon.blockCipher_eq_rounds p (av, bv, cv)
    rw [hbc]
    exact ⟨CVar.eval_le hle₂ h54.1, CVar.eval_le hle₂ h54.2.1,
      CVar.eval_le hle₂ h54.2.2⟩

end Poseidon

end Snarky.Kimchi
