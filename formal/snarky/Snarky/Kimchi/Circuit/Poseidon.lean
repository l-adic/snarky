import Snarky.Circuit.DSL.Monad
import Snarky.Backend.Read
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
- PS's width-3 `Vector` states are `Poseidon.Triple` — at `FVar F` in the circuit, at
  `F` in the value sponge, the one carrier (cells `s0`/`s1`/`s2` by name); the
  constraint payload's rows are the same triples.
- The PS `label "poseidon"` wrapper is dropped (labels are not threaded —
  `Kimchi/Constraint.lean`'s deviation ledger).
-/

namespace Snarky.Kimchi

open Snarky

variable {F c : Type}

/-- The bulk witness: read the input state, return all 55 round outputs, oldest
first (the PS `exists` body's `scanl`). -/
private def roundOutputsWit [Field F] (p : Poseidon.Params F)
    (s : Poseidon.Triple (FVar F)) : AsProver F (Vector (Poseidon.Triple F) 55) := do
  let s0 ← AsProver.readCVar s.s0
  let s1 ← AsProver.readCVar s.s1
  let s2 ← AsProver.readCVar s.s2
  pure (Vector.ofFn fun i => Kimchi.Gate.Poseidon.rounds
    (Kimchi.Gate.Poseidon.mdsOfParams p) (Kimchi.Gate.Poseidon.paramsRc p)
    (i.1 + 1) (s0, s1, s2))

/-- The Poseidon permutation gadget (PS `poseidon`): one bulk witness of the round
outputs, one block constraint over the 56 chained states at `p`'s data, the last
state returned. -/
def poseidon [Field F] [KimchiSystem F c] (p : Poseidon.Params F)
    (initialState : Poseidon.Triple (FVar F)) : CircuitM F c (Poseidon.Triple (FVar F)) := do
  let roundOutputs ← witness (val := Vector (Poseidon.Triple F) 55)
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
theorem poseidon_spec {V : Valuation F} [Field F] [DecidableEq F] (p : Poseidon.Params F)
    (hsize : p.roundConstants.size = Poseidon.fullRounds) (s : Poseidon.Triple (FVar F)) :
    ⦃⌜True⌝⦄
    (poseidon (c := Builder V (KimchiConstraint F)) p s)
    ⦃⇓ r _ => ⌜readVal V r = Poseidon.blockCipher p (readVal V s)⌝⦄ := by
  simp only [poseidon]
  mvcgen
  rename_i outs _ _ _ _ hpay
  simp only [readVal_prod, readVal_fvar]
  have hchain : chainHolds (mdsOf p.mds) p.roundConstants.toList 0
      (read V ⟨p.mds, p.roundConstants.toList,
        s :: outs.toList⟩) := hpay
  let vs : List (F × F × F) :=
    read V ⟨p.mds, p.roundConstants.toList,
      s :: outs.toList⟩
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
  have h0 : (w 0).s0 = (s.s0.val V, s.s1.val V, s.s2.val V) := rfl
  have h55 : (w 10).s5
      = (outs[54].1.val V, outs[54].2.1.val V, outs[54].2.2.val V) := by
    show vs.getD 55 (0, 0, 0) = _
    rw [List.getD_eq_getElem vs (0, 0, 0) (by omega)]
    simp [vs, read, Vector.getElem_toList]
  rw [h0, h55] at hbc
  exact hbc

end Poseidon

/-! ## Completeness

`Poseidon.poseidon_run`: the honest run on any in-scope input state — no domain
conditions — lands at `poseidonRun`, whose result reads as `Poseidon.blockCipher` of
the input reading. The witness values are the gate's canonical iterate
(`Kimchi.Gate.Poseidon.rounds`), so each window's satisfaction is the gate's
`complete` at its head state, and the output characterization is
`blockCipher_eq_rounds`. -/

namespace Poseidon

open Kimchi.Gate.Poseidon (rounds mdsOfParams paramsRc)

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
reading: each window is the gate's canonical `build` at its head state, so the gate's
`complete` applies window by window. -/
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

/-- The round outputs the gadget witnesses, of an input reading. -/
private def roundOutputs [Field F] (p : Poseidon.Params F) (sv : Poseidon.Triple F) :
    Vector (Poseidon.Triple F) 55 :=
  Vector.ofFn fun i => rounds (mdsOfParams p) (paramsRc p) (i.1 + 1) sv

/-- The state and result of `poseidon`'s honest run: the 55 round outputs of the
input reading, allocated in order; the last returned. -/
def poseidonRun [Field F] (p : Poseidon.Params F) (st : ProverState F)
    (s : Poseidon.Triple (FVar F)) : ProverState F × Poseidon.Triple (FVar F) :=
  (st.extendMany (CircuitType.valueToFields (F := F) (var := Vector (Poseidon.Triple (FVar F)) 55)
      (roundOutputs p (readVal st.env.toValuation s))).toList,
    (CircuitType.fieldsToVar (F := F) (val := Vector (Poseidon.Triple F) 55)
      (mapVec CVar.var (allocRange st.nv (CircuitType.size F (Vector (Poseidon.Triple F) 55)))))[54])

/-- The gadget's honest run on an in-scope state lands at `poseidonRun`: the bulk
witness, then the chain constraint accepted on the honest trajectory. -/
theorem poseidon_run [Field F] [DecidableEq F] (p : Poseidon.Params F)
    {s : Poseidon.Triple (FVar F)} (st : ProverState F)
    (hs : CircuitType.Scoped (Poseidon.Triple F) st s) :
    prove (Checker.holds (F := F) (c := KimchiConstraint F))
      (poseidon (c := KimchiConstraint F) p s) st.nv st.env
      = .ok ((poseidonRun p st s).1.out (poseidonRun p st s).2) := by
  have h0 : s.1.Scoped st := scoped_fvar_iff.mp (scoped_prod_iff.mp hs).1
  have h1 : s.2.1.Scoped st :=
    scoped_fvar_iff.mp (scoped_prod_iff.mp (scoped_prod_iff.mp hs).2).1
  have h2 : s.2.2.Scoped st :=
    scoped_fvar_iff.mp (scoped_prod_iff.mp (scoped_prod_iff.mp hs).2).2
  have hsv : readVal st.env.toValuation s
      = (s.1.val st.env.toValuation, s.2.1.val st.env.toValuation,
          s.2.2.val st.env.toValuation) := by
    simp only [readVal_prod, readVal_fvar]
  simp only [poseidon, prove_bind]
  rw [prove_witness_run (w := roundOutputsWit p s) st
    (.bind (.readCVar h0) fun _ => .bind (.readCVar h1) fun _ => .bind (.readCVar h2) fun _ =>
      trivial)
    (v := roundOutputs p (readVal st.env.toValuation s))
    (by simp [roundOutputsWit, roundOutputs, Except.bind, hsv])]
  have hg := fun i hi => Grants.alloc_vector_get (F := F) (var := Poseidon.Triple (FVar F)) st
    (roundOutputs p (readVal st.env.toValuation s)) i hi
  generalize houts : (CircuitType.fieldsToVar (F := F) (val := Vector (Poseidon.Triple F) 55)
    (mapVec CVar.var (allocRange st.nv (CircuitType.size F (Vector (Poseidon.Triple F) 55)))))
    = outs at hg ⊢
  generalize hst₁ : st.extendMany (CircuitType.valueToFields (F := F)
    (var := Vector (Poseidon.Triple (FVar F)) 55)
    (roundOutputs p (readVal st.env.toValuation s))).toList = st₁ at hg ⊢
  have hle : st.env.Le st₁.env := (hg 0 (by decide)).le
  simp only [Except.bind]
  have hcheck : Checker.holds (F := F) (c := KimchiConstraint F)
      (KimchiSystem.poseidon ⟨p.mds, p.roundConstants.toList, s :: outs.toList⟩) st₁.env
      = true := by
    show KimchiConstraint.check (.poseidon ⟨p.mds, p.roundConstants.toList, _⟩) _ = true
    have hstates : evalStates st₁.env (s :: outs.toList)
        = .ok (readVal st.env.toValuation s :: (List.ofFn fun i : Fin 55 =>
            rounds (mdsOfParams p) (paramsRc p) (i.1 + 1) (readVal st.env.toValuation s))) := by
      refine evalStates_ok _ _ ?_ (by simp)
      intro j hj hj'
      cases j with
      | zero =>
        simp only [List.getElem_cons_zero, hsv]
        exact ⟨by rw [CVar.eval_eq_val (h0.of_le hle), CVar.val_of_le hle h0],
          by rw [CVar.eval_eq_val (h1.of_le hle), CVar.val_of_le hle h1],
          by rw [CVar.eval_eq_val (h2.of_le hle), CVar.val_of_le hle h2]⟩
      | succ i =>
        simp only [List.length_cons, Vector.length_toList] at hj
        have hgi := hg i (by omega)
        have hsc := scoped_prod_iff.mp hgi.scope
        have hsc2 := scoped_prod_iff.mp hsc.2
        have hrd := hgi.read
        simp only [readVal_prod, readVal_fvar, roundOutputs, Vector.getElem_ofFn,
          Prod.ext_iff] at hrd
        simp only [List.getElem_cons_succ, Vector.getElem_toList, List.getElem_ofFn]
        rw [hsv, CVar.eval_eq_val (scoped_fvar_iff.mp hsc.1),
          CVar.eval_eq_val (scoped_fvar_iff.mp hsc2.1),
          CVar.eval_eq_val (scoped_fvar_iff.mp hsc2.2), hrd.1, hrd.2.1, hrd.2.2]
        exact ⟨rfl, rfl, rfl⟩
    simp only [KimchiConstraint.check, hstates]
    exact (chainOk_iff 0 _).mpr (chainHolds_rounds p _)
  rw [prove_addConstraint st₁ hcheck]
  subst hst₁ houts
  rfl

/-- The permutation's run grows the table, with its result in scope — whatever the
parameters. -/
theorem poseidonRun_scope [Field F] (p : Poseidon.Params F) (st : ProverState F)
    (s : Poseidon.Triple (FVar F)) :
    st.env.Le (poseidonRun p st s).1.env ∧
      CircuitType.Scoped (Poseidon.Triple F) (poseidonRun p st s).1 (poseidonRun p st s).2 :=
  let h := Grants.alloc_vector_get (F := F) (var := Poseidon.Triple (FVar F)) st
    (roundOutputs p (readVal st.env.toValuation s)) 54 (by decide)
  ⟨h.le, h.scope⟩

/-- `poseidonRun` reads as the block cipher of the input reading. -/
theorem poseidonRun_grants [Field F] (p : Poseidon.Params F)
    (hsize : p.roundConstants.size = Poseidon.fullRounds) (st : ProverState F)
    (s : Poseidon.Triple (FVar F)) :
    Grants (Poseidon.Triple F) st (poseidonRun p st s)
      (Poseidon.blockCipher p (readVal st.env.toValuation s)) := by
  have h := Grants.alloc_vector_get (F := F) (var := Poseidon.Triple (FVar F)) st
    (roundOutputs p (readVal st.env.toValuation s)) 54 (by decide)
  have hr := h.read
  dsimp only at hr
  refine ⟨h.le, h.scope, hr.trans ?_⟩
  simp only [roundOutputs, Vector.getElem_ofFn]
  rw [show (54 + 1 : ℕ) = p.roundConstants.size by rw [hsize]]
  exact (Kimchi.Gate.Poseidon.blockCipher_eq_rounds p _).symm

end Poseidon

end Snarky.Kimchi
