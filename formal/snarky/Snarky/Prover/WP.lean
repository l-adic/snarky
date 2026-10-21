import Snarky.Prover

/-!
# The operational transformer of `prove`

The completeness tag `Prover c` and the predicate transformer of the prover's run, by recursion
on the program: the state is the prover state, counter and table; a failing witness computation
hands its error to the failure condition; and each emitted row is an obligation at the state where
it is emitted. `proverWP_prove` is its adequacy with respect to `prove` and `build`. The assertion
language and the weakest-precondition instance built on this transformer are in
`Snarky.Prover.StableWP`.
-/

namespace Snarky

variable {F c : Type}

/-- The completeness tag: `c` read by the prover. A program enters the completeness reading as
`g (c := Prover c)`; instance search does not unfold `Prover`, so the tag gets its own `WP`
instance while the term stays a `CircuitM F c` program. -/
def Prover (c : Type) := c

instance [inst : ConstraintHolds F c] : ConstraintHolds F (Prover c) := inst

instance [inst : BasicSystem F c] : BasicSystem F (Prover c) := inst

instance [Add F] [Mul F] [Zero F] [One F] [BasicSystem F c] [ConstraintHolds F c]
    [inst : LawfulBasicSystem F c] : LawfulBasicSystem F (Prover c) := inst

/-- The prover's predicate transformer, by recursion on the program: `pure` lands the result at
the current state; an emitted row is an obligation at the current table, with its cells in scope
there (so it holds at every later table, `ProverState.holds_of_le`); a witness computation that
fails hands its error and the current state to the failure condition, and one that succeeds
continues at the state allocating its values, as `prove` does. -/
def proverWP [Zero F] [ConstraintHolds F c] {α : Type} :
    CircuitM F c α → (α → ProverState F → ULift Prop) →
      (EvalError → ProverState F → ULift Prop) → ProverState F → ULift Prop
  | .pure a, Q, _, st => Q a st
  | .addConstraintOp con k, Q, E, st =>
      .up (ConstraintHolds.Holds st.env.get con ∧
        (∀ x ∈ ConstraintHolds.cells (F := F) con, x.Scoped st) ∧ (proverWP k Q E st).down)
  | .existsOp n wit k, Q, E, st =>
      match wit.run st.env with
      | .error e => E e st
      | .ok xs => proverWP (k (allocRange st.nv n)) Q E (st.alloc xs)

/-- A sequence's transformer is the head's at the tail's, the shape `Std.Do.WPMonad` needs. -/
theorem proverWP_bind [Zero F] [ConstraintHolds F c] {α β : Type} (x : CircuitM F c α)
    (f : α → CircuitM F c β) (Q : β → ProverState F → ULift Prop)
    (E : EvalError → ProverState F → ULift Prop) (st : ProverState F) :
    proverWP (x >>= f) Q E st = proverWP x (fun a s => proverWP (f a) Q E s) E st := by
  show proverWP (CircuitM.bind x f) Q E st = _
  induction x generalizing st with
  | pure a => rfl
  | addConstraintOp con k ih => simp only [CircuitM.bind, proverWP, ih]
  | existsOp n wit k ih =>
    simp only [CircuitM.bind, proverWP]
    rcases h : wit.run st.env with e | xs
    · rfl
    · exact ih _ _

/-! ## The reading vocabulary

A cell's reading at a state is the total function `read`; a row whose cells are in scope keeps
holding as the table grows, and so does a bundle's reading. -/

/-- A cell's reading at a state. -/
abbrev ProverState.read [Add F] [Mul F] [Zero F] (st : ProverState F) (x : CVar F) : F :=
  x.val st.env.get

/-- A cell in scope stays in scope. -/
theorem CVar.Scoped.of_le {st st' : ProverState F} (hle : st ≤ st') {x : CVar F}
    (hx : x.Scoped st) : x.Scoped st' :=
  hx.mono (ProverState.nv_le_of_le hle)

/-- A row whose cells are in scope at a table holds at every later one once it holds there:
the frame fact for rows, `LawfulBasicSystem.holds_congr` at the scoped cells' stable readings. -/
theorem ProverState.holds_of_le [Add F] [Mul F] [Zero F] [One F] [BasicSystem F c]
    [ConstraintHolds F c] [LawfulBasicSystem F c] {con : c} {st st' : ProverState F}
    (hs : ∀ x ∈ ConstraintHolds.cells (F := F) con, x.Scoped st) (hle : st ≤ st')
    (h : ConstraintHolds.Holds st.env.get con) : ConstraintHolds.Holds st'.env.get con :=
  (LawfulBasicSystem.holds_congr con _ _ fun x hx => (CVar.val_of_le hle (hs x hx)).symm).mp h

/-- A bundle's reading survives the state's growth: `CircuitType.monotone_readsAs` as the
plain lemma a chain's conditions cite. -/
theorem CircuitType.ReadsAs.of_le [Add F] [Mul F] [Zero F] {val var : Type}
    [CircuitType F val var] {st st' : ProverState F} (hle : st ≤ st') {r : var} {v : val}
    (h : CircuitType.ReadsAs (val := val) st r v) : CircuitType.ReadsAs (val := val) st' r v :=
  CircuitType.monotone_readsAs hle h

/-! ## Adequacy

What the transformer promises of `prove`: from a state where it holds at a success condition,
with failure excluded, the run succeeds into the condition, and every row the builder emits
holds at every later table, carried there from where it is emitted by
`ProverState.holds_of_le` on its cells' scope. -/

/-- A run from a state where the transformer holds, with failure excluded, succeeds: its result
and final state satisfy the success condition, and every row the builder emits from the state's
counter holds at every table extending the final one. -/
theorem proverWP_prove [Add F] [Mul F] [Zero F] [One F] [BasicSystem F c] [ConstraintHolds F c]
    [LawfulBasicSystem F c] {α : Type} {x : CircuitM F c α} {Q : α → ProverState F → ULift Prop}
    {st : ProverState F} (h : (proverWP x Q (fun _ _ => .up False) st).down) :
    ∃ r st', prove x st.nv st.env = .ok (st'.out r) ∧ st ≤ st' ∧ (Q r st').down ∧
      ∀ stf, st' ≤ stf → ∀ con ∈ (build x st.nv).constraints,
        ConstraintHolds.Holds stf.env.get con := by
  induction x generalizing st with
  | pure r => exact ⟨r, st, rfl, le_rfl, h, fun _ _ _ hcon => by simp [build] at hcon⟩
  | addConstraintOp con k ih =>
    obtain ⟨hcon, hs, hk⟩ := h
    obtain ⟨r, st', hrun, hle, hQ, hrows⟩ := ih hk
    refine ⟨r, st', hrun, hle, hQ, fun stf hf con' hcon' => ?_⟩
    rcases List.mem_cons.mp hcon' with rfl | hcon'
    · exact ProverState.holds_of_le hs (hle.trans hf) hcon
    · exact hrows stf hf con' hcon'
  | existsOp n wit k ih =>
    simp only [proverWP] at h
    rcases hw : wit.run st.env with e | xs <;> rw [hw] at h
    · exact (h : False).elim
    · obtain ⟨r, st', hrun, hle, hQ, hrows⟩ := ih _ h
      refine ⟨r, st', ?_, (st.dom.le_extendList _).trans hle, hQ, hrows⟩
      simp only [prove, hw]
      exact hrun

end Snarky
