import Mathlib.Order.UpperLower.CompleteLattice
import Snarky.Prover.WP
import Std.WP

/-!
# Persistent prover assertions and weakest preconditions

Upper sets of prover states are ordered by entailment and adapted to `Std.WP.Assertion`. The boxed
constraint-checking transformer preserves these assertions across calls. Stable contracts
retain their operational meaning through `triple_iff`.

## Assertion model

The state order is assignment extension; the assertion order is inclusion. The lattice
bridges identify the assertion operations with their Mathlib counterparts.
-/

namespace Snarky.Prover

open Std.WP

/-- Assertions preserved by extension of the prover's assignment table. -/
abbrev Pred (F : Type) := OrderDual (UpperSet (ProverState F))

namespace Pred

variable {F : Type}

/-- Evaluate a persistent assertion at a prover state. -/
def holds (P : Pred F) (s : ProverState F) : Prop := s ∈ OrderDual.ofDual P

instance : CoeFun (OrderDual (UpperSet (ProverState F))) (fun _ ↦ ProverState F → Prop) :=
  ⟨holds⟩

/-- Bundle a state predicate with its preservation proof. -/
def mk (p : ProverState F → Prop) (h : ∀ {s t}, s ≤ t → p s → p t) : Pred F :=
  OrderDual.toDual ⟨{s | p s}, fun _ _ hst ↦ h hst⟩

/-- An assertion holds at every extension of a state where it holds. -/
theorem mono (P : Pred F) {s t : ProverState F} (hst : s ≤ t) (hp : P s) : P t :=
  (OrderDual.ofDual P).upper hst hp

@[ext] theorem ext {P Q : Pred F} (h : ∀ s, P s ↔ Q s) : P = Q :=
  UpperSet.ext (Set.ext h)

@[simp] theorem le_iff (P Q : Pred F) : P ≤ Q ↔ ∀ s, P s → Q s := Iff.rfl

@[simp] theorem inf_apply (P Q : Pred F) (s : ProverState F) :
    (P ⊓ Q) s ↔ P s ∧ Q s := Iff.rfl

@[simp] theorem top_apply (s : ProverState F) : (⊤ : Pred F) s ↔ True := Iff.rfl

@[simp] theorem bot_apply (s : ProverState F) : (⊥ : Pred F) s ↔ False := Iff.rfl

@[simp] theorem sSup_apply (ps : Set (Pred F)) (s : ProverState F) :
    sSup ps s ↔ ∃ P ∈ ps, P s := UpperSet.mem_sInf_iff

@[simp] theorem sInf_apply (ps : Set (Pred F)) (s : ProverState F) :
    sInf ps s ↔ ∀ P ∈ ps, P s := UpperSet.mem_sSup_iff

@[simp] theorem iSup_apply {ι : Sort u} (P : ι → Pred F) (s : ProverState F) :
    (⨆ i, P i) s ↔ ∃ i, P i s := UpperSet.mem_iInf_iff

@[simp] theorem iInf_apply {ι : Sort u} (P : ι → Pred F) (s : ProverState F) :
    (⨅ i, P i) s ↔ ∀ i, P i s := by
  simp only [iInf, sInf_apply, Set.mem_range, forall_exists_index, forall_apply_eq_imp_iff]

/-- A mathematical proposition as a persistent assertion. -/
def ofProp (p : Prop) : Pred F := mk (fun _ ↦ p) (fun _ h ↦ h)

@[instance_reducible]
private def mathlibToWP (α : Type u) [CompleteLattice α] : Lean.Order.CompleteLattice α where
  rel := (· ≤ ·)
  rel_refl := le_refl _
  rel_trans := le_trans
  rel_antisymm := le_antisymm
  has_sup ps := ⟨sSup {P | ps P}, fun _ ↦
    ⟨fun h _ hp ↦ le_trans (le_sSup hp) h, fun h ↦ sSup_le h⟩⟩

private instance : Lean.Order.CompleteLattice (OrderDual (UpperSet (ProverState F))) :=
  mathlibToWP _

@[simp] private theorem std_le (P Q : OrderDual (UpperSet (ProverState F))) :
    Lean.Order.PartialOrder.rel P Q ↔ P ≤ Q := Iff.rfl

@[simp] private theorem std_sSup (ps : OrderDual (UpperSet (ProverState F)) → Prop) :
    Lean.Order.CompleteLattice.sup ps = sSup {P | ps P} := by
  apply le_antisymm
  · exact Lean.Order.sup_le (α := Pred F) (x := sSup {P | ps P}) ps fun _ h ↦ le_sSup h
  · exact sSup_le fun _ h ↦ Lean.Order.le_sup (α := Pred F) ps h

@[simp] private theorem std_meet (P Q : OrderDual (UpperSet (ProverState F))) :
    Lean.Order.meet P Q = P ⊓ Q := by
  apply le_antisymm
  · exact le_inf (Lean.Order.meet_le_left P Q) (Lean.Order.meet_le_right P Q)
  · exact Lean.Order.le_meet (P ⊓ Q) P Q inf_le_left inf_le_right

@[simp] private theorem std_bot :
    Lean.Order.bot (α := OrderDual (UpperSet (ProverState F))) = (⊥ : Pred F) := by
  apply le_antisymm
  · exact Lean.Order.bot_le (⊥ : Pred F)
  · exact bot_le

private instance (P : OrderDual (UpperSet (ProverState F))) :
    Lean.Order.PreservesSup (Lean.Order.meet P) where
  map_sup ps := by
    apply ext
    intro s
    simp only [std_meet, std_sSup, inf_apply, sSup_apply]
    constructor
    · rintro ⟨hp, Q, hq, hqs⟩
      exact ⟨P ⊓ Q, ⟨Q, hq, rfl⟩, hp, hqs⟩
    · rintro ⟨_, ⟨Q, hq, rfl⟩, hp, hqs⟩
      exact ⟨hp, Q, hq, hqs⟩

end Pred

/-! ## The boxed interpretation

The bind law is the inequality required by `Std.WP.WPMonad`: the continuation must work
from every extension of an intermediate state.
-/

section Interpretation

variable {F c : Type}

/-- The constraint-checking transformer, with ordinary propositions at its boundary. -/
def raw [Zero F] [ConstraintHolds F c] (x : CircuitM F c α)
    (Q : α → ProverState F → Prop) (E : EvalError → ProverState F → Prop)
    (s : ProverState F) : Prop :=
  (proverWP.{0} x (fun a t ↦ .up (Q a t)) (fun e t ↦ .up (E e t)) s).down

theorem raw_mono [Zero F] [ConstraintHolds F c] {x : CircuitM F c α}
    {Q Q' : α → ProverState F → Prop} {E E' : EvalError → ProverState F → Prop}
    (hQ : ∀ a s, Q a s → Q' a s) (hE : ∀ e s, E e s → E' e s)
    {s} (h : raw x Q E s) : raw x Q' E' s := by
  induction x generalizing s with
  | pure a => exact hQ a s h
  | addConstraintOp con k ih => exact ⟨h.1, h.2.1, ih h.2.2⟩
  | existsOp n wit k ih =>
    unfold raw at h ⊢
    simp only [proverWP] at h ⊢
    cases hw : wit.run s.env with
    | error e => simp only [hw] at h; exact hE e s h
    | ok xs => simp only [hw] at h; exact ih _ h

private theorem raw_frame [Zero F] [ConstraintHolds F c] {x : CircuitM F c α}
    {Q : α → ProverState F → Prop} {E : EvalError → ProverState F → Prop}
    (R : Pred F) {s} (hr : R s) (h : raw x Q E s) :
    raw x (fun a t ↦ R t ∧ Q a t) E s := by
  induction x generalizing s with
  | pure a => exact ⟨hr, h⟩
  | addConstraintOp con k ih => exact ⟨h.1, h.2.1, ih hr h.2.2⟩
  | existsOp n wit k ih =>
    unfold raw at h ⊢
    simp only [proverWP] at h ⊢
    cases hw : wit.run s.env with
    | error e => simp only [hw] at h; exact h
    | ok xs =>
      simp only [hw] at h
      exact ih _ (R.mono (s.dom.le_extendList _) hr) h

/-- The greatest persistent assertion contained in the operational weakest precondition. -/
private def boxed [Zero F] [ConstraintHolds F c] (x : CircuitM F c α)
    (Q : α → Pred F) (E : EvalError → Pred F) : Pred F :=
  Pred.mk (fun s ↦ ∀ t, s ≤ t → raw x (fun a ↦ Q a) (fun e ↦ E e) t)
    (fun hst h u htu ↦ h u (hst.trans htu))

instance instStdWP [Zero F] [ConstraintHolds F c] :
    WP (CircuitM F (Prover c) α) α (Pred F) (EvalError → Pred F) where
  wpTrans x := ⟨boxed x⟩
  wp_trans_monotone _ := fun _ _ _ _ hE hQ _ h t ht ↦
    raw_mono hQ hE (h t ht)

private instance instStdWPMonad [Zero F] [ConstraintHolds F c] :
    WPMonad (CircuitM F (Prover c)) (Pred F) (EvalError → Pred F) where
  toWP _ := inferInstance
  pure_le_wp_pure a Q E := fun s h t ht ↦ (Q a).mono ht h
  bind_le_wp_bind x f Q E := by
    intro s h t ht
    change (proverWP (x >>= f) _ _ t).down
    rw [proverWP_bind]
    exact raw_mono (fun a u ha ↦ ha u le_rfl) (fun _ _ h ↦ h) (h t ht)

/-- Every assertion is framed by every program. -/
@[simp] private theorem frames [Zero F] [ConstraintHolds F c] (x : CircuitM F (Prover c) α)
    (R : Pred F) : WP.Frames (Lean.Order.meet (α := Pred F)) x R := by
  constructor
  intro Q E s h t ht
  rw [Pred.std_meet] at h
  change R s ∧ boxed x Q E s at h
  simp only [Pred.std_meet]
  exact raw_frame R (R.mono ht h.1) (h.2 t ht)

/-- Stable contracts have precisely the original meaning, including constraints and scope. -/
theorem triple_iff [Zero F] [ConstraintHolds F c]
    (x : CircuitM F (Prover c) α) (P : Pred F) (Q : α → Pred F)
    (E : EvalError → Pred F) :
    (⦃P⦄ x ⦃Q; E⦄) ↔ ∀ s, P s → raw x (fun a ↦ Q a) (fun e ↦ E e) s := by
  constructor
  · intro h s hp
    exact h.le_wp hp s le_rfl
  · intro h
    exact ⟨fun s hp t ht ↦ h t (P.mono ht hp)⟩

/-- A triple with impossible errors guarantees success and all emitted constraints at later
extensions. The scope obligation checked by `proverWP` makes each constraint's total
`Assignments.get` reading an assigned value, independent of its default for missing cells. -/
theorem adequate [Add F] [Mul F] [Zero F] [One F] [BasicSystem F c]
    [ConstraintHolds F c] [LawfulBasicSystem F c]
    {x : CircuitM F (Prover c) α} {P : Pred F} {Q : α → Pred F}
    (hx : ⦃P⦄ x ⦃Q⦄) {s : ProverState F} (hs : P s) :
    ∃ r t, prove x s.nv s.env = .ok (t.out r) ∧ s ≤ t ∧ Q r t ∧
      ∀ u, t ≤ u → ∀ con ∈ (build x s.nv).constraints,
        ConstraintHolds.Holds u.env.get con := by
  have h := (triple_iff x P Q _).mp hx s hs
  simp only [Lean.Order.bot_apply, Pred.std_bot] at h
  exact proverWP_prove h

end Interpretation

/-! ## Wire readings, advice and constraints

Each atom carries its preservation proof once. Gadget contracts use its mathematical
parameters without an entry state or a reading-transport premise.
-/

/-- A typed bundle's value, including its scope, as one persistent assertion. -/
def Reads [Add F] [Mul F] [Zero F] [CircuitType F val var]
    (r : var) (v : val) : Pred F :=
  Pred.mk (fun s ↦ CircuitType.ReadsAs s r v) (fun h hv ↦ hv.of_le h)

theorem Reads.prod_apply [Add F] [Mul F] [Zero F]
    [CircuitType F α vα] [CircuitType F β vβ] (r : vα × vβ) (v : α × β)
    (s : ProverState F) : Reads r v s ↔ Reads r.1 v.1 s ∧ Reads r.2 v.2 s := by
  change CircuitType.ReadsAs s r v ↔ CircuitType.ReadsAs s r.1 v.1 ∧
    CircuitType.ReadsAs s r.2 v.2
  simp only [CircuitType.ReadsAs, CircuitType.scoped_prod', CircuitType.reads_prod']
  tauto

theorem Reads.fvar_apply [Add F] [Mul F] [Zero F] (r : FVar F) (v : F)
    (s : ProverState F) : Reads r v s ↔ r.Scoped s ∧ r.val s.env.get = v := by
  change CircuitType.ReadsAs s r v ↔ _
  simp only [CircuitType.ReadsAs, CircuitType.scoped_fvar, CircuitType.reads_fvar]

theorem Reads.boolVar_apply [Add F] [Mul F] [Zero F] [One F] [DecidableEq F] [NeZero (1 : F)]
    (r : BoolVar F) (b : Bool) (s : ProverState F) :
    Reads r b s ↔ (↑r : CVar F).Scoped s ∧ (↑r : CVar F).val s.env.get = bit b := by
  change CircuitType.ReadsAs s r b ↔ _
  simp only [CircuitType.ReadsAs, CircuitType.scoped_boolVar, CircuitType.reads_boolVar]

theorem Reads.vector_apply [Add F] [Mul F] [Zero F] {n : Nat}
    (xs : Vector (FVar F) n) (v : Vector F n) (s : ProverState F) :
    Reads xs v s ↔ (∀ cv ∈ xs.toList, cv.Scoped s) ∧
      xs.toList.map (·.val s.env.get) = v.toList := by
  change CircuitType.ReadsAs s xs v ↔ _
  rw [CircuitType.ReadsAs, CircuitType.scoped_vector, CircuitType.reads_vector]
  simp only [CircuitType.scoped_fvar, CircuitType.reads_fvar]
  constructor
  · rintro ⟨hs, hr⟩
    refine ⟨?_, ?_⟩
    · intro cv hc
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hc
      exact hs i (by simpa using hi)
    · apply List.ext_getElem (by simp)
      intro i hi hi'
      simp only [List.getElem_map, Vector.getElem_toList]
      exact hr i (by simpa using hi')
  · rintro ⟨hs, hr⟩
    refine ⟨fun i hi ↦ hs _ (by simp), fun i hi ↦ ?_⟩
    have := congrArg (fun l ↦ l[i]?) hr
    simpa [hi] using this

private theorem advice_stable {F α : Type} (x : AsProver F α) {s t : ProverState F}
    (hst : s ≤ t) {a : α} (h : x.run s.env = .ok a) : x.run t.env = .ok a := by
  induction x with
  | pure b => exact h
  | fail e => cases h
  | read v k ih =>
    simp only [AsProver.run] at h ⊢
    cases hv : s.env v with
    | none => simp only [hv] at h; cases h
    | some b =>
      simp only [hv] at h
      rw [hst v b hv]
      exact ih b h

/-- Successful advice is persistent; failed advice need not be. -/
def Advice (x : AsProver F α) (a : α) : Pred F :=
  Pred.mk (fun s ↦ x.run s.env = .ok a) (fun h ha ↦ advice_stable x h ha)

@[simp] theorem Advice.apply (x : AsProver F α) (a : α) (s : ProverState F) :
    Advice x a s ↔ x.run s.env = .ok a := Iff.rfl

/-- The emitted constraint holds and all of its cells are in scope. -/
def Checked [Add F] [Mul F] [Zero F] [One F] [BasicSystem F c]
    [ConstraintHolds F c] [LawfulBasicSystem F c] (con : c) : Pred F :=
  Pred.mk (fun s ↦ ConstraintHolds.Holds s.env.get con ∧
      ∀ x ∈ ConstraintHolds.cells (F := F) con, x.Scoped s)
    (fun h hs ↦ ⟨ProverState.holds_of_le hs.2 h hs.1, fun x hx ↦ (hs.2 x hx).of_le h⟩)

theorem Checked.apply [Add F] [Mul F] [Zero F] [One F] [BasicSystem F c]
    [ConstraintHolds F c] [LawfulBasicSystem F c] (con : c) (s : ProverState F) :
    Checked con s ↔ ConstraintHolds.Holds s.env.get con ∧
      ∀ x ∈ ConstraintHolds.cells (F := F) con, x.Scoped s := Iff.rfl

theorem Checked.prover_eq [Add F] [Mul F] [Zero F] [One F] [BasicSystem F c]
    [ConstraintHolds F c] [LawfulBasicSystem F c] (con : c) :
    Checked (F := F) (c := Prover c) con = Checked (F := F) con := rfl

@[spec] theorem Spec.emit [Add F] [Mul F] [Zero F] [One F] [BasicSystem F c]
    [ConstraintHolds F c] [LawfulBasicSystem F c] (con : Prover c) :
    ⦃Checked con⦄ addConstraint (F := F) con ⦃fun _ ↦ ⊤⦄ := by
  rw [triple_iff]
  intro s hs
  exact ⟨hs.1, hs.2, trivial⟩

/-! ## The assertion discharger

`vcgen` leaves two kinds of obligation: that a program frames the current precondition, and an
entailment between assertions. The discharger closes the first by `frames`, drops the spent
contracts from the context, states the second at the goal only and closes it by assumption when
it is a pure frame condition; the caller's tactic receives the mathematical leaves. -/

open Lean Elab Tactic Meta in
/-- Clear the spent contracts: every hypothesis that is a (quantified) `Std.WP.Triple`. -/
elab (name := clearContracts) "clear_contracts" : tactic => do
  let g ← getMainGoal
  let spent ← g.withContext do
    let mut acc : Array FVarId := #[]
    for d in (← getLCtx) do
      if d.isImplementationDetail then continue
      let body := (← instantiateMVars d.type).getForallBody
      if body.getAppFn.isConstOf ``Std.WP.Triple then acc := acc.push d.fvarId
    return acc
  replaceMainGoal [← g.tryClearMany spent]

/-- Discharge a frame obligation, or state an entailment at the goal and close it by assumption
when it is a frame condition; the caller's tactic takes the mathematical leaves. -/
macro (name := proverAssertWith) "prover_assert" "with" ts:tacticSeq : tactic => `(tactic|
  (clear_contracts
   first
     | exact frames _ _
     | (simp only [Pred.std_le, Pred.std_meet, Pred.std_bot, Pred.le_iff, Pred.inf_apply,
          Pred.top_apply, Pred.bot_apply, Pred.iSup_apply, Pred.iInf_apply, Advice.apply,
          Lean.Order.le_pi_eq_forall, and_imp, implies_true, and_true, true_and]
        first | done | (intros; simp only [*]; done) | ($ts))))

/-- Close persistent assertion conditions by simplification and first-order reasoning. -/
@[tactic_alt proverAssertWith]
macro (name := proverAssert) "prover_assert" : tactic => `(tactic| prover_assert with grind)

end Snarky.Prover
