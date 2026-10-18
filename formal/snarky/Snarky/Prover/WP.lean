import Std.Tactic.Do
import Snarky.Prover
import Snarky.Witness

/-!
# The weakest-precondition interpretation of `prove`

The completeness reading of a circuit as a `Std.Do.WP` instance: the state is the prover state,
counter and table; a failing witness computation is the exception; and each emitted row is an
obligation at the state where it is emitted. The tag `Prover c` selects this reading, as
`Builder V c` selects the soundness reading, where rows are assumptions on a valuation.
-/

namespace Snarky

open Std.Do

set_option mvcgen.warning false

variable {F c : Type}

/-- The completeness tag: `c` read by the prover. A program enters the completeness reading as
`g (c := Prover c)`; instance search does not unfold `Prover`, so the tag gets its own `WP`
instance while the term stays a `CircuitM F c` program. -/
def Prover (c : Type) := c

instance [inst : ConstraintHolds F c] : ConstraintHolds F (Prover c) := inst

instance [inst : BasicSystem F c] : BasicSystem F (Prover c) := inst

instance [Add F] [Mul F] [Zero F] [One F] [BasicSystem F c] [ConstraintHolds F c]
    [inst : LawfulBasicSystem F c] : LawfulBasicSystem F (Prover c) := inst

/-- The prover's postcondition shape: the witness computations' errors, over the prover state. -/
abbrev ProverShape (F : Type) : PostShape := .except EvalError (.arg (ProverState F) .pure)

/-- The prover's predicate transformer, by recursion on the program: `pure` lands the result at
the current state; an emitted row is an obligation at the current table; a witness computation
that fails hands its error and the current state to the failure condition, and one that succeeds
continues at the state allocating its values, as `prove` does. -/
def proverWP [Zero F] [ConstraintHolds F c] {α : Type} :
    CircuitM F c α → (α → ProverState F → ULift Prop) →
      (EvalError → ProverState F → ULift Prop) → ProverState F → ULift Prop
  | .pure a, Q, _, st => Q a st
  | .addConstraintOp con k, Q, E, st =>
      .up (ConstraintHolds.Holds st.env.get con ∧ (proverWP k Q E st).down)
  | .existsOp n wit k, Q, E, st =>
      match wit.run st.env with
      | .error e => E e st
      | .ok xs => proverWP (k (allocRange st.nv n)) Q E (st.alloc xs)

/-- The transformer distributes over conjunction, pointwise in both conditions. -/
theorem proverWP_and [Zero F] [ConstraintHolds F c] {α : Type} (x : CircuitM F c α)
    (Q₁ Q₂ : α → ProverState F → ULift Prop) (E₁ E₂ : EvalError → ProverState F → ULift Prop)
    (st : ProverState F) :
    (proverWP x (fun a s => .up ((Q₁ a s).down ∧ (Q₂ a s).down))
        (fun e s => .up ((E₁ e s).down ∧ (E₂ e s).down)) st).down ↔
      (proverWP x Q₁ E₁ st).down ∧ (proverWP x Q₂ E₂ st).down := by
  induction x generalizing st with
  | pure a => exact Iff.rfl
  | addConstraintOp con k ih =>
    simp only [proverWP]
    constructor
    · intro h
      exact ⟨⟨h.1, ((ih st).mp h.2).1⟩, h.1, ((ih st).mp h.2).2⟩
    · intro h
      exact ⟨h.1.1, (ih st).mpr ⟨h.1.2, h.2.2⟩⟩
  | existsOp n wit k ih =>
    simp only [proverWP]
    rcases h : wit.run st.env with e | xs
    · exact Iff.rfl
    · exact ih _ _

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

/-- The completeness reading of `prove`: rows are obligations, failures are exceptions, the
prover state is the state. -/
instance Prover.instWP [Zero F] [ConstraintHolds F c] :
    WP (CircuitM F (Prover c)) (ProverShape F) where
  wp x := {
    trans := fun Q st => proverWP (c := Prover c) x Q.1 Q.2.1 st
    conjunctiveRaw := by
      intro Q₁ Q₂
      apply SPred.bientails.of_eq
      funext st
      show ULift.up (proverWP (c := Prover c) x (Q₁ ∧ₚ Q₂).1 (Q₁ ∧ₚ Q₂).2.1 st).down =
        ULift.up ((proverWP (c := Prover c) x Q₁.1 Q₁.2.1 st).down ∧
          (proverWP (c := Prover c) x Q₂.1 Q₂.2.1 st).down)
      exact congrArg ULift.up
        (propext (proverWP_and (c := Prover c) x Q₁.1 Q₂.1 Q₁.2.1 Q₂.2.1 st))
  }

/-- `wp` is a monad morphism: `pure` is the identity transformer and a sequence composes. -/
instance Prover.instWPMonad [Zero F] [ConstraintHolds F c] :
    WPMonad (CircuitM F (Prover c)) (ProverShape F) where
  wp_pure a := by
    ext Q st
    rfl
  wp_bind x f := by
    ext Q st
    simp only [PredTrans.apply_Bind_bind]
    exact Iff.of_eq (congrArg ULift.down (proverWP_bind (c := Prover c) x f Q.1 Q.2.1 st))

/-! ## The reading vocabulary

A cell's reading at a state is the total function `read`; a spec's values are all readings at
its one ghost, the entry state, so nothing is left for a caller to guess. Two lemmas carry a
cell's scope and reading across a run; they are what `grind` needs at a chain's conditions. -/

/-- A cell's reading at a state. -/
abbrev ProverState.read [Add F] [Mul F] [Zero F] (st : ProverState F) (x : CVar F) : F :=
  x.val st.env.get

/-- A cell in scope stays in scope. -/
theorem CVar.Scoped.of_le {st st' : ProverState F} (hle : st ≤ st') {x : CVar F}
    (hx : x.Scoped st) : x.Scoped st' :=
  hx.mono (ProverState.nv_le_of_le hle)

/-- A scoped cell reads the same at every later state. -/
theorem ProverState.read_of_le [Add F] [Mul F] [Zero F] {st st' : ProverState F}
    (hle : st ≤ st') {x : CVar F} (hx : x.Scoped st) : st'.read x = st.read x :=
  CVar.val_of_le hle hx

/-! ## Registration

A law is cited by hand; what `mvcgen` is given is its registered reading, a definition suffixed
`reg` that exists for the spec table and nowhere else. The reading wraps the postcondition:
`mvcgen` applies a spec by first unifying its postcondition with the goal's and only then
discharging the precondition, and a law's entry ghost is a plain metavariable there, so whenever
the last action's postcondition has the goal's shape the ghost is assigned the goal's entry and
the precondition's state equation is false. Wrapped, the two never unify, the post entailment is
always a condition, and the ghost is solved by the precondition. The primitive specs register
directly: their postconditions, a state equation and a witness clause, are shapes no law states. -/

/-- The wrapper on a registered postcondition, working around Lean's mvcgen (function mSpec in
module Lean.Elab.Tactic.Do.Spec, toolchain v4.30.0): the unification of a spec's postcondition
against the goal's, under full approximation, precedes the precondition's discharge and assigns
the entry ghost. The pattern-test sidecar outside the tree holds a negative control that fails
exactly while this is needed; when it passes on a toolchain, delete this, `Prover.register`, the
registered definitions, and `Prover.Reg.iff` from the grind calls. -/
@[irreducible] def Prover.Reg (p : Prop) : Prop := p

/-- The wrapper is transparent to a proof. -/
theorem Prover.Reg.iff {p : Prop} : Prover.Reg p ↔ p := by
  unfold Prover.Reg
  exact Iff.rfl

/-- The registered reading of a law. -/
theorem Prover.register [Zero F] [ConstraintHolds F c] {α : Type} {g : CircuitM F (Prover c) α}
    {pre : ProverState F → Prop} {post : ProverState F → α → ProverState F → Prop}
    (h : ∀ st₀, ⦃fun s => ⌜s = st₀ ∧ pre st₀⌝⦄ g ⦃⇓ r s' => ⌜post st₀ r s'⌝⦄)
    (st₀ : ProverState F) :
    ⦃fun s => ⌜s = st₀ ∧ pre st₀⌝⦄ g ⦃⇓ r s' => ⌜Prover.Reg (post st₀ r s')⌝⦄ := by
  intro s hs
  exact (wp g).mono _ _ ⟨fun r s' hp => Prover.Reg.iff.mpr hp, ExceptConds.entails_false⟩ s
    (h st₀ s hs)

/-! ## Primitive specs -/

/-- Emitting a row obliges it at the entry table; the state is unchanged. -/
@[spec] theorem Prover.addConstraint_spec [Zero F] [ConstraintHolds F c] (con : Prover c)
    (st₀ : ProverState F) :
    ⦃fun st => ⌜st = st₀ ∧ ConstraintHolds.Holds st₀.env.get con⌝⦄
    addConstraint (F := F) (c := Prover c) con
    ⦃⇓ _ st' => ⌜st' = st₀⌝⦄ := by
  rintro st ⟨rfl, h⟩
  show ConstraintHolds.Holds st.env.get con ∧ st = st
  exact ⟨h, rfl⟩

/-- Witnessing a field element: when the computation succeeds at the entry table, the fresh
cell is in scope and reads whatever the computation returned there, at a state extending the
entry. The value is the computation's, not a free variable, so the spec has one ghost. -/
@[spec] theorem Prover.witnessF_spec [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] (compute : AsProver F F) (st₀ : ProverState F) :
    ⦃fun st => ⌜st = st₀ ∧ ∃ v, compute.run st₀.env = .ok v⌝⦄
    witness (c := Prover c) (val := F) compute
    ⦃⇓ r st' => ⌜(∀ v, compute.run st₀.env = .ok v → r.Scoped st' ∧ st'.read r = v) ∧
      st₀ ≤ st'⌝⦄ := by
  rintro st ⟨rfl, v₀, h⟩
  show (proverWP (c := Prover c) (witness (c := Prover c) (val := F) compute) _ _ st).down
  simp only [Snarky.witness, proverWP, AsProver.map_eq, AsProver.run_bind, h, Except.bind,
    AsProver.run_pure, CheckedType.check]
  have hscope : CircuitType.Scoped (val := F) (st.alloc (CircuitType.valueToFields (F := F) v₀))
      (CircuitType.fieldsToVar (F := F) (val := F)
        (mapVec CVar.var (allocRange st.nv (CircuitType.size F F)))) := by
    intro cv hcv
    rw [CircuitType.var_roundTrip, toList_mapVec, List.mem_map] at hcv
    obtain ⟨w, hw, rfl⟩ := hcv
    exact show w < st.nv + CircuitType.size F F from (List.mem_range'_1.mp hw).2
  have hreads : CircuitType.Reads (st.alloc (CircuitType.valueToFields (F := F) v₀)).env.get
      (CircuitType.fieldsToVar (F := F) (val := F)
        (mapVec CVar.var (allocRange st.nv (CircuitType.size F F)))) v₀ := by
    unfold CircuitType.Reads
    rw [CircuitType.var_roundTrip]
    ext i hi
    simp only [getElem_mapVec, getElem_allocRange, CVar.val, ProverState.get_alloc]
    simp [Assignments.get, Assignments.extendList_get
      (show i < (CircuitType.valueToFields (F := F) v₀).toList.length by simpa using hi)]
  change (∀ v, Except.ok v₀ = Except.ok v →
      (CircuitType.fieldsToVar (F := F) (val := F)
        (mapVec CVar.var (allocRange st.nv (CircuitType.size F F)))).Scoped
          (st.alloc (CircuitType.valueToFields (F := F) v₀)) ∧
      (st.alloc (CircuitType.valueToFields (F := F) v₀)).read
        (CircuitType.fieldsToVar (F := F) (val := F)
          (mapVec CVar.var (allocRange st.nv (CircuitType.size F F)))) = v) ∧
    st ≤ st.alloc (CircuitType.valueToFields (F := F) v₀)
  refine ⟨fun v hv => ?_, st.dom.le_extendList _⟩
  cases Except.ok.inj hv
  exact ⟨CircuitType.scoped_fvar.mp hscope, CircuitType.reads_fvar.mp hreads⟩

/-! ## Traversal: the `Vector.mapM` law

A higher-order spec, proved once and generic in the per-element conditions: `P` at an element's
entry state, `Q` of its entry, result and exit, with the transports as hypotheses — the condition
carried forward to later entries, the fact re-read at the traversal's entry, the fact carried
through later entries, and the element advancing the state — each a grind line at a gadget's
instance. The law gives every element's condition at the traversal's entry and every result's
fact there, per index: the shape `grind` carries through later runs, where a `List.Forall₂`
conclusion is not, a lemma whose conclusion holds a lambda having no E-matching pattern, so the
list law behind the vector one is internal. The law is not registered, since its conditions
are not determined by the program; a gadget that is traversed derives its instance once, which
the program does determine, and registers that. -/

/-- The `List.mapM` law, the induction behind the vector law. -/
private theorem Prover.mapM_spec [Zero F] [ConstraintHolds F c] {α β : Type}
    (f : α → CircuitM F (Prover c) β)
    (P : ProverState F → α → Prop) (Q : ProverState F → α → β → ProverState F → Prop)
    (hP : ∀ st st' x, st ≤ st' → P st x → P st' x)
    (hQ : ∀ st st' x r s', st ≤ st' → P st x → Q st' x r s' → Q st x r s')
    (hQ' : ∀ st x r s' s'', s' ≤ s'' → Q st x r s' → Q st x r s'')
    (hle : ∀ st x r s', Q st x r s' → st ≤ s')
    (hf : ∀ st x, ⦃fun s => ⌜s = st ∧ P st x⌝⦄ f x ⦃⇓ r s' => ⌜Q st x r s'⌝⦄) :
    ∀ (xs : List α) (st₀ : ProverState F),
      ⦃fun s => ⌜s = st₀ ∧ ∀ x ∈ xs, P st₀ x⌝⦄
      xs.mapM f
      ⦃⇓ rs s' => ⌜List.Forall₂ (fun x r => Q st₀ x r s') xs rs ∧ st₀ ≤ s'⌝⦄
  | [], st₀ => by
    rw [List.mapM_nil]
    mvcgen
    rename_i s h
    exact ⟨.nil, le_of_eq h.1.symm⟩
  | x :: xs, st₀ => by
    rw [List.mapM_cons]
    have ih := Prover.mapM_spec f P Q hP hQ hQ' hle hf xs
    mvcgen [hf, ih]
    case pre =>
      rename_i s h
      obtain ⟨rfl, hmem⟩ := h
      exact ⟨trivial, hmem x (List.mem_cons_self ..)⟩
    case post.success.pre =>
      rename_i s h r s₁ hr
      obtain ⟨rfl, hmem⟩ := h
      exact ⟨trivial, fun y hy => hP _ _ y (hle _ _ _ _ hr) (hmem y (List.mem_cons_of_mem _ hy))⟩
    case post.success.post.success =>
      rename_i s h r s₁ hr rs s₂ hrs
      obtain ⟨rfl, hmem⟩ := h
      refine ⟨.cons (hQ' _ _ _ _ _ hrs.2 hr) ?_, (hle _ _ _ _ hr).trans hrs.2⟩
      exact ((List.forall₂_and_left xs rs).mpr
        ⟨fun y hy => hmem y (List.mem_cons_of_mem _ hy), hrs.1⟩).imp
          fun y r' ⟨hy, hq⟩ => hQ _ _ _ _ _ (hle _ _ _ _ hr) hy hq

/-- A specification of `f <$> m` is one of `m` read through `f`. -/
private theorem Prover.spec_of_map [Zero F] [ConstraintHolds F c] {α β : Type}
    (m : CircuitM F (Prover c) α) (f : α → β) {P : Assertion (ProverShape F)}
    {Q : PostCond β (ProverShape F)} (h : Triple (f <$> m) P Q) :
    Triple m P (fun a => Q.1 (f a), Q.2) := by
  intro s hs
  have hb := h s hs
  rw [CircuitM.map_eq] at hb
  change (proverWP (c := Prover c) (m >>= fun a => pure (f a)) Q.1 Q.2.1 s).down at hb
  rw [proverWP_bind] at hb
  exact hb

/-- The `Vector.mapM` law: the list law's postcondition read per index. -/
theorem Prover.vector_mapM_spec [Zero F] [ConstraintHolds F c] {α β : Type} {n : ℕ}
    (f : α → CircuitM F (Prover c) β)
    (P : ProverState F → α → Prop) (Q : ProverState F → α → β → ProverState F → Prop)
    (hP : ∀ st st' x, st ≤ st' → P st x → P st' x)
    (hQ : ∀ st st' x r s', st ≤ st' → P st x → Q st' x r s' → Q st x r s')
    (hQ' : ∀ st x r s' s'', s' ≤ s'' → Q st x r s' → Q st x r s'')
    (hle : ∀ st x r s', Q st x r s' → st ≤ s')
    (hf : ∀ st x, ⦃fun s => ⌜s = st ∧ P st x⌝⦄ f x ⦃⇓ r s' => ⌜Q st x r s'⌝⦄)
    (xs : Vector α n) (st₀ : ProverState F) :
    ⦃fun s => ⌜s = st₀ ∧ ∀ i : Fin n, P st₀ xs[i]⌝⦄
    xs.mapM f
    ⦃⇓ rs s' => ⌜(∀ i : Fin n, Q st₀ xs[i] rs[i] s') ∧ st₀ ≤ s'⌝⦄ := by
  have hl := Prover.mapM_spec f P Q hP hQ hQ' hle hf xs.toList st₀
  have heq : (fun rs : Vector β n => rs.toList) <$> xs.mapM f = xs.toList.mapM f := by
    rw [← Vector.toList_toArray, ← Array.toList_mapM, ← Vector.toArray_mapM, ← comp_map]
    rfl
  rw [← heq] at hl
  refine Triple.of_entails_wp (Triple.entails_wp_of_pre_post (Prover.spec_of_map _ _ hl) ?_ ?_)
  · rintro s ⟨rfl, hpre⟩
    refine ⟨rfl, fun x hx => ?_⟩
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
    simpa using hpre ⟨i, by simpa using hi⟩
  · refine ⟨fun rs s' ⟨h, hle'⟩ => ⟨fun i => ?_, hle'⟩, .rfl⟩
    have hg := (List.forall₂_iff_get.mp h).2 i (by simp) (by simp)
    simpa using hg

end Snarky
