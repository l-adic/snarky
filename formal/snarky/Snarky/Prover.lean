import Mathlib.Data.List.Forall2
import Snarky.Assignments
import Snarky.Encoding
import Snarky.Builder
import Snarky.WP

/-!
# The witness prover

Interpret a `CircuitM` tree by running the witness computations against the accumulating
assignment, in lockstep with `build`. Constraints are not consulted: the run fills the
table, and whether the table satisfies the built rows is a separate statement (`Sat`).
-/

namespace Snarky

universe u v

variable {F c : Type u} {α : Type v}

/-- Run a witness computation against an assignment (PS `runAsProver`, minus `Effect`):
a read of an assigned variable continues with its value; one of an unassigned
variable, or a `fail`, ends the run. -/
def AsProver.run {α : Type u} : AsProver F α → Assignments F → Except EvalError α
  | .pure a, _ => .ok a
  | .read v k, env =>
    match env v with
    | some x => (k x).run env
    | none => .error (.unassigned v)
  | .fail e, _ => .error e

namespace AsProver

variable {α β : Type u}

@[simp] theorem run_pure (a : α) (env : Assignments F) :
    (AsProver.pure a : AsProver F α).run env = .ok a := rfl

@[simp] theorem run_read (v : Variable) (k : F → AsProver F α) (env : Assignments F) :
    (AsProver.read v k).run env = match env v with
      | some x => (k x).run env
      | none => .error (.unassigned v) := by
  rcases h : env v with _ | x <;> simp [run, h]

@[simp] theorem run_bind (x : AsProver F α) (f : α → AsProver F β) (env : Assignments F) :
    (AsProver.bind x f).run env = (x.run env).bind fun a => (f a).run env := by
  induction x with
  | pure a => rfl
  | read v k ih =>
    simp only [AsProver.bind, run]
    cases env v with
    | none => rfl
    | some x => exact ih x
  | fail e => rfl

end AsProver

/-- The prover's output: the computation's result, the final next-variable counter, and
the final assignment — the mirror of `Built`, with the witness table where the builder
has the constraints. -/
structure Proved (F : Type u) (α : Type v) where
  /-- The computation's result value. -/
  result : α
  /-- The next-variable counter after the run — in lockstep with `Built.nextVar`. -/
  nextVar : Nat
  /-- The final assignment: every variable the run allocated, mapped to its witness value. -/
  assignments : Assignments F

/-- Interpret a circuit as a prover run: allocate variables in lockstep with `build` and
run witness computations to fill the assignment. Constraints are passed over — judging
the table is not the prover's job. Succeeds iff every witness computation succeeds. -/
def prove : CircuitM F c α → Nat → Assignments F → Except EvalError (Proved F α)
  | .pure a, nv, env => .ok ⟨a, nv, env⟩
  | .addConstraintOp _ k, nv, env => prove k nv env
  | .existsOp n wit k, nv, env =>
    match wit.run env with
    | .error e => .error e
    | .ok xs => prove (k (allocRange nv n)) (nv + n) (env.extendList nv xs.toList)

/-! ## The interpreter's equations -/

@[simp] theorem prove_pure (a : α) (nv : Nat) (env : Assignments F) :
    prove (pure a : CircuitM F c α) nv env = .ok ⟨a, nv, env⟩ :=
  rfl

@[simp] theorem prove_addConstraint (con : c) (nv : Nat) (env : Assignments F) :
    prove (addConstraint con) nv env = .ok ⟨PUnit.unit, nv, env⟩ :=
  rfl

@[simp] theorem prove_pure' (a : α) (nv : Nat) (env : Assignments F) :
    prove (CircuitM.pure a : CircuitM F c α) nv env = .ok ⟨a, nv, env⟩ :=
  rfl

/-- Proving a sequence is proving the head, then the tail from its final state. -/
@[simp] theorem prove_bind {β : Type v} (m : CircuitM F c α)
    (f : α → CircuitM F c β) (nv : Nat) (env : Assignments F) :
    prove (m >>= f) nv env =
      (prove m nv env).bind
        fun out => prove (f out.result) out.nextVar out.assignments := by
  show prove (CircuitM.bind m f) nv env = _
  induction m generalizing nv env with
  | pure a => rfl
  | addConstraintOp con k ih => exact ih ..
  | existsOp n wit k ih =>
    simp only [CircuitM.bind, prove]
    split
    · rfl
    · exact ih ..

/-! ## Interpreter laws -/

/-- A run keeps the table's domain at its counter. -/
private theorem prove_dom {m : CircuitM F c α} {nv : Nat}
    {env : Assignments F} {o : Proved F α} (hd : env.Dom nv)
    (h : prove m nv env = .ok o) : o.assignments.Dom o.nextVar := by
  induction m generalizing nv env with
  | pure a =>
    simp only [prove, Except.ok.injEq] at h
    subst h
    exact hd
  | addConstraintOp con k ih =>
    simp only [prove] at h
    exact ih hd h
  | existsOp n wit k ih =>
    simp only [prove] at h
    split at h
    · cases h
    · next xs _ => exact ih _ (by simpa using hd.extendList xs.toList) h

/-- A run only extends the table. -/
private theorem prove_le {m : CircuitM F c α} {nv : Nat}
    {env : Assignments F} {o : Proved F α} (hd : env.Dom nv)
    (h : prove m nv env = .ok o) : env.Le o.assignments := by
  induction m generalizing nv env with
  | pure a =>
    simp only [prove, Except.ok.injEq] at h
    subst h
    exact Assignments.Le.refl _
  | addConstraintOp con k ih =>
    simp only [prove] at h
    exact ih hd h
  | existsOp n wit k ih =>
    simp only [prove] at h
    split at h
    · cases h
    · next xs _ =>
      exact (hd.le_extendList _).trans (ih _ (by simpa using hd.extendList xs.toList) h)

/-- The counter only advances. -/
private theorem prove_nv_le {m : CircuitM F c α}
    {nv : Nat} {env : Assignments F} {o : Proved F α} (h : prove m nv env = .ok o) :
    nv ≤ o.nextVar := by
  induction m generalizing nv env with
  | pure a =>
    simp only [prove, Except.ok.injEq] at h
    subst h
    exact Nat.le_refl _
  | addConstraintOp con k ih =>
    simp only [prove] at h
    exact ih h
  | existsOp n wit k ih =>
    simp only [prove] at h
    split at h
    · cases h
    · exact Nat.le_trans (Nat.le_add_right nv n) (ih _ h)

/-- Lockstep: a run's result and counter are the builder's. Public because the
whole-circuit layer reads a solve's result off the compiled system. -/
theorem prove_build_agrees {m : CircuitM F c α}
    {nv : Nat} {env : Assignments F} {o : Proved F α} (h : prove m nv env = .ok o) :
    o.result = (build m nv).result ∧ o.nextVar = (build m nv).nextVar := by
  induction m generalizing nv env with
  | pure a =>
    simp only [prove, Except.ok.injEq] at h
    subst h
    exact ⟨rfl, rfl⟩
  | addConstraintOp con k ih =>
    simp only [prove] at h
    simp only [build]
    exact ih h
  | existsOp n wit k ih =>
    simp only [prove] at h
    simp only [build]
    split at h
    · cases h
    · exact ih _ h

/-! ## The prover state -/

/-- A prover state: the allocation counter, the table, and the invariant relating them —
the table is defined exactly below the counter. Two states with the same counter and
table are equal (`ProverState.ext`): the invariant is not data. -/
@[ext] structure ProverState (F : Type u) where
  /-- The next-variable counter. -/
  nv : Nat
  /-- The witness table filled so far. -/
  env : Assignments F
  /-- The table is defined exactly below the counter — carried, never re-proved. -/
  dom : env.Dom nv

namespace ProverState

/-- What a run returns, read off a state: the result, and the state's counter and
table. -/
abbrev out (st : ProverState F) (a : α) : Proved F α := ⟨a, st.nv, st.env⟩

/-- `v ∈ st`: the variable is in scope — allocated by this state or one before it. -/
instance : Membership Variable (ProverState F) := ⟨fun st v => v < st.nv⟩

/-- The state after allocating `xs` at the counter: the one way a run makes a new state. -/
def alloc (st : ProverState F) {n : Nat} (xs : Vector F n) : ProverState F :=
  ⟨st.nv + n, st.env.extendList st.nv xs.toList, by simpa using st.dom.extendList xs.toList⟩

/-- A variable in scope holds its reading. -/
private theorem get_eq [Zero F] (st : ProverState F) {v : Variable} (hv : v ∈ st) :
    st.env v = some (st.env.get v) :=
  st.dom.get_eq hv

/-- Allocation only grows the table. -/
theorem le_alloc (st : ProverState F) {n : Nat} (xs : Vector F n) :
    st.env.Le (st.alloc xs).env :=
  st.dom.le_extendList _

/-- A variable in scope reads the same in any extension. -/
private theorem get_of_le [Zero F] {st st' : ProverState F} (hle : st.env.Le st'.env)
    {v : Variable} (hv : v ∈ st) : st'.env.get v = st.env.get v :=
  Assignments.get_of_le hle ((st.dom v).mpr hv)

/-- Reading an allocated state is reading the batch-extended table. -/
@[simp] theorem get_alloc [Zero F] (st : ProverState F) {n : Nat} (xs : Vector F n)
    (v : Variable) :
    (st.alloc xs).env.get v = (st.env.extendList st.nv xs.toList).get v := rfl

/-- Preserving every assignment forces the counter along: each table is defined exactly
below its own counter, so a slot live at the smaller frontier is live — hence below the
counter — in the extension. What lets a fact quantified over `env.Le` extensions alone
still transport counter-indexed structure. -/
theorem nv_le_of_env_le {st st' : ProverState F} (hle : st.env.Le st'.env) :
    st.nv ≤ st'.nv := by
  rcases Nat.lt_or_ge st'.nv st.nv with h | h
  · obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp ((st.dom st'.nv).mpr h)
    exact absurd ((st'.dom st'.nv).mp (Option.isSome_iff_exists.mpr ⟨x, hle _ _ hx⟩))
      (Nat.lt_irrefl _)
  · exact h

end ProverState

/-! ## Scope -/

/-- `x.Scoped st`: every variable of the expression is in scope. -/
def CVar.Scoped (st : ProverState F) (x : CVar F) : Prop := x.ScopedBy (· ∈ st)

@[simp] theorem CVar.scoped_var (st : ProverState F) (v : Variable) :
    (CVar.var v : CVar F).Scoped st ↔ v ∈ st := Iff.rfl

@[simp] theorem CVar.scoped_const (st : ProverState F) (k : F) :
    (CVar.const k).Scoped st := trivial

@[simp] theorem CVar.scoped_add (st : ProverState F) (a b : CVar F) :
    (CVar.add a b).Scoped st ↔ a.Scoped st ∧ b.Scoped st := Iff.rfl

@[simp] theorem CVar.scoped_scale (st : ProverState F) (k : F) (y : CVar F) :
    (CVar.scale k y).Scoped st ↔ y.Scoped st := Iff.rfl

/-- The folds are scope-preserving. -/

@[simp] theorem CVar.Scoped.add_ {st : ProverState F} [Add F] {a b : CVar F} (ha : a.Scoped st)
    (hb : b.Scoped st) : (CVar.add_ a b).Scoped st :=
  CVar.ScopedBy.add_ ha hb

@[simp] theorem CVar.Scoped.scale_ {st : ProverState F} [Zero F] [One F] [DecidableEq F] {k : F}
    {x : CVar F} (hx : x.Scoped st) : (CVar.scale_ k x).Scoped st :=
  CVar.ScopedBy.scale_ hx

@[simp] theorem CVar.Scoped.sub_ {st : ProverState F} [Add F] [Sub F] [Zero F] [One F] [Neg F]
    [DecidableEq F] {a b : CVar F} (ha : a.Scoped st) (hb : b.Scoped st) :
    (CVar.sub_ a b).Scoped st :=
  CVar.ScopedBy.sub_ ha hb

/-- Scope survives any run: the counter only advances. -/
theorem CVar.Scoped.mono {st st' : ProverState F} (hnv : st.nv ≤ st'.nv) {x : CVar F}
    (h : x.Scoped st) : x.Scoped st' := by
  induction x with
  | var v => exact Nat.lt_of_lt_of_le h hnv
  | const k => trivial
  | add a b iha ihb => exact ⟨iha h.1, ihb h.2⟩
  | scale k y ih => exact ih h

/-- A scoped expression reads the same in any extension. -/
theorem CVar.val_of_le [Add F] [Mul F] [Zero F] {st st' : ProverState F}
    (hle : st.env.Le st'.env) {x : CVar F} (hx : x.Scoped st) :
    x.val st'.env.get = x.val st.env.get := by
  induction x with
  | var v => exact ProverState.get_of_le hle hx
  | const k => rfl
  | add a b iha ihb => simp only [CVar.val, iha hx.1, ihb hx.2]
  | scale k y ih => simp only [CVar.val, ih hx]

/-- The equations `Except.bind` computes by. -/
@[simp] theorem except_bind_ok {ε α β : Type} (a : α) (f : α → Except ε β) :
    (Except.ok a).bind f = f a := rfl

/-- A scoped expression reads as its total reading. -/
@[simp] theorem AsProver.readCVar_run [Add F] [Mul F] [Zero F] {st : ProverState F} {x : CVar F}
    (hx : x.Scoped st) : (AsProver.readCVar x).run st.env = .ok (x.val st.env.get) := by
  induction x with
  | var v => simp [AsProver.readCVar, st.get_eq hx, CVar.val]
  | const k => rfl
  | add a b iha ihb => simp [AsProver.readCVar, iha hx.1, ihb hx.2, CVar.val, Except.bind]
  | scale k y ih => simp [AsProver.readCVar, ih hx, CVar.val, Except.bind]

/-! ## Typed bundles, read against the table -/

section Bundles

variable {F val var : Type}

/-- Every field of the bundle is in scope. -/
def CircuitType.Scoped [CircuitType F val var] (st : ProverState F) (v : var) : Prop :=
  ∀ cv ∈ (CircuitType.varToFields (val := val) v).toList, cv.Scoped st

/-- A scoped bundle stays scoped as the table grows. -/
theorem CircuitType.Scoped.mono [CircuitType F val var] {st st' : ProverState F}
    (hnv : st.nv ≤ st'.nv) {v : var} (h : CircuitType.Scoped (val := val) st v) :
    CircuitType.Scoped (val := val) st' v :=
  fun cv hcv => (h cv hcv).mono hnv

/-- The bundle's fields read as the encoding of `a` on the table — the operand
contract: vacuous information at `FVar` (every field element encodes), booleanity at
`BoolVar`. Producers establish it; consumers assume it. -/
def CircuitType.Reads [Add F] [Mul F] [inst : CircuitType F val var]
    (V : Valuation F) (v : var) (a : val) : Prop :=
  mapVec (·.val V) (inst.varToFields v) = inst.valueToFields a

/-- A value's constant bundle: its encoding, materialized as constant expressions. Every
value has one, and it reads as that value at every table — which is what makes
admissibility (`CheckedType.Valid`) readable off a former factor by factor. -/
def CircuitType.constVar [inst : CircuitType F val var] (a : val) : var :=
  inst.fieldsToVar (mapVec CVar.const (inst.valueToFields a))

/-- The constant bundle reads as its value. -/
theorem CircuitType.reads_constVar [Add F] [Mul F] [inst : CircuitType F val var]
    (V : Valuation F) (a : val) :
    CircuitType.Reads V (CircuitType.constVar (F := F) (var := var) a) a := by
  unfold CircuitType.Reads CircuitType.constVar
  rw [inst.var_roundTrip]
  ext i hi
  simp only [getElem_mapVec]
  rfl

/-- A bundle read: in scope, and reading as this value. The two travel as one — at any
later table the same bundle reads the same value — which is what a multi-stage
completeness proof carries from stage to stage. -/
def CircuitType.ReadsAs [Add F] [Mul F] [Zero F] [CircuitType F val var]
    (st : ProverState F) (r : var) (v : val) : Prop :=
  CircuitType.Scoped (val := val) st r ∧ CircuitType.Reads st.env.get r v

/-- A scoped bundle's reading survives any extension of the table. -/
theorem CircuitType.Reads.of_le [Add F] [Mul F] [Zero F] [CircuitType F val var]
    {st st' : ProverState F} {r : var} {v : val}
    (h : CircuitType.Reads st.env.get r v) (hs : CircuitType.Scoped (val := val) st r)
    (hle : st.env.Le st'.env) : CircuitType.Reads st'.env.get r v := by
  unfold CircuitType.Reads at h ⊢
  rw [← h]
  ext i hi
  simp only [getElem_mapVec]
  exact CVar.val_of_le hle (hs _ (by simp))

/-- The bundle's reading under the table's total reading. -/
def CircuitType.readVal [Add F] [Mul F] [inst : CircuitType F val var]
    (V : Valuation F) (v : var) : val :=
  inst.fieldsToValue (mapVec (·.val V) (inst.varToFields v))

/-- The bundle's readings lie in the encoding's image. -/
def CircuitType.WellFormed [Add F] [Mul F] [CircuitType F val var]
    (V : Valuation F) (v : var) : Prop :=
  ∃ a, CircuitType.Reads (val := val) V v a

/-- The operand contract, split: an encoding-faithful reading is a well-formed bundle
whose decoded value is the value read. -/
theorem CircuitType.reads_iff [Add F] [Mul F] [Zero F] [inst : CircuitType F val var]
    {V : Valuation F} {v : var} {a : val} :
    CircuitType.Reads V v a ↔
      CircuitType.WellFormed (val := val) V v ∧ CircuitType.readVal V v = a := by
  have hval : ∀ {a' : val}, CircuitType.Reads (val := val) V v a' →
      CircuitType.readVal (val := val) V v = a' := by
    intro a' h
    unfold CircuitType.readVal
    rw [h, inst.value_roundTrip]
  constructor
  · intro h
    exact ⟨⟨a, h⟩, hval h⟩
  · rintro ⟨⟨a', h'⟩, hv⟩
    rw [← hv, hval h']
    exact h'

/-- A read survives the table's growth: scope carries the value with it. -/
theorem CircuitType.ReadsAs.mono [Add F] [Mul F] [Zero F] [CircuitType F val var]
    {st st' : ProverState F} {r : var} {v : val} (hnv : st.nv ≤ st'.nv)
    (hle : st.env.Le st'.env) (h : CircuitType.ReadsAs st r v) :
    CircuitType.ReadsAs st' r v :=
  ⟨CircuitType.Scoped.mono hnv h.1, CircuitType.Reads.of_le h.2 h.1 hle⟩

@[simp] theorem CircuitType.scoped_fvar {st : ProverState F} {x : FVar F} :
    CircuitType.Scoped (val := F) st x ↔ x.Scoped st := by
  show (∀ cv ∈ [x], cv.Scoped st) ↔ x.Scoped st
  simp

@[simp] theorem CircuitType.readVal_fvar [Add F] [Mul F] [Zero F] (V : Valuation F)
    (x : FVar F) : CircuitType.readVal (val := F) V x = x.val V := rfl


/-- A field bundle reads as its expression's reading. -/
@[simp] theorem CircuitType.reads_fvar [Add F] [Mul F] [Zero F] {V : Valuation F}
    {x : FVar F} {a : F} : CircuitType.Reads V x a ↔ x.val V = a := by
  constructor
  · intro h
    exact congrArg (fun v : Vector F (CircuitType.size F F) =>
      v[0]'(show 0 < CircuitType.size F F from Nat.one_pos)) h
  · intro h
    show (#v[x.val V] : Vector F 1) = #v[a]
    rw [h]

/-- A boolean bundle is in scope when its variable is. -/
@[simp] theorem CircuitType.scoped_boolVar [Add F] [Mul F] [Zero F] [One F] [DecidableEq F]
    [NeZero (1 : F)] {st : ProverState F} {b : BoolVar F} :
    CircuitType.Scoped (val := Bool) st b ↔ (↑b : CVar F).Scoped st := by
  show (∀ cv ∈ [(↑b : CVar F)], cv.Scoped st) ↔ _
  simp

/-- A boolean bundle reads as a bit. -/
@[simp] theorem CircuitType.reads_boolVar [Add F] [Mul F] [Zero F] [One F] [DecidableEq F]
    [NeZero (1 : F)]
    {V : Valuation F} {b : BoolVar F} {bb : Bool} :
    CircuitType.Reads V b bb ↔ (↑b : CVar F).val V = bit bb := by
  constructor
  · intro h
    exact congrArg (fun v : Vector F (CircuitType.size F Bool) =>
      v[0]'(show 0 < CircuitType.size F Bool from Nat.one_pos)) h
  · intro h
    show (#v[(↑b : CVar F).val V] : Vector F 1) = #v[bit bb]
    rw [h]

/-- The wrapper is invisible to scope. -/
@[simp] theorem CircuitType.scoped_unchecked [CircuitType F val var] {st : ProverState F}
    {v : var} : CircuitType.Scoped (val := UnChecked val) st ⟨v⟩ ↔
      CircuitType.Scoped (val := val) st v := Iff.rfl

/-- The wrapper is invisible to the reading. -/
@[simp] theorem CircuitType.reads_unchecked [Add F] [Mul F] [Zero F] [CircuitType F val var]
    {V : Valuation F} {v : var} {x : val} :
    CircuitType.Reads V (UnChecked.mk v) (UnChecked.mk x) ↔ CircuitType.Reads V v x := Iff.rfl

/-! The readings, at the formers. -/

section Formers

variable {a va b vb : Type}

@[simp] theorem CircuitType.scoped_unit {st : ProverState F} :
    CircuitType.Scoped (val := Unit) st () := by
  simp [CircuitType.Scoped]

theorem CircuitType.reads_unit [Add F] [Mul F] {V : Valuation F} :
    CircuitType.Reads V () () := rfl

@[simp] theorem CircuitType.scoped_prod [CircuitType F a va] [CircuitType F b vb]
    {st : ProverState F} {v : va} {w : vb} :
    CircuitType.Scoped (val := a × b) st (v, w) ↔
      CircuitType.Scoped (val := a) st v ∧ CircuitType.Scoped (val := b) st w := by
  simp [CircuitType.Scoped, or_imp, forall_and]

@[simp] theorem CircuitType.reads_prod [Add F] [Mul F] [Zero F] [CircuitType F a va]
    [CircuitType F b vb] {V : Valuation F} {v : va} {w : vb} {x : a} {y : b} :
    CircuitType.Reads V (v, w) (x, y) ↔ CircuitType.Reads V v x ∧ CircuitType.Reads V w y := by
  simp [CircuitType.Reads, mapVec_append, append_inj_iff]

@[simp] theorem CircuitType.readVal_prod [Add F] [Mul F] [Zero F] [CircuitType F a va]
    [CircuitType F b vb] {V : Valuation F} {v : va} {w : vb} :
    CircuitType.readVal (val := a × b) V (v, w)
      = (CircuitType.readVal (val := a) V v, CircuitType.readVal (val := b) V w) := by
  simp [CircuitType.readVal, mapVec_append]

theorem CircuitType.scoped_vector [CircuitType F a va] {n : Nat} {st : ProverState F}
    {vs : Vector va n} :
    CircuitType.Scoped (val := Vector a n) st vs ↔
      ∀ (i : Nat) (hi : i < n), CircuitType.Scoped (val := a) st vs[i] := by
  simp only [CircuitType.Scoped, CircuitType.varToFields_vector, mapVec_eq_map]
  constructor
  · intro h i hi cv hcv
    exact h cv (by
      rw [Vector.mem_toList_iff, Vector.mem_flatten]
      exact ⟨_, Vector.mem_map.mpr ⟨vs[i], Vector.getElem_mem hi, rfl⟩,
        Vector.mem_toList_iff.mp hcv⟩)
  · intro h cv hcv
    rw [Vector.mem_toList_iff, Vector.mem_flatten] at hcv
    obtain ⟨xs, hxs, hcv⟩ := hcv
    obtain ⟨v, hv, rfl⟩ := Vector.mem_map.mp hxs
    obtain ⟨i, hi, rfl⟩ := Vector.mem_iff_getElem.mp hv
    exact h i hi cv (Vector.mem_toList_iff.mpr hcv)

theorem CircuitType.reads_vector [Add F] [Mul F] [Zero F] [CircuitType F a va] {n : Nat}
    {V : Valuation F} {vs : Vector va n} {xs : Vector a n} :
    CircuitType.Reads V vs xs ↔
      ∀ (i : Nat) (hi : i < n), CircuitType.Reads V vs[i] xs[i] := by
  simp only [CircuitType.Reads, CircuitType.varToFields_vector, CircuitType.valueToFields_vector,
    mapVec_eq_map, Vector.map_flatten]
  rw [← Vector.eq_iff_flatten_eq]
  simp only [Vector.ext_iff, Vector.getElem_map]

theorem CircuitType.readVal_vector [Add F] [Mul F] [Zero F] [CircuitType F a va] {n : Nat}
    {V : Valuation F} {vs : Vector va n} :
    CircuitType.readVal (val := Vector a n) V vs
      = mapVec (fun v => CircuitType.readVal (val := a) V v) vs := by
  simp only [CircuitType.readVal, CircuitType.varToFields_vector, CircuitType.fieldsToValue_vector,
    mapVec_eq_map, Vector.map_flatten, chunkVec_flatten, Vector.map_map]
  rfl

theorem CircuitType.scoped_ofEquiv [inst : CircuitType F a va] (ev : b ≃ a) (ew : vb ≃ va)
    {st : ProverState F} {v : vb} :
    @CircuitType.Scoped F b vb (CircuitType.ofEquiv ev ew) st v ↔
      CircuitType.Scoped (val := a) st (ew v) := Iff.rfl

theorem CircuitType.reads_ofEquiv [Add F] [Mul F] [Zero F] [inst : CircuitType F a va]
    (ev : b ≃ a) (ew : vb ≃ va) {V : Valuation F} {v : vb} {x : b} :
    @CircuitType.Reads F b vb _ _ (CircuitType.ofEquiv ev ew) V v x ↔
      CircuitType.Reads V (ew v) (ev x) := Iff.rfl

theorem CircuitType.readVal_ofEquiv [Add F] [Mul F] [Zero F] [inst : CircuitType F a va]
    (ev : b ≃ a) (ew : vb ≃ va) {V : Valuation F} {v : vb} :
    @CircuitType.readVal F b vb _ _ (CircuitType.ofEquiv ev ew) V v
      = ev.symm (CircuitType.readVal V (ew v)) := rfl

end Formers

end Bundles

/-! ## The graph -/

/-- The prover's graph: from `st`, `g` runs to the result `a` at `st'`. -/
private def Runs (g : CircuitM F c α) (st : ProverState F) (a : α)
    (st' : ProverState F) : Prop :=
  prove g st.nv st.env = .ok (st'.out a)

/-- Every run only extends the table. -/
private theorem Runs.le {g : CircuitM F c α} {st st' : ProverState F} {a : α}
    (h : Runs g st a st') : st.env.Le st'.env :=
  prove_le st.dom h

/-- Every run only advances the counter. -/
private theorem Runs.nv_le {g : CircuitM F c α} {st st' : ProverState F} {a : α}
    (h : Runs g st a st') : st.nv ≤ st'.nv :=
  prove_nv_le h

/-- Runs compose: the sequence runs through the head's final state. -/
private theorem Runs.bind {β : Type v} {g : CircuitM F c α} {k : α → CircuitM F c β}
    {st st₁ st₂ : ProverState F} {a : α} {b : β}
    (h₁ : Runs g st a st₁) (h₂ : Runs (k a) st₁ b st₂) :
    Runs (g >>= k) st b st₂ := by
  rw [Runs, prove_bind, show prove g st.nv st.env = .ok (st₁.out a) from h₁]
  exact h₂

section CompleteDef

variable {F c : Type} {α : Type v}

/-- The rows the builder emits from the run's initial counter, satisfied at the total
reading of the run's final table — the half of completeness the run itself does not
judge. -/
private def Sat [Zero F] [ConstraintHolds F c] (g : CircuitM F c α) (st st' : ProverState F) :
    Prop :=
  ∀ con ∈ (build g st.nv).constraints, ConstraintHolds.Holds st'.env.get con

/-- The completeness statement: from every state satisfying `pre`, the run succeeds, the
rows it built are satisfied at every extension of its final table — the quantifier is
monotonicity collected where it is provable, at the concrete rows — and its result and
final state satisfy `post`. -/
def Complete [Zero F] [ConstraintHolds F c] (pre : ProverState F → Prop)
    (g : CircuitM F c α) (post : α → ProverState F → Prop) : Prop :=
  ∀ st, pre st → ∃ a st', Runs g st a st' ∧
    (∀ {stf : ProverState F}, st'.nv ≤ stf.nv → st'.env.Le stf.env → Sat g st stf) ∧
    post a st'

/-- Rows of a sequence are satisfied when the head's and — in lockstep through the
head's run — the tail's are. -/
private theorem Sat.bind [Zero F] [ConstraintHolds F c] {β : Type v} {g : CircuitM F c α}
    {k : α → CircuitM F c β} {st st₁ stf : ProverState F} {a : α}
    (hrun : Runs g st a st₁) (h₁ : Sat g st stf) (h₂ : Sat (k a) st₁ stf) :
    Sat (g >>= k) st stf := by
  intro con hcon
  have hres : a = (build g st.nv).result := (prove_build_agrees hrun).1
  have hnv : st₁.nv = (build g st.nv).nextVar := (prove_build_agrees hrun).2
  simp only [build_bind] at hcon
  rw [← hres, ← hnv] at hcon
  rcases List.mem_append.mp hcon with h | h
  · exact h₁ con h
  · exact h₂ con h

/-- The two order facts of a completeness law's run component — the counter and the
table only grow — for the seam proofs that destructure `Complete` directly and cannot
name the run's own projections. -/
theorem run_le {g : CircuitM F c α} {st st' : ProverState F} {a : α}
    (h : Runs g st a st') : st.nv ≤ st'.nv ∧ st.env.Le st'.env :=
  ⟨h.nv_le, h.le⟩

/-- `addConstraint` is passive at the prover: no allocation, no failure. -/
private theorem Runs.addConstraint {con : c} {st : ProverState F} :
    Runs (Snarky.addConstraint con) st PUnit.unit st := rfl

/-- `pure` emits no rows. -/
private theorem Sat.pure [Zero F] [ConstraintHolds F c] {a : α} {st stf : ProverState F} :
    Sat (pure a : CircuitM F c α) st stf := by
  intro con hcon
  simp [build] at hcon

/-- A state predicate that survives the table's growth. The ambient context of a
multi-stage completeness proof is one of these, built up conjunct by conjunct. -/
def Mono (P : ProverState F → Prop) : Prop :=
  ∀ st st' : ProverState F, st.nv ≤ st'.nv → st.env.Le st'.env → P st → P st'

/-- Conjunction of monotone facts is monotone — how a context accumulates. -/
theorem Mono.and [Zero F] {P Q : ProverState F → Prop} (hP : Mono (F := F) P)
    (hQ : Mono (F := F) Q) : Mono (F := F) fun st => P st ∧ Q st :=
  fun _ _ hnv hle h => ⟨hP _ _ hnv hle h.1, hQ _ _ hnv hle h.2⟩

/-- A reading is monotone. -/
theorem Mono.readsAs [Add F] [Mul F] [Zero F] {val var : Type} [CircuitType F val var]
    {v : var} {a : val} : Mono (F := F) fun st => CircuitType.ReadsAs st v a :=
  fun _ _ hnv hle h => h.mono hnv hle

/-- A `Forall₂` of readings is monotone, entrywise. -/
theorem Mono.forall₂ [Add F] [Mul F] [Zero F] {val var : Type} [CircuitType F val var]
    {xs : List var} {vs : List val} :
    Mono (F := F) fun st => List.Forall₂ (CircuitType.ReadsAs st) xs vs :=
  fun _ _ hnv hle h => h.imp fun _ _ hr => hr.mono hnv hle

/-- Sequencing: the tail runs from what the head established. The monadic bind, with no
side condition — the head's post IS the tail's pre, and it is stated at the head's own
final state, so nothing has to cross the run. -/
theorem Complete.bind [Zero F] [ConstraintHolds F c] {β : Type v}
    {pre : ProverState F → Prop} {g : CircuitM F c α} {mid : α → ProverState F → Prop}
    {k : α → CircuitM F c β} {post : β → ProverState F → Prop}
    (hg : Complete pre g mid) (hk : ∀ a, Complete (mid a) (k a) post) :
    Complete pre (g >>= k) post := by
  intro st hpre₀
  obtain ⟨a, st₁, hrun₁, hsat₁, hmid⟩ := hg st hpre₀
  obtain ⟨b, st₂, hrun₂, hsat₂, hpost⟩ := hk a st₁ hmid
  exact ⟨b, st₂, hrun₁.bind hrun₂, fun hnv hle =>
    Sat.bind hrun₁ (hsat₁ (Nat.le_trans hrun₂.nv_le hnv) (hrun₂.le.trans hle))
      (hsat₂ hnv hle), hpost⟩

/-- A precondition nothing satisfies is complete for any program — what a branch the
precondition rules out is discharged by. -/
theorem Complete.of_false [Zero F] [ConstraintHolds F c] {pre : ProverState F → Prop}
    {g : CircuitM F c α} {post : α → ProverState F → Prop} (h : ∀ st, ¬ pre st) :
    Complete pre g post := fun st hst => absurd hst (h st)

/-- A precondition that determines a parameter: if every state satisfying it fixes some
`i`, and the program is complete from each `P i`, it is complete from the precondition.
The dual of `of_false` — that one handles a precondition no state satisfies, this one a
precondition whose states carry a value the law is indexed by. -/
theorem Complete.instantiate [Zero F] [ConstraintHolds F c] {ι : Type}
    {pre : ProverState F → Prop} {P : ι → ProverState F → Prop} {g : CircuitM F c α}
    {post : α → ProverState F → Prop} (h : ∀ st, pre st → ∃ i, P i st)
    (hg : ∀ i, Complete (P i) g post) : Complete pre g post :=
  fun st hst => let ⟨i, hi⟩ := h st hst; hg i st hi

/-- A cell in scope stays in scope. -/
theorem Mono.scoped [Zero F] {x : CVar F} : Mono (F := F) fun st => x.Scoped st :=
  fun _ _ hnv _ h => h.mono hnv

/-- The frame rule: a monotone fact the program does not disturb crosses it. This is the
only rule that needs monotonicity — sequencing itself does not. -/
theorem Complete.frame [Zero F] [ConstraintHolds F c] {pre R : ProverState F → Prop}
    {g : CircuitM F c α} {post : α → ProverState F → Prop}
    (hR : Mono (F := F) R) (h : Complete pre g post) :
    Complete (fun st => pre st ∧ R st) g fun a st' => post a st' ∧ R st' := by
  rintro st ⟨hpre, hr⟩
  obtain ⟨a, st₁, hrun, hsat, hp⟩ := h st hpre
  exact ⟨a, st₁, hrun, hsat, hp, hR _ _ hrun.nv_le hrun.le hr⟩

/-- The rule of consequence: strengthen the precondition, weaken the postcondition. -/
theorem Complete.imp [Zero F] [ConstraintHolds F c] {pre pre' : ProverState F → Prop}
    {g : CircuitM F c α} {post post' : α → ProverState F → Prop}
    (hpre : ∀ st, pre' st → pre st) (hpost : ∀ a st, post a st → post' a st)
    (h : Complete pre g post) : Complete pre' g post' := by
  intro st hst
  obtain ⟨a, st₁, hrun, hsat, hp⟩ := h st (hpre st hst)
  exact ⟨a, st₁, hrun, hsat, hpost a st₁ hp⟩

/-- Sequencing that keeps what it had. The tail runs from everything the head established
AND everything the head's own precondition already guaranteed — so a multi-stage proof
never names its context: the context IS the precondition, and it accumulates one conjunct
per stage. The monotone hypothesis is what lets the precondition cross the head's run. -/
theorem Complete.seq [Zero F] [ConstraintHolds F c] {β : Type v}
    {pre : ProverState F → Prop} {g : CircuitM F c α} {mid : α → ProverState F → Prop}
    {k : α → CircuitM F c β} {post : β → ProverState F → Prop}
    (hpre : Mono (F := F) pre) (hg : Complete pre g mid)
    (hk : ∀ a, Complete (fun st => pre st ∧ mid a st) (k a) post) :
    Complete pre (g >>= k) post :=
  Complete.bind
    (Complete.imp (fun _ h => ⟨h, h⟩) (fun _ _ h => ⟨h.2, h.1⟩)
      (Complete.frame hpre hg))
    hk

/-- `pure` at a postcondition the entry state already satisfies — the tail of a `bind`
chain, where the value is in hand and nothing more is emitted. -/
theorem Complete.pure_of [Zero F] [ConstraintHolds F c] {pre : ProverState F → Prop}
    {a : α} {post : α → ProverState F → Prop} (h : ∀ st, pre st → post a st) :
    Complete pre (pure a : CircuitM F c α) post :=
  fun st hst => ⟨a, st, rfl, fun _ _ => Sat.pure, h st hst⟩

/-- A program that emits no rows and allocates nothing is complete from every state. -/
theorem Complete.pure [Zero F] [ConstraintHolds F c] {pre : ProverState F → Prop} {a : α} :
    Complete pre (pure a : CircuitM F c α) fun _ _ => True :=
  fun st _ => ⟨a, st, rfl, fun _ _ => Sat.pure, trivial⟩

/-- `addConstraint`'s one row is satisfied exactly by its identity — the row obligation
is the caller's contribution. -/
private theorem Sat.addConstraint [Zero F] [ConstraintHolds F c] {con : c} {st stf : ProverState F}
    (h : ConstraintHolds.Holds stf.env.get con) : Sat (Snarky.addConstraint con) st stf := by
  intro c' hc'
  simp [Snarky.addConstraint, build] at hc'
  subst hc'
  exact h

/-- One emitted row: the prover allocates nothing and cannot fail, so the state is
unchanged and the precondition survives. The row's obligation is the caller's, and it is
owed at every extension of the table — which is what `Sat`'s quantifier asks for. -/
theorem Complete.addConstraint [Zero F] [ConstraintHolds F c] {pre : ProverState F → Prop}
    {con : c} (h : ∀ st, pre st → ∀ stf : ProverState F, st.env.Le stf.env →
      ConstraintHolds.Holds stf.env.get con) :
    Complete pre (Snarky.addConstraint (F := F) con) fun _ st => pre st :=
  fun st hst => ⟨PUnit.unit, st, Runs.addConstraint,
    fun _ hle => Sat.addConstraint (h st hst _ hle), hst⟩

end CompleteDef

/-! ## The reading, from soundness -/

section Simulation

open Std.Do

variable {F c : Type} {α : Type}

/-- A program, read at the soundness tag. -/
abbrev atBuilder (V : Valuation F) (g : CircuitM F c α) : CircuitM F (Builder V c) α := g

/-- A soundness law at every valuation, read at the table a run built and satisfied, is
a fact about the run's result. What lets a completeness law state its result's reading
without re-deriving it: the value comes from the operation's own spec. -/
theorem runs_post [Zero F] [ConstraintHolds F c]
    {g : CircuitM F c α} {post : Valuation F → α → Prop}
    (hspec : ∀ V : Valuation F, ⦃⌜True⌝⦄ atBuilder V g ⦃⇓ r _ => ⌜post V r⌝⦄)
    {st st' : ProverState F} {a : α} (h : Runs g st a st') (hsat : Sat g st st') :
    post st'.env.get a := by
  have hb := (builder_spec_iff (atBuilder st'.env.get g) (post st'.env.get)).mp (hspec _) st.nv
  have hres : (build (atBuilder st'.env.get g) st.nv).result = a :=
    (prove_build_agrees h).1.symm
  rw [hres] at hb
  exact hb fun con hcon => hsat con hcon

/-- A completeness law's post, strengthened by the gadget's soundness law read at the
final table — the reading recovered, not restated. -/
theorem Complete.post [Zero F] [ConstraintHolds F c]
    {pre : ProverState F → Prop} {g : CircuitM F c α} {Q : α → ProverState F → Prop}
    {post : Valuation F → α → Prop}
    (hspec : ∀ V : Valuation F, ⦃⌜True⌝⦄ atBuilder V g ⦃⇓ r _ => ⌜post V r⌝⦄)
    (hc : Complete pre g Q) :
    Complete pre g fun a st' => Q a st' ∧ post st'.env.get a :=
  fun st hpre =>
    let ⟨a, st', h, hsat, hq⟩ := hc st hpre
    ⟨a, st', h, hsat, hq,
      runs_post hspec h (hsat (Nat.le_refl _) (Assignments.Le.refl _))⟩

end Simulation

end Snarky
