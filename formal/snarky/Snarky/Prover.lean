import Mathlib.Data.List.Forall2
import Mathlib.Order.BoundedOrder.Monotone
import Snarky.Assignments
import Snarky.Encoding
import Snarky.Builder
import Snarky.WP

/-!
# The witness prover

Interpret a `CircuitM` tree by running the witness computations against the accumulating
assignment, in lockstep with `build`. Constraints are not consulted: the run fills the
table, and whether the table satisfies the built rows is the completeness reading's statement
(`Snarky.Prover.WP`).
-/

namespace Snarky

universe u v

variable {F c : Type u} {α : Type v}

/-- Run a witness computation against an assignment: a read of an assigned variable
continues with its value; a read of an unassigned variable, or a `fail`, ends the run. -/
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

/-- The prover's output: the result, the final counter and the final assignment — the
mirror of `Built`, with the witness table in place of the constraints. -/
structure Proved (F : Type u) (α : Type v) where
  /-- The computation's result value. -/
  result : α
  /-- The next-variable counter after the run, in lockstep with `Built.nextVar`. -/
  nextVar : Nat
  /-- The final assignment. -/
  assignments : Assignments F

/-- Interpret a circuit as a prover run: allocate variables in lockstep with `build` and
run the witness computations to fill the assignment, skipping constraints. Succeeds iff
every witness computation succeeds. -/
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

/-- Lockstep: a run's result and counter are the builder's. -/
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

/-- A prover state: the counter, the table, and the invariant that the table is defined
exactly below the counter. The invariant is a proof, so `ProverState.ext` compares only
counter and table. -/
@[ext] structure ProverState (F : Type u) where
  /-- The next-variable counter. -/
  nv : Nat
  /-- The witness table filled so far. -/
  env : Assignments F
  /-- The table is defined exactly below the counter. -/
  dom : env.Dom nv

namespace ProverState

/-- A run's output ending at this state with result `a`. -/
abbrev out (st : ProverState F) (a : α) : Proved F α := ⟨a, st.nv, st.env⟩

/-- `v ∈ st`: the variable is below the counter. -/
instance : Membership Variable (ProverState F) := ⟨fun st v => v < st.nv⟩

/-- The state after allocating `xs` at the counter. -/
def alloc (st : ProverState F) {n : Nat} (xs : Vector F n) : ProverState F :=
  ⟨st.nv + n, st.env.extendList st.nv xs.toList, by simpa using st.dom.extendList xs.toList⟩

/-- A variable in scope holds its reading. -/
private theorem get_eq [Zero F] (st : ProverState F) {v : Variable} (hv : v ∈ st) :
    st.env v = some (st.env.get v) :=
  st.dom.get_eq hv

/-- A variable in scope reads the same in any extension. -/
private theorem get_of_le [Zero F] {st st' : ProverState F} (hle : st.env.Le st'.env)
    {v : Variable} (hv : v ∈ st) : st'.env.get v = st.env.get v :=
  Assignments.get_of_le hle ((st.dom v).mpr hv)

/-- Reading an allocated state is reading the batch-extended table. -/
@[simp] theorem get_alloc [Zero F] (st : ProverState F) {n : Nat} (xs : Vector F n)
    (v : Variable) :
    (st.alloc xs).env.get v = (st.env.extendList st.nv xs.toList).get v := rfl

/-- Table growth: `st ≤ st'` when `st'`'s table extends `st`'s. The counter advances with it
(`nv_le_of_le`). -/
instance : Preorder (ProverState F) where
  le st st' := st.env.Le st'.env
  le_refl st := Assignments.Le.refl st.env
  le_trans _ _ _ := Assignments.Le.trans

/-- A larger state has an advanced counter: every slot defined below the old counter stays
defined, hence below the new one. -/
theorem nv_le_of_le {st st' : ProverState F} (hle : st ≤ st') : st.nv ≤ st'.nv := by
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

/-! The constant-folding constructors preserve scope. -/

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

/-- Scope survives any advance of the counter. -/
theorem CVar.Scoped.mono {st st' : ProverState F} (hnv : st.nv ≤ st'.nv) {x : CVar F}
    (h : x.Scoped st) : x.Scoped st' := by
  induction x with
  | var v => exact Nat.lt_of_lt_of_le h hnv
  | const k => trivial
  | add a b iha ihb => exact ⟨iha h.1, ihb h.2⟩
  | scale k y ih => exact ih h

/-- A scoped expression reads the same in any extension. -/
theorem CVar.val_of_le [Add F] [Mul F] [Zero F] {st st' : ProverState F}
    (hle : st ≤ st') {x : CVar F} (hx : x.Scoped st) :
    x.val st'.env.get = x.val st.env.get := by
  induction x with
  | var v => exact ProverState.get_of_le hle hx
  | const k => rfl
  | add a b iha ihb => simp only [CVar.val, iha hx.1, ihb hx.2]
  | scale k y ih => simp only [CVar.val, ih hx]

/-- `Except.bind` on `ok` applies the continuation. -/
@[simp] theorem except_bind_ok {ε α β : Type} (a : α) (f : α → Except ε β) :
    (Except.ok a).bind f = f a := rfl

/-- Reading a scoped expression succeeds with its total reading. -/
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

/-- A scoped bundle stays scoped as the counter advances. -/
theorem CircuitType.Scoped.mono [CircuitType F val var] {st st' : ProverState F}
    (hnv : st.nv ≤ st'.nv) {v : var} (h : CircuitType.Scoped (val := val) st v) :
    CircuitType.Scoped (val := val) st' v :=
  fun cv hcv => (h cv hcv).mono hnv

/-- The operand contract: the bundle's fields read as the encoding of `a`. Vacuous at
`FVar`, booleanity at `BoolVar`. Producers establish it; consumers assume it. -/
def CircuitType.Reads [Add F] [Mul F] [inst : CircuitType F val var]
    (V : Valuation F) (v : var) (a : val) : Prop :=
  mapVec (·.val V) (inst.varToFields v) = inst.valueToFields a

/-- Reading is an equation of encodings, decidable when equality of field elements is. -/
instance CircuitType.decidableReads [Add F] [Mul F] [DecidableEq F] [CircuitType F val var]
    (V : Valuation F) (v : var) (a : val) : Decidable (CircuitType.Reads V v a) :=
  inferInstanceAs (Decidable (_ = _))

/-- A value's constant bundle: its encoding as constant expressions. It reads as the
value at every valuation, which lets `CheckedType.Valid` split factor by factor. -/
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

/-- A bundle in scope and reading as this value. It survives table growth
(`CircuitType.monotone_readsAs`), so completeness proofs carry it between stages. -/
def CircuitType.ReadsAs [Add F] [Mul F] [Zero F] [CircuitType F val var]
    (st : ProverState F) (r : var) (v : val) : Prop :=
  CircuitType.Scoped (val := val) st r ∧ CircuitType.Reads st.env.get r v

/-- A scoped bundle's reading survives any extension of the table. -/
theorem CircuitType.Reads.of_le [Add F] [Mul F] [Zero F] [CircuitType F val var]
    {st st' : ProverState F} {r : var} {v : val}
    (h : CircuitType.Reads st.env.get r v) (hs : CircuitType.Scoped (val := val) st r)
    (hle : st ≤ st') : CircuitType.Reads st'.env.get r v := by
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

/-- The operand contract, split: a bundle reads as `a` iff it is well formed and
decodes to `a`. -/
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

/-- A bundle read survives the table's growth. -/
theorem CircuitType.monotone_readsAs [Add F] [Mul F] [Zero F] [CircuitType F val var]
    {v : var} {a : val} : Monotone fun st : ProverState F => CircuitType.ReadsAs st v a :=
  fun _ _ hle h =>
    ⟨CircuitType.Scoped.mono (ProverState.nv_le_of_le hle) h.1,
      CircuitType.Reads.of_le h.2 h.1 hle⟩

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

/-- `UnChecked` is invisible to scope. -/
@[simp] theorem CircuitType.scoped_unchecked [CircuitType F val var] {st : ProverState F}
    {v : var} : CircuitType.Scoped (val := UnChecked val) st ⟨v⟩ ↔
      CircuitType.Scoped (val := val) st v := Iff.rfl

/-- `UnChecked` is invisible to the reading. -/
@[simp] theorem CircuitType.reads_unchecked [Add F] [Mul F] [Zero F] [CircuitType F val var]
    {V : Valuation F} {v : var} {x : val} :
    CircuitType.Reads V (UnChecked.mk v) (UnChecked.mk x) ↔ CircuitType.Reads V v x := Iff.rfl

/-- An unchecked bundle is in scope when its payload is, in projection form: the shape of a
bundle a run returns, which `scoped_unchecked` states at the constructor. -/
theorem CircuitType.scoped_unchecked' [CircuitType F val var] {st : ProverState F}
    {u : UnChecked var} :
    CircuitType.Scoped (val := UnChecked val) st u ↔ CircuitType.Scoped (val := val) st u.val :=
  Iff.rfl

/-- An unchecked bundle reads as its payload, in projection form. -/
theorem CircuitType.reads_unchecked' [Add F] [Mul F] [Zero F] [CircuitType F val var]
    {V : Valuation F} {u : UnChecked var} {x : UnChecked val} :
    CircuitType.Reads V u x ↔ CircuitType.Reads V u.val x.val := Iff.rfl

/-! The readings, at the formers. -/

section Formers

variable {a va b vb : Type}

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

/-- A pair bundle is in scope when its components are, in projection form: the shape of a
bundle a run returns, which `scoped_prod` states at the constructor. -/
theorem CircuitType.scoped_prod' [CircuitType F a va] [CircuitType F b vb]
    {st : ProverState F} {p : va × vb} :
    CircuitType.Scoped (val := a × b) st p ↔
      CircuitType.Scoped (val := a) st p.1 ∧ CircuitType.Scoped (val := b) st p.2 := by
  obtain ⟨v, w⟩ := p
  exact CircuitType.scoped_prod

/-- A pair bundle reads componentwise, in projection form. -/
theorem CircuitType.reads_prod' [Add F] [Mul F] [Zero F] [CircuitType F a va]
    [CircuitType F b vb] {V : Valuation F} {p : va × vb} {q : a × b} :
    CircuitType.Reads V p q ↔ CircuitType.Reads V p.1 q.1 ∧ CircuitType.Reads V p.2 q.2 := by
  obtain ⟨v, w⟩ := p
  obtain ⟨x, y⟩ := q
  exact CircuitType.reads_prod

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

/-- A vector of bundles reads as a vector of values iff their lists read entrywise. -/
theorem CircuitType.reads_vector_iff_forall₂ [Add F] [Mul F] [Zero F] [CircuitType F a va]
    {n : Nat} {V : Valuation F} {vs : Vector va n} {xs : Vector a n} :
    CircuitType.Reads V vs xs ↔ List.Forall₂ (CircuitType.Reads V) vs.toList xs.toList := by
  rw [reads_vector, List.forall₂_iff_get]
  simp

/-- A vector of bundles reads as some vector of values when each entry reads as some value. -/
theorem CircuitType.exists_reads_vector [Add F] [Mul F] [Zero F] [CircuitType F a va] {n : Nat}
    {V : Valuation F} {vs : Vector va n}
    (h : ∀ (i : Nat) (hi : i < n), ∃ x : a, CircuitType.Reads V vs[i] x) :
    ∃ xs : Vector a n, CircuitType.Reads V vs xs :=
  ⟨Vector.ofFn fun i => (h i i.isLt).choose,
    reads_vector.mpr fun i hi => by simpa using (h i hi).choose_spec⟩

theorem CircuitType.scoped_ofEquiv [inst : CircuitType F a va] (ev : b ≃ a) (ew : vb ≃ va)
    {st : ProverState F} {v : vb} :
    @CircuitType.Scoped F b vb (CircuitType.ofEquiv ev ew) st v ↔
      CircuitType.Scoped (val := a) st (ew v) := Iff.rfl

theorem CircuitType.reads_ofEquiv [Add F] [Mul F] [Zero F] [inst : CircuitType F a va]
    (ev : b ≃ a) (ew : vb ≃ va) {V : Valuation F} {v : vb} {x : b} :
    @CircuitType.Reads F b vb _ _ (CircuitType.ofEquiv ev ew) V v x ↔
      CircuitType.Reads V (ew v) (ev x) := Iff.rfl

end Formers

end Bundles

/-! ## The reading, from soundness -/

section Simulation

open Std.Do

variable {F c : Type} {α : Type}

/-- A program, read at the soundness tag. -/
abbrev atBuilder (V : Valuation F) (g : CircuitM F c α) : CircuitM F (Builder V c) α := g

end Simulation

end Snarky
