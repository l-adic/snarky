import Snarky.Backend.Builder

/-!
# The witness prover

Port of `Snarky.Backend.Prover` (packages/snarky/src/Snarky/Backend/Prover.purs,
`runCircuitProver`/`proverOps`): interpret a `CircuitM` tree by *running* the witness
computations against the accumulating assignment. As with the builder, the PS mutable
`ProverState` becomes explicit arguments and results, mirroring `build` so the
interpreter-agreement laws below read (and prove) symmetrically. Written with
explicit `match` (not `do`) so those proofs can `split` on every intermediate result.

## The semantic strengthening: constraints are always checked

The PS PRODUCTION prover does not check constraints at all — "they're assumed validated
during compilation" (module header); `SolveCircuit (Basic f)`'s `proverConstraint` is a
no-op outside debug mode, and validity is the proof system's concern. `prove` instead
checks every constraint at emission time with `holds`, unconditionally: it is PS's
DEBUG-mode semantics (minus message rendering) made total. That is what gives
`prove_complete` below its content: a successful run is a satisfiability certificate
for the built system, not just a witness table.

Consequence, shared with PS debug mode (whose `debugCheck` also fails on unassigned
variables): a constraint may only be emitted once its variables are witnessed —
"witness before constrain". Not a restriction the PRODUCTION PS prover has (it checks
nothing); lifting it (deferring checks to the end of the run) is a design change to
take up only if a ported circuit hits it.

## Further dispositions

- The constraint check is a pure parameter `holds : c → Assignments F → Bool`, not the
  PS `SolveCircuit` class. Note the class is more than a checker: `proverConstraint`
  is a STATE TRANSFORM — backends like kimchi allocate and assign intermediates while
  reducing constraints at prove time. `holds` covers the checking fragment; the reducing
  fragment is the un-ported backend seam.
- Assignment is guarded (`Assignments.extendPairs`): re-assigning is an error, so prover
  runs are monotone in `Assignments.Le` (`prove_assignments_le`) — enforcing what PS
  `allocAssignments`/`Assignments.set` promise by write-once contract.
- `debug`, `labelStack`, `contextualize`, and `runWitness`'s error-wrapping are the
  error-attribution machinery; they follow the inert `labelOp`. The advice handler
  threading in `runWitness` is the dropped advice row (`Circuit/DSL/Monad`).

The public surface is the port surface — `Proved` and `prove` — plus `ProverState` (the
invariant-carrying state the triple layer runs over) and the prover-side interpreter
laws, which live beside their subject: monotonicity (`prove_assignments_le`,
`prove_nextVar_le`), freshness preservation (`prove_freshFrom`, packaged as
`ProverState.freshOut`), builder/prover agreement (`prove_build_agrees`), completeness
(`prove_complete` — a successful run satisfies every built constraint, given a `holds`
monotone in the extension order), and the composition/plumbing lemmas (`prove_bind`,
`prove_witnessCore`). No PS QuickCheck property targets the prover alone; the suite
exercises it through solve round trips, and these laws are Lean-only — the reason the
deep embedding exists.
-/

namespace Snarky

variable {F c : Type u}

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

/-- Interpret a circuit as a prover run: allocate variables in lockstep with `build`, run
witness computations to fill the assignment, and check every added constraint with
`holds`. Succeeds with the result, the final counter, and the final assignment iff every
witness computation succeeds, no variable is assigned twice, and every constraint holds
when added. -/
def prove (holds : c → Assignments F → Bool) :
    CircuitM F c α → Nat → Assignments F → Except EvalError (Proved F α)
  | .pure a, nv, env => .ok ⟨a, nv, env⟩
  | .addConstraintOp con k, nv, env =>
    if holds con env then prove holds k nv env
    else .error .unsatisfiedConstraint
  | .existsOp n wit k, nv, env =>
    match wit.run env with
    | .error e => .error e
    | .ok xs =>
      match env.extendPairs ((allocRange nv n).toList.zip xs.toList) with
      | .error e => .error e
      | .ok env' => prove holds (k (allocRange nv n)) (nv + n) env'
  | .assignOp vs wit k, nv, env =>
    match vs.toList.find? (nv ≤ ·) with
    | some v => .error (.conflict v)
    | none =>
      match wit.run env with
      | .error e => .error e
      | .ok xs =>
        match env.extendPairs (vs.toList.zip xs.toList) with
        | .error e => .error e
        | .ok env' => prove holds k nv env'
  | .labelOp _ k, nv, env => prove holds k nv env

/-- Proving a `pure` is immediate: the result passes through and the state is
untouched. -/
@[circuitVal] theorem prove_pure (holds : c → Assignments F → Bool) (a : α) (nv : Nat)
    (env : Assignments F) :
    prove holds (pure a : CircuitM F c α) nv env = .ok ⟨a, nv, env⟩ := rfl

/-- Proving a sequence is proving the head, then the tail from its final state. The
intermediate state is fresh whenever the initial one is, by `prove_freshFrom` below. -/
theorem prove_bind (holds : c → Assignments F → Bool) (m : CircuitM F c α)
    (f : α → CircuitM F c β) (nv : Nat) (env : Assignments F) :
    prove holds (m >>= f) nv env =
      (prove holds m nv env).bind
        fun out => prove holds (f out.result) out.nextVar out.assignments := by
  show prove holds (CircuitM.bind m f) nv env = _
  induction m generalizing nv env with
  | pure a => rfl
  | addConstraintOp con k ih =>
    simp only [CircuitM.bind, prove]
    split
    · exact ih ..
    · rfl
  | existsOp n wit k ih =>
    simp only [CircuitM.bind, prove]
    split
    · rfl
    · split
      · rfl
      · exact ih ..
  | assignOp vs wit k ih =>
    simp only [CircuitM.bind, prove]
    split
    · rfl
    · split
      · rfl
      · split
        · rfl
        · exact ih ..
  | labelOp s k ih => exact ih ..

/-- The honest run of the one-variable core shape — `witness` a field value, pin it with
one constraint, return it: the run succeeds and assigns the witnessed value at `nv`,
whenever the witness computation succeeds and the constraint accepts the result. -/
theorem prove_witnessCore {holds : c → Assignments F → Bool} {w : AsProver F F}
    {mk : CVar F → c} {nv : Nat} {env : Assignments F} {v : F}
    (hw : w.run env = .ok v) (hfresh : env.FreshFrom nv)
    (hch : holds (mk (.var nv)) (env.extend nv v) = true) :
    prove holds (do
        let z ← witness (val := F) w
        addConstraint (mk z)
        pure z) nv env
      = .ok ⟨.var nv, nv + 1, env.extend nv v⟩ := by
  have hnv : env nv = none := hfresh nv (Nat.le_refl nv)
  have hwit : (CircuitType.valueToFields (F := F) (val := F) <$> w).run env
      = .ok ⟨#[v], rfl⟩ := by
    simp only [AsProver.map_eq, AsProver.run_bind, hw, Except.bind]
    rfl
  have hext : env.extendPairs
      ((allocRange nv 1).toList.zip (⟨#[v], rfl⟩ : Vector F 1).toList)
      = .ok (env.extend nv v) := by
    show env.extendPairs [(nv, v)] = .ok _
    simp [Assignments.extendPairs, hnv]
  show prove holds (.existsOp 1 (_ <$> w) _) nv env = _
  simp only [prove, hwit, hext]
  show prove holds (.addConstraintOp (mk (.var nv)) (.pure (CVar.var nv))) (nv + 1)
    (env.extend nv v) = _
  simp only [prove, hch, if_true]

/-! ## Prover runs only extend the assignment -/

/-- A successful prover run never re-assigns a variable, so its final assignment extends
its initial one. -/
theorem prove_assignments_le {holds : c → Assignments F → Bool} {m : CircuitM F c α}
    {nv nv' : Nat} {env env' : Assignments F} {x : α}
    (h : prove holds m nv env = .ok ⟨x, nv', env'⟩) : env.Le env' := by
  induction m generalizing nv nv' env env' x with
  | pure a =>
    simp only [prove, Except.ok.injEq, Proved.mk.injEq] at h
    obtain ⟨-, -, rfl⟩ := h
    exact Assignments.Le.refl _
  | addConstraintOp con k ih =>
    simp only [prove] at h
    split at h
    · exact ih h
    · cases h
  | existsOp n wit k ih =>
    simp only [prove] at h
    split at h
    · cases h
    · split at h
      · cases h
      · next hext => exact (Assignments.le_extendPairs hext).trans (ih _ h)
  | assignOp vs wit k ih =>
    simp only [prove] at h
    split at h
    · cases h
    · split at h
      · cases h
      · split at h
        · cases h
        · next hext => exact (Assignments.le_extendPairs hext).trans (ih h)
  | labelOp str k ih =>
    simp only [prove] at h
    exact ih h

/-- The counter only advances. Allocation moves it forward and nothing moves it
back — what places a run's allocations strictly above every slot preallocated before
it. -/
theorem prove_nextVar_le {holds : c → Assignments F → Bool} {m : CircuitM F c α}
    {nv nv' : Nat} {env env' : Assignments F} {x : α}
    (h : prove holds m nv env = .ok ⟨x, nv', env'⟩) : nv ≤ nv' := by
  induction m generalizing nv env with
  | pure a =>
    simp only [prove, Except.ok.injEq, Proved.mk.injEq] at h
    omega
  | addConstraintOp con k ih =>
    simp only [prove] at h
    split at h
    · exact ih h
    · cases h
  | existsOp n wit k ih =>
    simp only [prove] at h
    split at h
    · cases h
    · split at h
      · cases h
      · exact Nat.le_trans (Nat.le_add_right nv n) (ih _ h)
  | assignOp vs wit k ih =>
    simp only [prove] at h
    split at h
    · cases h
    · split at h
      · cases h
      · split at h
        · cases h
        · exact ih h
  | labelOp s k ih => exact ih h

/-- Freshness is preserved by every prover run. A run that starts with nothing
assigned at or above its counter ends the same way: allocation writes exactly at the
counter and advances past it, and `assignOp` — guarded above — cannot reach the fresh
region. The invariant `ProverState` below carries. -/
theorem prove_freshFrom {holds : c → Assignments F → Bool} {m : CircuitM F c α}
    {nv nv' : Nat} {env env' : Assignments F} {x : α}
    (hfresh : env.FreshFrom nv) (h : prove holds m nv env = .ok ⟨x, nv', env'⟩) :
    env'.FreshFrom nv' := by
  induction m generalizing nv env with
  | pure a =>
    simp only [prove, Except.ok.injEq, Proved.mk.injEq] at h
    obtain ⟨-, hnv, henv⟩ := h
    exact hnv ▸ henv ▸ hfresh
  | addConstraintOp con k ih =>
    simp only [prove] at h
    split at h
    · exact ih hfresh h
    · cases h
  | existsOp n wit k ih =>
    simp only [prove] at h
    split at h
    · cases h
    · split at h
      · cases h
      · next hext =>
        refine ih _ (fun v hv => ?_) h
        refine Assignments.extendPairs_none hext (fun p hp hpv => ?_)
          (hfresh v (by omega))
        obtain ⟨hmem, -⟩ := List.of_mem_zip hp
        exact absurd (hpv ▸ (mem_allocRange hmem).2) (by omega)
  | assignOp vs wit k ih =>
    simp only [prove] at h
    split at h
    · cases h
    · next hfind =>
      split at h
      · cases h
      · split at h
        · cases h
        · next hext =>
          refine ih (fun v hv => ?_) h
          refine Assignments.extendPairs_none hext (fun p hp hpv => ?_) (hfresh v hv)
          obtain ⟨hmem, -⟩ := List.of_mem_zip hp
          have hlt := List.find?_eq_none.mp hfind p.1 hmem
          simp only [decide_eq_true_eq] at hlt
          exact absurd (hpv ▸ hv) hlt
  | labelOp s k ih => exact ih hfresh h

/-! ## The prover state, invariant-carrying

PS keeps the counter and the store in ONE mutable object whose only mutator is
allocation, so "nothing at or above the counter is assigned" holds by construction and
cannot even be violated. The pure rendering above splits them into two independent
arguments, which lets a caller form a pair PS cannot represent — so the invariant has
to live somewhere. Here it lives in the type: a `ProverState` cannot be built without
it, and `prove_freshFrom` supplies it for every successor state, so the statements
downstream never mention freshness again. -/

/-- A prover state: the allocation counter, the table, and the invariant relating
them. Two states with the same counter and table are equal (`ProverState.ext`): the
invariant is not data. -/
@[ext] structure ProverState (F : Type u) where
  /-- The next-variable counter. -/
  nv : Nat
  /-- The witness table filled so far. -/
  env : Assignments F
  /-- Nothing at or above the counter is assigned — carried, never re-proved. -/
  fresh : env.FreshFrom nv

/-- A successful run from an invariant-carrying state leaves an invariant-carrying
state. -/
theorem ProverState.freshOut {holds : c → Assignments F → Bool} {m : CircuitM F c α}
    {st : ProverState F} {out : Proved F α}
    (h : prove holds m st.nv st.env = .ok out) :
    out.assignments.FreshFrom out.nextVar :=
  prove_freshFrom st.fresh h

/-! ## Scope

What a completeness law assumes about a variable is that it is *in scope*: `v ∈ st`.
Scope is assignment — the slot has a value — not a bound on the counter: the seam
(`compileBody`) reserves the public output slots below the counter and fills them
after the body has run, so "below the counter" would let a law read a hole. In scope
means readable, and the reading is total: `st.env.toValuation v`. The laws below are
everything a proof uses of scope — it survives extension (`mem_of_le`), an allocation
puts its slots in scope and disturbs no other (`mem_extendMany_iff`), and a reading is
stable across both (`get_of_le`, `get_extendMany_of_mem`). That names are numbers and
the counter bounds them appears only inside these proofs. -/

/-- `v ∈ st`: the variable is in scope — it has a value. -/
instance : Membership Variable (ProverState F) := ⟨fun st v => (st.env v).isSome⟩

theorem ProverState.mem_def {st : ProverState F} {v : Variable} :
    v ∈ st ↔ (st.env v).isSome := Iff.rfl

/-- An assigned variable is in scope. -/
theorem ProverState.mem_of_assigned {st : ProverState F} {v : Variable} {x : F}
    (hv : st.env v = some x) : v ∈ st := by
  rw [ProverState.mem_def, hv]; rfl

/-- In scope is below the counter — used only to prove the laws below. -/
theorem ProverState.mem_lt {st : ProverState F} {v : Variable} (hv : v ∈ st) : v < st.nv := by
  by_contra h
  rw [ProverState.mem_def, st.fresh v (Nat.le_of_not_lt h)] at hv
  cases hv

/-- Scope survives any extension of the table. -/
theorem ProverState.mem_of_le {st st' : ProverState F} (hle : st.env.Le st'.env)
    {v : Variable} (hv : v ∈ st) : v ∈ st' := by
  obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hv
  exact ProverState.mem_of_assigned (hle v x hx)

/-- In scope means assigned, and the slot holds its completed reading. -/
theorem ProverState.get_eq [Zero F] (st : ProverState F) {v : Variable} (hv : v ∈ st) :
    st.env v = some (st.env.toValuation v) :=
  Assignments.toValuation_eq hv

/-- An in-scope reading survives any extension of the table. -/
theorem ProverState.get_of_le [Zero F] {st st' : ProverState F} (hle : st.env.Le st'.env)
    {v : Variable} (hv : v ∈ st) : st'.env.toValuation v = st.env.toValuation v := by
  have h := hle v _ (st.get_eq hv)
  simp [Assignments.toValuation, h]

/-- Allocate `xs` at the counter: the state after an `existsOp`. The only way a run
makes a new state, and the invariant comes with it. -/
def ProverState.extendMany (st : ProverState F) (xs : List F) : ProverState F :=
  ⟨st.nv + xs.length, st.env.extendList st.nv xs, st.fresh.extendList xs⟩

theorem ProverState.extendMany_nv (st : ProverState F) (xs : List F) :
    (st.extendMany xs).nv = st.nv + xs.length := rfl

theorem ProverState.extendMany_env (st : ProverState F) (xs : List F) :
    (st.extendMany xs).env = st.env.extendList st.nv xs := rfl

/-- Allocation only grows the table. -/
theorem ProverState.le_extendMany (st : ProverState F) (xs : List F) :
    st.env.Le (st.extendMany xs).env :=
  st.fresh.le_extendList xs

/-- Scope survives allocation. -/
theorem ProverState.mem_extendMany {st : ProverState F} {v : Variable} (hv : v ∈ st)
    (xs : List F) : v ∈ st.extendMany xs :=
  ProverState.mem_of_le (st.le_extendMany xs) hv

/-- The allocated names are in scope. -/
theorem ProverState.new_mem_extendMany (st : ProverState F) {xs : List F} {i : Nat}
    (hi : i < xs.length) : st.nv + i ∈ st.extendMany xs := by
  rw [ProverState.mem_def, ProverState.extendMany_env, Assignments.extendList_get hi]
  rfl

/-- The scope after an allocation: the scope before, and the allocated names. The form
`simp` uses, so that a name's scope at a grown state reduces to its scope at the
start, however many allocations deep. -/
@[simp] theorem ProverState.mem_extendMany_iff {st : ProverState F} {xs : List F}
    {v : Variable} :
    v ∈ st.extendMany xs ↔ v ∈ st ∨ ∃ i, i < xs.length ∧ v = st.nv + i := by
  constructor
  · intro h
    by_cases hlt : v < st.nv
    · left
      rw [ProverState.mem_def, ProverState.extendMany_env,
        Assignments.extendList_below hlt] at h
      exact h
    · right
      by_cases hge : st.nv + xs.length ≤ v
      · exfalso
        rw [ProverState.mem_def, ProverState.extendMany_env,
          Assignments.extendList_above hge, st.fresh v (by omega)] at h
        cases h
      · exact ⟨v - st.nv, Nat.sub_lt_left_of_lt_add (Nat.le_of_not_lt hlt) (Nat.lt_of_not_le hge),
          (Nat.add_sub_cancel' (Nat.le_of_not_lt hlt)).symm⟩
  · rintro (h | ⟨i, hi, rfl⟩)
    · exact ProverState.mem_extendMany h xs
    · exact st.new_mem_extendMany hi

/-- An allocated slot reads as what was written. -/
@[simp] theorem ProverState.get_extendMany_new [Zero F] (st : ProverState F) {xs : List F}
    {i : Nat} (hi : i < xs.length) :
    (st.extendMany xs).env.toValuation (st.nv + i) = xs[i] := by
  show ((st.extendMany xs).env (st.nv + i)).getD 0 = _
  rw [ProverState.extendMany_env, Assignments.extendList_get hi]
  rfl

/-- An in-scope name reads the same through an allocation. -/
@[simp] theorem ProverState.get_extendMany_of_mem [Zero F] (st : ProverState F)
    {v : Variable} (hv : v ∈ st) (xs : List F) :
    (st.extendMany xs).env.toValuation v = st.env.toValuation v := by
  show ((st.extendMany xs).env v).getD 0 = (st.env v).getD 0
  rw [ProverState.extendMany_env, Assignments.extendList_below (ProverState.mem_lt hv)]

/-! ## Scoped witness blocks

`w.Scoped st`: every variable the block can read is in scope. A scoped block cannot
fail on a lookup — its run is its evaluation at the completed table
(`run_eq_eval`) — so the value a law mentions is `w.eval st.env.toValuation`, a
function of the state with nothing to name and nothing to case on. -/

/-- Every variable the block can read is in scope at `st`. -/
def AsProver.Scoped (st : ProverState F) : AsProver F α → Prop
  | .pure _ => True
  | .read v k => v ∈ st ∧ ∀ x, (k x).Scoped st
  | .fail _ => True

@[simp] theorem AsProver.scoped_pure (st : ProverState F) (a : α) :
    (AsProver.pure a : AsProver F α).Scoped st := trivial

@[simp] theorem AsProver.scoped_read (st : ProverState F) (v : Variable)
    (k : F → AsProver F α) :
    (AsProver.read v k).Scoped st ↔ v ∈ st ∧ ∀ x, (k x).Scoped st := Iff.rfl

@[simp] theorem AsProver.scoped_fail (st : ProverState F) (e : EvalError) :
    (AsProver.fail e : AsProver F α).Scoped st := trivial

/-- A scoped block's run is its evaluation at the completed table: no lookup fails. -/
theorem AsProver.run_eq_eval [Zero F] {w : AsProver F α} {st : ProverState F}
    (hs : w.Scoped st) : w.run st.env = w.eval st.env.toValuation := by
  induction w with
  | pure a => rfl
  | read v k ih =>
    obtain ⟨hv, hk⟩ := hs
    simp only [AsProver.run, AsProver.eval, st.get_eq hv]
    exact ih _ (hk _)
  | fail e => rfl

/-- A scoped block reads only in scope, so two readings that agree there evaluate it
alike. -/
theorem AsProver.eval_congr {w : AsProver F α} {st : ProverState F} (hs : w.Scoped st)
    {V V' : Valuation F} (hg : ∀ v, v ∈ st → V v = V' v) : w.eval V = w.eval V' := by
  induction w with
  | pure a => rfl
  | read v k ih =>
    obtain ⟨hv, hk⟩ := hs
    simp only [AsProver.eval, hg v hv]
    exact ih _ (hk _)
  | fail e => rfl

/-! ## Interpreter agreement -/

/-- Builder/prover agreement: on a successful prover run the two interpreters compute
the same result and the same final variable counter — they allocate variables in lockstep
(the PS builder and prover run the same closure against two `CircuitOps` records; here
that is a theorem rather than an intention). -/
theorem prove_build_agrees {holds : c → Assignments F → Bool} {m : CircuitM F c α}
    {nv nv' : Nat} {env env' : Assignments F} {x : α}
    (h : prove holds m nv env = .ok ⟨x, nv', env'⟩) :
    (build m nv).result = x ∧ (build m nv).nextVar = nv' := by
  induction m generalizing nv nv' env env' x with
  | pure a =>
    simp only [prove, Except.ok.injEq, Proved.mk.injEq] at h
    obtain ⟨rfl, rfl, -⟩ := h
    exact ⟨rfl, rfl⟩
  | addConstraintOp con k ih =>
    simp only [prove] at h
    simp only [build]
    split at h
    · exact ih h
    · cases h
  | existsOp n wit k ih =>
    simp only [prove] at h
    simp only [build]
    split at h
    · cases h
    · split at h
      · cases h
      · exact ih _ h
  | assignOp vs wit k ih =>
    simp only [prove] at h
    simp only [build]
    split at h
    · cases h
    · split at h
      · cases h
      · split at h
        · cases h
        · exact ih h
  | labelOp str k ih =>
    simp only [prove] at h
    simp only [build]
    exact ih h

/-! ## Completeness -/

/-- Completeness: if the prover run succeeds, the final assignment satisfies every
constraint the builder emits — provided `holds` is monotone in the assignment-extension
order (true of any constraint that evaluates its `CVar`s, by `CVar.eval_le`). The prover
checked each constraint when it was added; monotonicity carries the check to the end of
the run. -/
theorem prove_complete {holds : c → Assignments F → Bool}
    (hmono : ∀ (con : c) {a a' : Assignments F},
      a.Le a' → holds con a = true → holds con a' = true)
    {m : CircuitM F c α} {nv nv' : Nat} {env env' : Assignments F} {x : α}
    (h : prove holds m nv env = .ok ⟨x, nv', env'⟩) :
    ∀ con ∈ (build m nv).constraints, holds con env' = true := by
  induction m generalizing nv nv' env env' x with
  | pure a =>
    intro con hcon
    simp [build] at hcon
  | addConstraintOp con' k ih =>
    simp only [prove] at h
    split at h
    · next hh =>
      intro con hcon
      simp only [build, List.mem_cons] at hcon
      rcases hcon with rfl | hcon
      · exact hmono con (prove_assignments_le h) hh
      · exact ih h con hcon
    · cases h
  | existsOp n wit k ih =>
    simp only [prove] at h
    simp only [build]
    split at h
    · cases h
    · split at h
      · cases h
      · exact ih _ h
  | assignOp vs wit k ih =>
    simp only [prove] at h
    simp only [build]
    split at h
    · cases h
    · split at h
      · cases h
      · split at h
        · cases h
        · exact ih h
  | labelOp str k ih =>
    simp only [prove] at h
    simp only [build]
    exact ih h

end Snarky
