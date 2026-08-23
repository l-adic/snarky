import Snarky.Backend.Prover

/-!
# The backend seam: one interpreter, pluggable ops

Port of the PS backend classes `CompileCircuit`/`SolveCircuit`
(packages/snarky/src/Snarky/Backend/{Builder,Prover}.purs): PS has ONE interpreter
pair in the core library, parameterized by the backend through per-constraint STATE
TRANSFORMS — `appendBuilderConstraint` reduces a constraint into emitted gates while
allocating intermediates against the shared counter, `proverConstraint` does the same
against the witness table, `finalize` flushes backend state after a run. The classes
render as the ops record `BackendOps` (`Backend/Prover.lean` originally
ported only the checking fragment as the pure `holds` parameter and recorded the
reducing fragment as the un-ported seam — this module is that seam), and the
interpreters as `buildWith`/`proveWith`/`finalizeWith` over the same reified
`CircuitM`.

The base interpreters are the trivial instantiation: `checkedOps` appends each
constraint as itself and checks it with `holds`, and
`buildWith_checkedOps`/`proveWith_checkedOps` prove `build`/`prove` are exactly
`buildWith`/`proveWith` at those ops — so the base laws transfer across the seam.

The composition laws (`buildWith_bind`/`proveWith_bind`) are the base
`build_bind`/`prove_bind` proved once, generically: every backend inherits them.
Laws that need more from the ops take the corresponding coherence fact about the
ops record as a hypothesis (`§ Ops coherence` below): per-constraint counter
lockstep (`BackendOps.Lockstep`) yields whole-program allocation agreement between
the two interpreters, and per-constraint prover extension
(`BackendOps.ProveExtends`) yields whole-program table monotonicity. Both facts
are hypotheses per backend; `checkedOps`'s are discharged immediately below their
consequences.
-/

namespace Snarky

variable {F c g σ : Type u}

/-- A backend's per-constraint seams (the PS `CompileCircuit`/`SolveCircuit`
classes, as a record): reduce a constraint into gates against the builder state,
reduce it against the prover state, and flush after a run. Both reductions may
allocate — they borrow and return the SHARED variable counter, which is what lets a
backend interleave internal allocations with user allocations. -/
structure BackendOps (F g c σ : Type u) where
  /-- Reduce one constraint into its emitted gates (in emission order), advancing
  the counter and the backend state (PS `appendBuilderConstraint`). -/
  appendConstraint : c → Nat → σ → List g × Nat × σ
  /-- Reduce one constraint against the witness table, advancing the counter and the
  table, or fail (PS `proverConstraint`). -/
  proveConstraint : c → Nat → Assignments F → Except EvalError (Nat × Assignments F)
  /-- Flush the backend state after a run, possibly emitting one trailing gate (PS
  `finalize`). -/
  finalize : σ → Option g × σ

/-- The generic builder's output: the base `Built` plus the backend state. -/
structure BuiltWith (g σ : Type u) (α : Type v) where
  /-- The computation's result value. -/
  result : α
  /-- The next-variable counter after the run. -/
  nextVar : Nat
  /-- The emitted gates, in emission order. -/
  constraints : List g
  /-- The backend state after the run. -/
  aux : σ

/-- Interpret a circuit as its gates through a backend's ops (PS
`runCircuitBuilder`): allocation mirrors `build`; each constraint runs the backend's
builder seam against the shared counter and state. -/
def buildWith (ops : BackendOps F g c σ) :
    CircuitM F c α → Nat → σ → BuiltWith g σ α
  | .pure a, n, s => ⟨a, n, [], s⟩
  | .addConstraintOp con k, n, s =>
    let red := ops.appendConstraint con n s
    let r := buildWith ops k red.2.1 red.2.2
    ⟨r.result, r.nextVar, red.1 ++ r.constraints, r.aux⟩
  | .existsOp m _ k, n, s => buildWith ops (k (allocRange n m)) (n + m) s
  | .assignOp _ _ k, n, s => buildWith ops k n s
  | .labelOp _ k, n, s => buildWith ops k n s

/-- Flush the backend state after a build (the PS `finalize` seam applied): a
trailing gate appends, the state updates. -/
def finalizeWith (ops : BackendOps F g c σ) (b : BuiltWith g σ α) : BuiltWith g σ α :=
  match ops.finalize b.aux with
  | (none, s') => { b with aux := s' }
  | (some gate, s') => { b with constraints := b.constraints ++ [gate], aux := s' }

/-- Finalization only flushes queued rows: the counter is untouched. -/
theorem finalizeWith_nextVar (ops : BackendOps F g c σ) (b : BuiltWith g σ α) :
    (finalizeWith ops b).nextVar = b.nextVar := by
  unfold finalizeWith
  rcases ops.finalize b.aux with ⟨_ | gate, s'⟩ <;> rfl

/-- Interpret a circuit as a prover run through a backend's ops (PS
`runCircuitProver`): witness handling and the assignment guard mirror `prove`; each
constraint runs the backend's prover seam against the shared counter and table. -/
def proveWith (ops : BackendOps F g c σ) :
    CircuitM F c α → Nat → Assignments F → Except EvalError (Proved F α)
  | .pure a, nv, env => .ok ⟨a, nv, env⟩
  | .addConstraintOp con k, nv, env =>
    match ops.proveConstraint con nv env with
    | .error e => .error e
    | .ok (nv', env') => proveWith ops k nv' env'
  | .existsOp n wit k, nv, env =>
    match wit.run env with
    | .error e => .error e
    | .ok xs =>
      match env.extendPairs ((allocRange nv n).toList.zip xs.toList) with
      | .error e => .error e
      | .ok env' => proveWith ops (k (allocRange nv n)) (nv + n) env'
  | .assignOp vs wit k, nv, env =>
    match vs.toList.find? (nv ≤ ·) with
    | some v => .error (.conflict v)
    | none =>
      match wit.run env with
      | .error e => .error e
      | .ok xs =>
        match env.extendPairs (vs.toList.zip xs.toList) with
        | .error e => .error e
        | .ok env' => proveWith ops k nv env'
  | .labelOp _ k, nv, env => proveWith ops k nv env

/-! ## The base interpreters are the trivial instantiation -/

/-- The base backend's ops: append each constraint as itself (no reduction, no
state), check it with `holds` at prove time, flush nothing. -/
def checkedOps (holds : c → Assignments F → Bool) : BackendOps F c c PUnit where
  appendConstraint con n s := ([con], n, s)
  proveConstraint con nv env :=
    if holds con env then .ok (nv, env) else .error .unsatisfiedConstraint
  finalize s := (none, s)

/-- `build` is `buildWith` at the base ops. -/
theorem buildWith_checkedOps (holds : c → Assignments F → Bool)
    (m : CircuitM F c α) (n : Nat) :
    buildWith (checkedOps holds) m n ⟨⟩ =
      ⟨(build m n).result, (build m n).nextVar, (build m n).constraints, ⟨⟩⟩ := by
  induction m generalizing n with
  | pure a => rfl
  | addConstraintOp con k ih =>
    have h1 : (checkedOps (F := F) holds).appendConstraint con n PUnit.unit =
        ([con], n, PUnit.unit) := rfl
    simp only [buildWith, build, h1, ih, List.singleton_append]
  | existsOp n' wit k ih => exact ih ..
  | assignOp vs wit k ih => exact ih ..
  | labelOp s k ih => exact ih ..

/-- `prove` is `proveWith` at the base ops. -/
theorem proveWith_checkedOps (holds : c → Assignments F → Bool)
    (m : CircuitM F c α) (nv : Nat) (env : Assignments F) :
    proveWith (checkedOps holds) m nv env = prove holds m nv env := by
  induction m generalizing nv env with
  | pure a => rfl
  | addConstraintOp con k ih =>
    have h1 : (checkedOps (F := F) holds).proveConstraint con nv env =
        if holds con env then .ok (nv, env) else .error .unsatisfiedConstraint := rfl
    simp only [proveWith, prove, h1]
    by_cases h : holds con env
    · simp only [if_pos h, ih]
    · simp only [if_neg h]
  | existsOp n wit k ih =>
    simp only [proveWith, prove]
    cases hw : wit.run env with
    | error e => rfl
    | ok xs =>
      simp only []
      cases hp : env.extendPairs ((allocRange nv n).toList.zip xs.toList) with
      | error e => rfl
      | ok env' => exact ih ..
  | assignOp vs wit k ih =>
    simp only [proveWith, prove]
    cases hg : vs.toList.find? (nv ≤ ·) with
    | some v => rfl
    | none =>
      simp only []
      cases hw : wit.run env with
      | error e => rfl
      | ok xs =>
        simp only []
        cases hp : env.extendPairs (vs.toList.zip xs.toList) with
        | error e => rfl
        | ok env' => exact ih ..
  | labelOp s k ih => exact ih ..

/-! ## Ops coherence

The per-constraint facts the cross-seam laws parameterize over. Both seams borrow the
one shared variable counter, so the CS the builder emits and the table the
prover fills only correspond if every constraint advances that counter identically in
both — that is `Lockstep`. `ProveExtends` is the prover-side write-once contract at
the ops level: a successful seam only grows the table. Each backend discharges these
for its own ops record; the theorems below turn them into whole-program facts. -/

/-- Per-constraint counter lockstep between a backend's two seams: whenever the
prover seam succeeds, the builder seam advances the shared counter to the same value,
for every backend state (so the advance is also state-independent). -/
def BackendOps.Lockstep (ops : BackendOps F g c σ) : Prop :=
  ∀ con n env n' env' (s : σ),
    ops.proveConstraint con n env = .ok (n', env') →
    (ops.appendConstraint con n s).2.1 = n'

/-- Per-constraint prover extension: a successful prover seam only extends the
witness table and never retreats the counter. -/
def BackendOps.ProveExtends (ops : BackendOps F g c σ) : Prop :=
  ∀ con n env n' env',
    ops.proveConstraint con n env = .ok (n', env') →
    env.Le env' ∧ n ≤ n'

/-- Whole-program allocation lockstep: at a `Lockstep` backend, a successful
prover run and the builder run allocate identically — the builder ends at the
prover's final counter, from any backend state. -/
theorem buildWith_proveWith_nextVar {ops : BackendOps F g c σ} (hl : ops.Lockstep)
    {m : CircuitM F c α} {nv : Nat} {env : Assignments F} {p : Proved F α}
    (h : proveWith ops m nv env = .ok p) (s : σ) :
    (buildWith ops m nv s).nextVar = p.nextVar := by
  induction m generalizing nv env s with
  | pure a => cases h; rfl
  | addConstraintOp con k ih =>
    simp only [proveWith] at h
    split at h
    · cases h
    · next nv' env' hc =>
      simp only [buildWith]
      rw [hl con nv env nv' env' s hc]
      exact ih h _
  | existsOp n wit k ih =>
    simp only [proveWith] at h
    split at h
    · cases h
    · split at h
      · cases h
      · exact ih _ h s
  | assignOp vs wit k ih =>
    simp only [proveWith] at h
    split at h
    · cases h
    · split at h
      · cases h
      · split at h
        · cases h
        · exact ih h s
  | labelOp s' k ih => exact ih h s

/-- Whole-program table monotonicity: at a `ProveExtends` backend, a successful
prover run only extends the table and never retreats the counter (the generic
`prove_assignments_le`). -/
theorem proveWith_extends {ops : BackendOps F g c σ} (hp : ops.ProveExtends)
    {m : CircuitM F c α} {nv : Nat} {env : Assignments F} {p : Proved F α}
    (h : proveWith ops m nv env = .ok p) :
    env.Le p.assignments ∧ nv ≤ p.nextVar := by
  induction m generalizing nv env with
  | pure a =>
    cases h
    exact ⟨Assignments.Le.refl _, Nat.le_refl _⟩
  | addConstraintOp con k ih =>
    simp only [proveWith] at h
    split at h
    · cases h
    · next nv' env' hc =>
      obtain ⟨hle₀, hn₀⟩ := hp con nv env nv' env' hc
      obtain ⟨hle, hn⟩ := ih h
      exact ⟨hle₀.trans hle, hn₀.trans hn⟩
  | existsOp n wit k ih =>
    simp only [proveWith] at h
    split at h
    · cases h
    · split at h
      · cases h
      · next env' hext =>
        obtain ⟨hle, hn⟩ := ih _ h
        exact ⟨(Assignments.le_extendPairs hext).trans hle,
          (Nat.le_add_right nv n).trans hn⟩
  | assignOp vs wit k ih =>
    simp only [proveWith] at h
    split at h
    · cases h
    · split at h
      · cases h
      · split at h
        · cases h
        · next env' hext =>
          obtain ⟨hle, hn⟩ := ih h
          exact ⟨(Assignments.le_extendPairs hext).trans hle, hn⟩
  | labelOp s' k ih => exact ih h

/-- The base ops are in lockstep: neither seam ever allocates. -/
theorem checkedOps_lockstep (holds : c → Assignments F → Bool) :
    (checkedOps (F := F) holds).Lockstep := by
  intro con n env n' env' s hc
  simp only [checkedOps] at hc
  split at hc
  · cases hc; rfl
  · cases hc

/-- The base ops only extend: the prover seam checks and touches nothing. -/
theorem checkedOps_proveExtends (holds : c → Assignments F → Bool) :
    (checkedOps (F := F) holds).ProveExtends := by
  intro con n env n' env' hc
  simp only [checkedOps] at hc
  split at hc
  · cases hc; exact ⟨Assignments.Le.refl _, Nat.le_refl _⟩
  · cases hc

/-! ## The composition laws, once for every backend -/

/-- Building a sequence splits (`build_bind`, proved once for every backend):
the tail builds from the head's result, counter, and backend state, and the gates
concatenate in emission order. -/
theorem buildWith_bind (ops : BackendOps F g c σ) (m : CircuitM F c α)
    (f : α → CircuitM F c β) (nv : Nat) (s : σ) :
    buildWith ops (m >>= f) nv s =
      ⟨(buildWith ops (f (buildWith ops m nv s).result)
          (buildWith ops m nv s).nextVar (buildWith ops m nv s).aux).result,
       (buildWith ops (f (buildWith ops m nv s).result)
          (buildWith ops m nv s).nextVar (buildWith ops m nv s).aux).nextVar,
       (buildWith ops m nv s).constraints
         ++ (buildWith ops (f (buildWith ops m nv s).result)
              (buildWith ops m nv s).nextVar (buildWith ops m nv s).aux).constraints,
       (buildWith ops (f (buildWith ops m nv s).result)
          (buildWith ops m nv s).nextVar (buildWith ops m nv s).aux).aux⟩ := by
  show buildWith ops (CircuitM.bind m f) nv s = _
  induction m generalizing nv s with
  | pure a => rfl
  | addConstraintOp con k ih =>
    simp only [CircuitM.bind, buildWith, ih, List.append_assoc]
  | existsOp n wit k ih => exact ih ..
  | assignOp vs wit k ih => exact ih ..
  | labelOp s' k ih => exact ih ..

/-- Proving a sequence is proving the head, then the tail from its final state
(`prove_bind`, proved once for every backend). -/
theorem proveWith_bind (ops : BackendOps F g c σ) (m : CircuitM F c α)
    (f : α → CircuitM F c β) (nv : Nat) (env : Assignments F) :
    proveWith ops (m >>= f) nv env =
      (proveWith ops m nv env).bind
        fun out => proveWith ops (f out.result) out.nextVar out.assignments := by
  show proveWith ops (CircuitM.bind m f) nv env = _
  induction m generalizing nv env with
  | pure a => rfl
  | addConstraintOp con k ih =>
    simp only [CircuitM.bind, proveWith]
    split
    · rfl
    · exact ih ..
  | existsOp n wit k ih =>
    simp only [CircuitM.bind, proveWith]
    split
    · rfl
    · split
      · rfl
      · exact ih ..
  | assignOp vs wit k ih =>
    simp only [CircuitM.bind, proveWith]
    split
    · rfl
    · split
      · rfl
      · split
        · rfl
        · exact ih ..
  | labelOp s' k ih => exact ih ..

end Snarky
