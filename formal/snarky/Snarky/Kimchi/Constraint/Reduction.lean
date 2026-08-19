import Snarky.Backend.Assignments
import Snarky.Kimchi.Constraint.Types

/-!
# The affine-reduction layer of the kimchi backend

Port of `Snarky.Constraint.Kimchi.Reduction`
(packages/snarky-kimchi/src/Snarky/Constraint/Kimchi/Reduction.purs), itself a
transcription of OCaml snarky's `reduce_lincom`/`completely_reduce`: the op vocabulary
`PlonkReductionM`, the generic algorithms `reduceAffineExpression`/`reduceToVariable`
that rewrite an affine form into `c·v` while emitting generic constraints, and the two
concrete interpreters — the builder (rows, gate batching, wiring, constant cache) and
the prover (witness values).

Name map: every PS export keeps its name (`PlonkReductionM` with its three methods,
`reduceAffineExpression`, `reduceToVariable`, `Rows`, `mkPadRow`,
`finalizeGateQueue`, `reduceAsBuilder`, `reduceAsProver`); `completelyReduce` stays the
private helper. `addEqualsConstraint`'s anonymous record argument gets the Lean name
`EqualsConstraint`. PS `incrementVariable` is `+ 1` (as in the base interpreters).

Deviations from the PS original (per `formal/docs/snarky-kimchi-alignment.md`):
- `PlonkBuilder` is `StateM`, `PlonkProver` is `StateT _ (Except EvalError)`: PS
  hand-rolls both monads over `Effect`, but the `Effect` existed only for the mutable
  union-find and assignment store, both pure here, and the hand-rolling was a measured
  JS-runtime optimisation with no Lean analogue. The builder still accumulates its row
  list newest-first and reverses once in `reduceAsBuilder` — the emission ORDER is
  fixture bytes — the byte contract.
- The class carries no `Monad` superclass (the algorithms take `[Monad m]` themselves),
  and the PS functional dependency `m -> f` is recovered from argument types. PS
  `PrimeField` splits into the weakest classes each definition needs; division appears
  only in the builder's constant-cache normalisation.
- `reduceAsBuilder`/`reduceAsProver` take their computation at the concrete monad: the
  PS rank-2 argument is an abstraction firewall with no Lean consumer; PS needs it
  because its agreement laws quantify over class-polymorphic programs, where the
  firewall carries meaning.
- The prover's write is guarded (`Assignments.extendPairs`), mirroring the base
  prover's strengthening of the PS write-once contract; on counter-fresh states it
  agrees with PS `set`.
- PS throws on the statically-contradictory assertion `constant cl = constant cr` with
  `cl ≠ cr`; the total Lean builder instead emits the corresponding unsatisfiable
  generic row (`c = cl − cr`), the same move PS itself makes in the one-sided constant
  cases. Contradiction-free circuits behave identically; a contradictory circuit now
  compiles to an unsatisfiable system instead of crashing the compiler.
- PS `Map.lookup/insert` on the constant cache becomes assoc-list `lookup`/cons: keys
  are inserted only on lookup miss, so first-match lookup is map lookup. The cache's
  iteration order is NOT fixture-observable — the dumper sorts by variable
  (`Array.sortWith _.variable` in pickles-circuit-diffs) and the only in-code consumer
  is `lookup` — which settles the ordering question `Constraint/Types` deferred.

## One shared counter — how the reducing interpreters render

PS threads ONE `nextVariable` counter through user allocation and reduction-internal
allocation: `reduceAsBuilder` borrows and returns the compile state's counter. That
interleaving is fixture bytes, not an internal detail: gate rows record raw variable
ids per cell — `div_step_circuit.json`'s packed generic row reads
`variables: [0, 3, 4, 2, 3, …]`, internals `3, 4` numbered between user variables in
program order. So the base `build`/`prove` numbering (user variables consecutive)
cannot be reused post hoc; the kimchi backend gets its own interpreter pair over the
same reified `CircuitM`, mirroring PS's `CompileCircuit`/`SolveCircuit` instances and
threading the states defined here.

## What is stated here

Nothing semantic: this module is the computational layer only — the payloads' op
vocabulary, the two reduction algorithms, the row emission, and the three instances.
The builder's batching queues an incoming constraint and packs pairs into
`emitDoubleGateRow` rows (`addGenericPlonkConstraint` below). The meaning of the
emitted constraints and the faithfulness of the reduction are deliberately not stated
in this package.

The seam-coherence section at the end states per-op bookkeeping only: which ops move
the shared counter, and that the prover's guarded write only extends the table.

The PS package has no QuickCheck rows for this module — its tests exercise the
circuit layer, and the fixture corpus is the oracle; the byte-equality seam replays
it against this port.
-/

namespace Snarky.Kimchi

open Snarky

/-! ## The equals-constraint payload -/

/-- The payload of `addEqualsConstraint` (the PS anonymous record): assert
`cl·vl = cr·vr`, where an absent slot stands for the constant `1`. -/
structure EqualsConstraint (F : Type u) where
  /-- Left coefficient. -/
  cl : F
  /-- Left variable; `none` = the constant `1`. -/
  vl : Option Variable
  /-- Right coefficient. -/
  cr : F
  /-- Right variable; `none` = the constant `1`. -/
  vr : Option Variable


/-! ## The op vocabulary and the generic algorithms -/

/-- The reduction-op vocabulary (PS `class PlonkReductionM`): allocate an internal
variable for an affine expression, emit a generic constraint, assert a two-sided
equality. The builder and the prover interpret it below. -/
class PlonkReductionM (F : Type) (m : Type → Type) where
  /-- Allocate a fresh variable standing for the given affine expression (the prover
  assigns it the expression's value; the builder only advances the counter). -/
  createInternalVariable : AffineExpression F → m Variable
  /-- Emit one generic constraint (the builder batches two per row). -/
  addGenericPlonkConstraint : GenericPlonkConstraint F → m Unit
  /-- Assert `cl·vl = cr·vr` (the builder wires, caches, or emits; see the instance). -/
  addEqualsConstraint : EqualsConstraint F → m Unit

export PlonkReductionM (createInternalVariable addGenericPlonkConstraint
  addEqualsConstraint)

variable {F : Type} {m : Type → Type}

/-- Right-recursively reduce a nonempty term list to a single scaled variable, emitting
one generic constraint per combination step, deepest terms first (PS
`completelyReduce`, transcribing OCaml's `completely_reduce` — the recursion direction
is constraint-emission order, hence fixture bytes). -/
private def completelyReduce [Zero F] [One F] [Neg F] [Monad m] [PlonkReductionM F m]
    (single : Variable × F) : List (Variable × F) → m (Variable × F)
  | [] => pure single
  | next :: rest => do
    let r ← completelyReduce next rest
    let vo ← createInternalVariable ⟨none, [single, r]⟩
    addGenericPlonkConstraint
      { cl := single.2, vl := some single.1, cr := r.2, vr := some r.1, co := -1,
        vo := some vo, m := 0, c := 0 }
    pure (vo, 1)

/-- Reduce an affine form to `c·v` (`(some v, c)`) or a bare constant (`(none, c)`),
emitting the generic constraints that pin the intermediates (PS
`reduceAffineExpression`, transcribing OCaml's `reduce_lincom`): no terms is the
constant; one term folds a nonzero constant through a fresh output; two or more terms
save the head and right-reduce the tail. Every constructed term list keeps the
ascending-variable invariant: tails of an ascending input, and fresh outputs exceed
every allocated variable. -/
def reduceAffineExpression [Zero F] [One F] [Neg F] [DecidableEq F] [Monad m]
    [PlonkReductionM F m] (ae : AffineExpression F) : m (Option Variable × F) :=
  match ae.terms with
  | [] => pure (none, ae.constant.getD 0)
  | [head] =>
    match ae.constant with
    | none => pure (some head.1, head.2)
    | some c =>
      if c = 0 then pure (some head.1, head.2)
      else do
        let vo ← createInternalVariable ⟨some c, [head]⟩
        addGenericPlonkConstraint
          { cl := head.2, vl := some head.1, cr := 0, vr := none, co := -1,
            vo := some vo, m := 0, c := c }
        pure (some vo, 1)
  | head :: first :: rest => do
    let r ← completelyReduce first rest
    let vo ← createInternalVariable ⟨ae.constant, [head, r]⟩
    addGenericPlonkConstraint
      { cl := head.2, vl := some head.1, cr := r.2, vr := some r.1, co := -1,
        vo := some vo, m := 0, c := ae.constant.getD 0 }
    pure (some vo, 1)

/-- Reduce a `CVar` all the way to a single variable (PS `reduceToVariable`): reduce
the canonical affine form, then pin a bare constant with an equals constraint or fold a
nonunit scale through a fresh output. -/
def reduceToVariable [Add F] [Mul F] [Zero F] [One F] [Neg F] [DecidableEq F] [Monad m]
    [PlonkReductionM F m] (x : CVar F) : m Variable := do
  let r ← reduceAffineExpression x.reduceToAffineExpression
  match r.1 with
  | none => do
    let vl ← createInternalVariable ⟨some r.2, []⟩
    addEqualsConstraint { cl := 1, vl := some vl, cr := r.2, vr := none }
    pure vl
  | some v =>
    if r.2 = 1 then pure v
    else do
      let cv ← createInternalVariable ⟨none, [(v, r.2)]⟩
      addGenericPlonkConstraint
        { cl := r.2, vl := some v, cr := 0, vr := none, co := -1, vo := some cv,
          m := 0, c := 0 }
      pure cv

/-! ## Row emission -/

/-- The builder's constraint wrapper (PS `newtype Rows`): one emitted gate row. -/
structure Rows (F : Type u) where
  /-- The wrapped row. -/
  row : KimchiRow F
  deriving Repr, DecidableEq

instance : ToKimchiRows F (Rows F) where
  toKimchiRows r := [r.row]

/-- The padding row: a Generic-kind row over seven wired cells and no coefficients
(PS `mkPadRow`) — the generic equation is degenerate, so the row's only content is
its wiring. -/
def mkPadRow (vs : Vector Variable 7) : Rows F :=
  ⟨{ kind := .genericPlonk,
     vars := ⟨⟨vs.toList.map some ++ List.replicate 8 none⟩, by simp⟩,
     coeffs := [] }⟩

/-- The five coefficient cells of one queued constraint, in row order
`[cl, cr, co, m, c]` (PS `constraintToCoeffs`). -/
private def constraintToCoeffs (g : GenericPlonkConstraint F) : List F :=
  [g.cl, g.cr, g.co, g.m, g.c]

/-- Flush a half-full gate queue into its single-constraint row (PS
`finalizeGateQueue`, taking the queue field rather than PS's open record). -/
def finalizeGateQueue (queued : Option (GenericPlonkConstraint F)) : Option (Rows F) :=
  queued.map fun g =>
    ⟨{ kind := .genericPlonk,
       vars := ⟨⟨[g.vl, g.vr, g.vo] ++ List.replicate 12 none⟩, by simp⟩,
       coeffs := constraintToCoeffs g }⟩

/-! ## The builder -/

/-- The builder's reduction state (PS `BuilderReductionState`): emitted rows (newest
first — materialised forward once, in `reduceAsBuilder`), the shared variable counter,
and the auxiliary state. -/
structure BuilderReductionState (F : Type u) where
  /-- Emitted rows, newest first. -/
  constraints : List (KimchiRow F)
  /-- The shared variable counter (user and internal allocations interleave on it;
  see the module docstring). -/
  nextVariable : Variable
  /-- The wire state and the gate queue. -/
  aux : AuxState F

/-- The builder's reduction monad (PS `PlonkBuilder`, minus the `Effect` that only
served the mutable union-find). -/
abbrev PlonkBuilder (F : Type) := StateM (BuilderReductionState F)

/-- Pack the queued and the incoming constraint into one double Generic row — the NEW
gate's cells first, the QUEUED gate's second, matching OCaml (PS `emitDoubleGateRow`). -/
private def emitDoubleGateRow (queued new : GenericPlonkConstraint F) : KimchiRow F :=
  { kind := .genericPlonk,
    vars := ⟨⟨[new.vl, new.vr, new.vo, queued.vl, queued.vr, queued.vo] ++
      List.replicate 9 none⟩, by simp⟩,
    coeffs := constraintToCoeffs new ++ constraintToCoeffs queued }

/-- Queue an incoming generic constraint, or pack it with the queued one into a
finished row (PS `handleGateBatching`). -/
private def handleGateBatching (newGate : GenericPlonkConstraint F) :
    PlonkBuilder F (Option (KimchiRow F)) := fun s =>
  match s.aux.queuedGenericGate with
  | none => (none, { s with aux.queuedGenericGate := some newGate })
  | some queued =>
    (some (emitDoubleGateRow queued newGate), { s with aux.queuedGenericGate := none })

/-- Merge two variables' classes in the wire state's union-find (PS `unionB`). -/
private def unionB (x y : Variable) : PlonkBuilder F Unit := fun s =>
  ((), { s with aux.wireState.unionFind := s.aux.wireState.unionFind.union x y })

/-- The builder's generic-constraint op: batch, and emit any finished row (the PS
`addGenericPlonkConstraint` instance method). -/
private def addGenericB (c : GenericPlonkConstraint F) : PlonkBuilder F Unit := fun s =>
  match handleGateBatching c s with
  | (none, s') => ((), s')
  | (some row, s') => ((), { s' with constraints := row :: s'.constraints })

/-- The builder's allocation op: touch the fresh variable into the union-find (PS
`findB`, result discarded), record it as internal, and advance the counter (the PS
`createInternalVariable` instance method). The cons onto `internalVariables` is
set-faithful because the counter is strictly increasing — the variable is never
already present. -/
private def createInternalB : PlonkBuilder F Variable := fun s =>
  let nv := s.nextVariable
  let (_, uf) := s.aux.wireState.unionFind.find nv
  (nv, { s with
          nextVariable := nv + 1,
          aux.wireState.unionFind := uf,
          aux.wireState.internalVariables :=
            nv :: s.aux.wireState.internalVariables })

/-- The builder's equality op (the PS `addEqualsConstraint` instance method), the guard
cascade in PS order: trivial coefficients are dropped; two variables with equal
coefficients are WIRED (union), with unequal coefficients constrained; a variable
against a constant first consults the constant cache — a hit wires it to the cached
variable, a miss emits the pinning row and caches it; a zero-coefficient or
variable-free side degenerates to a constant assertion (unsatisfiable when false — see
the module docstring for the PS-throw rendering). -/
private def addEqualsB [Zero F] [Neg F] [Sub F] [Div F] [DecidableEq F]
    (c : EqualsConstraint F) : PlonkBuilder F Unit :=
  if c.cl = 0 ∧ c.cr = 0 then pure ()
  else
    match c.vl, c.vr with
    | some l, some r =>
      if c.cl = c.cr then unionB l r
      else
        addGenericB
          { cl := c.cl, vl := some l, cr := -c.cr, vr := some r, co := 0, vo := none,
            m := 0, c := 0 }
    | some l, none =>
      if c.cl = 0 then
        addGenericB
          { cl := 0, vl := none, cr := 0, vr := none, co := 0, vo := none, m := 0,
            c := c.cr }
      else do
        let constVal := c.cr / c.cl
        match (← get).aux.wireState.cachedConstants.lookup constVal with
        | some cached => unionB l cached
        | none => do
          addGenericB
            { cl := c.cl, vl := some l, cr := 0, vr := none, co := 0, vo := none,
              m := 0, c := -c.cr }
          modify fun s =>
            { s with aux.wireState.cachedConstants :=
                (constVal, l) :: s.aux.wireState.cachedConstants }
    | none, some r =>
      if c.cr = 0 then
        addGenericB
          { cl := 0, vl := none, cr := 0, vr := none, co := 0, vo := none, m := 0,
            c := c.cl }
      else do
        let constVal := c.cl / c.cr
        match (← get).aux.wireState.cachedConstants.lookup constVal with
        | some cached => unionB r cached
        | none => do
          addGenericB
            { cl := 0, vl := none, cr := c.cr, vr := some r, co := 0, vo := none,
              m := 0, c := -c.cl }
          modify fun s =>
            { s with aux.wireState.cachedConstants :=
                (constVal, r) :: s.aux.wireState.cachedConstants }
    | none, none =>
      if c.cl = c.cr then pure ()
      else
        addGenericB
          { cl := 0, vl := none, cr := 0, vr := none, co := 0, vo := none, m := 0,
            c := c.cl - c.cr }

instance [Zero F] [Neg F] [Sub F] [Div F] [DecidableEq F] :
    PlonkReductionM F (PlonkBuilder F) where
  createInternalVariable _ := createInternalB
  addGenericPlonkConstraint := addGenericB
  addEqualsConstraint := addEqualsB

/-- Run a reduction in the builder from a borrowed counter and auxiliary state (PS
`reduceAsBuilder`): returns the result, the emitted rows in emission order (the
newest-first accumulator reversed exactly once), and the counter and auxiliary state
to hand back. -/
def reduceAsBuilder (nextVariable : Variable) (aux : AuxState F)
    (x : PlonkBuilder F α) : α × List (Rows F) × Variable × AuxState F :=
  let (a, s) := x.run ⟨[], nextVariable, aux⟩
  (a, s.constraints.reverse.map Rows.mk, s.nextVariable, s.aux)

/-! ## The prover -/

/-- The prover's reduction state (PS `ProverReductionState`): the shared counter and
the accumulating witness table. -/
structure ProverReductionState (F : Type u) where
  /-- The shared variable counter, in lockstep with the builder's. -/
  nextVariable : Variable
  /-- The witness table. -/
  assignments : Assignments F

/-- The prover's reduction monad (PS `PlonkProver`, the same fused state-and-error
shape with `Effect` dropped). -/
abbrev PlonkProver (F : Type) := StateT (ProverReductionState F) (Except EvalError)

/-- The prover's allocation op: evaluate the expression against the current table and
assign the fresh variable its value (the PS `createInternalVariable` instance method,
with the guarded write — see the module docstring). -/
private def createInternalP [Add F] [Mul F] [Zero F] (e : AffineExpression F) :
    PlonkProver F Variable := fun s =>
  match e.eval s.assignments with
  | .error err => .error err
  | .ok a =>
    match s.assignments.extendPairs [(s.nextVariable, a)] with
    | .error err => .error err
    | .ok env => .ok (s.nextVariable, ⟨s.nextVariable + 1, env⟩)

instance [Add F] [Mul F] [Zero F] : PlonkReductionM F (PlonkProver F) where
  createInternalVariable := createInternalP
  addGenericPlonkConstraint _ := pure ()
  addEqualsConstraint _ := pure ()

/-- Run a reduction in the prover (PS `reduceAsProver`): a bare run — failure carries
the evaluation error out. -/
def reduceAsProver (s : ProverReductionState F) (x : PlonkProver F α) :
    Except EvalError (α × ProverReductionState F) :=
  x.run s

/-! ## Seam coherence: the op-level facts

Only `createInternalVariable` moves the shared counter — by exactly one, on both
sides. The other builder ops touch rows, the gate queue, the union-find, and the
constant cache; the other prover ops are inert. Stated here per op: the builder's
counter behavior, total, and the prover op's success inversion, whose table extension
is unconditional because `extendPairs` is guarded — success implies no overwrite. -/

/-- The builder's allocation op, applied: return the current counter, advance it,
touch the union-find, record the internal variable. -/
theorem createInternalB_apply (s : BuilderReductionState F) :
    createInternalB s
      = (s.nextVariable,
          { s with
            nextVariable := s.nextVariable + 1,
            aux.wireState.unionFind :=
              (s.aux.wireState.unionFind.find s.nextVariable).2,
            aux.wireState.internalVariables :=
              s.nextVariable :: s.aux.wireState.internalVariables }) := rfl

/-- The builder's generic-constraint op never moves the counter: it queues or packs. -/
private theorem addGenericB_nextVariable (c : GenericPlonkConstraint F)
    (s : BuilderReductionState F) :
    (addGenericB c s).2.nextVariable = s.nextVariable := by
  rcases hq : s.aux.queuedGenericGate with _ | g <;>
    simp [addGenericB, handleGateBatching, hq]

/-- The builder's equality op never moves the counter: every branch of the guard
cascade wires, caches, batches, or no-ops. -/
private theorem addEqualsB_nextVariable [Zero F] [Neg F] [Sub F] [Div F]
    [DecidableEq F] (c : EqualsConstraint F) (s : BuilderReductionState F) :
    (addEqualsB c s).2.nextVariable = s.nextVariable := by
  rcases c with ⟨cl, vl, cr, vr⟩
  dsimp only [addEqualsB]
  split
  · rfl
  rcases vl with _ | l <;> rcases vr with _ | r <;> dsimp only
  · -- constant against constant
    split
    · rfl
    · exact addGenericB_nextVariable ..
  · -- constant against a variable
    split
    · exact addGenericB_nextVariable ..
    · dsimp only [Bind.bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get]
      rcases _hc : s.aux.wireState.cachedConstants.lookup (cl / cr) with _ | cached
      · exact addGenericB_nextVariable ..
      · rfl
  · -- a variable against a constant
    split
    · exact addGenericB_nextVariable ..
    · dsimp only [Bind.bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get]
      rcases _hc : s.aux.wireState.cachedConstants.lookup (cr / cl) with _ | cached
      · exact addGenericB_nextVariable ..
      · rfl
  · -- two variables: wire or constrain
    split
    · rfl
    · exact addGenericB_nextVariable ..

/-- The prover's allocation op, inverted at success: it returns the borrowed counter,
advances it by one, and only extends the table (the guarded write). -/
private theorem createInternalP_ok [Add F] [Mul F] [Zero F] {e : AffineExpression F}
    {n : Variable} {env : Assignments F} {a : Variable} {s' : ProverReductionState F}
    (h : createInternalP e ⟨n, env⟩ = .ok (a, s')) :
    a = n ∧ s'.nextVariable = n + 1 ∧ env.Le s'.assignments := by
  unfold createInternalP at h
  split at h
  · cases h
  split at h
  · cases h
  next env' hext =>
    cases h
    exact ⟨rfl, rfl, Assignments.le_extendPairs hext⟩

/-! ## Seam coherence: the generic algorithms

The paired-run walks: a successful prover run of each reduction algorithm pins the
builder run from any state at the same counter — same result, same final counter —
and only extends the prover's table. Result agreement is load-bearing: downstream
branching consumes returned variables, so the branches agree exactly when the
counters do. -/

/-- Invert one prover bind: a successful sequenced run factors through a successful
prefix. -/
theorem PlonkProver.bind_ok {α β : Type} {x : PlonkProver F α}
    {f : α → PlonkProver F β} {s s' : ProverReductionState F} {b : β} :
    (x >>= f) s = .ok (b, s') ↔
      ∃ a s₁, x s = .ok (a, s₁) ∧ f a s₁ = .ok (b, s') := by
  constructor
  · intro h
    rcases hx : x s with e | ⟨a, s₁⟩ <;>
      simp only [Bind.bind, StateT.bind, hx, Except.bind] at h
    · cases h
    · exact ⟨a, s₁, rfl, h⟩
  · rintro ⟨a, s₁, hx, hf⟩
    simp only [Bind.bind, StateT.bind, hx, Except.bind]
    exact hf

/-- The prover's `pure`, applied. -/
theorem PlonkProver.pure_apply {α : Type} (a : α) (s : ProverReductionState F) :
    (pure a : PlonkProver F α) s = .ok (a, s) := rfl

/-- Step one builder bind: the state monad sequences by application. -/
theorem PlonkBuilder.bind_apply {α β : Type} (x : PlonkBuilder F α)
    (f : α → PlonkBuilder F β) (s : BuilderReductionState F) :
    (x >>= f) s = f (x s).1 (x s).2 := rfl

/-- The builder's `pure`, applied. -/
theorem PlonkBuilder.pure_apply {α : Type} (a : α) (s : BuilderReductionState F) :
    (pure a : PlonkBuilder F α) s = (a, s) := rfl

/-- The class ops at the builder instance, named (`simp` fodder for the walks). -/
theorem createInternal_builder [Zero F] [Neg F] [Sub F] [Div F] [DecidableEq F]
    (e : AffineExpression F) :
    createInternalVariable (m := PlonkBuilder F) e = createInternalB := rfl

private theorem addGeneric_builder [Zero F] [Neg F] [Sub F] [Div F] [DecidableEq F]
    (c : GenericPlonkConstraint F) :
    addGenericPlonkConstraint (m := PlonkBuilder F) c = addGenericB c := rfl

private theorem addEquals_builder [Zero F] [Neg F] [Sub F] [Div F] [DecidableEq F]
    (c : EqualsConstraint F) :
    addEqualsConstraint (m := PlonkBuilder F) c = addEqualsB c := rfl

/-- The row-emitting ops at the prover instance are inert. -/
theorem addGeneric_prover [Add F] [Mul F] [Zero F]
    (c : GenericPlonkConstraint F) :
    addGenericPlonkConstraint (m := PlonkProver F) c = pure () := rfl

/-- The equality op at the prover instance is inert. -/
theorem addEquals_prover [Add F] [Mul F] [Zero F] (c : EqualsConstraint F) :
    addEqualsConstraint (m := PlonkProver F) c = pure () := rfl

/-! ## Seam coherence: the composable pairing

The gate reducers are `reduceToVariable` chains and structural folds, so their walks
compose rather than re-walk: `Seam` pairs a builder run with a prover run and is
preserved by `pure`, `bind`, and `map`; the leaves are the reduction algorithms and
the two row-emitting ops. The per-gate walks live beside their reducers and consume
this vocabulary. -/

/-- The paired-run property the per-gate walks compose: whenever the prover run
succeeds, the builder run from any state at the same counter returns the same result
and lands at the prover's final counter, and the prover's table only grew. -/
def Seam {α : Type} (xB : PlonkBuilder F α) (xP : PlonkProver F α) : Prop :=
  ∀ {sP sP' : ProverReductionState F} {a : α}, xP sP = .ok (a, sP') →
    ∀ sB : BuilderReductionState F, sB.nextVariable = sP.nextVariable →
      (xB sB).1 = a ∧ (xB sB).2.nextVariable = sP'.nextVariable ∧
      sP.assignments.Le sP'.assignments ∧ sP.nextVariable ≤ sP'.nextVariable

/-- `pure` is a seam. -/
protected theorem Seam.pure {α : Type} (a : α) :
    Seam (pure a : PlonkBuilder F α) (pure a) := by
  intro sP sP' a' h sB hn
  simp only [PlonkProver.pure_apply, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  exact ⟨rfl, hn, Assignments.Le.refl _, Nat.le_refl _⟩

/-- Seams compose over `bind`: the prefix's result agreement feeds the
continuation. -/
protected theorem Seam.bind {α β : Type} {xB : PlonkBuilder F α}
    {xP : PlonkProver F α} {fB : α → PlonkBuilder F β} {fP : α → PlonkProver F β}
    (hx : Seam xB xP) (hf : ∀ a, Seam (fB a) (fP a)) :
    Seam (xB >>= fB) (xP >>= fP) := by
  intro sP sP' b h sB hn
  rw [PlonkProver.bind_ok] at h
  obtain ⟨a, sP₁, h₁, h₂⟩ := h
  obtain ⟨ha, hn₁, hle₁, hm₁⟩ := hx h₁ sB hn
  obtain ⟨hb, hn₂, hle₂, hm₂⟩ := hf a h₂ (xB sB).2 hn₁
  rw [PlonkBuilder.bind_apply, ha]
  exact ⟨hb, hn₂, hle₁.trans hle₂, hm₁.trans hm₂⟩

/-- Seams compose over `map`. -/
protected theorem Seam.map {α β : Type} {xB : PlonkBuilder F α}
    {xP : PlonkProver F α} (f : α → β) (hx : Seam xB xP) :
    Seam (f <$> xB) (f <$> xP) := by
  rw [← bind_pure_comp, ← bind_pure_comp]
  exact hx.bind fun a => Seam.pure (f a)

/-- Seams compose over a shared conditional. -/
protected theorem Seam.ite {α : Type} {c : Prop} [Decidable c]
    {xB yB : PlonkBuilder F α} {xP yP : PlonkProver F α}
    (hx : c → Seam xB xP) (hy : ¬c → Seam yB yP) :
    Seam (if c then xB else yB) (if c then xP else yP) := by
  by_cases h : c
  · rw [if_pos h, if_pos h]
    exact hx h
  · rw [if_neg h, if_neg h]
    exact hy h

/-- The generic-constraint op is a seam: inert for the prover, counter-inert for the
builder. -/
theorem addGeneric_seam [Add F] [Mul F] [Zero F] [Neg F] [Sub F] [Div F]
    [DecidableEq F] (g : GenericPlonkConstraint F) :
    Seam (addGenericPlonkConstraint (m := PlonkBuilder F) g)
      (addGenericPlonkConstraint (m := PlonkProver F) g) := by
  intro sP sP' u h sB hn
  simp only [addGeneric_prover, PlonkProver.pure_apply, Except.ok.injEq,
    Prod.mk.injEq] at h
  obtain ⟨-, rfl⟩ := h
  refine ⟨rfl, ?_, Assignments.Le.refl _, Nat.le_refl _⟩
  rw [addGeneric_builder, addGenericB_nextVariable, hn]

/-- The equality op is a seam: inert for the prover, counter-inert for the
builder. -/
theorem addEquals_seam [Add F] [Mul F] [Zero F] [Neg F] [Sub F] [Div F]
    [DecidableEq F] (e : EqualsConstraint F) :
    Seam (addEqualsConstraint (m := PlonkBuilder F) e)
      (addEqualsConstraint (m := PlonkProver F) e) := by
  intro sP sP' u h sB hn
  simp only [addEquals_prover, PlonkProver.pure_apply, Except.ok.injEq,
    Prod.mk.injEq] at h
  obtain ⟨-, rfl⟩ := h
  refine ⟨rfl, ?_, Assignments.Le.refl _, Nat.le_refl _⟩
  rw [addEquals_builder, addEqualsB_nextVariable, hn]

variable [Add F] [Mul F] [Sub F] [Div F] [Zero F] [One F] [Neg F] [DecidableEq F]

/-- `completelyReduce` in lockstep: same result, same final counter, table only
grown. -/
private theorem completelyReduce_lockstep {single : Variable × F}
    {ts : List (Variable × F)} {sP sP' : ProverReductionState F} {a : Variable × F}
    (h : completelyReduce (m := PlonkProver F) single ts sP = .ok (a, sP'))
    (sB : BuilderReductionState F) (hn : sB.nextVariable = sP.nextVariable) :
    (completelyReduce (m := PlonkBuilder F) single ts sB).1 = a ∧
    (completelyReduce (m := PlonkBuilder F) single ts sB).2.nextVariable
      = sP'.nextVariable ∧
    sP.assignments.Le sP'.assignments ∧ sP.nextVariable ≤ sP'.nextVariable := by
  induction ts generalizing single sP sB a sP' with
  | nil =>
    simp only [completelyReduce, PlonkProver.pure_apply, Except.ok.injEq,
      Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, hn, Assignments.Le.refl _, Nat.le_refl _⟩
  | cons next rest ih =>
    simp only [completelyReduce] at h ⊢
    rw [PlonkProver.bind_ok] at h
    obtain ⟨r, sP₁, h₁, h⟩ := h
    rw [PlonkProver.bind_ok] at h
    obtain ⟨vo, sP₂, h₂, h⟩ := h
    rw [PlonkProver.bind_ok] at h
    obtain ⟨u, sP₃, h₃, h⟩ := h
    simp only [addGeneric_prover, PlonkProver.pure_apply, Except.ok.injEq,
      Prod.mk.injEq] at h₃ h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨-, rfl⟩ := h₃
    obtain ⟨-, ihn, ihle, ihmono⟩ := ih h₁ sB hn
    obtain ⟨rfl, hn₂, hle₂⟩ := createInternalP_ok h₂
    refine ⟨?_, ?_, ihle.trans hle₂, by rw [hn₂]; exact Nat.le_succ_of_le ihmono⟩
    · simp only [PlonkBuilder.bind_apply, createInternal_builder,
        createInternalB_apply, addGeneric_builder, PlonkBuilder.pure_apply, ihn]
    · simp only [PlonkBuilder.bind_apply, createInternal_builder,
        createInternalB_apply, addGeneric_builder, PlonkBuilder.pure_apply,
        addGenericB_nextVariable, ihn, hn₂]

/-- `reduceAffineExpression` in lockstep. -/
private theorem reduceAffineExpression_lockstep {ae : AffineExpression F}
    {sP sP' : ProverReductionState F} {a : Option Variable × F}
    (h : reduceAffineExpression (m := PlonkProver F) ae sP = .ok (a, sP'))
    (sB : BuilderReductionState F) (hn : sB.nextVariable = sP.nextVariable) :
    (reduceAffineExpression (m := PlonkBuilder F) ae sB).1 = a ∧
    (reduceAffineExpression (m := PlonkBuilder F) ae sB).2.nextVariable
      = sP'.nextVariable ∧
    sP.assignments.Le sP'.assignments ∧ sP.nextVariable ≤ sP'.nextVariable := by
  rcases hts : ae.terms with _ | ⟨head, _ | ⟨first, rest⟩⟩ <;>
    simp only [reduceAffineExpression, hts] at h ⊢
  · simp only [PlonkProver.pure_apply, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, hn, Assignments.Le.refl _, Nat.le_refl _⟩
  · rcases hc : ae.constant with _ | c <;> simp only [hc] at h ⊢
    · simp only [PlonkProver.pure_apply, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨rfl, hn, Assignments.Le.refl _, Nat.le_refl _⟩
    · by_cases h0 : c = 0
      · rw [if_pos h0] at h ⊢
        simp only [PlonkProver.pure_apply, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨rfl, hn, Assignments.Le.refl _, Nat.le_refl _⟩
      · rw [if_neg h0] at h ⊢
        rw [PlonkProver.bind_ok] at h
        obtain ⟨vo, sP₁, h₁, h⟩ := h
        rw [PlonkProver.bind_ok] at h
        obtain ⟨u, sP₂, h₂, h⟩ := h
        simp only [addGeneric_prover, PlonkProver.pure_apply, Except.ok.injEq,
          Prod.mk.injEq] at h₂ h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨-, rfl⟩ := h₂
        obtain ⟨rfl, hn₁, hle₁⟩ := createInternalP_ok h₁
        refine ⟨?_, ?_, hle₁, by rw [hn₁]; exact Nat.le_succ _⟩
        · simp only [PlonkBuilder.bind_apply, createInternal_builder,
            createInternalB_apply, addGeneric_builder, PlonkBuilder.pure_apply, hn]
        · simp only [PlonkBuilder.bind_apply, createInternal_builder,
            createInternalB_apply, addGeneric_builder, PlonkBuilder.pure_apply,
            addGenericB_nextVariable, hn, hn₁]
  · rw [PlonkProver.bind_ok] at h
    obtain ⟨r, sP₁, h₁, h⟩ := h
    rw [PlonkProver.bind_ok] at h
    obtain ⟨vo, sP₂, h₂, h⟩ := h
    rw [PlonkProver.bind_ok] at h
    obtain ⟨u, sP₃, h₃, h⟩ := h
    simp only [addGeneric_prover, PlonkProver.pure_apply, Except.ok.injEq,
      Prod.mk.injEq] at h₃ h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨-, rfl⟩ := h₃
    obtain ⟨-, ihn, ihle, ihmono⟩ := completelyReduce_lockstep h₁ sB hn
    obtain ⟨rfl, hn₂, hle₂⟩ := createInternalP_ok h₂
    refine ⟨?_, ?_, ihle.trans hle₂, by rw [hn₂]; exact Nat.le_succ_of_le ihmono⟩
    · simp only [PlonkBuilder.bind_apply, createInternal_builder,
        createInternalB_apply, addGeneric_builder, PlonkBuilder.pure_apply, ihn]
    · simp only [PlonkBuilder.bind_apply, createInternal_builder,
        createInternalB_apply, addGeneric_builder, PlonkBuilder.pure_apply,
        addGenericB_nextVariable, ihn, hn₂]

/-- `reduceToVariable` in lockstep: the walks' one public boundary — same variable,
same final counter, table only grown. -/
theorem reduceToVariable_lockstep {x : CVar F}
    {sP sP' : ProverReductionState F} {v : Variable}
    (h : reduceToVariable (m := PlonkProver F) x sP = .ok (v, sP'))
    (sB : BuilderReductionState F) (hn : sB.nextVariable = sP.nextVariable) :
    (reduceToVariable (m := PlonkBuilder F) x sB).1 = v ∧
    (reduceToVariable (m := PlonkBuilder F) x sB).2.nextVariable
      = sP'.nextVariable ∧
    sP.assignments.Le sP'.assignments ∧ sP.nextVariable ≤ sP'.nextVariable := by
  simp only [reduceToVariable] at h ⊢
  rw [PlonkProver.bind_ok] at h
  obtain ⟨r, sP₁, h₁, h⟩ := h
  obtain ⟨ihr, ihn, ihle, ihmono⟩ := reduceAffineExpression_lockstep h₁ sB hn
  simp only [PlonkBuilder.bind_apply, ihr]
  rcases hr : r.1 with _ | rv <;> rw [hr] at h <;> dsimp only at h ⊢
  · rw [PlonkProver.bind_ok] at h
    obtain ⟨vl, sP₂, h₂, h⟩ := h
    rw [PlonkProver.bind_ok] at h
    obtain ⟨u, sP₃, h₃, h⟩ := h
    simp only [addEquals_prover, PlonkProver.pure_apply, Except.ok.injEq,
      Prod.mk.injEq] at h₃ h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨-, rfl⟩ := h₃
    obtain ⟨rfl, hn₂, hle₂⟩ := createInternalP_ok h₂
    refine ⟨?_, ?_, ihle.trans hle₂, by rw [hn₂]; exact Nat.le_succ_of_le ihmono⟩
    · simp only [PlonkBuilder.bind_apply, createInternal_builder,
        createInternalB_apply, addEquals_builder, PlonkBuilder.pure_apply, ihn]
    · simp only [PlonkBuilder.bind_apply, createInternal_builder,
        createInternalB_apply, addEquals_builder, PlonkBuilder.pure_apply,
        addEqualsB_nextVariable, ihn, hn₂]
  · by_cases h1 : r.2 = 1
    · rw [if_pos h1] at h ⊢
      simp only [PlonkProver.pure_apply, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨rfl, ihn, ihle, ihmono⟩
    · rw [if_neg h1] at h ⊢
      rw [PlonkProver.bind_ok] at h
      obtain ⟨cv, sP₂, h₂, h⟩ := h
      rw [PlonkProver.bind_ok] at h
      obtain ⟨u, sP₃, h₃, h⟩ := h
      simp only [addGeneric_prover, PlonkProver.pure_apply, Except.ok.injEq,
        Prod.mk.injEq] at h₃ h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨-, rfl⟩ := h₃
      obtain ⟨rfl, hn₂, hle₂⟩ := createInternalP_ok h₂
      refine ⟨?_, ?_, ihle.trans hle₂, by rw [hn₂]; exact Nat.le_succ_of_le ihmono⟩
      · simp only [PlonkBuilder.bind_apply, createInternal_builder,
          createInternalB_apply, addGeneric_builder, PlonkBuilder.pure_apply, ihn]
      · simp only [PlonkBuilder.bind_apply, createInternal_builder,
          createInternalB_apply, addGeneric_builder, PlonkBuilder.pure_apply,
          addGenericB_nextVariable, ihn, hn₂]

/-- `reduceToVariable` is a seam (`reduceToVariable_lockstep`, repackaged). -/
theorem reduceToVariable_seam (x : CVar F) :
    Seam (reduceToVariable (m := PlonkBuilder F) x)
      (reduceToVariable (m := PlonkProver F) x) := by
  intro sP sP' a h sB hn
  exact reduceToVariable_lockstep h sB hn

/-- `reduceAffineExpression` is a seam (`reduceAffineExpression_lockstep`,
repackaged): the `Basic` reducer branches on its results, which agree. -/
theorem reduceAffineExpression_seam (ae : AffineExpression F) :
    Seam (reduceAffineExpression (m := PlonkBuilder F) ae)
      (reduceAffineExpression (m := PlonkProver F) ae) := by
  intro sP sP' a h sB hn
  exact reduceAffineExpression_lockstep h sB hn

end Snarky.Kimchi
