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
  cases. Reachable behaviour is unchanged; a contradictory circuit now compiles to an
  unsatisfiable system instead of crashing the compiler.
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
equality. The builder, the prover, and the law-vehicle trace interpret it below. -/
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

end Snarky.Kimchi
