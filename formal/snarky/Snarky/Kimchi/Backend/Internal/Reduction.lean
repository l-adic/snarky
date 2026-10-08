import Snarky.Kimchi.Constraint.Reduction

/-!
# The builder's operations as transitions

What the recording interpreter and the lowering's proofs know about the reduction layer's
builder: its generic and allocation ops as state transitions, and its equality op as a decision
against the constant cache, `outcomeOf`, followed by that decision's effect, `applyOutcome`.
The builder does not compute the decision; `addEqualsConstraint_apply` proves the op equal to
deciding and applying.

## Main definitions

- `GenericPlonkConstraint.vars`, `GenericPlonkConstraint.AbsentZero`: the variables a generic
  constraint names, and its absent cells carrying no coefficient.
- `EqualOutcome`, `outcomeOf`, `applyOutcome`, `EqualOutcome.names`: what the equality op did
  with a request, the decision against a cache, its effect on the builder's state, and the
  variables it fuses or writes.

## Main results

- `addGenericPlonkConstraint_apply`, `createInternalVariable_apply`,
  `addEqualsConstraint_apply`: the builder's ops as state transitions.
- `outcomeOf_cached_mem`, `outcomeOf_names`, `outcomeOf_pinned_absentZero`,
  `outcomeOf_row_absentZero`: a cache hit names a cached pair, the decision names only the
  constraint's variables, and its pinning and queued rows carry no coefficient on an absent
  cell.
-/

namespace Snarky.Kimchi

open Snarky

variable {F : Type}

/-! ## Generic constraints -/

/-- The variables a generic constraint names: its present left, right and output cells. -/
def GenericPlonkConstraint.vars {F : Type u} (g : GenericPlonkConstraint F) : List Variable :=
  g.vl.toList ++ g.vr.toList ++ g.vo.toList

/-- A generic constraint's absent cells carry no coefficient: an arbitrary table's value in
such a cell is irrelevant to the equation. -/
def GenericPlonkConstraint.AbsentZero {F : Type u} [Zero F] (g : GenericPlonkConstraint F) :
    Prop :=
  (g.vl = none → g.cl = 0 ∧ g.m = 0) ∧ (g.vr = none → g.cr = 0 ∧ g.m = 0) ∧
    (g.vo = none → g.co = 0)

/-! ## The builder's ops -/

/-- The builder's generic-constraint op, as a state transition: an empty queue takes the
constraint; an occupied one packs its constraint behind the incoming one into a row and
empties. -/
theorem addGenericPlonkConstraint_apply [Zero F] [Neg F] [Sub F] [Div F] [DecidableEq F]
    (g : GenericPlonkConstraint F) (s : BuilderReductionState F) :
    (addGenericPlonkConstraint g : PlonkBuilder F Unit) s =
      ((), match s.aux.queuedGenericGate with
        | none => { s with aux.queuedGenericGate := some g }
        | some queued =>
          { s with constraints := emitDoubleGateRow queued g :: s.constraints,
                   aux.queuedGenericGate := none }) := by
  show addGenericB g s = _
  unfold addGenericB handleGateBatching
  cases s.aux.queuedGenericGate <;> rfl

/-- The builder's allocation op, as a state transition: the counter's variable, touched into
the union-find and recorded as internal, the counter advanced. -/
theorem createInternalVariable_apply [Zero F] [Neg F] [Sub F] [Div F] [DecidableEq F]
    (e : AffineExpression F) (s : BuilderReductionState F) :
    (createInternalVariable e : PlonkBuilder F Variable) s =
      (s.nextVariable, { s with
        nextVariable := s.nextVariable + 1,
        aux.wireState.unionFind := (s.aux.wireState.unionFind.find s.nextVariable).2,
        aux.wireState.internalVariables :=
          s.nextVariable :: s.aux.wireState.internalVariables }) :=
  rfl

/-! ## The equality op's decision -/

/-- What the equality op did with a request, decided by its coefficients and the constant
cache. -/
inductive EqualOutcome (F : Type u) where
  /-- The union-find joined the two variables. -/
  | merge (l r : Variable)
  /-- The variable joined the one already pinned to the constant. -/
  | cached (l v : Variable) (k : F)
  /-- A pinning row queued, the constant cached at the variable. -/
  | pinned (v : Variable) (k : F) (g : GenericPlonkConstraint F)
  /-- A generic equation queued, nothing else. -/
  | row (g : GenericPlonkConstraint F)
  /-- Nothing. -/
  | trivial
  deriving DecidableEq

/-- The equality op's decision for a request against a cache: trivial coefficients drop it;
two variables with equal coefficients merge, with unequal ones a row; a variable against a
constant merges with the cached variable or pins and caches; two constants are trivial or a
row. -/
def outcomeOf [Zero F] [Neg F] [Sub F] [Div F] [DecidableEq F] (c : EqualsConstraint F)
    (cache : List (F × Variable)) : EqualOutcome F :=
  if c.cl = 0 ∧ c.cr = 0 then .trivial
  else
    match c.vl, c.vr with
    | some l, some r =>
      if c.cl = c.cr then .merge l r
      else
        .row { cl := c.cl, vl := some l, cr := -c.cr, vr := some r, co := 0, vo := none,
               m := 0, c := 0 }
    | some l, none =>
      if c.cl = 0 then
        .row { cl := 0, vl := none, cr := 0, vr := none, co := 0, vo := none, m := 0,
               c := c.cr }
      else
        match cache.lookup (c.cr / c.cl) with
        | some cached => .cached l cached (c.cr / c.cl)
        | none =>
          .pinned l (c.cr / c.cl)
            { cl := c.cl, vl := some l, cr := 0, vr := none, co := 0, vo := none, m := 0,
              c := -c.cr }
    | none, some r =>
      if c.cr = 0 then
        .row { cl := 0, vl := none, cr := 0, vr := none, co := 0, vo := none, m := 0,
               c := c.cl }
      else
        match cache.lookup (c.cl / c.cr) with
        | some cached => .cached r cached (c.cl / c.cr)
        | none =>
          .pinned r (c.cl / c.cr)
            { cl := 0, vl := none, cr := c.cr, vr := some r, co := 0, vo := none, m := 0,
              c := -c.cl }
    | none, none =>
      if c.cl = c.cr then .trivial
      else
        .row { cl := 0, vl := none, cr := 0, vr := none, co := 0, vo := none, m := 0,
               c := c.cl - c.cr }

/-- An outcome's effect on the builder's state. -/
def applyOutcome [Zero F] [Neg F] [Sub F] [Div F] [DecidableEq F] :
    EqualOutcome F → BuilderReductionState F → BuilderReductionState F
  | .merge l r, s => { s with aux.wireState.unionFind := s.aux.wireState.unionFind.union l r }
  | .cached l v _, s =>
    { s with aux.wireState.unionFind := s.aux.wireState.unionFind.union l v }
  | .pinned v k g, s =>
    let s' := ((addGenericPlonkConstraint g : PlonkBuilder F Unit) s).2
    { s' with aux.wireState.cachedConstants := (k, v) :: s'.aux.wireState.cachedConstants }
  | .row g, s => ((addGenericPlonkConstraint g : PlonkBuilder F Unit) s).2
  | .trivial, s => s

/-- The builder's equality op decides its outcome against the cache and applies it. -/
theorem addEqualsConstraint_apply [Zero F] [Neg F] [Sub F] [Div F] [DecidableEq F]
    (c : EqualsConstraint F) (s : BuilderReductionState F) :
    (addEqualsConstraint c : PlonkBuilder F Unit) s =
      ((), applyOutcome (outcomeOf c s.aux.wireState.cachedConstants) s) := by
  show addEqualsB c s = _
  unfold addEqualsB outcomeOf
  by_cases h0 : c.cl = 0 ∧ c.cr = 0
  · rw [if_pos h0, if_pos h0]
    rfl
  · rw [if_neg h0, if_neg h0]
    cases hvl : c.vl <;> cases hvr : c.vr <;> dsimp only
    · by_cases h1 : c.cl = c.cr
      · rw [if_pos h1, if_pos h1]
        rfl
      · rw [if_neg h1, if_neg h1]
        rfl
    · by_cases h1 : c.cr = 0
      · rw [if_pos h1, if_pos h1]
        rfl
      · rw [if_neg h1, if_neg h1]
        simp only [bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get, pure, modify,
          modifyGet, MonadStateOf.modifyGet]
        cases List.lookup (c.cl / c.cr) s.aux.wireState.cachedConstants <;> rfl
    · by_cases h1 : c.cl = 0
      · rw [if_pos h1, if_pos h1]
        rfl
      · rw [if_neg h1, if_neg h1]
        simp only [bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get, pure, modify,
          modifyGet, MonadStateOf.modifyGet]
        cases List.lookup (c.cr / c.cl) s.aux.wireState.cachedConstants <;> rfl
    · by_cases h1 : c.cl = c.cr
      · rw [if_pos h1, if_pos h1]
        rfl
      · rw [if_neg h1, if_neg h1]
        rfl

/-- A cache hit names a pair the cache held. -/
theorem outcomeOf_cached_mem [Zero F] [Neg F] [Sub F] [Div F] [DecidableEq F]
    {c : EqualsConstraint F} {cache : List (F × Variable)} {l v : Variable} {k : F}
    (h : outcomeOf c cache = .cached l v k) : (k, v) ∈ cache := by
  unfold outcomeOf at h
  split at h
  · cases h
  · split at h
    · split at h <;> cases h
    · split at h
      · cases h
      · split at h
        · cases h
          obtain ⟨l₁, l₂, hl, -⟩ := List.lookup_eq_some_iff.mp ‹List.lookup _ cache = some _›
          rw [hl]
          exact List.mem_append_right _ (List.mem_cons_self ..)
        · cases h
    · split at h
      · cases h
      · split at h
        · cases h
          obtain ⟨l₁, l₂, hl, -⟩ := List.lookup_eq_some_iff.mp ‹List.lookup _ cache = some _›
          rw [hl]
          exact List.mem_append_right _ (List.mem_cons_self ..)
        · cases h
    · split at h <;> cases h

/-- The variables an outcome fuses or writes: a merge's pair, a cache hit's variable, a pin's
variable with its row's cells, a row's cells. The cached variable of a hit is not among them. -/
def EqualOutcome.names : EqualOutcome F → List Variable
  | .merge l r => [l, r]
  | .cached l _ _ => [l]
  | .pinned v _ g => v :: g.vars
  | .row g => g.vars
  | .trivial => []

/-- The equality op's decision names only the constraint's own variables. -/
theorem outcomeOf_names [Zero F] [Neg F] [Sub F] [Div F] [DecidableEq F] (c : EqualsConstraint F)
    (cache : List (F × Variable)) :
    ∀ w ∈ (outcomeOf c cache).names, w ∈ c.vl.toList ++ c.vr.toList := by
  intro w hw
  unfold outcomeOf at hw
  repeat' split at hw
  all_goals simp_all [EqualOutcome.names, GenericPlonkConstraint.vars]

/-- The row a decision pins with carries no coefficient on an absent cell. -/
theorem outcomeOf_pinned_absentZero [Zero F] [Neg F] [Sub F] [Div F] [DecidableEq F]
    {c : EqualsConstraint F} {cache : List (F × Variable)} {v : Variable} {k : F}
    {g : GenericPlonkConstraint F} (h : outcomeOf c cache = .pinned v k g) : g.AbsentZero := by
  unfold outcomeOf at h
  repeat' split at h
  all_goals (cases h; try simp [GenericPlonkConstraint.AbsentZero])

/-- The row a decision queues carries no coefficient on an absent cell. -/
theorem outcomeOf_row_absentZero [Zero F] [Neg F] [Sub F] [Div F] [DecidableEq F]
    {c : EqualsConstraint F} {cache : List (F × Variable)} {g : GenericPlonkConstraint F}
    (h : outcomeOf c cache = .row g) : g.AbsentZero := by
  unfold outcomeOf at h
  repeat' split at h
  all_goals (cases h; try simp [GenericPlonkConstraint.AbsentZero])

end Snarky.Kimchi
