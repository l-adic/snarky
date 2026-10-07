import Snarky.Kimchi.Backend.RowCorrespondence
import Snarky.Kimchi.Backend.TraceSemantics
import Kimchi.Gate.Generic
import Kimchi.Columns

/-!
# Generic receipts

Where each queued equation landed. A Boolean's equation is not among its own step's rows: it
enters the batching queue and leaves it packed behind the next queued equation, wherever that
is, or alone at the final flush. The same holds for the pinning rows and the unequal-coefficient
rows the equality op queues. The walk here replays the queue over the recorded events, step by
step with each step's gate rows between, and issues every queued equation a receipt: the body
row holding it and the half of that row. The first half is the row's cells `0` to `2` with
coefficients `0` to `4`, the second its cells `3` to `5` with coefficients `5` to `9`; a packed
row holds the incoming equation first.

An event queues an equation or does not (`ReductionEvent.queued?`): a generic constraint and
the two row-queuing outcomes of an equality do, an allocation and the merging, cache-hit and
trivial outcomes do not and are passed over, since they leave the queue alone. So the walk is
total, and because it tracks the builder's actual queue by equality, its receipts are proved
located for the recorded lowering of any constraint list: the cells and coefficients at a
receipt are exactly its equation's.

Receipts locate equations only. An equality discharged by a merge or a cache hit queues
nothing, and its obligation is met elsewhere: a merge through the wiring's classes, a cache hit
through the class and the pinning row of the cached variable, which has a receipt of its own.

## Main definitions

- `ReductionEvent.queued?`: the generic equation an event queued, if any.
- `GenericReceipt`, `GenericReceipt.Located`: a receipt and what it claims of the body rows.
- `receipts`: every queued equation's receipt.
- `RecordedGates.allRows`: the body rows with the final flush's row.

## Main results

- `receipts_located`: every receipt is located in the lowering's rows.
- `receipts_complete`: every queued equation has a receipt.
- `replayEvent_queue`, `queued?_vars`: one faithful event's effect on the queue and the rows,
  and a queued equation's cells among its event's names.
- `genericValue_of_located`: at a located receipt, a generic row holding at cells agreeing
  with a valuation makes the constraint's equation hold, when its absent cells carry no
  coefficient.
-/

open Kimchi

namespace Snarky.Kimchi

open Snarky

variable {F : Type}

/-! ## Receipts -/

/-- Where a generic event's equation landed: the body row and the half of its cells. -/
structure GenericReceipt (F : Type) where
  /-- The event's constraint. -/
  gate : GenericPlonkConstraint F
  /-- The body row holding its equation. -/
  row : Nat
  /-- The half of that row. -/
  half : Fin 2
  deriving DecidableEq

/-- The three cells of a packed row's half. -/
def halfCells (row : KimchiRow F) (half : Fin 2) :
    Option Variable × Option Variable × Option Variable :=
  (row.vars[3 * half.val]'(by have := half.isLt; omega),
    row.vars[3 * half.val + 1]'(by have := half.isLt; omega),
    row.vars[3 * half.val + 2]'(by have := half.isLt; omega))

/-- The five coefficients of a packed row's half. -/
def halfCoeffs (row : KimchiRow F) (half : Fin 2) : List F :=
  (row.coeffs.drop (5 * half.val)).take 5

/-- A receipt is located: its row is a generic row whose cells and coefficients at the half
are its constraint's. -/
def GenericReceipt.Located (body : List (KimchiRow F)) (rc : GenericReceipt F) : Prop :=
  ∃ row, body[rc.row]? = some row ∧ row.kind = .generic ∧
    halfCells row rc.half = (rc.gate.vl, rc.gate.vr, rc.gate.vo) ∧
    halfCoeffs row rc.half = [rc.gate.cl, rc.gate.cr, rc.gate.co, rc.gate.m, rc.gate.c]

instance [DecidableEq F] (body : List (KimchiRow F)) (rc : GenericReceipt F) :
    Decidable (rc.Located body) :=
  match h : body[rc.row]? with
  | none => isFalse fun hloc => by
      obtain ⟨_, h', -⟩ := hloc
      rw [h] at h'
      exact absurd h' (by simp)
  | some row =>
    decidable_of_iff (row.kind = .generic ∧
      halfCells row rc.half = (rc.gate.vl, rc.gate.vr, rc.gate.vo) ∧
      halfCoeffs row rc.half = [rc.gate.cl, rc.gate.cr, rc.gate.co, rc.gate.m, rc.gate.c])
      ⟨fun ⟨a, b, c⟩ => Exists.intro row ⟨h, a, b, c⟩, fun hloc => by
        obtain ⟨row', h', a, b, c⟩ := hloc
        rw [h, Option.some.injEq] at h'
        subst h'
        exact ⟨a, b, c⟩⟩

private theorem GenericReceipt.Located.append {body : List (KimchiRow F)} {rc : GenericReceipt F}
    (h : rc.Located body) (more : List (KimchiRow F)) : rc.Located (body ++ more) := by
  obtain ⟨row, hrow, h⟩ := h
  exact ⟨row, by rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp hrow).1]; exact hrow,
    h⟩

/-- The body rows with the final flush's row, if any. -/
def RecordedGates.allRows [Zero F] (r : RecordedGates F) : List (KimchiRow F) :=
  r.bodyRows ++ ((finalizeGateQueue r.aux.queuedGenericGate).map (·.row)).toList

/-! ## The walk -/

/-- The generic equation an event queued, if any: a generic constraint, or the row an
equality's outcome queued. -/
def ReductionEvent.queued? : ReductionEvent F → Option (GenericPlonkConstraint F)
  | .generic g => some g
  | .equal _ (.pinned _ _ g) => some g
  | .equal _ (.row g) => some g
  | _ => none

/-- A queued equation's cells are among its event's names. -/
theorem queued?_vars {e : ReductionEvent F} {g : GenericPlonkConstraint F}
    (h : e.queued? = some g) : ∀ w ∈ g.vars, w ∈ e.names := by
  cases e with
  | alloc _ _ => cases h
  | generic g' =>
    simp only [ReductionEvent.queued?, Option.some.injEq] at h
    subst h
    exact fun _ hw => hw
  | equal c o =>
    cases o with
    | pinned v k g' =>
      simp only [ReductionEvent.queued?, Option.some.injEq] at h
      subst h
      exact fun _ hw => List.mem_cons_of_mem _ hw
    | row g' =>
      simp only [ReductionEvent.queued?, Option.some.injEq] at h
      subst h
      exact fun _ hw => hw
    | merge _ _ => cases h
    | cached _ _ _ => cases h
    | trivial => cases h

/-- The walk's state: the next body row, the queued constraint, and the receipts so far. -/
private structure Walk (F : Type) where
  row : Nat
  pending : Option (GenericPlonkConstraint F)
  receipts : List (GenericReceipt F)

/-- The builder's batching over one step's events, issuing receipts: a queued equation packs
in front of the waiting one into the next row; an event queuing nothing is passed over. -/
private def walkEvents : List (ReductionEvent F) → Walk F → Walk F
  | [], w => w
  | e :: es, w =>
    match e.queued? with
    | none => walkEvents es w
    | some g =>
      match w.pending with
      | none => walkEvents es { w with pending := some g }
      | some q => walkEvents es ⟨w.row + 1, none, w.receipts ++ [⟨g, w.row, 0⟩, ⟨q, w.row, 1⟩]⟩

/-- The walk over the steps: each step's events, then its gate's rows. -/
private def walkSteps : List (RecordedStep F) → Walk F → Walk F
  | [], w => w
  | s :: rest, w =>
    let w := walkEvents s.events w
    walkSteps rest { w with row := w.row + s.gateRows.length }

/-- Every queued equation's receipt, the final flush receiving the waiting constraint. -/
def receipts (r : RecordedGates F) : List (GenericReceipt F) :=
  let w := walkSteps r.steps ⟨0, none, []⟩
  match w.pending with
  | none => w.receipts
  | some g => w.receipts ++ [⟨g, w.row, 0⟩]

section Walk

variable [Field F] [DecidableEq F]

omit [Field F] [DecidableEq F] in
private theorem located_packed (q g : GenericPlonkConstraint F) (body : List (KimchiRow F)) :
    GenericReceipt.Located (body ++ [emitDoubleGateRow q g]) ⟨g, body.length, 0⟩ ∧
      GenericReceipt.Located (body ++ [emitDoubleGateRow q g]) ⟨q, body.length, 1⟩ := by
  have hrow : (body ++ [emitDoubleGateRow q g])[body.length]? = some (emitDoubleGateRow q g) := by
    rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
    rfl
  exact ⟨⟨emitDoubleGateRow q g, hrow, rfl, rfl, rfl⟩, ⟨emitDoubleGateRow q g, hrow, rfl, rfl, rfl⟩⟩

/-- One faithful event's effect on the queue and the rows: an event queuing an equation batches
it, any other leaves them. -/
theorem replayEvent_queue (s : BuilderReductionState F) (e : ReductionEvent F)
    (hf : OutcomesFaithful s [e]) :
    (replayEvent s e).aux.queuedGenericGate =
        (match e.queued? with
          | none => s.aux.queuedGenericGate
          | some g =>
            match s.aux.queuedGenericGate with
            | none => some g
            | some _ => none) ∧
      (replayEvent s e).constraints =
        (match e.queued? with
          | none => s.constraints
          | some g =>
            match s.aux.queuedGenericGate with
            | none => s.constraints
            | some q => emitDoubleGateRow q g :: s.constraints) := by
  cases e with
  | alloc v ex =>
    show ((createInternalVariable ex : PlonkBuilder F Variable) s).2.aux.queuedGenericGate = _ ∧
      ((createInternalVariable ex : PlonkBuilder F Variable) s).2.constraints = _
    rw [createInternalVariable_apply]
    exact ⟨rfl, rfl⟩
  | generic g =>
    show ((addGenericPlonkConstraint g : PlonkBuilder F Unit) s).2.aux.queuedGenericGate = _ ∧
      ((addGenericPlonkConstraint g : PlonkBuilder F Unit) s).2.constraints = _
    rw [addGenericPlonkConstraint_apply]
    cases s.aux.queuedGenericGate <;> exact ⟨rfl, rfl⟩
  | equal c o =>
    have ho : o = outcomeOf c s.aux.wireState.cachedConstants := hf.1
    rw [replayEvent_equal s c ho]
    cases o with
    | merge l r => exact ⟨rfl, rfl⟩
    | cached l v k => exact ⟨rfl, rfl⟩
    | trivial => exact ⟨rfl, rfl⟩
    | row g =>
      show ((addGenericPlonkConstraint g : PlonkBuilder F Unit) s).2.aux.queuedGenericGate = _ ∧
        ((addGenericPlonkConstraint g : PlonkBuilder F Unit) s).2.constraints = _
      rw [addGenericPlonkConstraint_apply]
      cases s.aux.queuedGenericGate <;> exact ⟨rfl, rfl⟩
    | pinned v k g =>
      show ((addGenericPlonkConstraint g : PlonkBuilder F Unit) s).2.aux.queuedGenericGate = _ ∧
        ((addGenericPlonkConstraint g : PlonkBuilder F Unit) s).2.constraints = _
      rw [addGenericPlonkConstraint_apply]
      cases s.aux.queuedGenericGate <;> exact ⟨rfl, rfl⟩

/-- Walking faithful events from a state agreeing with the walk's start: the walk ends
tracking the replay's queue and row count, every receipt is located in the replayed rows,
earlier receipts persist, and every queued equation is receipted or still waiting. -/
private theorem walkEvents_spec :
    ∀ (es : List (ReductionEvent F)) (w : Walk F) (s : BuilderReductionState F)
      (pre : List (KimchiRow F)),
      OutcomesFaithful s es →
      w.pending = s.aux.queuedGenericGate →
      w.row = pre.length + s.constraints.length →
      (∀ rc ∈ w.receipts, rc.Located (pre ++ s.constraints.reverse)) →
      (walkEvents es w).pending = (replay s es).aux.queuedGenericGate ∧
        (walkEvents es w).row = pre.length + (replay s es).constraints.length ∧
        (∀ rc ∈ (walkEvents es w).receipts,
          rc.Located (pre ++ (replay s es).constraints.reverse)) ∧
        (∀ rc ∈ w.receipts, rc ∈ (walkEvents es w).receipts) ∧
        (∀ g, ((∃ e ∈ es, e.queued? = some g) ∨ w.pending = some g) →
          (∃ rc ∈ (walkEvents es w).receipts, rc.gate = g) ∨
            (walkEvents es w).pending = some g)
  | [], w, s, pre, _, hp, hr, hl => by
    refine ⟨hp, hr, hl, fun _ h => h, fun g hg => ?_⟩
    simp only [List.not_mem_nil, false_and, exists_false, false_or] at hg
    exact Or.inr hg
  | e :: es, w, s, pre, hf, hp, hr, hl => by
    obtain ⟨hf1, hf2⟩ := outcomesFaithful_cons hf
    obtain ⟨hq, hc⟩ := replayEvent_queue s e hf1
    have hstep : replay s (e :: es) = replay (replayEvent s e) es := rfl
    rw [hstep]
    cases hqe : e.queued? with
    | none =>
      rw [hqe] at hq hc
      simp only at hq hc
      simp only [walkEvents, hqe]
      obtain ⟨h1, h2, h3, h4, h5⟩ := walkEvents_spec es w (replayEvent s e) pre hf2
        (by rw [hq]; exact hp) (by rw [hc]; exact hr) (by rw [hc]; exact hl)
      refine ⟨h1, h2, h3, h4, fun g hg => ?_⟩
      rcases hg with ⟨e', he', hge⟩ | hg
      · rcases List.mem_cons.mp he' with rfl | he'
        · rw [hqe] at hge
          exact absurd hge (by simp)
        · exact h5 g (Or.inl ⟨e', he', hge⟩)
      · exact h5 g (Or.inr hg)
    | some g =>
      rw [hqe, ← hp] at hq hc
      simp only [walkEvents, hqe]
      cases hpend : w.pending with
      | none =>
        simp only [hpend] at hq hc
        obtain ⟨h1, h2, h3, h4, h5⟩ := walkEvents_spec es { w with pending := some g }
          (replayEvent s e) pre hf2 (by rw [hq]) (by rw [hc]; exact hr) (by rw [hc]; exact hl)
        refine ⟨h1, h2, h3, h4, fun g' hg => ?_⟩
        rcases hg with ⟨e', he', hge⟩ | hg
        · rcases List.mem_cons.mp he' with rfl | he'
          · rw [hqe] at hge
            cases hge
            exact h5 g (Or.inr rfl)
          · exact h5 g' (Or.inl ⟨e', he', hge⟩)
        · cases hg
      | some q =>
        simp only [hpend] at hq hc
        have hloc := located_packed q g (pre ++ s.constraints.reverse)
        obtain ⟨h1, h2, h3, h4, h5⟩ := walkEvents_spec es
          ⟨w.row + 1, none, w.receipts ++ [⟨g, w.row, 0⟩, ⟨q, w.row, 1⟩]⟩ (replayEvent s e) pre
          hf2 (by rw [hq]) (by rw [hc]; simp only [List.length_cons]; omega)
          (by
            intro rc hrc
            rw [hc]
            simp only [List.reverse_cons, ← List.append_assoc]
            simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hrc
            rcases hrc with hrc | rfl | rfl
            · exact (hl rc hrc).append _
            · rw [hr]
              simpa [List.length_append, List.length_reverse] using hloc.1
            · rw [hr]
              simpa [List.length_append, List.length_reverse] using hloc.2)
        refine ⟨h1, h2, h3, fun rc hrc => h4 rc (by simp [hrc]), fun g' hg => ?_⟩
        rcases hg with ⟨e', he', hge⟩ | hg
        · rcases List.mem_cons.mp he' with rfl | he'
          · rw [hqe] at hge
            cases hge
            exact Or.inl ⟨⟨g, w.row, 0⟩, h4 _ (by simp), rfl⟩
          · exact h5 g' (Or.inl ⟨e', he', hge⟩)
        · cases hg
          exact Or.inl ⟨⟨q, w.row, 1⟩, h4 _ (by simp), rfl⟩

/-- Walking the recorded fold from a state agreeing with its start: the walk ends tracking the
fold's queue and row count, every receipt is located in its body rows, earlier receipts
persist, and every queued equation of every step is receipted or still waiting. -/
private theorem walkSteps_fold :
    ∀ (source : List (KimchiConstraint F)) (nv : Variable) (aux : AuxState F) (w : Walk F)
      (pre : List (KimchiRow F)),
      w.pending = aux.queuedGenericGate →
      w.row = pre.length →
      (∀ rc ∈ w.receipts, rc.Located pre) →
      (walkSteps (recordGates source nv aux).steps w).pending =
          (recordGates source nv aux).aux.queuedGenericGate ∧
        (walkSteps (recordGates source nv aux).steps w).row =
          pre.length + (recordGates source nv aux).bodyRows.length ∧
        (∀ rc ∈ (walkSteps (recordGates source nv aux).steps w).receipts,
          rc.Located (pre ++ (recordGates source nv aux).bodyRows)) ∧
        (∀ rc ∈ w.receipts, rc ∈ (walkSteps (recordGates source nv aux).steps w).receipts) ∧
        (∀ s ∈ (recordGates source nv aux).steps, ∀ g, (∃ e ∈ s.events, e.queued? = some g) →
          (∃ rc ∈ (walkSteps (recordGates source nv aux).steps w).receipts, rc.gate = g) ∨
            (walkSteps (recordGates source nv aux).steps w).pending = some g) ∧
        (∀ g, w.pending = some g →
          (∃ rc ∈ (walkSteps (recordGates source nv aux).steps w).receipts, rc.gate = g) ∨
            (walkSteps (recordGates source nv aux).steps w).pending = some g)
  | [], nv, aux, w, pre, hp, hr, hl => by
    simp only [recordGates, walkSteps]
    refine ⟨hp, ?_, ?_, fun _ h => h, fun _ h => by simp [recordGates] at h, fun _ h => Or.inr h⟩
    · simp [RecordedGates.bodyRows, hr]
    · simpa [RecordedGates.bodyRows] using hl
  | con :: cons, nv, aux, w, pre, hp, hr, hl => by
    have hrep := record_constraint_replays nv aux con
    simp only [RecordedReduction.finish] at hrep
    have hrows := congrArg BuilderReductionState.constraints hrep
    have haux := congrArg BuilderReductionState.aux hrep
    simp only at hrows haux
    obtain ⟨h1, h2, h3, h4, h5⟩ := walkEvents_spec _ w ⟨[], nv, aux⟩ pre
      (record_constraint_decides nv aux con) hp (by simpa using hr) (by simpa using hl)
    rw [← hrows, List.length_reverse, List.length_map] at h2
    rw [← hrows, List.reverse_reverse] at h3
    rw [← haux] at h1
    have hsteps : (recordGates (con :: cons) nv aux).steps =
        (⟨(recordReduction nv aux con.reduce).rows, (recordReduction nv aux con.reduce).result,
          (recordReduction nv aux con.reduce).events⟩ : RecordedStep F) ::
          (recordGates cons (recordReduction nv aux con.reduce).nextVariable
            (recordReduction nv aux con.reduce).aux).steps := rfl
    rw [hsteps]
    simp only [walkSteps]
    obtain ⟨g1, g2, g3, g4, g5, g6⟩ := walkSteps_fold cons _ _
      { walkEvents (recordReduction nv aux con.reduce).events w with
        row := (walkEvents (recordReduction nv aux con.reduce).events w).row +
          (⟨(recordReduction nv aux con.reduce).rows, (recordReduction nv aux con.reduce).result,
            (recordReduction nv aux con.reduce).events⟩ : RecordedStep F).gateRows.length }
      (pre ++ (⟨(recordReduction nv aux con.reduce).rows,
        (recordReduction nv aux con.reduce).result,
        (recordReduction nv aux con.reduce).events⟩ : RecordedStep F).bodyRows) h1
      (by simp only [List.length_append, RecordedStep.bodyRows, List.length_map]; omega)
      (by
        intro rc hrc
        simpa [RecordedStep.bodyRows, ← List.append_assoc] using (h3 rc hrc).append _)
    refine ⟨g1, ?_, ?_, fun rc hrc => g4 rc (h4 rc hrc), ?_, ?_⟩
    · simp only [recordGates, RecordedGates.bodyRows, List.flatMap_cons, List.length_append]
        at g2 ⊢
      omega
    · simpa [recordGates, RecordedGates.bodyRows, List.flatMap_cons, List.append_assoc] using g3
    · intro s hs g hg
      simp only [recordGates, List.mem_cons] at hs
      rcases hs with rfl | hs
      · rcases h5 g (Or.inl hg) with ⟨rc, hrc, hrcg⟩ | hpend
        · exact Or.inl ⟨rc, g4 rc hrc, hrcg⟩
        · exact g6 g hpend
      · exact g5 s hs g hg
    · intro g hg
      rcases h5 g (Or.inr hg) with ⟨rc, hrc, hrcg⟩ | hpend
      · exact Or.inl ⟨rc, g4 rc hrc, hrcg⟩
      · exact g6 g hpend

/-- Every receipt of the recorded lowering of a constraint list, from an empty queue, is
located in its rows with the final flush. -/
theorem receipts_located (source : List (KimchiConstraint F)) (nv : Variable)
    (aux : AuxState F) (hq : aux.queuedGenericGate = none) :
    ∀ rc ∈ receipts (recordGates source nv aux),
      rc.Located (recordGates source nv aux).allRows := by
  obtain ⟨h1, h2, h3, -⟩ := walkSteps_fold source nv aux ⟨0, none, []⟩ [] (by simpa using hq.symm)
    rfl (fun _ h => (List.not_mem_nil h).elim)
  simp only [List.nil_append, List.length_nil, Nat.zero_add] at h2 h3
  simp only [receipts, RecordedGates.allRows, ← h1]
  intro rc hrc
  cases hpend : (walkSteps (recordGates source nv aux).steps ⟨0, none, []⟩).pending with
  | none =>
    rw [hpend] at hrc
    exact (h3 rc hrc).append _
  | some g =>
    rw [hpend] at hrc
    simp only [List.mem_append, List.mem_singleton] at hrc
    rcases hrc with hrc | rfl
    · exact (h3 rc hrc).append _
    · refine ⟨{ kind := .generic
                vars := ⟨⟨[g.vl, g.vr, g.vo] ++ List.replicate 12 none⟩, by simp⟩
                coeffs := constraintToCoeffs g }, ?_, rfl, rfl, rfl⟩
      rw [h2, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
      rfl

/-- Every queued equation of the recorded lowering of a constraint list has a receipt. -/
theorem receipts_complete (source : List (KimchiConstraint F)) (nv : Variable)
    (aux : AuxState F) (hq : aux.queuedGenericGate = none) :
    ∀ s ∈ (recordGates source nv aux).steps, ∀ g, (∃ e ∈ s.events, e.queued? = some g) →
      ∃ rc ∈ receipts (recordGates source nv aux), rc.gate = g := by
  obtain ⟨-, -, -, -, h5, -⟩ := walkSteps_fold source nv aux ⟨0, none, []⟩ []
    (by simpa using hq.symm) rfl (fun _ h => (List.not_mem_nil h).elim)
  intro s hs g hg
  simp only [receipts]
  rcases h5 s hs g hg with ⟨rc, hrc, hrcg⟩ | hpend
  · refine ⟨rc, ?_, hrcg⟩
    cases (walkSteps (recordGates source nv aux).steps ⟨0, none, []⟩).pending <;> simp [hrc]
  · rw [hpend]
    exact ⟨⟨g, (walkSteps (recordGates source nv aux).steps ⟨0, none, []⟩).row, 0⟩, by simp, rfl⟩

end Walk

/-! ## Packing -/

/-- A generic constraint's absent cells carry no coefficient: an arbitrary table's value in
such a cell is irrelevant to the equation. -/
def GenericPlonkConstraint.AbsentZero (g : GenericPlonkConstraint F) [Zero F] : Prop :=
  (g.vl = none → g.cl = 0 ∧ g.m = 0) ∧ (g.vr = none → g.cr = 0 ∧ g.m = 0) ∧
    (g.vo = none → g.co = 0)

section Packing

variable [Field F] [DecidableEq F]

/-- The generic gate's row at a body row: its coefficients zero-extended, the cells from the
table. -/
def genericAt (row : KimchiRow F) (w : Fin wCols → F) : Kimchi.Gate.Generic F :=
  ⟨fun c => row.coeffs.getD c.val 0, w⟩

omit [DecidableEq F] in
/-- One generic equation read at a valuation, its cells read as given values that agree with
the valuation where the cell is present; an absent cell's value drops out with its zero
coefficient. -/
private theorem genericValue_eq (gate : GenericPlonkConstraint F) (habsent : gate.AbsentZero)
    (V : Valuation F) (a b c : F) (ha : ∀ v, gate.vl = some v → a = V v)
    (hb : ∀ v, gate.vr = some v → b = V v) (hc : ∀ v, gate.vo = some v → c = V v) :
    genericValue V gate = gate.cl * a + gate.cr * b + gate.co * c + gate.m * (a * b) + gate.c := by
  obtain ⟨hl, hr, ho⟩ := habsent
  simp only [genericValue]
  rcases hvl : gate.vl with _ | vl <;> rcases hvr : gate.vr with _ | vr <;>
    rcases hvo : gate.vo with _ | vo
  · simp [(hl hvl).1, (hl hvl).2, (hr hvr).1, ho hvo]
  · simp [(hl hvl).1, (hl hvl).2, (hr hvr).1, hc vo hvo]
  · simp [(hl hvl).1, (hl hvl).2, hb vr hvr, ho hvo]
  · simp [(hl hvl).1, (hl hvl).2, hb vr hvr, hc vo hvo]
  · simp [ha vl hvl, (hr hvr).1, (hr hvr).2, ho hvo]
  · simp [ha vl hvl, (hr hvr).1, (hr hvr).2, hc vo hvo]
  · simp [ha vl hvl, hb vr hvr, ho hvo]
  · simp [ha vl hvl, hb vr hvr, hc vo hvo]

omit [DecidableEq F] in
/-- At a located receipt, a generic row holding at cells that agree with a valuation on the
labelled cells makes the receipt's equation hold at the valuation, when the constraint's
absent cells carry no coefficient. -/
theorem genericValue_of_located {body : List (KimchiRow F)} {rc : GenericReceipt F}
    (hloc : rc.Located body) {row : KimchiRow F} (hrow : body[rc.row]? = some row)
    (w : Fin wCols → F) (V : Valuation F)
    (hw : ∀ (i : Fin wCols) (v : Variable), row.vars[i] = some v → w i = V v)
    (habsent : rc.gate.AbsentZero) (hholds : (genericAt row w).Holds) :
    genericValue V rc.gate = 0 := by
  obtain ⟨row', hrow', -, hcells, hcoeffs⟩ := hloc
  rw [hrow, Option.some.injEq] at hrow'
  subst hrow'
  obtain ⟨gate, r, half⟩ := rc
  simp only at hcells hcoeffs habsent ⊢
  have hc : ∀ k, k < 5 → row.coeffs.getD (5 * half.val + k) 0 =
      [gate.cl, gate.cr, gate.co, gate.m, gate.c].getD k 0 := by
    intro k hk
    have := congrArg (fun l => l[k]?) hcoeffs
    simp only [halfCoeffs, List.getElem?_take, List.getElem?_drop, hk, ite_true] at this
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, this]
  rw [Kimchi.Gate.Generic.holds_iff] at hholds
  simp only [genericAt] at hholds
  simp only [halfCells, Prod.mk.injEq] at hcells
  obtain ⟨h0, h1, h2⟩ := hcells
  fin_cases half
  · simp only [Nat.mul_zero, Nat.zero_add] at hc h0 h1 h2
    have hh : row.coeffs.getD 0 0 * w 0 + row.coeffs.getD 1 0 * w 1 + row.coeffs.getD 2 0 * w 2 +
        row.coeffs.getD 3 0 * (w 0 * w 1) + row.coeffs.getD 4 0 = 0 := hholds.1
    rw [genericValue_eq gate habsent V (w 0) (w 1) (w 2)
      (fun v hv => hw 0 v (h0.trans hv)) (fun v hv => hw 1 v (h1.trans hv))
      (fun v hv => hw 2 v (h2.trans hv))]
    have e0 : row.coeffs.getD 0 0 = gate.cl := by simpa using hc 0 (by omega)
    have e1 : row.coeffs.getD 1 0 = gate.cr := by simpa using hc 1 (by omega)
    have e2 : row.coeffs.getD 2 0 = gate.co := by simpa using hc 2 (by omega)
    have e3 : row.coeffs.getD 3 0 = gate.m := by simpa using hc 3 (by omega)
    have e4 : row.coeffs.getD 4 0 = gate.c := by simpa using hc 4 (by omega)
    rw [e0, e1, e2, e3, e4] at hh
    exact hh
  · simp only [Nat.mul_one] at hc h0 h1 h2
    have hh : row.coeffs.getD 5 0 * w 3 + row.coeffs.getD 6 0 * w 4 + row.coeffs.getD 7 0 * w 5 +
        row.coeffs.getD 8 0 * (w 3 * w 4) + row.coeffs.getD 9 0 = 0 := hholds.2
    rw [genericValue_eq gate habsent V (w 3) (w 4) (w 5)
      (fun v hv => hw 3 v (h0.trans hv)) (fun v hv => hw 4 v (h1.trans hv))
      (fun v hv => hw 5 v (h2.trans hv))]
    have e0 : row.coeffs.getD 5 0 = gate.cl := by simpa using hc 0 (by omega)
    have e1 : row.coeffs.getD 6 0 = gate.cr := by simpa using hc 1 (by omega)
    have e2 : row.coeffs.getD 7 0 = gate.co := by simpa using hc 2 (by omega)
    have e3 : row.coeffs.getD 8 0 = gate.m := by simpa using hc 3 (by omega)
    have e4 : row.coeffs.getD 9 0 = gate.c := by simpa using hc 4 (by omega)
    rw [e0, e1, e2, e3, e4] at hh
    exact hh

end Packing

end Snarky.Kimchi
