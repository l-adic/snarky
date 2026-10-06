import Snarky.Kimchi.Backend.RowCorrespondence
import Snarky.Kimchi.Backend.TraceSemantics
import Kimchi.Gate.Generic
import Kimchi.Columns

/-!
# Generic receipts

Where each generic event's equation landed. A Boolean's equation is not among its own step's
rows: it enters the batching queue and leaves it packed behind the next generic equation,
wherever that is, or alone at the final flush. The walk here replays the queue over the
recorded events, step by step with each step's gate rows between, and issues every generic
event a receipt: the body row holding its equation and the half of that row. The first half
is the row's cells `0` to `2` with coefficients `0` to `4`, the second its cells `3` to `5`
with coefficients `5` to `9`; a packed row holds the incoming equation first.

The walk tracks the builder's actual queue by equality, so its receipts are proved located
for the recorded lowering of any constraint list whose events are all generic: the cells
and coefficients at a receipt are exactly its constraint's. It rejects an allocation or
equality event rather than skipping its obligation; their receipts are later work.

## Main definitions

- `GenericReceipt`, `GenericReceipt.Located`: a receipt and what it claims of the body rows.
- `receipts`: every generic event's receipt, or `none` on an unsupported event.
- `RecordedGates.allRows`: the body rows with the final flush's row.

## Main results

- `receipts_located`: every receipt is located in the lowering's rows.
- `receipts_complete`: every generic event has a receipt.
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

private theorem GenericReceipt.Located.append {body : List (KimchiRow F)} {rc : GenericReceipt F}
    (h : rc.Located body) (more : List (KimchiRow F)) : rc.Located (body ++ more) := by
  obtain ⟨row, hrow, h⟩ := h
  exact ⟨row, by rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp hrow).1]; exact hrow,
    h⟩

/-- The body rows with the final flush's row, if any. -/
def RecordedGates.allRows [Zero F] (r : RecordedGates F) : List (KimchiRow F) :=
  r.bodyRows ++ ((finalizeGateQueue r.aux.queuedGenericGate).map (·.row)).toList

/-! ## The walk -/

/-- The walk's state: the next body row, the queued constraint, and the receipts so far. -/
private structure Walk (F : Type) where
  row : Nat
  pending : Option (GenericPlonkConstraint F)
  receipts : List (GenericReceipt F)

/-- The builder's batching over one step's events, issuing receipts: an incoming constraint
packs in front of the queued one into the next row. Any other event is rejected. -/
private def walkEvents : List (ReductionEvent F) → Walk F → Option (Walk F)
  | [], w => some w
  | .generic g :: es, w =>
    match w.pending with
    | none => walkEvents es { w with pending := some g }
    | some q => walkEvents es ⟨w.row + 1, none, w.receipts ++ [⟨g, w.row, 0⟩, ⟨q, w.row, 1⟩]⟩
  | _ :: _, _ => none

/-- The walk over the steps: each step's events, then its gate's rows. -/
private def walkSteps : List (RecordedStep F) → Walk F → Option (Walk F)
  | [], w => some w
  | s :: rest, w => do
    let w ← walkEvents s.events w
    walkSteps rest { w with row := w.row + s.gateRows.length }

/-- Every generic event's receipt, the final flush receiving the queued constraint; `none`
when an allocation or equality event occurs. -/
def receipts (r : RecordedGates F) : Option (List (GenericReceipt F)) := do
  let w ← walkSteps r.steps ⟨0, none, []⟩
  return match w.pending with
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

/-- Walking a step's events from a state agreeing with the builder's: the walk tracks the
replayed queue and row count, every receipt is located, earlier receipts survive, and every
generic event seen is receipted or queued. -/
private theorem walkEvents_spec :
    ∀ (es : List (ReductionEvent F)) (w w' : Walk F) (s : BuilderReductionState F)
      (pre : List (KimchiRow F)),
      walkEvents es w = some w' →
      w.pending = s.aux.queuedGenericGate →
      w.row = pre.length + s.constraints.length →
      (∀ rc ∈ w.receipts, rc.Located (pre ++ s.constraints.reverse)) →
      w'.pending = (replay s es).aux.queuedGenericGate ∧
        w'.row = pre.length + (replay s es).constraints.length ∧
        (∀ rc ∈ w'.receipts, rc.Located (pre ++ (replay s es).constraints.reverse)) ∧
        (∀ rc ∈ w.receipts, rc ∈ w'.receipts) ∧
        (∀ g, (.generic g ∈ es ∨ w.pending = some g) →
          (∃ rc ∈ w'.receipts, rc.gate = g) ∨ w'.pending = some g)
  | [], w, w', s, pre, hw, hp, hr, hl => by
    simp only [walkEvents, Option.some.injEq] at hw
    subst hw
    refine ⟨hp, hr, hl, fun _ h => h, fun g hg => ?_⟩
    simp only [List.not_mem_nil, false_or] at hg
    exact Or.inr hg
  | .alloc _ _ :: _, _, _, _, _, hw, _, _, _ => by simp [walkEvents] at hw
  | .equal _ :: _, _, _, _, _, hw, _, _, _ => by simp [walkEvents] at hw
  | .generic g :: es, w, w', s, pre, hw, hp, hr, hl => by
    have hstep : replay s (.generic g :: es) =
        replay ((addGenericPlonkConstraint g : PlonkBuilder F Unit) s).2 es := rfl
    rw [hstep, addGenericPlonkConstraint_apply]
    simp only [walkEvents] at hw
    rw [← hp]
    cases hpend : w.pending with
    | none =>
      rw [hpend] at hw
      simp only
      obtain ⟨h1, h2, h3, h4, h5⟩ := walkEvents_spec es _ w'
        { s with aux.queuedGenericGate := some g } pre hw rfl hr hl
      refine ⟨h1, h2, h3, h4, fun g' hg => ?_⟩
      rcases hg with hg | hg
      · rcases List.mem_cons.mp hg with hg | hg
        · cases hg
          exact h5 g (Or.inr rfl)
        · exact h5 g' (Or.inl hg)
      · cases hg
    | some q =>
      rw [hpend] at hw
      simp only
      have hloc := located_packed q g (pre ++ s.constraints.reverse)
      obtain ⟨h1, h2, h3, h4, h5⟩ := walkEvents_spec es _ w'
        { s with constraints := emitDoubleGateRow q g :: s.constraints,
                 aux.queuedGenericGate := none } pre hw rfl
        (by simp only [List.length_cons]; omega)
        (by
          intro rc hrc
          simp only [List.reverse_cons, ← List.append_assoc]
          simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hrc
          rcases hrc with hrc | rfl | rfl
          · exact (hl rc hrc).append _
          · rw [hr]
            simpa [List.length_append, List.length_reverse] using hloc.1
          · rw [hr]
            simpa [List.length_append, List.length_reverse] using hloc.2)
      refine ⟨h1, h2, h3, fun rc hrc => h4 rc (by simp [hrc]), fun g' hg => ?_⟩
      rcases hg with hg | hg
      · rcases List.mem_cons.mp hg with hg | hg
        · cases hg
          exact Or.inl ⟨⟨g, w.row, 0⟩, h4 _ (by simp), rfl⟩
        · exact h5 g' (Or.inl hg)
      · cases hg
        exact Or.inl ⟨⟨q, w.row, 1⟩, h4 _ (by simp), rfl⟩

/-- Walking the recorded fold from a state agreeing with its start: the walk ends tracking the
fold's queue and row count, every receipt is located in its body rows, and every generic
event of every step is receipted or queued. -/
private theorem walkSteps_fold :
    ∀ (source : List (KimchiConstraint F)) (nv : Variable) (aux : AuxState F) (w w' : Walk F)
      (pre : List (KimchiRow F)),
      walkSteps (recordGates source nv aux).steps w = some w' →
      w.pending = aux.queuedGenericGate →
      w.row = pre.length →
      (∀ rc ∈ w.receipts, rc.Located pre) →
      w'.pending = (recordGates source nv aux).aux.queuedGenericGate ∧
        w'.row = pre.length + (recordGates source nv aux).bodyRows.length ∧
        (∀ rc ∈ w'.receipts, rc.Located (pre ++ (recordGates source nv aux).bodyRows)) ∧
        (∀ rc ∈ w.receipts, rc ∈ w'.receipts) ∧
        (∀ s ∈ (recordGates source nv aux).steps, ∀ g, .generic g ∈ s.events →
          (∃ rc ∈ w'.receipts, rc.gate = g) ∨ w'.pending = some g) ∧
        (∀ g, w.pending = some g → (∃ rc ∈ w'.receipts, rc.gate = g) ∨ w'.pending = some g)
  | [], nv, aux, w, w', pre, hw, hp, hr, hl => by
    simp only [recordGates, walkSteps, Option.some.injEq] at hw
    subst hw
    refine ⟨hp, ?_, ?_, fun _ h => h, fun _ h => by simp [recordGates] at h, fun _ h => Or.inr h⟩
    · simp [recordGates, RecordedGates.bodyRows, hr]
    · simpa [recordGates, RecordedGates.bodyRows] using hl
  | con :: cons, nv, aux, w, w', pre, hw, hp, hr, hl => by
    simp only [recordGates, walkSteps, Option.bind_eq_bind, Option.bind_eq_some_iff] at hw
    obtain ⟨w₁, hw₁, hw'⟩ := hw
    have hrep := record_constraint_replays nv aux con
    simp only [RecordedReduction.finish] at hrep
    have hrows := congrArg BuilderReductionState.constraints hrep
    have haux := congrArg BuilderReductionState.aux hrep
    simp only at hrows haux
    obtain ⟨h1, h2, h3, h4, h5⟩ := walkEvents_spec _ w w₁ ⟨[], nv, aux⟩ pre hw₁ hp
      (by simpa using hr) (by simpa using hl)
    rw [← hrows, List.length_reverse, List.length_map] at h2
    rw [← hrows, List.reverse_reverse] at h3
    rw [← haux] at h1
    obtain ⟨g1, g2, g3, g4, g5, g6⟩ := walkSteps_fold cons _ _ _ w'
      (pre ++ (⟨(recordReduction nv aux con.reduce).rows,
        (recordReduction nv aux con.reduce).result,
        (recordReduction nv aux con.reduce).events⟩ : RecordedStep F).bodyRows) hw' h1
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

/-- Every receipt of the recorded lowering of a constraint list is located in its rows. -/
theorem receipts_located (source : List (KimchiConstraint F)) (nv : Variable)
    (aux : AuxState F) (hq : aux.queuedGenericGate = none) (rs : List (GenericReceipt F))
    (h : receipts (recordGates source nv aux) = some rs) :
    ∀ rc ∈ rs, rc.Located (recordGates source nv aux).allRows := by
  simp only [receipts, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq] at h
  obtain ⟨w, hw, rfl⟩ := h
  obtain ⟨h1, h2, h3, -⟩ := walkSteps_fold source nv aux _ w [] hw (by simpa using hq.symm) rfl
    (fun _ h => (List.not_mem_nil h).elim)
  simp only [List.nil_append, List.length_nil, Nat.zero_add] at h2 h3
  simp only [RecordedGates.allRows, ← h1]
  intro rc hrc
  cases hpend : w.pending with
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

/-- Every generic event of the recorded lowering of a constraint list has a receipt. -/
theorem receipts_complete (source : List (KimchiConstraint F)) (nv : Variable)
    (aux : AuxState F) (hq : aux.queuedGenericGate = none) (rs : List (GenericReceipt F))
    (h : receipts (recordGates source nv aux) = some rs) :
    ∀ s ∈ (recordGates source nv aux).steps, ∀ g, .generic g ∈ s.events →
      ∃ rc ∈ rs, rc.gate = g := by
  simp only [receipts, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq] at h
  obtain ⟨w, hw, rfl⟩ := h
  obtain ⟨-, -, -, -, h5, -⟩ := walkSteps_fold source nv aux _ w [] hw (by simpa using hq.symm)
    rfl (fun _ h => (List.not_mem_nil h).elim)
  intro s hs g hg
  rcases h5 s hs g hg with ⟨rc, hrc, hrcg⟩ | hpend
  · refine ⟨rc, ?_, hrcg⟩
    cases w.pending <;> simp [hrc]
  · rw [hpend]
    exact ⟨⟨g, w.row, 0⟩, by simp, rfl⟩

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
