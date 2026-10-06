import Snarky.Kimchi.Backend.Trace
import Snarky.Kimchi.Backend.Compile

/-!
# The recorded lowering of a constraint list

The builder's fold over a constraint list, recorded: `recordGates` mirrors `reduceGates`
step for step and keeps each step's flushed rows, gate and events apart, and `recordBuilt`
mirrors `reduceBuilt` with the final flush. Erasing the events returns exactly the ordinary
fold, so every structural fact proved of the recorded steps is a fact about the lowering.

The body rows are the steps' rows in order, each step's flushed generic rows before its
gate's rows, then the final flush. `placements` locates every step in that list, and the
slice lemmas read a row at a located position as the step's own row, kind, labels and
coefficients included. Positions count body rows; the assembled table prepends the public
rows.

## Main definitions

- `RecordedStep`, `RecordedGates`, `recordGates`: the fold with its steps kept apart.
- `RecordedBuilt`, `recordBuilt`: the whole-circuit lowering beside its steps.
- `RowSpan`, `StepPlacement`, `RecordedGates.placements`: where each step's rows sit among the
  body rows.

## Main results

- `recordGates_erase`, `recordBuilt_erase`: the recorded folds erase to the ordinary ones.
- `recordBuilt_bodyRows`: the whole circuit's body rows are the steps' rows, then the flush.
- `RecordedGates.length_placements`, `bodyRows_placed`, `placements_genericRows_count`,
  `placements_customRows_count`, `placements_customRows_le`,
  `getElem_bodyRows_generic`, `getElem_bodyRows_gate`: a row at a step's located position is
  that step's flushed generic row or gate row.
-/

namespace Snarky.Kimchi

open Snarky

variable {F : Type}

/-! ## The recorded fold -/

/-- One source constraint's recorded step: the generic rows flushed while reducing it, its
gate, and its events. -/
structure RecordedStep (F : Type) where
  /-- The generic rows flushed while reducing the constraint, in emission order. -/
  rows : List (Rows F)
  /-- The constraint's gate. -/
  gate : KimchiGate F
  /-- The reduction's events, in execution order. -/
  events : List (ReductionEvent F)

/-- The gates a step contributes, as `reduceStep` orders them: the flushed rows, then the
gate. -/
def RecordedStep.gates (s : RecordedStep F) : List (KimchiGate F) :=
  s.rows.map .plonk ++ [s.gate]

/-- The rows of a step's gate. -/
def RecordedStep.gateRows (s : RecordedStep F) : List (KimchiRow F) :=
  toKimchiRows s.gate

/-- The body rows a step contributes: the flushed generic rows, then its gate's rows. -/
def RecordedStep.bodyRows (s : RecordedStep F) : List (KimchiRow F) :=
  s.rows.map (·.row) ++ s.gateRows

/-- A constraint list's recorded lowering: its steps in source order, and the counter and
auxiliary state handed back. -/
structure RecordedGates (F : Type) where
  /-- The steps, in source order. -/
  steps : List (RecordedStep F)
  /-- The counter handed back. -/
  nextVariable : Variable
  /-- The auxiliary state handed back. -/
  aux : AuxState F

/-- The emitted gates, in order. -/
def RecordedGates.gates (r : RecordedGates F) : List (KimchiGate F) :=
  r.steps.flatMap RecordedStep.gates

/-- The body rows before the final flush, in order. -/
def RecordedGates.bodyRows (r : RecordedGates F) : List (KimchiRow F) :=
  r.steps.flatMap RecordedStep.bodyRows

/-- Forget the events: the shape `reduceGates` returns. -/
def RecordedGates.erase (r : RecordedGates F) : List (KimchiGate F) × Variable × AuxState F :=
  (r.gates, r.nextVariable, r.aux)

/-- Packed rows' gates flatten to the rows. -/
private theorem flatMap_plonk_rows (rows : List (Rows F)) :
    (rows.map KimchiGate.plonk).flatMap (toKimchiRows (F := F)) = rows.map (·.row) := by
  induction rows with
  | nil => rfl
  | cons r rest ih =>
    simp only [List.map_cons, List.flatMap_cons, ih]
    rfl

/-- The rows of a step's gates are its body rows. -/
private theorem flatMap_gates_toKimchiRows (steps : List (RecordedStep F)) :
    (steps.flatMap RecordedStep.gates).flatMap (toKimchiRows (F := F)) =
      steps.flatMap RecordedStep.bodyRows := by
  induction steps with
  | nil => rfl
  | cons s rest ih =>
    simp only [List.flatMap_cons, List.flatMap_append, ih, RecordedStep.gates,
      RecordedStep.bodyRows, RecordedStep.gateRows, flatMap_plonk_rows, List.flatMap_nil,
      List.append_nil]

section Fold

variable [Field F] [DecidableEq F]

/-- Fold the recording reduction over a constraint list, one step per constraint. -/
def recordGates : List (KimchiConstraint F) → Variable → AuxState F → RecordedGates F
  | [], nv, aux => ⟨[], nv, aux⟩
  | con :: cons, nv, aux =>
    let red := recordReduction nv aux (KimchiConstraint.reduce con)
    let rest := recordGates cons red.nextVariable red.aux
    ⟨⟨red.rows, red.result, red.events⟩ :: rest.steps, rest.nextVariable, rest.aux⟩

/-- The recorded fold erases to the ordinary fold. -/
theorem recordGates_erase (source : List (KimchiConstraint F)) (nv : Variable)
    (aux : AuxState F) : (recordGates source nv aux).erase = reduceGates source nv aux := by
  induction source generalizing nv aux with
  | nil => rfl
  | cons con cons ih =>
    have h := record_constraint_erases nv aux con
    simp only [RecordedReduction.erase] at h
    have hres := congrArg Prod.fst h
    have hrows := congrArg (fun p => p.2.1) h
    have hnv := congrArg (fun p => p.2.2.1) h
    have haux := congrArg (fun p => p.2.2.2) h
    simp only at hres hrows hnv haux
    have ih' := ih (reduceAsBuilder nv aux con.reduce).2.2.1
      (reduceAsBuilder nv aux con.reduce).2.2.2
    simp only [RecordedGates.erase, RecordedGates.gates] at ih'
    have hg := congrArg Prod.fst ih'
    have hn := congrArg (fun p => p.2.1) ih'
    have ha := congrArg (fun p => p.2.2) ih'
    simp only at hg hn ha
    simp only [recordGates, RecordedGates.erase, RecordedGates.gates, RecordedStep.gates,
      List.flatMap_cons, reduceGates, reduceStep, hres, hrows, hnv, haux, hg, hn, ha,
      List.append_assoc]

/-- A built circuit's recorded lowering: the ordinary result with the final flush, beside
the recorded steps. -/
structure RecordedBuilt (F : Type) (α : Type) where
  /-- The lowering, as `reduceBuilt` returns it. -/
  built : KimchiBuilt F α
  /-- The recorded steps and the state they hand to the final flush. -/
  record : RecordedGates F

/-- A built circuit reduced to kimchi gates with its steps recorded: the recorded fold from
the build's counter, the odd queued constraint flushed into one more packed row. -/
def recordBuilt {α : Type} (built : Built (KimchiConstraint F) α) : RecordedBuilt F α :=
  let red := recordGates built.constraints built.nextVar initialAuxState
  let flush := (finalizeGateQueue red.aux.queuedGenericGate).map KimchiGate.plonk
  ⟨⟨built.result, red.gates ++ flush.toList, red.nextVariable,
    { red.aux with queuedGenericGate := none }⟩, red⟩

/-- The recorded whole-circuit lowering is the ordinary one. -/
theorem recordBuilt_erase {α : Type} (built : Built (KimchiConstraint F) α) :
    (recordBuilt built).built = reduceBuilt built := by
  have h := recordGates_erase built.constraints built.nextVar initialAuxState
  simp only [RecordedGates.erase] at h
  have hg := congrArg Prod.fst h
  have hn := congrArg (fun p => p.2.1) h
  have ha := congrArg (fun p => p.2.2) h
  simp only at hg hn ha
  simp only [recordBuilt, reduceBuilt, hg, hn, ha]

/-- The whole circuit's body rows: the steps' rows, then the final flush's row, if any. -/
theorem recordBuilt_bodyRows {α : Type} (built : Built (KimchiConstraint F) α) :
    (recordBuilt built).built.gates.flatMap (toKimchiRows (F := F)) =
      (recordBuilt built).record.bodyRows ++
        ((finalizeGateQueue (recordBuilt built).record.aux.queuedGenericGate).map (·.row)).toList
    := by
  simp only [recordBuilt, RecordedGates.gates, RecordedGates.bodyRows, List.flatMap_append,
    flatMap_gates_toKimchiRows]
  cases finalizeGateQueue
    ((recordGates built.constraints built.nextVar initialAuxState).aux.queuedGenericGate) <;> rfl

end Fold

/-! ## Placement -/

/-- A contiguous run of rows: the first row's position and the row count. -/
structure RowSpan where
  /-- The first row's position. -/
  first : Nat
  /-- The number of rows. -/
  count : Nat

/-- Where one step's rows sit among the body rows: the generic rows flushed while reducing
it, then its gate's rows, none for a `Basic` constraint. -/
structure StepPlacement where
  /-- The generic rows flushed while reducing the constraint. -/
  genericRows : RowSpan
  /-- The constraint's own gate rows. -/
  customRows : RowSpan

/-- A span contains a row position. -/
def RowSpan.Contains (sp : RowSpan) (k : Nat) : Prop :=
  sp.first ≤ k ∧ k < sp.first + sp.count

/-- Each step's placement, the first at `offset`, each next at the end of the one before. -/
private def placements : List (RecordedStep F) → Nat → List StepPlacement
  | [], _ => []
  | s :: rest, offset =>
    ⟨⟨offset, s.rows.length⟩, ⟨offset + s.rows.length, s.gateRows.length⟩⟩ ::
      placements rest (offset + s.bodyRows.length)

/-- A step's placement, from the start of the body rows. -/
def RecordedGates.placements (r : RecordedGates F) : List StepPlacement :=
  Snarky.Kimchi.placements r.steps 0

private theorem length_placements (steps : List (RecordedStep F)) (offset : Nat) :
    (placements steps offset).length = steps.length := by
  induction steps generalizing offset with
  | nil => rfl
  | cons s rest ih => simp [placements, ih]

/-- A step's generic rows start where the preceding steps' rows end. -/
private theorem placements_genericRows (steps : List (RecordedStep F)) (offset : Nat) (i : Nat)
    (hi : i < steps.length) :
    (placements steps offset)[i]'((length_placements steps offset).symm ▸ hi) =
      ⟨⟨offset + ((steps.take i).flatMap RecordedStep.bodyRows).length, steps[i].rows.length⟩,
       ⟨offset + ((steps.take i).flatMap RecordedStep.bodyRows).length + steps[i].rows.length,
        steps[i].gateRows.length⟩⟩ := by
  induction steps generalizing offset i with
  | nil => exact absurd hi (Nat.not_lt_zero _)
  | cons s rest ih =>
    cases i with
    | zero => simp [placements]
    | succ i =>
      simp only [placements, List.getElem_cons_succ, List.take_succ_cons, List.flatMap_cons,
        List.length_append]
      rw [ih (offset + s.bodyRows.length) i (Nat.lt_of_succ_lt_succ hi)]
      simp only [Nat.add_assoc]

/-- The body row at a position inside a step's rows is that step's row. -/
private theorem getElem_flatMap_bodyRows (steps : List (RecordedStep F)) (i : Nat)
    (hi : i < steps.length) (j : Nat) (hj : j < steps[i].bodyRows.length)
    (hk : ((steps.take i).flatMap RecordedStep.bodyRows).length + j <
      (steps.flatMap RecordedStep.bodyRows).length) :
    (steps.flatMap RecordedStep.bodyRows)[((steps.take i).flatMap RecordedStep.bodyRows).length + j]
      = steps[i].bodyRows[j] := by
  induction steps generalizing i with
  | nil => exact absurd hi (Nat.not_lt_zero _)
  | cons s rest ih =>
    cases i with
    | zero =>
      simp only [List.take_zero, List.flatMap_nil, List.length_nil, Nat.zero_add,
        List.flatMap_cons, List.getElem_cons_zero] at hk ⊢
      exact List.getElem_append_left (by simpa using hj)
    | succ i =>
      simp only [List.take_succ_cons, List.flatMap_cons, List.length_append,
        List.getElem_cons_succ] at hk hj ⊢
      rw [List.getElem_append_right (by omega)]
      have := ih i (Nat.lt_of_succ_lt_succ hi) hj (by omega)
      convert this using 2
      omega

/-- One placement per step. -/
theorem RecordedGates.length_placements (r : RecordedGates F) :
    r.placements.length = r.steps.length :=
  Snarky.Kimchi.length_placements r.steps 0

private theorem placements_count (steps : List (RecordedStep F)) (offset : Nat) (i : Nat)
    (hi : i < steps.length) :
    ((placements steps offset)[i]'((length_placements _ _).symm ▸ hi)).genericRows.count =
        steps[i].rows.length ∧
      ((placements steps offset)[i]'((length_placements _ _).symm ▸ hi)).customRows.count =
        steps[i].gateRows.length := by
  induction steps generalizing offset i with
  | nil => exact absurd hi (Nat.not_lt_zero _)
  | cons s rest ih =>
    cases i with
    | zero => exact ⟨rfl, rfl⟩
    | succ i => exact ih _ i (Nat.lt_of_succ_lt_succ hi)

/-- A step's generic span counts its flushed rows. -/
theorem placements_genericRows_count (r : RecordedGates F) (i : Nat) (hi : i < r.steps.length) :
    (r.placements[i]'((length_placements _ _).symm ▸ hi)).genericRows.count =
      r.steps[i].rows.length :=
  (placements_count r.steps 0 i hi).1

/-- A step's gate span counts its gate rows. -/
theorem placements_customRows_count (r : RecordedGates F) (i : Nat) (hi : i < r.steps.length) :
    (r.placements[i]'((length_placements _ _).symm ▸ hi)).customRows.count =
      r.steps[i].gateRows.length :=
  (placements_count r.steps 0 i hi).2

private theorem placements_le (steps : List (RecordedStep F)) (offset : Nat) (i : Nat)
    (hi : i < steps.length) :
    ((placements steps offset)[i]'((length_placements _ _).symm ▸ hi)).customRows.first +
        ((placements steps offset)[i]'((length_placements _ _).symm ▸ hi)).customRows.count ≤
      offset + (steps.flatMap RecordedStep.bodyRows).length := by
  induction steps generalizing offset i with
  | nil => exact absurd hi (Nat.not_lt_zero _)
  | cons s rest ih =>
    simp only [List.flatMap_cons, List.length_append]
    cases i with
    | zero =>
      simp only [placements, List.getElem_cons_zero, RecordedStep.bodyRows, List.length_append,
        List.length_map]
      omega
    | succ i =>
      have := ih (offset + s.bodyRows.length) i (Nat.lt_of_succ_lt_succ hi)
      simp only [placements, List.getElem_cons_succ]
      omega

/-- A step's gate span ends within the body rows. -/
theorem placements_customRows_le (r : RecordedGates F) (i : Nat) (hi : i < r.steps.length) :
    (r.placements[i]'((length_placements _ _).symm ▸ hi)).customRows.first +
        (r.placements[i]'((length_placements _ _).symm ▸ hi)).customRows.count ≤
      r.bodyRows.length := by
  have := placements_le r.steps 0 i hi
  simpa only [RecordedGates.placements, RecordedGates.bodyRows, Nat.zero_add] using this

private theorem placed (steps : List (RecordedStep F)) (offset k : Nat)
    (hk : k < (steps.flatMap RecordedStep.bodyRows).length) :
    ∃ (i : Nat) (hi : i < steps.length),
      ((placements steps offset)[i]'((length_placements _ _).symm ▸ hi)).genericRows.Contains
          (offset + k) ∨
        ((placements steps offset)[i]'((length_placements _ _).symm ▸ hi)).customRows.Contains
          (offset + k) := by
  induction steps generalizing offset k with
  | nil => simp at hk
  | cons s rest ih =>
    simp only [List.flatMap_cons, List.length_append] at hk
    by_cases h : k < s.bodyRows.length
    · refine ⟨0, Nat.succ_pos _, ?_⟩
      simp only [placements, List.getElem_cons_zero, RowSpan.Contains]
      simp only [RecordedStep.bodyRows, List.length_append, List.length_map] at h
      by_cases h2 : k < s.rows.length
      · exact Or.inl ⟨by omega, by omega⟩
      · exact Or.inr ⟨by omega, by omega⟩
    · obtain ⟨i, hi, hc⟩ := ih (offset + s.bodyRows.length) (k - s.bodyRows.length) (by omega)
      refine ⟨i + 1, Nat.succ_lt_succ hi, ?_⟩
      simp only [placements, List.getElem_cons_succ]
      have e : offset + s.bodyRows.length + (k - s.bodyRows.length) = offset + k := by omega
      rw [e] at hc
      exact hc

/-- Every body row lies in one step's placement: in its generic span or its gate span. -/
theorem bodyRows_placed (r : RecordedGates F) (k : Nat) (hk : k < r.bodyRows.length) :
    ∃ (i : Nat) (hi : i < r.steps.length),
      (r.placements[i]'((length_placements _ _).symm ▸ hi)).genericRows.Contains k ∨
        (r.placements[i]'((length_placements _ _).symm ▸ hi)).customRows.Contains k := by
  have := placed r.steps 0 k hk
  simpa only [RecordedGates.placements, Nat.zero_add] using this

/-- A row at a position of a step's generic span is that step's flushed generic row. -/
theorem getElem_bodyRows_generic (r : RecordedGates F) (i : Nat) (hi : i < r.steps.length)
    (j : Nat) (hj : j < r.steps[i].rows.length)
    (hk : (r.placements[i]'((length_placements _ _).symm ▸ hi)).genericRows.first + j <
      r.bodyRows.length) :
    r.bodyRows[(r.placements[i]'((length_placements _ _).symm ▸ hi)).genericRows.first + j] =
      r.steps[i].rows[j].row := by
  have hp := placements_genericRows r.steps 0 i hi
  simp only [RecordedGates.placements, RecordedGates.bodyRows] at hp hk ⊢
  simp only [hp, Nat.zero_add] at hk ⊢
  rw [getElem_flatMap_bodyRows r.steps i hi j
    (by simp only [RecordedStep.bodyRows, List.length_append, List.length_map]; omega) hk]
  simp only [RecordedStep.bodyRows]
  rw [List.getElem_append_left (by simpa using hj)]
  simp

/-- A row at a position of a step's gate span is that step's gate row. -/
theorem getElem_bodyRows_gate (r : RecordedGates F) (i : Nat) (hi : i < r.steps.length)
    (j : Nat) (hj : j < r.steps[i].gateRows.length)
    (hk : (r.placements[i]'((length_placements _ _).symm ▸ hi)).customRows.first + j <
      r.bodyRows.length) :
    r.bodyRows[(r.placements[i]'((length_placements _ _).symm ▸ hi)).customRows.first + j] =
      r.steps[i].gateRows[j] := by
  have hp := placements_genericRows r.steps 0 i hi
  simp only [RecordedGates.placements, RecordedGates.bodyRows] at hp hk ⊢
  simp only [hp, Nat.zero_add, Nat.add_assoc] at hk ⊢
  rw [getElem_flatMap_bodyRows r.steps i hi (r.steps[i].rows.length + j)
    (by simp only [RecordedStep.bodyRows, List.length_append, List.length_map]; omega) hk]
  simp only [RecordedStep.bodyRows]
  rw [List.getElem_append_right (by simp)]
  simp

end Snarky.Kimchi
