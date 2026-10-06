import Snarky.Kimchi.Backend.Trace
import Snarky.Kimchi.Backend.Compile

/-!
# The recorded lowering of a constraint list

The builder's fold over a constraint list, recorded: `recordGates` mirrors `reduceGates`
step for step and keeps each step's events, and `recordBuilt` mirrors `reduceBuilt` with the
final flush. Erasing the events returns exactly the ordinary fold, so every structural fact
proved of the recorded gates is a fact about the lowering itself.

## Main definitions

- `RecordedGates`, `recordGates`: the fold with one event list per source constraint.
- `RecordedBuilt`, `recordBuilt`: the whole-circuit lowering beside its steps' events.

## Main results

- `recordGates_erase`, `recordBuilt_erase`: the recorded folds erase to the ordinary ones.
-/

namespace Snarky.Kimchi

open Snarky

variable {F : Type} [Field F] [DecidableEq F]

/-- A constraint list's recorded lowering: the gates in emission order, one event list per
source constraint in order, and the counter and auxiliary state handed back. -/
structure RecordedGates (F : Type) where
  /-- The emitted gates, in order. -/
  gates : List (KimchiGate F)
  /-- Each source constraint's events, in execution order, in source order. -/
  steps : List (List (ReductionEvent F))
  /-- The counter handed back. -/
  nextVariable : Variable
  /-- The auxiliary state handed back. -/
  aux : AuxState F

/-- Forget the events: the shape `reduceGates` returns. -/
def RecordedGates.erase (r : RecordedGates F) : List (KimchiGate F) × Variable × AuxState F :=
  (r.gates, r.nextVariable, r.aux)

/-- Fold the recording reduction over a constraint list: each step's flushed generic rows,
then its gate, as `reduceStep` orders them, beside the step's events. -/
def recordGates : List (KimchiConstraint F) → Variable → AuxState F → RecordedGates F
  | [], nv, aux => ⟨[], [], nv, aux⟩
  | con :: cons, nv, aux =>
    let red := recordReduction nv aux (KimchiConstraint.reduce con)
    let rest := recordGates cons red.nextVariable red.aux
    ⟨red.rows.map .plonk ++ [red.result] ++ rest.gates, red.events :: rest.steps,
      rest.nextVariable, rest.aux⟩

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
    simp only [RecordedGates.erase] at ih'
    have hg := congrArg Prod.fst ih'
    have hn := congrArg (fun p => p.2.1) ih'
    have ha := congrArg (fun p => p.2.2) ih'
    simp only at hg hn ha
    simp only [recordGates, RecordedGates.erase, reduceGates, reduceStep, hres, hrows, hnv, haux,
      hg, hn, ha, List.append_assoc]

/-- A built circuit's recorded lowering: the ordinary result with the final flush, beside
each source constraint's events. -/
structure RecordedBuilt (F : Type) (α : Type) where
  /-- The lowering, as `reduceBuilt` returns it. -/
  built : KimchiBuilt F α
  /-- Each source constraint's events, in source order. -/
  steps : List (List (ReductionEvent F))

/-- A built circuit reduced to kimchi gates with its steps recorded: the recorded fold from
the build's counter, the odd queued constraint flushed into one more packed row. -/
def recordBuilt {α : Type} (built : Built (KimchiConstraint F) α) : RecordedBuilt F α :=
  let red := recordGates built.constraints built.nextVar initialAuxState
  let flush := (finalizeGateQueue red.aux.queuedGenericGate).map KimchiGate.plonk
  ⟨⟨built.result, red.gates ++ flush.toList, red.nextVariable,
    { red.aux with queuedGenericGate := none }⟩, red.steps⟩

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

end Snarky.Kimchi
