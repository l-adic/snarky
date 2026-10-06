import Snarky.Kimchi.Constraint.Reduction

/-!
# The lowering trace

The builder's reduction with its provenance kept: which reduction operations a constraint's
reducer invoked, in execution order, and where its rows land among the emitted body rows.
The data is compiler-internal, naming no index and no gate semantics, and
`RecordedReduction.erase` returns exactly what `reduceAsBuilder` returns, so a recorded
reduction is the existing lowering beside its history.

## Main definitions

- `ReductionEvent`: one reduction operation with its payload, as the reducer issued it.
- `RecordedReduction`: a reduction's result, events, rows, and the counter and auxiliary
  state handed back; `RecordedReduction.erase` forgets the events.
- `RowSpan`, `StepPlacement`: where one source constraint's flushed generic rows and its own
  gate rows sit among the body rows.
- `RecordingState`, `RecordingBuilder`: the builder's state beside the events logged so far,
  and the monad a recording interpreter runs in.

## Implementation notes

An allocation event keeps the affine expression the reducer allocated for. That records the
intended advice computation only: the builder's allocation ignores it, and nothing reads it
as an equation. Events carry payloads, not state snapshots; a snapshot per event would copy
the union-find and the constant cache at every operation.
-/

namespace Snarky.Kimchi

open Snarky

variable {F α : Type}

/-- One reduction operation as the reducer issued it: an allocation with the affine
expression it stands for, a generic constraint handed to the batching queue, or a two-sided
equality handed to the wiring, the constant cache, or row emission. -/
inductive ReductionEvent (F : Type) where
  /-- The variable allocated for an affine expression; the expression is the intended advice
  computation, not an equation. -/
  | alloc (v : Variable) (expression : AffineExpression F)
  /-- A generic constraint handed to the batching queue. -/
  | generic (constraint : GenericPlonkConstraint F)
  /-- A two-sided equality. -/
  | equal (constraint : EqualsConstraint F)

/-- A reduction run with its provenance: the result, the operations in execution order, the
emitted rows in emission order, and the counter and auxiliary state handed back. -/
structure RecordedReduction (F : Type) (α : Type) where
  /-- The reducer's result. -/
  result : α
  /-- The operations, in execution order. -/
  events : List (ReductionEvent F)
  /-- The emitted rows, in emission order. -/
  rows : List (Rows F)
  /-- The counter handed back. -/
  nextVariable : Variable
  /-- The auxiliary state handed back. -/
  aux : AuxState F

/-- Forget the events: the shape `reduceAsBuilder` returns. -/
def RecordedReduction.erase (r : RecordedReduction F α) :
    α × List (Rows F) × Variable × AuxState F :=
  (r.result, r.rows, r.nextVariable, r.aux)

/-- A contiguous run of rows: the first row's position and the row count. -/
structure RowSpan where
  /-- The first row's position. -/
  first : Nat
  /-- The number of rows. -/
  count : Nat

/-- Where one source constraint's rows sit among the body rows: the generic rows flushed
while reducing it, then its own gate rows, none for a `Basic` constraint. Positions count
body rows; the assembled table prepends the public rows. -/
structure StepPlacement where
  /-- The generic rows flushed while reducing the constraint. -/
  genericRows : RowSpan
  /-- The constraint's own gate rows. -/
  customRows : RowSpan

/-- The builder's state beside the events logged so far. -/
structure RecordingState (F : Type) where
  /-- The builder's state. -/
  core : BuilderReductionState F
  /-- The events logged so far, newest first. -/
  eventsRev : List (ReductionEvent F)

/-- The monad a recording interpreter runs in. -/
abbrev RecordingBuilder (F : Type) := StateM (RecordingState F)

end Snarky.Kimchi
