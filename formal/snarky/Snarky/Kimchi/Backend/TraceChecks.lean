import Snarky.Kimchi.Backend.Trace
import Mathlib.Algebra.Field.Rat

/-!
# Recording checks

Recorded reductions over `ℚ`, decided by the kernel: generic batching across a custom block
and at the final flush, an equality discharged by wiring, a constant pinned once and reused
from the cache, and an allocation logged with its expression while the queue it packs into
was already occupied. Each theorem states the exact events, rows and auxiliary state the
recorder reports, so a change to the builder's emission order or to the recorder shows here.

## Main results

- `recorded_batching`, `recorded_wiring`, `recorded_constantCache`, `recorded_allocation`.
-/

namespace Snarky.Kimchi

open Snarky

deriving instance DecidableEq for EqualsConstraint, AffineExpression, ReductionEvent, KimchiRow,
  Rows

/-- The generic equation of a Boolean on variable `v`: `-l + l·r = 0` at `l = r = v`. -/
private def booleanGate (v : Variable) : GenericPlonkConstraint ℚ :=
  { cl := -1, vl := some v, cr := 0, vr := some v, co := 0, vo := none, m := 1, c := 0 }

/-- A packed generic row: the incoming equation's cells and coefficients, then the queued
equation's. -/
private def doubleRow (incoming queued : GenericPlonkConstraint ℚ) : Rows ℚ :=
  ⟨{ kind := .generic,
     vars := ⟨⟨[incoming.vl, incoming.vr, incoming.vo, queued.vl, queued.vr, queued.vo] ++
       List.replicate 9 none⟩, by simp⟩,
     coeffs := [incoming.cl, incoming.cr, incoming.co, incoming.m, incoming.c,
       queued.cl, queued.cr, queued.co, queued.m, queued.c] }⟩

/-- The single-equation row the final flush emits for one queued equation. -/
private def singleRow (g : GenericPlonkConstraint ℚ) : Rows ℚ :=
  ⟨{ kind := .generic,
     vars := ⟨⟨[g.vl, g.vr, g.vo] ++ List.replicate 12 none⟩, by simp⟩,
     coeffs := [g.cl, g.cr, g.co, g.m, g.c] }⟩

/-! ## Generic batching -/

private def twoBooleans : RecordedReduction ℚ Unit :=
  recordReduction 2 initialAuxState (do
    reduce (F := ℚ) (.boolean (.var 0))
    reduce (F := ℚ) (.boolean (.var 1)))

private def addition : AddComplete ℚ :=
  { p1 := ⟨.var 2, .var 3⟩, p2 := ⟨.var 4, .var 5⟩, p3 := ⟨.var 6, .var 7⟩,
    inf := .var 8, sameX := .var 9, s := .var 10, infZ := .var 11, x21Inv := .var 12 }

private def additionRow : Rows ℚ :=
  ⟨{ kind := .completeAdd,
     vars := ⟨⟨[some 2, some 3, some 4, some 5, some 6, some 7, some 8, some 9, some 10,
       some 11, some 12] ++ List.replicate 4 none⟩, by simp⟩,
     coeffs := [] }⟩

private def booleanThenAddition : RecordedReduction ℚ (Rows ℚ) :=
  recordReduction 13 initialAuxState (do
    reduce (F := ℚ) (.boolean (.var 0))
    addition.reduce)

/-- Two Booleans log two generic events and pack into one row, the incoming equation in the
first three cells. A Boolean followed by a complete addition over bare variables logs one
event: the addition allocates nothing and asserts no equality, its row is the reducer's
result rather than a flushed row, and the Boolean's equation outlives the custom block to be
emitted alone by the final flush. -/
theorem recorded_batching :
    twoBooleans.events = [.generic (booleanGate 0), .generic (booleanGate 1)] ∧
    twoBooleans.rows = [doubleRow (booleanGate 1) (booleanGate 0)] ∧
    twoBooleans.aux.queuedGenericGate = none ∧
    booleanThenAddition.events = [.generic (booleanGate 0)] ∧
    booleanThenAddition.result = additionRow ∧ booleanThenAddition.rows = [] ∧
    booleanThenAddition.aux.queuedGenericGate = some (booleanGate 0) ∧
    finalizeGateQueue booleanThenAddition.aux.queuedGenericGate =
      some (singleRow (booleanGate 0)) := by
  decide +kernel

/-! ## Equality through wiring -/

private def equalVariables : RecordedReduction ℚ Unit :=
  recordReduction 2 initialAuxState (reduce (F := ℚ) (.equal (.var 0) (.var 1)))

/-- An equality of two variables with equal coefficients logs one equality event, emits no
row, and puts both variables in one class. -/
theorem recorded_wiring :
    equalVariables.events = [.equal { cl := 1, vl := some 0, cr := 1, vr := some 1 }] ∧
    equalVariables.rows = [] ∧ equalVariables.aux.queuedGenericGate = none ∧
    equalVariables.aux.wireState.unionFind.rootOf = #[0, 0] := by
  decide +kernel

/-! ## Constant-cache reuse -/

private def pinnedTwice : RecordedReduction ℚ Unit :=
  recordReduction 2 initialAuxState (do
    reduce (F := ℚ) (.equal (.var 0) (.const 5))
    reduce (F := ℚ) (.equal (.var 1) (.const 5)))

/-- Pinning two variables to the same constant logs both equalities. The first queues one
pinning equation and caches the constant; the second hits the cache and wires to the cached
variable, emitting nothing. -/
theorem recorded_constantCache :
    pinnedTwice.events =
      [.equal { cl := 1, vl := some 0, cr := 5, vr := none },
       .equal { cl := 1, vl := some 1, cr := 5, vr := none }] ∧
    pinnedTwice.aux.queuedGenericGate =
      some { cl := 1, vl := some 0, cr := 0, vr := none, co := 0, vo := none, m := 0, c := -5 } ∧
    pinnedTwice.rows = [] ∧
    pinnedTwice.aux.wireState.cachedConstants = [(5, 0)] ∧
    pinnedTwice.aux.wireState.unionFind.rootOf = #[1, 1] := by
  decide +kernel

/-! ## Allocation into an occupied queue -/

/-- The auxiliary state after one Boolean: its equation waits in the queue. -/
private def queued : AuxState ℚ :=
  (reduceAsBuilder 2 initialAuxState (reduce (F := ℚ) (.boolean (.var 0)))).2.2.2

private def sumFromQueue : RecordedReduction ℚ Variable :=
  recordReduction 2 queued (reduceToVariable (F := ℚ) (.add (.var 0) (.var 1)))

/-- The generic equation pinning the sum of variables `0` and `1` to the fresh variable `2`. -/
private def sumGate : GenericPlonkConstraint ℚ :=
  { cl := 1, vl := some 0, cr := 1, vr := some 1, co := -1, vo := some 2, m := 0, c := 0 }

/-- Reducing a sum to a variable from an occupied queue logs the allocation with the
expression it stands for, then its generic equation, which packs in front of the waiting one;
the counter advances past the fresh variable, recorded as internal. -/
theorem recorded_allocation :
    sumFromQueue.events = [.alloc 2 ⟨none, [(0, 1), (1, 1)]⟩, .generic sumGate] ∧
    sumFromQueue.result = 2 ∧ sumFromQueue.nextVariable = 3 ∧
    sumFromQueue.rows = [doubleRow sumGate (booleanGate 0)] ∧
    sumFromQueue.aux.queuedGenericGate = none ∧
    sumFromQueue.aux.wireState.internalVariables = [2] := by
  decide +kernel

end Snarky.Kimchi
