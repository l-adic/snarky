import Pickles.Application.MatrixRun

/-!
# A consumer of lifted executions

Both lifts applied, against the supported interface only: from a checked application, a step
table and a wrap table, a step execution and a wrap execution at the tables' statements, with
no valuation, satisfaction or build fact supplied.
-/

namespace Pickles.Application.MatrixRunConsumer

open Snarky

variable {D : Shape} {L : Layout D}

/-- A step table and a wrap table accepted by a checked application's indices have executions
at their statements, preserving the fixed matrix readings. -/
theorem lifts_both {C : Circuits D L} (checked : CheckedApplication C) (b : D.Branch)
    (ts : StepTable checked.indices b) (tw : WrapTable checked.indices) :
    ∃ (s : StepRun C b) (w : WrapRun C),
      CircuitType.Reads s.V s.cells.out ts.statement ∧
        CircuitType.Reads w.V wrapStatement tw.statement ∧
        s.V = stepValuation C checked.indices b ts ∧
        w.V = wrapValuation C checked.indices tw := by
  obtain ⟨s, hs, hvs⟩ := checked.lift_step b ts
  obtain ⟨w, hw, hvw⟩ := checked.lift_wrap tw
  exact ⟨s, w, hs, hw, hvs, hvw⟩

end Pickles.Application.MatrixRunConsumer
