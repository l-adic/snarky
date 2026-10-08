import Snarky.Kimchi.Backend.Checks.WiredFixtures
import Snarky.Kimchi.Backend.Internal.TraceSemantics
import Kimchi.Columns

/-!
# The checks' witness table

The table a valuation fills over a lowering's rows, at which the wired-fragment and
checked-compilation checks decide their indices' satisfaction. It reads a row's cells through
`rowValues`, a reading of the lowering's proofs, so it sits with the checks rather than with
the fixture data.
-/

open Kimchi

namespace Snarky.Kimchi

open Snarky

namespace WiredFixture

/-- A table: each row's cells under a valuation, zero beyond the lowering. -/
def tableOf (V : Valuation K) (rows : List (KimchiRow K)) : Fin 16 → Fin wCols → K :=
  fun i j =>
    match rows[i.val]? with
    | some r => rowValues V r j
    | none => 0

end WiredFixture

end Snarky.Kimchi
