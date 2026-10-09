import Pickles.KeyDerivation

/-!
# Commitment comparator checks

The located comparator accepts equal two-chunk columns and rejects a change in each column
family and both chunks. The six selector positions are checked individually. These decisions
use scalar labels; the derivation's polynomial correspondence is proved generically and the
manifest driver checks its actual curve points against production keys.
-/

namespace Pickles.Application.KeyDerivationChecks

open scoped Kimchi

private def columns : Vector (Vector Nat 2) (permCols + coeffCols + selectorCols) :=
  Vector.ofFn fun col => #v[2 * col.val, 2 * col.val + 1]

private def changed (col : KeyColumn) (chunk : Fin 2) :=
  columns.set col.val ((columns[col]).set chunk.val (columns[col][chunk] + 1))

/-- Equal commitment columns compare equal. -/
theorem accepts : compareColumns? columns columns = none := by decide +kernel

/-- Each column and chunk is checked, and its exact location is returned. -/
theorem rejects :
    (List.finRange (permCols + coeffCols + selectorCols)).all (fun col =>
      (List.finRange 2).all fun chunk =>
        compareColumns? columns (changed col chunk) == some ⟨col, chunk.val⟩) = true := by
  decide +kernel

/-- A successful comparison supplies the equality required by a consumer. -/
theorem columns_equal {G : Type} [DecidableEq G] {nc : Nat}
    {a b : Vector (Vector G nc) (permCols + coeffCols + selectorCols)}
    (h : compareColumns? a b = none) : a = b :=
  compareColumns?_eq_none_iff.mp h

end Pickles.Application.KeyDerivationChecks
