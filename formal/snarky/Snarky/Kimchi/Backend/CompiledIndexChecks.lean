import Snarky.Kimchi.Backend.CompiledIndex
import Snarky.Kimchi.Backend.Direct
import Snarky.Kimchi.Backend.WiredFixtures
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.NormNum.Prime

/-!
# Compiled-index checks

The index constructor decided on the wired-fragment checks' sources over a field of 113
elements, in the kernel. Each concrete case rewrites the assembled gates to the class-based
ones with `directGates_eq_classGates` and evaluates the shared table and constructor
unchanged.

The constructor builds an index for each of the eight accepted sources. It rejects a Poseidon
block at another matrix and an endomorphism multiplication at another coefficient, by their
parameters, and a domain too small for the rows. The table rejects a wire column and a wire
row outside it, a row with more coefficients than the columns, and a list longer than the
domain, and it pads with zero gates wired to themselves.

## Main results

- `compiledIndex_accepts`, `compiledIndex_rejects`: the constructor on the sources.
- `gateTable_rejects`, `gateTable_padding`: the table's rejections and its padding.
-/

open Kimchi

namespace Snarky.Kimchi

open Snarky WiredFixture

instance : Fact (Nat.Prime 113) := ⟨by norm_num⟩

/-- The constructor builds an index for the first four accepted sources. -/
theorem compiledIndex_accepts :
    (compiledIndex? source publicVars 20 16 3 40 0 mds shifts).isSome ∧
    (compiledIndex? endoSource endoPublic 11 16 3 40 0 mds shifts).isSome ∧
    (compiledIndex? chainSource chainPublic 22 16 3 40 0 mds shifts).isSome ∧
    (compiledIndex? scaleSource scalePublic 25 16 3 40 0 mds shifts).isSome := by
  simp only [compiledIndex?, directGates_eq_classGates]
  decide +kernel

/-- The constructor builds an index for the other four accepted sources, each at its own
parameters. -/
theorem compiledIndex_accepts' :
    (compiledIndex? scaleChainSource scaleChainPublic 46 16 3 40 0 mds shifts).isSome ∧
    (compiledIndex? endoMulSource endoMulPublic 28 16 3 40 2 mds shifts).isSome ∧
    (compiledIndex? poseidonSource poseidonPublic 32 16 3 40 0 poseidonMds shifts).isSome ∧
    (compiledIndex? padSource padPublic 5 16 3 40 0 mds shifts).isSome := by
  simp only [compiledIndex?, directGates_eq_classGates]
  decide +kernel

/-- The constructor rejects a Poseidon block at another matrix and an endomorphism
multiplication at another coefficient, and the Poseidon block's seven rows on a domain of
eight with three masked rows. -/
theorem compiledIndex_rejects :
    (compiledIndex? poseidonSource poseidonPublic 32 16 3 40 0 mds shifts).isNone ∧
    (compiledIndex? endoMulSource endoMulPublic 28 16 3 40 3 mds shifts).isNone ∧
    (compiledIndex? poseidonSource poseidonPublic 32 8 3 18 0 poseidonMds shifts).isNone := by
  simp only [compiledIndex?, directGates_eq_classGates]
  decide +kernel

/-- A generic row with one coefficient, each cell wired to itself. -/
private def okGate : AssembledGate K :=
  { kind := .generic, coeffs := [1],
    wires := #v[⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 2⟩, ⟨0, 3⟩, ⟨0, 4⟩, ⟨0, 5⟩, ⟨0, 6⟩] }

/-- The row with its first cell wired to the column `7`, outside the permuted columns. -/
private def badColumn : AssembledGate K :=
  { okGate with wires := #v[⟨0, 7⟩, ⟨0, 1⟩, ⟨0, 2⟩, ⟨0, 3⟩, ⟨0, 4⟩, ⟨0, 5⟩, ⟨0, 6⟩] }

/-- The row with its first cell wired to the row `16`, outside a table of sixteen rows. -/
private def badRow : AssembledGate K :=
  { okGate with wires := #v[⟨16, 0⟩, ⟨0, 1⟩, ⟨0, 2⟩, ⟨0, 3⟩, ⟨0, 4⟩, ⟨0, 5⟩, ⟨0, 6⟩] }

/-- The row with sixteen coefficients, one more than the columns. -/
private def manyCoeffs : AssembledGate K := { okGate with coeffs := List.replicate 16 1 }

/-- The table takes the row, and rejects a wire column and a wire row outside it, a row with
too many coefficients, and seventeen rows on a domain of sixteen. -/
theorem gateTable_rejects :
    (gateTable? [okGate] 16).isSome ∧ (gateTable? [badColumn] 16).isNone ∧
    (gateTable? [badRow] 16).isNone ∧ (gateTable? [manyCoeffs] 16).isNone ∧
    (gateTable? (List.replicate 17 okGate) 16).isNone := by
  decide +kernel

/-- The first source's table pads its eleven rows beyond the five emitted with zero gates,
zero coefficients and every cell wired to itself. -/
theorem gateTable_padding :
    ((gateTable? (directGates source publicVars 20) 16).any fun t =>
      decide (∀ i : Fin 16, 5 ≤ i.val → (t i).typ = .zero ∧
        (∀ c : Fin coeffCols, (t i).coeffs c = 0) ∧
          ∀ c : Fin permCols, (t i).wires c = (c, i))) = true := by
  rw [directGates_eq_classGates]
  decide +kernel

end Snarky.Kimchi
