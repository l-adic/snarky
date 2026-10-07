import Snarky.Kimchi.Backend.Direct
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.NormNum.Prime

/-!
# Direct-fragment checks

One lowering of the fragment decided end to end over a field of 113 elements: two public
variables, a Boolean queued across a complete addition, the pair packed after it, and one
equation left to the final flush. The index is built from the lowering's rows and the
class-based wiring by `Index.build?`, its table satisfies it, and the closed theorem is
invoked on them. Then the boundaries: a source aliasing an unwired operand with a Boolean,
with a public variable, or with another unwired operand is out of scope; a receipt moved
to the other half is not located; a table breaking a copy constraint while every gate still
holds does not satisfy the index; an index with a packed row's coefficients altered, or with
a required copy wire rerouted, is not the lowering's.

## Main results

- `direct_example_holds`: the closed theorem on the decided instance.
- `direct_rejections`, `direct_rejections_index`: the boundaries.
-/

open Kimchi

namespace Snarky.Kimchi

open Snarky

instance : Fact (Nat.Prime 113) := ⟨by norm_num⟩

/-- The field: `16 ∣ 112`, with seven cosets of the sixteenth roots of unity. -/
private abbrev K := ZMod 113

/-- A complete addition over bare variables, its `inf` flag the first public variable. -/
private def addition : AddComplete K :=
  { p1 := ⟨.var 3, .var 4⟩, p2 := ⟨.var 5, .var 6⟩, p3 := ⟨.var 7, .var 8⟩,
    inf := .var 0, sameX := .var 9, s := .var 10, infZ := .var 11, x21Inv := .var 12 }

/-- A Boolean queued across the addition, its pair packed after it, one left to the flush. -/
private def source : List (KimchiConstraint K) :=
  [.basic (.boolean (.var 0)), .addComplete addition, .basic (.boolean (.var 1)),
    .basic (.boolean (.var 2))]

private def publicVars : List Variable := [0, 1]

/-- The prover's values: the Booleans, and the addition `(1, 1) + (2, 3) = (1, -1)` with
slope `2`, distinct abscissae and their difference's inverse `1`. -/
private def V : Valuation K := fun v => [0, 1, 1, 1, 1, 2, 3, 1, 112, 0, 2, 0, 1].getD v 0

private def rows : List (KimchiRow K) := directRows source publicVars 20

private def roots : Array Variable := directRoots source 20

/-- The table: each row's cells under `V`, zero beyond the lowering. -/
private def table : Fin 16 → Fin wCols → K := fun i j =>
  match rows[i.val]? with
  | some r => rowValues V r j
  | none => 0

/-- The gate table: the lowering's rows with the class-based wiring, zero rows identity-wired
beyond them. -/
private def gates : Fin 16 → Index.GateRow K 16 := fun i =>
  match rows[i.val]? with
  | some r =>
    { typ := r.kind
      coeffs := fun c => r.coeffs.getD c.val 0
      wires := fun c =>
        (⟨(classTarget roots rows i.val c.val).col % 7, Nat.mod_lt _ (by decide)⟩,
          ⟨(classTarget roots rows i.val c.val).row % 16, Nat.mod_lt _ (by decide)⟩) }
  | none => { typ := .zero, coeffs := fun _ => 0, wires := fun c => (c, i) }

private def mds : Gate.Poseidon.Mds K :=
  { m00 := 0, m01 := 0, m02 := 0, m10 := 0, m11 := 0, m12 := 0, m20 := 0, m21 := 0, m22 := 0 }

/-- Powers of the generator `3`: one representative per coset of the sixteenth roots. -/
private def shifts : Fin permCols → K := fun c => [1, 3, 9, 27, 81, 17, 51].getD c.val 0

private def index? : Option (Index K 16) :=
  Index.build? gates publicVars.length 3 40 0 mds shifts

/-- The laws hold on the gate table: the index is built. -/
theorem direct_example_built : index?.isSome := by
  decide +kernel

private def idx : Index K 16 := index?.get direct_example_built

private def pub : Fin idx.publicCount → K := fun i => V (publicVars.getD i.val 0)

/-- The source is in scope. -/
theorem direct_example_scoped : KimchiConstraint.Direct.Scoped source publicVars := by
  decide +kernel

/-- The index is the lowering's assembly. -/
theorem direct_example_indexOf : IndexOf source publicVars 20 idx :=
  indexOf_of_classTarget source publicVars 20 idx (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- The table satisfies the index at the public input. -/
theorem direct_example_satisfies : idx.Satisfies pub table := by
  decide +kernel

/-- The closed theorem on the decided instance. -/
theorem direct_example_holds :
    ∃ W : Valuation K, (∀ c ∈ source, KimchiConstraint.Holds W c) ∧
      ∀ i : Fin publicVars.length, W publicVars[i] = pub (direct_example_indexOf.publicIndex i) :=
  KimchiConstraint.Direct.holds_of_satisfies direct_example_scoped direct_example_indexOf pub
    table direct_example_satisfies

/-! ## Boundaries -/

/-- The Booleanity equation on a variable. -/
private def booleanGate (v : Variable) : GenericPlonkConstraint K :=
  { cl := -1, vl := some v, cr := 0, vr := some v, co := 0, vo := none, m := 1, c := 0 }

/-- The addition's slope aliased with the first Boolean's variable. -/
private def aliasedSource : List (KimchiConstraint K) :=
  [.basic (.boolean (.var 0)), .addComplete { addition with s := .var 0 },
    .basic (.boolean (.var 1)), .basic (.boolean (.var 2))]

/-- The addition's two inverse-like operands sharing a variable. -/
private def repeatedSource : List (KimchiConstraint K) :=
  [.basic (.boolean (.var 0)), .addComplete { addition with infZ := .var 12 },
    .basic (.boolean (.var 1)), .basic (.boolean (.var 2))]

/-- The table with the packed Boolean's two cells zeroed: its equation still holds, the copy
to its public row does not. -/
private def brokenTable : Fin 16 → Fin wCols → K := fun i j =>
  if i.val = 3 ∧ j.val < 2 then 0 else table i j

/-- An unwired operand aliased with a Boolean, or with a public variable, is out of scope; a
receipt moved to the other half is not located; a table breaking a copy constraint while every
gate holds does not satisfy the index. -/
theorem direct_rejections :
    ¬ KimchiConstraint.Direct.Scoped aliasedSource publicVars ∧
    ¬ KimchiConstraint.Direct.Scoped source [0, 12] ∧
    ¬ KimchiConstraint.Direct.Scoped repeatedSource publicVars ∧
    (receipts (recordGates source 20 initialAuxState) =
      [⟨booleanGate 1, 1, 0⟩, ⟨booleanGate 0, 1, 1⟩, ⟨booleanGate 2, 2, 0⟩] ∧
      ∀ rc ∈ [(⟨booleanGate 1, 1, 0⟩ : GenericReceipt K), ⟨booleanGate 0, 1, 1⟩,
          ⟨booleanGate 2, 2, 0⟩],
        rc.Located (recordGates source 20 initialAuxState).allRows ∧
          ¬ ({ rc with half := ⟨1 - rc.half.val, by omega⟩ } : GenericReceipt K).Located
            (recordGates source 20 initialAuxState).allRows) ∧
    ((∀ i, Index.rowSatisfies idx pub brokenTable i) ∧ ¬ idx.Satisfies pub brokenTable) := by
  decide +kernel

/-- The gate table with the packed row's coefficients zeroed. -/
private def gatesCoeffs : Fin 16 → Index.GateRow K 16 := fun i =>
  if i.val = 3 then { gates i with coeffs := fun _ => 0 } else gates i

/-- The gate table with the packed Boolean's copy cycle rerouted: its first cell back to the
public row, its second to itself, still a permutation. -/
private def gatesWires : Fin 16 → Index.GateRow K 16 := fun i =>
  if i.val = 3 then
    { gates i with wires := fun c =>
        if c.val = 0 then (⟨0, by decide⟩, ⟨1, by decide⟩)
        else if c.val = 1 then (⟨1, by decide⟩, ⟨3, by decide⟩)
        else (gates i).wires c }
  else gates i

private theorem built_coeffs : (Index.build? gatesCoeffs publicVars.length 3 40 0 mds shifts).isSome
    := by
  decide +kernel

private theorem built_wires : (Index.build? gatesWires publicVars.length 3 40 0 mds shifts).isSome
    := by
  decide +kernel

/-- Both altered tables build indices, and neither is the lowering's: the coefficients of the
packed row, and the wire out of its first cell, disagree with the assembly. -/
theorem direct_rejections_index :
    ¬ IndexOf source publicVars 20
        ((Index.build? gatesCoeffs publicVars.length 3 40 0 mds shifts).get built_coeffs) ∧
    ¬ IndexOf source publicVars 20
        ((Index.build? gatesWires publicVars.length 3 40 0 mds shifts).get built_wires) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have hc := h.coeffs ⟨3, by decide⟩ (by rw [length_directGates]; decide +kernel) ⟨0, by decide⟩
    rw [getElem_directGates source publicVars 20 3 (by decide +kernel)] at hc
    exact absurd hc (by decide +kernel)
  · have hw := (h.wires ⟨3, by decide⟩ (by rw [length_directGates]; decide +kernel)
      ⟨0, by decide⟩).2
    rw [getElem_directGates source publicVars 20 3 (by decide +kernel)] at hw
    simp only [wireTarget_eq] at hw
    exact absurd hw (by decide +kernel)

end Snarky.Kimchi
