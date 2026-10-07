import Snarky.Kimchi.Backend.Wired
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.NormNum.Prime

/-!
# Wired-fragment checks

One lowering of the fragment decided end to end over a field of 113 elements: a public
variable pinned to a constant, two public-side variables merged, a complete addition whose
first abscissa is a sum and whose second ordinate is a scaled variable, a second variable
hitting the constant's cache, and a Boolean on the merged variable. The pin's row packs with
the sum's intermediate, the scaled operand's row with the Boolean. The index is built from
the lowering's rows and the class-based wiring by `Index.build?`, its table satisfies it, and
the closed theorem is invoked on them. Then the boundaries, one for each premise: a source
with a constant in an unwired slot, with an unwired operand named again by a merge that
writes no row, or by a term of the sum, or naming a variable at the counter, is out of scope;
a table splitting the merged class, or reading the intermediate away from its pinning cell,
while every gate holds, does not satisfy the index; an index with the packed row's
coefficients altered, or with the pinned variable's copy wire rerouted, is not the lowering's.

Then a challenge decomposition, in two lowerings. One round from the initial accumulators,
its crumbs fresh and its output `n` public: its two `2`s pin one allocation through the cache
and its `0` pins another, the two pins packed in one row before the gate row. Two rounds, the
second's accumulators the first's outputs: the gate block's second row sits one past its
first, and each threaded accumulator labels a wired cell in each, one class. Their
boundaries: a crumb reused by a Boolean keeps every constraint wired and breaks the scope; a
crumb written as a sum is not wired.

## Main results

- `wired_example_holds`, `endo_example_holds`, `chain_example_holds`: the closed theorem on
  the decided instances.
- `wired_rejections_scope`, `wired_rejections_table`, `wired_rejections_index`,
  `endo_rejections`: the boundaries, by premise.
- `endo_example_layout`, `chain_example_layout`: the lowerings' logs, rows and classes.
-/

open Kimchi

namespace Snarky.Kimchi

open Snarky

instance : Fact (Nat.Prime 113) := ⟨by norm_num⟩

/-- The field: `16 ∣ 112`, with seven cosets of the sixteenth roots of unity. -/
private abbrev K := ZMod 113

/-- A complete addition with an affine first abscissa and a scaled second ordinate, its
`inf` flag the merged variable. -/
private def addition : AddComplete K :=
  { p1 := ⟨.add (.var 3) (.var 13), .var 4⟩, p2 := ⟨.var 5, .scale 2 (.var 6)⟩,
    p3 := ⟨.var 7, .var 8⟩, inf := .var 2, sameX := .var 9, s := .var 10, infZ := .var 11,
    x21Inv := .var 12 }

/-- A pin, a merge, the addition, a cache hit on the pin's constant, a Boolean on the merged
variable. -/
private def source : List (KimchiConstraint K) :=
  [.basic (.equal (.var 0) (.const 5)), .basic (.equal (.var 1) (.var 2)),
    .addComplete addition, .basic (.equal (.var 14) (.const 5)), .basic (.boolean (.var 2))]

private def publicVars : List Variable := [0, 1]

/-- The prover's values: the pinned constant, the merged pair at `0`, the addition
`(1, 1) + (2, 3) = (1, -1)` with slope `2`, the sum `1 + 0` at its intermediate `20`, the
scaled ordinate `2 · 58` at its intermediate `21`, and the cache hit's variable at the
constant. -/
private def V : Valuation K := fun v =>
  [5, 0, 0, 1, 1, 2, 58, 1, 112, 0, 2, 0, 1, 0, 5, 0, 0, 0, 0, 0, 1, 3].getD v 0

private def rows : List (KimchiRow K) := directRows source publicVars 20

private def roots : Array Variable := directRoots source 20

/-- A table: each row's cells under a valuation, zero beyond the lowering. -/
private def tableOf (V : Valuation K) (rows : List (KimchiRow K)) : Fin 16 → Fin wCols → K :=
  fun i j =>
    match rows[i.val]? with
    | some r => rowValues V r j
    | none => 0

/-- A gate table: the lowering's rows with the class-based wiring, zero rows identity-wired
beyond them. -/
private def gatesOf (roots : Array Variable) (rows : List (KimchiRow K)) :
    Fin 16 → Index.GateRow K 16 := fun i =>
  match rows[i.val]? with
  | some r =>
    { typ := r.kind
      coeffs := fun c => r.coeffs.getD c.val 0
      wires := fun c =>
        (⟨(classTarget roots rows i.val c.val).col % 7, Nat.mod_lt _ (by decide)⟩,
          ⟨(classTarget roots rows i.val c.val).row % 16, Nat.mod_lt _ (by decide)⟩) }
  | none => { typ := .zero, coeffs := fun _ => 0, wires := fun c => (c, i) }

private def table : Fin 16 → Fin wCols → K := tableOf V rows

private def gates : Fin 16 → Index.GateRow K 16 := gatesOf roots rows

private def mds : Gate.Poseidon.Mds K :=
  { m00 := 0, m01 := 0, m02 := 0, m10 := 0, m11 := 0, m12 := 0, m20 := 0, m21 := 0, m22 := 0 }

/-- Powers of the generator `3`: one representative per coset of the sixteenth roots. -/
private def shifts : Fin permCols → K := fun c => [1, 3, 9, 27, 81, 17, 51].getD c.val 0

private def index? : Option (Index K 16) :=
  Index.build? gates publicVars.length 3 40 0 mds shifts

/-- The laws hold on the gate table: the index is built. -/
theorem wired_example_built : index?.isSome := by
  decide +kernel

private def idx : Index K 16 := index?.get wired_example_built

private def pub : Fin idx.publicCount → K := fun i => V (publicVars.getD i.val 0)

/-- The source is in scope. -/
theorem wired_example_scoped : KimchiConstraint.Wired.Scoped 20 source publicVars := by
  decide +kernel

/-- The index is the lowering's assembly. -/
theorem wired_example_indexOf : IndexOf source publicVars 20 idx :=
  indexOf_of_classTarget source publicVars 20 idx (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- The table satisfies the index at the public input. -/
theorem wired_example_satisfies : idx.Satisfies pub table := by
  decide +kernel

/-- The closed theorem on the decided instance. -/
theorem wired_example_holds :
    ∃ W : Valuation K, (∀ c ∈ source, KimchiConstraint.Holds W c) ∧
      ∀ i : Fin publicVars.length, W publicVars[i] = pub (wired_example_indexOf.publicIndex i) :=
  KimchiConstraint.Wired.holds_of_satisfies wired_example_scoped wired_example_indexOf pub
    table wired_example_satisfies

/-! ## Boundaries -/

/-- The addition with a constant in an unwired slot. -/
private def constSource : List (KimchiConstraint K) :=
  [.basic (.equal (.var 0) (.const 5)), .basic (.equal (.var 1) (.var 2)),
    .addComplete { addition with sameX := .const 1 }, .basic (.equal (.var 14) (.const 5)),
    .basic (.boolean (.var 2))]

/-- An unwired operand named again by an equality of two variables: a merge, which writes
no cell. -/
private def equalSource : List (KimchiConstraint K) :=
  source ++ [.basic (.equal (.var 9) (.var 16))]

/-- An unwired operand named again as a term of the sum. -/
private def termSource : List (KimchiConstraint K) :=
  [.basic (.equal (.var 0) (.const 5)), .basic (.equal (.var 1) (.var 2)),
    .addComplete { addition with p1 := ⟨.add (.var 9) (.var 13), .var 4⟩ },
    .basic (.equal (.var 14) (.const 5)), .basic (.boolean (.var 2))]

/-- A source naming the counter's own variable. -/
private def highSource : List (KimchiConstraint K) :=
  source ++ [.basic (.boolean (.var 20))]

/-- Out of scope: a constant in an unwired slot, an unwired operand named twice, in an
equality that writes no cell or in a term of the sum, and a variable at the counter. The
equality is recorded as a merge and adds no row: the lowering's steps log, in order, the pin,
the merge of the public-side pair, the addition's two allocations with the row it flushes,
the cache hit, the Boolean with the row it flushes, and the merge of the unwired operand, over
the same three body rows. -/
theorem wired_rejections_scope :
    ¬ KimchiConstraint.Wired.Scoped 20 constSource publicVars ∧
    ¬ KimchiConstraint.Wired.Scoped 20 equalSource publicVars ∧
    ¬ KimchiConstraint.Wired.Scoped 20 termSource publicVars ∧
    ¬ KimchiConstraint.Wired.Scoped 20 highSource publicVars ∧
    ((recordGates equalSource 20 initialAuxState).steps.map (fun s => allocs s.events) =
        [[], [], [20, 21], [], [], []] ∧
      (recordGates equalSource 20 initialAuxState).steps.map (fun s => fusions s.events) =
        [[], [(1, 2)], [], [(14, 0)], [], [(9, 16)]] ∧
      (recordGates equalSource 20 initialAuxState).steps.map (fun s => pinsOf s.events) =
        [[(5, 0)], [], [], [], [], []] ∧
      (recordGates equalSource 20 initialAuxState).steps.map (fun s => s.rows.length) =
        [0, 0, 1, 0, 1, 0] ∧
      (recordGates equalSource 20 initialAuxState).allRows.length = 3) := by
  decide +kernel

/-- The table with the Boolean's two cells, the merged variable's, set to `1` while its
public row reads `0`: the Boolean still holds, the merged class is split. -/
private def splitTable : Fin 16 → Fin wCols → K := fun i j =>
  if i.val = 4 ∧ j.val < 2 then 1 else table i j

/-- The table with the sum's row reading `1 + 1 = 2`: its equation still holds, the
intermediate's cell in the addition row still reads `1`. -/
private def driftTable : Fin 16 → Fin wCols → K := fun i j =>
  if i.val = 2 ∧ j.val = 1 then 1 else if i.val = 2 ∧ j.val = 2 then 2 else table i j

/-- A table splitting the merged class, or reading the intermediate away from its pinning
cell, while every gate holds, does not satisfy the index. -/
theorem wired_rejections_table :
    ((∀ i, Index.rowSatisfies idx pub splitTable i) ∧ ¬ idx.Satisfies pub splitTable) ∧
    ((∀ i, Index.rowSatisfies idx pub driftTable i) ∧ ¬ idx.Satisfies pub driftTable) := by
  decide +kernel

/-- The gate table with the packed row's coefficients zeroed. -/
private def gatesCoeffs : Fin 16 → Index.GateRow K 16 := fun i =>
  if i.val = 2 then { gates i with coeffs := fun _ => 0 } else gates i

/-- The gate table with the pinned variable's copy cycle cut: its cell in the packed row and
its public row's cell each wired to itself, still a permutation. -/
private def gatesWires : Fin 16 → Index.GateRow K 16 := fun i =>
  if i.val = 2 then
    { gates i with wires := fun c =>
        if c.val = 3 then (⟨3, by decide⟩, ⟨2, by decide⟩) else (gates i).wires c }
  else if i.val = 0 then
    { gates i with wires := fun c =>
        if c.val = 0 then (⟨0, by decide⟩, ⟨0, by decide⟩) else (gates i).wires c }
  else gates i

private theorem built_coeffs : (Index.build? gatesCoeffs publicVars.length 3 40 0 mds shifts).isSome
    := by
  decide +kernel

private theorem built_wires : (Index.build? gatesWires publicVars.length 3 40 0 mds shifts).isSome
    := by
  decide +kernel

/-- Both altered tables build indices, and neither is the lowering's: the coefficients of the
packed row, and the wire out of the pinned variable's cell, disagree with the assembly. -/
theorem wired_rejections_index :
    ¬ IndexOf source publicVars 20
        ((Index.build? gatesCoeffs publicVars.length 3 40 0 mds shifts).get built_coeffs) ∧
    ¬ IndexOf source publicVars 20
        ((Index.build? gatesWires publicVars.length 3 40 0 mds shifts).get built_wires) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have hc := h.coeffs ⟨2, by decide⟩ (by rw [length_directGates]; decide +kernel) ⟨0, by decide⟩
    rw [getElem_directGates source publicVars 20 2 (by decide +kernel)] at hc
    exact absurd hc (by decide +kernel)
  · have hw := (h.wires ⟨2, by decide⟩ (by rw [length_directGates]; decide +kernel)
      ⟨3, by decide⟩).2
    rw [getElem_directGates source publicVars 20 2 (by decide +kernel)] at hw
    simp only [wireTarget_eq] at hw
    exact absurd hw (by decide +kernel)

/-! ## A challenge decomposition -/

/-- A round from the initial accumulators, its eight crumbs fresh, its outputs the variables
`8`, `9`, `10`. -/
private def round1 : EndoScalarRound K :=
  { n0 := .const 0, n8 := .var 8, a0 := .const 2, a8 := .var 9, b0 := .const 2, b8 := .var 10,
    xs := #v[.var 0, .var 1, .var 2, .var 3, .var 4, .var 5, .var 6, .var 7] }

/-- One round, its output `n` accumulator public. -/
private def endoSource : List (KimchiConstraint K) := [.endoScalar [round1]]

private def endoPublic : List Variable := [8]

/-- The crumbs `1 2 3 0 1 2 3 1`, the accumulators they fold to from `0`, `2`, `2`, and the
pinned registers at the allocations `11`, `12`, `13`. -/
private def endoV : Valuation K := fun v =>
  [1, 2, 3, 0, 1, 2, 3, 1, 72, 26, 68, 2, 2, 0].getD v 0

private def endoRows : List (KimchiRow K) := directRows endoSource endoPublic 11

private def endoRoots : Array Variable := directRoots endoSource 11

private def endoIndex? : Option (Index K 16) :=
  Index.build? (gatesOf endoRoots endoRows) endoPublic.length 3 40 0 mds shifts

theorem endo_example_built : endoIndex?.isSome := by
  decide +kernel

private def endoIdx : Index K 16 := endoIndex?.get endo_example_built

private def endoPub : Fin endoIdx.publicCount → K := fun i => endoV (endoPublic.getD i.val 0)

theorem endo_example_scoped : KimchiConstraint.Wired.Scoped 11 endoSource endoPublic := by
  decide +kernel

theorem endo_example_indexOf : IndexOf endoSource endoPublic 11 endoIdx :=
  indexOf_of_classTarget endoSource endoPublic 11 endoIdx (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem endo_example_satisfies : endoIdx.Satisfies endoPub (tableOf endoV endoRows) := by
  decide +kernel

/-- The closed theorem on the one-round instance. -/
theorem endo_example_holds :
    ∃ W : Valuation K, (∀ c ∈ endoSource, KimchiConstraint.Holds W c) ∧
      ∀ i : Fin endoPublic.length,
        W endoPublic[i] = endoPub (endo_example_indexOf.publicIndex i) :=
  KimchiConstraint.Wired.holds_of_satisfies endo_example_scoped endo_example_indexOf endoPub
    (tableOf endoV endoRows) endo_example_satisfies

/-- The one-round log: the registers allocate `11`, `12`, `13` in reduction order `b0`, `a0`,
`n0`; the second `2` hits the first's cache and fuses with it; the two pins pack into the row
before the gate row; the cache hit's class holds the pinned cell and both register cells. -/
theorem endo_example_layout :
    (recordGates endoSource 11 initialAuxState).steps.map (fun s => allocs s.events) =
        [[11, 12, 13]] ∧
      (recordGates endoSource 11 initialAuxState).steps.map (fun s => fusions s.events) =
        [[(12, 11)]] ∧
      (recordGates endoSource 11 initialAuxState).steps.map (fun s => pinsOf s.events) =
        [[(0, 13), (2, 11)]] ∧
      endoRows.length = 3 ∧ gateRowOf endoSource endoPublic 11 0 (by decide) = 2 ∧
      classCells endoRoots endoRows 12 = [(1, 3), (2, 2), (2, 3)] := by
  decide +kernel

/-- A second round threading the first's outputs into its accumulators, its crumbs fresh, its
outputs `19`, `20`, `21`. -/
private def round2 : EndoScalarRound K :=
  { n0 := .var 8, n8 := .var 19, a0 := .var 9, a8 := .var 20, b0 := .var 10, b8 := .var 21,
    xs := #v[.var 11, .var 12, .var 13, .var 14, .var 15, .var 16, .var 17, .var 18] }

/-- Two rounds, the final `n` accumulator public. -/
private def chainSource : List (KimchiConstraint K) := [.endoScalar [round1, round2]]

private def chainPublic : List Variable := [19]

/-- The first round as before, the second's crumbs `2 0 1 3 2 0 1 3` folding its outputs on,
and the pinned registers at the allocations `22`, `23`, `24`. -/
private def chainV : Valuation K := fun v =>
  [1, 2, 3, 0, 1, 2, 3, 1, 72, 26, 68, 2, 0, 1, 3, 2, 0, 1, 3, 55, 96, 85, 2, 2, 0].getD v 0

private def chainRows : List (KimchiRow K) := directRows chainSource chainPublic 22

private def chainRoots : Array Variable := directRoots chainSource 22

private def chainIndex? : Option (Index K 16) :=
  Index.build? (gatesOf chainRoots chainRows) chainPublic.length 3 40 0 mds shifts

theorem chain_example_built : chainIndex?.isSome := by
  decide +kernel

private def chainIdx : Index K 16 := chainIndex?.get chain_example_built

private def chainPub : Fin chainIdx.publicCount → K := fun i =>
  chainV (chainPublic.getD i.val 0)

theorem chain_example_scoped : KimchiConstraint.Wired.Scoped 22 chainSource chainPublic := by
  decide +kernel

theorem chain_example_indexOf : IndexOf chainSource chainPublic 22 chainIdx :=
  indexOf_of_classTarget chainSource chainPublic 22 chainIdx (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

theorem chain_example_satisfies : chainIdx.Satisfies chainPub (tableOf chainV chainRows) := by
  decide +kernel

/-- The closed theorem on the two-round instance. -/
theorem chain_example_holds :
    ∃ W : Valuation K, (∀ c ∈ chainSource, KimchiConstraint.Holds W c) ∧
      ∀ i : Fin chainPublic.length,
        W chainPublic[i] = chainPub (chain_example_indexOf.publicIndex i) :=
  KimchiConstraint.Wired.holds_of_satisfies chain_example_scoped chain_example_indexOf chainPub
    (tableOf chainV chainRows) chain_example_satisfies

/-- The two-round layout: the second round logs nothing, the block's rows are the third and
fourth, and each threaded accumulator's class holds the first row's output cell and the
second row's input cell, the public one also its public cell. -/
theorem chain_example_layout :
    (recordGates chainSource 22 initialAuxState).steps.map (fun s => allocs s.events) =
        [[22, 23, 24]] ∧
      chainRows.length = 4 ∧ gateRowOf chainSource chainPublic 22 0 (by decide) = 2 ∧
      classCells chainRoots chainRows 8 = [(2, 1), (3, 0)] ∧
      classCells chainRoots chainRows 9 = [(2, 4), (3, 2)] ∧
      classCells chainRoots chainRows 10 = [(2, 5), (3, 3)] ∧
      classCells chainRoots chainRows 19 = [(0, 0), (3, 1)] := by
  decide +kernel

/-! ## Its boundaries -/

/-- The chain with a crumb of the second round reused by a Boolean. -/
private def reusedSource : List (KimchiConstraint K) :=
  chainSource ++ [.basic (.boolean (.var 12))]

/-- The second round with a crumb written as a sum. -/
private def summedRound : EndoScalarRound K :=
  { round2 with
    xs := #v[.var 11, .var 12, .var 13, .add (.var 14) (.var 15), .var 15, .var 16, .var 17,
      .var 18] }

/-- A reused bare crumb keeps every constraint wired and breaks the scope; a summed crumb is
not wired. -/
theorem endo_rejections :
    ((∀ c ∈ reusedSource, c.Wired) ∧
      ¬ KimchiConstraint.Wired.Scoped 22 reusedSource chainPublic) ∧
    ¬ (KimchiConstraint.endoScalar [round1, summedRound]).Wired := by
  decide +kernel

end Snarky.Kimchi
