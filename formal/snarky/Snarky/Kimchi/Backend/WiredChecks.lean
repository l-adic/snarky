import Snarky.Kimchi.Backend.Wired
import Snarky.Kimchi.Backend.CompiledIndex
import Snarky.Kimchi.Backend.WiredFixtures
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.NormNum.Prime

/-!
# Wired-fragment checks

One lowering of the fragment decided end to end over a field of 113 elements: a public variable
pinned to a constant, two variables merged, a complete addition with a sum and a scaled
variable among its wired operands, a second variable hitting the constant's cache, a Boolean on
the merged variable. The index is built from the lowering's rows and the class-based wiring by
`Index.build?`, its table satisfies it, and the closed theorem is invoked on them. Then the
boundaries, one for each premise: a constant in an unwired slot, an unwired operand named again
by a rowless merge or by a term of the sum, a variable at the counter, each out of scope; a
table splitting the merged class or drifting the intermediate from its pinning cell, every gate
holding, fails the index; an index with the packed row's coefficients altered or the pinned
variable's copy wire rerouted is not the lowering's.

Then a challenge decomposition, in two lowerings. One round from the initial accumulators, its
crumbs fresh and its output `n` public: its two `2`s pin one allocation through the cache and
its `0` another, the pins packed in one row before the gate row. Two rounds, the second's
accumulators the first's outputs: the block's second row one past its first, each threaded
accumulator one class across both. Their boundaries: a crumb reused by a Boolean keeps every
constraint wired and breaks the scope; a crumb written as a sum is not wired.

Then a scalar multiplication, whose row pairs the index reads through the successor row: one
round from a base and an accumulator of distinct abscissae, its register pinned in the row
flushed last, its output public; two rounds threading the output accumulator and register, the
second pair at block offset two. Its boundaries: a slope reused by a Boolean keeps every
constraint wired and breaks the scope; a summed accumulator is not wired; the second row's
output abscissa altered fails the gate at the first row.

Then an endomorphism multiplication of two rounds at a nonzero coefficient, both selecting the
endomorphism, the second's inputs the first's outputs by the successor read alone, their wired
cells singleton classes, the finals public in the terminal row. Its boundaries: a slope reused
by a Boolean breaks the scope; a summed midpoint is not wired; the terminal row's output
abscissa altered fails the gate at the last round's row; an index at another coefficient
disagrees with the source's parameter.

Then a Poseidon block of two windows, eleven states from the round function at a small matrix
and ten distinct nonzero constants, one input element pinned, the output state public in the
terminal row. Its boundaries: an unwired state element reused by a Boolean breaks the scope; a
summed one is not wired; five or seven states are off the shape, not wired; the terminal row's
first cell altered fails the gate at the last window's row; indices at another matrix or with a
consumed constant altered fail the parameters or the coefficients.

Then a padding row among `Basic` constraints, its seven cells all wired: bare variables, a sum
and a scaled variable through their intermediates, and a constant hitting the pinned variable's
cache. It asserts nothing and only wires. Its boundaries: a padding row naming another gate's
unwired operand keeps every constraint wired and breaks the scope; a table altering one of its
cells, every gate holding, breaks the copy constraint.

## Main results

- `wired_example_holds`, `endo_example_holds`, `chain_example_holds`, `scale_example_holds`,
  `scaleChain_example_holds`, `endoMul_example_holds`, `poseidon_example_holds`,
  `pad_example_holds`, and `wired_example_holds_compiled` through `compiledIndex?`'s index.
- `wired_rejections_scope`, `wired_rejections_table`, `wired_rejections_index`,
  `endo_rejections`, `scale_rejections`, `endoMul_rejections`, `endoMul_rejections_index`,
  `poseidon_rejections`, `poseidon_rejections_index`, `pad_rejections`: boundaries by premise.
- `endo_example_layout`, `chain_example_layout`, `scale_example_layout`,
  `scaleChain_example_layout`, `endoMul_example_layout`, `poseidon_example_layout`,
  `pad_example_layout`: the lowerings' logs, rows and classes.
-/

open Kimchi

namespace Snarky.Kimchi

open Snarky

instance : Fact (Nat.Prime 113) := ⟨by norm_num⟩

open WiredFixture

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

/-- The compiler's constructor on the first source: its index, by the class-based gates. -/
private def compiledIdx : Index K 16 :=
  (indexOfGates? (classGates roots rows) source publicVars.length 16 3 40 0 mds shifts).get
    (by decide +kernel)

/-- The constructor returns that index. -/
private theorem compiled_eq :
    compiledIndex? source publicVars 20 16 3 40 0 mds shifts = some compiledIdx := by
  rw [compiledIndex?, directGates_eq_classGates]
  exact (Option.some_get _).symm

private def compiledPub : Fin compiledIdx.publicCount → K := fun i =>
  V (publicVars.getD i.val 0)

/-- The closed theorem on the same table through the compiler's own index, its
correspondence derived by `compiledIndex?_indexOf`. -/
theorem wired_example_holds_compiled :
    ∃ W : Valuation K, (∀ c ∈ source, KimchiConstraint.Holds W c) ∧
      ∀ i : Fin publicVars.length,
        W publicVars[i] = compiledPub ((compiledIndex?_indexOf compiled_eq).publicIndex i) :=
  KimchiConstraint.Wired.holds_of_satisfies wired_example_scoped
    (compiledIndex?_indexOf compiled_eq) compiledPub table (by decide +kernel)

/-! ## Boundaries -/

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

/-- A reused bare crumb keeps every constraint wired and breaks the scope; a summed crumb is
not wired. -/
theorem endo_rejections :
    ((∀ c ∈ reusedSource, c.Wired) ∧
      ¬ KimchiConstraint.Wired.Scoped 22 reusedSource chainPublic) ∧
    ¬ (KimchiConstraint.endoScalar [round1, summedRound]).Wired := by
  decide +kernel

/-! ## A scalar multiplication -/

/-- The base `(3, 5)`, the accumulator `(7, 11)`, the bits `1 0 1 1 0`, and the accumulators,
register and slopes the gate's builder derives, the pinned register at the allocation `25`. -/
private def scaleV : Valuation K := fun v =>
  [3, 5, 7, 11, 20, 82, 34, 104, 76, 94, 22, 30, 22, 24, 24, 1, 0, 1, 1, 0, 58, 45, 36, 91, 97,
    0].getD v 0

private def scaleRows : List (KimchiRow K) := directRows scaleSource scalePublic 25

private def scaleRoots : Array Variable := directRoots scaleSource 25

private def scaleIndex? : Option (Index K 16) :=
  Index.build? (gatesOf scaleRoots scaleRows) scalePublic.length 3 40 0 mds shifts

theorem scale_example_built : scaleIndex?.isSome := by
  decide +kernel

private def scaleIdx : Index K 16 := scaleIndex?.get scale_example_built

private def scalePub : Fin scaleIdx.publicCount → K := fun i =>
  scaleV (scalePublic.getD i.val 0)

theorem scale_example_scoped : KimchiConstraint.Wired.Scoped 25 scaleSource scalePublic := by
  decide +kernel

theorem scale_example_indexOf : IndexOf scaleSource scalePublic 25 scaleIdx :=
  indexOf_of_classTarget scaleSource scalePublic 25 scaleIdx (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

theorem scale_example_satisfies : scaleIdx.Satisfies scalePub (tableOf scaleV scaleRows) := by
  decide +kernel

/-- The closed theorem on the one-round instance. -/
theorem scale_example_holds :
    ∃ W : Valuation K, (∀ c ∈ scaleSource, KimchiConstraint.Holds W c) ∧
      ∀ i : Fin scalePublic.length,
        W scalePublic[i] = scalePub (scale_example_indexOf.publicIndex i) :=
  KimchiConstraint.Wired.holds_of_satisfies scale_example_scoped scale_example_indexOf scalePub
    (tableOf scaleV scaleRows) scale_example_satisfies

/-- The one-round layout: the register's allocation is pinned in the row flushed after the
pair, its two cells one class; the pair follows the two public rows, whose cells join the
output accumulator's. -/
theorem scale_example_layout :
    (recordGates scaleSource 25 initialAuxState).steps.map (fun s => allocs s.events) = [[25]] ∧
      (recordGates scaleSource 25 initialAuxState).steps.map (fun s => pinsOf s.events) =
        [[(0, 25)]] ∧
      scaleRows.length = 5 ∧ gateRowOf scaleSource scalePublic 25 0 (by decide) = 2 ∧
      classCells scaleRoots scaleRows 25 = [(2, 4), (4, 0)] ∧
      classCells scaleRoots scaleRows 13 = [(0, 0), (3, 0)] := by
  decide +kernel

/-- The first round as before, the second's bits `0 1 1 0 1` folding its outputs on, and the
pinned register at the allocation `46`. -/
private def scaleChainV : Valuation K := fun v =>
  [3, 5, 7, 11, 20, 82, 34, 104, 76, 94, 22, 30, 22, 24, 24, 1, 0, 1, 1, 0, 58, 45, 36, 91, 97,
    70, 55, 94, 15, 58, 18, 68, 52, 39, 6, 7, 0, 1, 1, 0, 1, 109, 107, 92, 60, 72, 0].getD v 0

private def scaleChainRows : List (KimchiRow K) :=
  directRows scaleChainSource scaleChainPublic 46

private def scaleChainRoots : Array Variable := directRoots scaleChainSource 46

private def scaleChainIndex? : Option (Index K 16) :=
  Index.build? (gatesOf scaleChainRoots scaleChainRows) scaleChainPublic.length 3 40 0 mds
    shifts

theorem scaleChain_example_built : scaleChainIndex?.isSome := by
  decide +kernel

private def scaleChainIdx : Index K 16 := scaleChainIndex?.get scaleChain_example_built

private def scaleChainPub : Fin scaleChainIdx.publicCount → K := fun i =>
  scaleChainV (scaleChainPublic.getD i.val 0)

theorem scaleChain_example_scoped :
    KimchiConstraint.Wired.Scoped 46 scaleChainSource scaleChainPublic := by
  decide +kernel

theorem scaleChain_example_indexOf :
    IndexOf scaleChainSource scaleChainPublic 46 scaleChainIdx :=
  indexOf_of_classTarget scaleChainSource scaleChainPublic 46 scaleChainIdx (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

theorem scaleChain_example_satisfies :
    scaleChainIdx.Satisfies scaleChainPub (tableOf scaleChainV scaleChainRows) := by
  decide +kernel

/-- The closed theorem on the two-round instance. -/
theorem scaleChain_example_holds :
    ∃ W : Valuation K, (∀ c ∈ scaleChainSource, KimchiConstraint.Holds W c) ∧
      ∀ i : Fin scaleChainPublic.length,
        W scaleChainPublic[i] = scaleChainPub (scaleChain_example_indexOf.publicIndex i) :=
  KimchiConstraint.Wired.holds_of_satisfies scaleChain_example_scoped
    scaleChain_example_indexOf scaleChainPub (tableOf scaleChainV scaleChainRows)
    scaleChain_example_satisfies

/-- The two-round layout: the second pair at the fifth and sixth rows, the base one class
across both first rows, the threaded accumulator and register each one class across the pair
boundary, the final accumulator's cells joining the public rows. -/
theorem scaleChain_example_layout :
    scaleChainRows.length = 7 ∧ gateRowOf scaleChainSource scaleChainPublic 46 0 (by decide) = 2 ∧
      classCells scaleChainRoots scaleChainRows 0 = [(2, 0), (4, 0)] ∧
      classCells scaleChainRoots scaleChainRows 12 = [(2, 5), (4, 4)] ∧
      classCells scaleChainRoots scaleChainRows 13 = [(3, 0), (4, 2)] ∧
      classCells scaleChainRoots scaleChainRows 14 = [(3, 1), (4, 3)] ∧
      classCells scaleChainRoots scaleChainRows 34 = [(0, 0), (5, 0)] := by
  decide +kernel

/-! ## Its boundaries -/

/-- The one-round table with the second row's output abscissa raised by one. -/
private def shiftedTable : Fin 16 → Fin wCols → K := fun i j =>
  if i.val = 3 ∧ j.val = 0 then tableOf scaleV scaleRows i j + 1 else tableOf scaleV scaleRows i j

/-- A reused bare slope keeps every constraint wired and breaks the scope; a summed
accumulator is not wired; the altered successor row fails the gate at the first row. -/
theorem scale_rejections :
    ((∀ c ∈ reusedScale, c.Wired) ∧
      ¬ KimchiConstraint.Wired.Scoped 25 reusedScale scalePublic) ∧
    ¬ (KimchiConstraint.varBaseMul [summedScale]).Wired ∧
    ¬ Index.rowSatisfies scaleIdx scalePub shiftedTable ⟨2, by decide⟩ := by
  decide +kernel

/-! ## An endomorphism multiplication -/

/-- The target `(3, 5)`, the accumulator `(7, 11)`, the bits `1 0 1 1` then `0 1 1 0`, and the
inverses, midpoints, slopes, outputs and registers solving the gate at the coefficient `2`,
the pinned register at the allocation `28`. -/
private def endoMulV : Valuation K := fun v =>
  [3, 5, 7, 11, 42, 27, 14, 16, 65, 1, 0, 1, 1, 57, 19, 11, 30, 109, 96, 17, 69, 0, 1, 1, 0,
    73, 91, 69, 0].getD v 0

private def endoMulRows : List (KimchiRow K) := directRows endoMulSource endoMulPublic 28

private def endoMulRoots : Array Variable := directRoots endoMulSource 28

private def endoMulIndex? : Option (Index K 16) :=
  Index.build? (gatesOf endoMulRoots endoMulRows) endoMulPublic.length 3 40 2 mds shifts

theorem endoMul_example_built : endoMulIndex?.isSome := by
  decide +kernel

private def endoMulIdx : Index K 16 := endoMulIndex?.get endoMul_example_built

private def endoMulPub : Fin endoMulIdx.publicCount → K := fun i =>
  endoMulV (endoMulPublic.getD i.val 0)

theorem endoMul_example_scoped :
    KimchiConstraint.Wired.Scoped 28 endoMulSource endoMulPublic := by
  decide +kernel

theorem endoMul_example_indexOf : IndexOf endoMulSource endoMulPublic 28 endoMulIdx :=
  indexOf_of_classTarget endoMulSource endoMulPublic 28 endoMulIdx (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

theorem endoMul_example_satisfies :
    endoMulIdx.Satisfies endoMulPub (tableOf endoMulV endoMulRows) := by
  decide +kernel

/-- The closed theorem on the two-round instance. -/
theorem endoMul_example_holds :
    ∃ W : Valuation K, (∀ c ∈ endoMulSource, KimchiConstraint.Holds W c) ∧
      ∀ i : Fin endoMulPublic.length,
        W endoMulPublic[i] = endoMulPub (endoMul_example_indexOf.publicIndex i) :=
  KimchiConstraint.Wired.holds_of_satisfies endoMul_example_scoped endoMul_example_indexOf
    endoMulPub (tableOf endoMulV endoMulRows) endoMul_example_satisfies

/-- The layout: the register's allocation pinned in the row flushed after the block; the two
round rows at the fourth and fifth, the terminal row at the sixth; the target one class across
both round rows; the second round's input accumulator a singleton class, no copy constraint
linking it to the first round, whose outputs reach it by the successor read; the finals'
cells joining the public rows. -/
theorem endoMul_example_layout :
    (recordGates endoMulSource 28 initialAuxState).steps.map (fun s => allocs s.events) =
        [[28]] ∧
      (recordGates endoMulSource 28 initialAuxState).steps.map (fun s => pinsOf s.events) =
        [[(0, 28)]] ∧
      endoMulRows.length = 7 ∧ gateRowOf endoMulSource endoMulPublic 28 0 (by decide) = 3 ∧
      classCells endoMulRoots endoMulRows 28 = [(3, 6), (6, 0)] ∧
      classCells endoMulRoots endoMulRows 0 = [(3, 0), (4, 0)] ∧
      classCells endoMulRoots endoMulRows 13 = [(4, 4)] ∧
      classCells endoMulRoots endoMulRows 25 = [(0, 0), (5, 4)] := by
  decide +kernel

/-! ## Its boundaries -/

/-- The table with the terminal row's output abscissa raised by one. -/
private def shiftedEndoMulTable : Fin 16 → Fin wCols → K := fun i j =>
  if i.val = 5 ∧ j.val = 4 then tableOf endoMulV endoMulRows i j + 1
  else tableOf endoMulV endoMulRows i j

/-- A reused bare slope keeps every constraint wired and breaks the scope; a summed midpoint
is not wired; the altered terminal row fails the gate at the last round's row. -/
theorem endoMul_rejections :
    ((∀ c ∈ reusedEndoMul, c.Wired) ∧
      ¬ KimchiConstraint.Wired.Scoped 28 reusedEndoMul endoMulPublic) ∧
    ¬ (KimchiConstraint.endoMul summedEndoMul).Wired ∧
    ¬ Index.rowSatisfies endoMulIdx endoMulPub shiftedEndoMulTable ⟨4, by decide⟩ := by
  decide +kernel

/-- The same gate table built at the coefficient `3`. -/
private def endoMulIndex3? : Option (Index K 16) :=
  Index.build? (gatesOf endoMulRoots endoMulRows) endoMulPublic.length 3 40 3 mds shifts

private theorem built_endoMul3 : endoMulIndex3?.isSome := by
  decide +kernel

/-- The index at the other coefficient builds from the same rows and wiring, and is not the
lowering's: the source's coefficient disagrees with it. -/
theorem endoMul_rejections_index :
    ¬ (KimchiConstraint.endoMul emul).ParamsAgree (endoMulIndex3?.get built_endoMul3).mds
        (endoMulIndex3?.get built_endoMul3).endoBase ∧
      ¬ IndexOf endoMulSource endoMulPublic 28 (endoMulIndex3?.get built_endoMul3) :=
  ⟨by decide +kernel, fun h => absurd (h.params _ (List.mem_singleton_self _)) (by decide +kernel)⟩

/-! ## A Poseidon block -/

/-- The input `(3, 5, 0)` and the ten states the round function derives at the matrix and
constants, the pinned element at the allocation `32`. -/
private def poseidonV : Valuation K := fun v =>
  [3, 5, 12, 33, 54, 75, 25, 40, 111, 42, 21, 31, 101, 18, 17, 98, 110, 4, 51, 58, 51, 38, 103,
    26, 8, 38, 95, 74, 5, 14, 91, 97, 0].getD v 0

private def poseidonRows : List (KimchiRow K) := directRows poseidonSource poseidonPublic 32

private def poseidonRoots : Array Variable := directRoots poseidonSource 32

private def poseidonIndex? : Option (Index K 16) :=
  Index.build? (gatesOf poseidonRoots poseidonRows) poseidonPublic.length 3 40 0 poseidonMds
    shifts

theorem poseidon_example_built : poseidonIndex?.isSome := by
  decide +kernel

private def poseidonIdx : Index K 16 := poseidonIndex?.get poseidon_example_built

private def poseidonPub : Fin poseidonIdx.publicCount → K := fun i =>
  poseidonV (poseidonPublic.getD i.val 0)

theorem poseidon_example_scoped :
    KimchiConstraint.Wired.Scoped 32 poseidonSource poseidonPublic := by
  decide +kernel

theorem poseidon_example_indexOf : IndexOf poseidonSource poseidonPublic 32 poseidonIdx :=
  indexOf_of_classTarget poseidonSource poseidonPublic 32 poseidonIdx (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

theorem poseidon_example_satisfies :
    poseidonIdx.Satisfies poseidonPub (tableOf poseidonV poseidonRows) := by
  decide +kernel

/-- The closed theorem on the two-window instance. -/
theorem poseidon_example_holds :
    ∃ W : Valuation K, (∀ c ∈ poseidonSource, KimchiConstraint.Holds W c) ∧
      ∀ i : Fin poseidonPublic.length,
        W poseidonPublic[i] = poseidonPub (poseidon_example_indexOf.publicIndex i) :=
  KimchiConstraint.Wired.holds_of_satisfies poseidon_example_scoped poseidon_example_indexOf
    poseidonPub (tableOf poseidonV poseidonRows) poseidon_example_satisfies

/-- The layout: the pinned element's allocation in the row flushed after the block; the two
window rows at the fourth and fifth, the terminal row at the sixth; the second window's first
state a singleton class in the first wired cells of its row, reached from the first window by
the successor read; the output state's cells joining the public rows. -/
theorem poseidon_example_layout :
    (recordGates poseidonSource 32 initialAuxState).steps.map (fun s => allocs s.events) =
        [[32]] ∧
      (recordGates poseidonSource 32 initialAuxState).steps.map (fun s => pinsOf s.events) =
        [[(0, 32)]] ∧
      poseidonRows.length = 7 ∧ gateRowOf poseidonSource poseidonPublic 32 0 (by decide) = 3 ∧
      classCells poseidonRoots poseidonRows 32 = [(3, 2), (6, 0)] ∧
      classCells poseidonRoots poseidonRows 14 = [(4, 0)] ∧
      classCells poseidonRoots poseidonRows 29 = [(0, 0), (5, 0)] := by
  decide +kernel

/-! ## Its boundaries -/

/-- The table with the terminal row's first cell raised by one. -/
private def shiftedPoseidonTable : Fin 16 → Fin wCols → K := fun i j =>
  if i.val = 5 ∧ j.val = 0 then tableOf poseidonV poseidonRows i j + 1
  else tableOf poseidonV poseidonRows i j

/-- A reused bare state element keeps every constraint wired and breaks the scope; a summed
one is not wired; five or seven states are not wired; the altered terminal row fails the gate
at the last window's row. -/
theorem poseidon_rejections :
    ((∀ c ∈ reusedPoseidon, c.Wired) ∧
      ¬ KimchiConstraint.Wired.Scoped 32 reusedPoseidon poseidonPublic) ∧
    ¬ (KimchiConstraint.poseidon summedPoseidon).Wired ∧
    ¬ (KimchiConstraint.poseidon { pblock with state := pblock.state.take 5 }).Wired ∧
    ¬ (KimchiConstraint.poseidon { pblock with state := pblock.state.take 7 }).Wired ∧
    ¬ Index.rowSatisfies poseidonIdx poseidonPub shiftedPoseidonTable ⟨4, by decide⟩ := by
  decide +kernel

/-- The same gate table built at another matrix. -/
private def poseidonIndexMds? : Option (Index K 16) :=
  Index.build? (gatesOf poseidonRoots poseidonRows) poseidonPublic.length 3 40 0
    { poseidonMds with m00 := 2 } shifts

private theorem built_poseidonMds : poseidonIndexMds?.isSome := by
  decide +kernel

/-- The gate table with the first window row's fifth coefficient, round one's second
constant, raised by one. -/
private def gatesPoseidonRc : Fin 16 → Index.GateRow K 16 := fun i =>
  if i.val = 3 then
    { gatesOf poseidonRoots poseidonRows i with coeffs := fun c =>
        if c.val = 4 then (gatesOf poseidonRoots poseidonRows i).coeffs c + 1
        else (gatesOf poseidonRoots poseidonRows i).coeffs c }
  else gatesOf poseidonRoots poseidonRows i

private def poseidonIndexRc? : Option (Index K 16) :=
  Index.build? gatesPoseidonRc poseidonPublic.length 3 40 0 poseidonMds shifts

private theorem built_poseidonRc : poseidonIndexRc?.isSome := by
  decide +kernel

/-- Both indices build from the same rows and wiring, and neither is the lowering's: the one
at another matrix disagrees with the source's parameter, the one with an altered constant
with the window row's coefficients. -/
theorem poseidon_rejections_index :
    (¬ (KimchiConstraint.poseidon pblock).ParamsAgree (poseidonIndexMds?.get built_poseidonMds).mds
        (poseidonIndexMds?.get built_poseidonMds).endoBase ∧
      ¬ IndexOf poseidonSource poseidonPublic 32 (poseidonIndexMds?.get built_poseidonMds)) ∧
    ¬ IndexOf poseidonSource poseidonPublic 32 (poseidonIndexRc?.get built_poseidonRc) := by
  refine ⟨⟨by decide +kernel, fun h => absurd (h.params _ (List.mem_singleton_self _))
    (by decide +kernel)⟩, fun h => ?_⟩
  have hc := h.coeffs ⟨3, by decide⟩ (by rw [length_directGates]; decide +kernel) ⟨4, by decide⟩
  rw [getElem_directGates poseidonSource poseidonPublic 32 3 (by decide +kernel)] at hc
  exact absurd hc (by decide +kernel)

/-! ## A padding row -/

/-- The pinned `5`, the Boolean `1`, and the padding row's intermediates: the sum `1 + 10` at
the allocation `5`, the constant at `6`, the double `2 · 7` at `7`. -/
private def padV : Valuation K := fun v => [5, 1, 10, 7, 9, 11, 5, 14].getD v 0

private def padRows : List (KimchiRow K) := directRows padSource padPublic 5

private def padRoots : Array Variable := directRoots padSource 5

private def padIndex? : Option (Index K 16) :=
  Index.build? (gatesOf padRoots padRows) padPublic.length 3 40 0 mds shifts

theorem pad_example_built : padIndex?.isSome := by
  decide +kernel

private def padIdx : Index K 16 := padIndex?.get pad_example_built

private def padPub : Fin padIdx.publicCount → K := fun i => padV (padPublic.getD i.val 0)

theorem pad_example_scoped : KimchiConstraint.Wired.Scoped 5 padSource padPublic := by
  decide +kernel

theorem pad_example_indexOf : IndexOf padSource padPublic 5 padIdx :=
  indexOf_of_classTarget padSource padPublic 5 padIdx (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem pad_example_satisfies : padIdx.Satisfies padPub (tableOf padV padRows) := by
  decide +kernel

/-- The closed theorem on the padded instance. -/
theorem pad_example_holds :
    ∃ W : Valuation K, (∀ c ∈ padSource, KimchiConstraint.Holds W c) ∧
      ∀ i : Fin padPublic.length, W padPublic[i] = padPub (pad_example_indexOf.publicIndex i) :=
  KimchiConstraint.Wired.holds_of_satisfies pad_example_scoped pad_example_indexOf padPub
    (tableOf padV padRows) pad_example_satisfies

/-- The layout: the padding row is the third, a generic row without coefficients; its sum,
constant and double allocate `5`, `6`, `7`; the constant hits the pin's cache, so one class
holds the public cell, the pin's and the row's first and fourth cells; the sum's intermediate
ties its defining row to its padding cell, the Boolean's variable its padding cell to the
Boolean's row. -/
theorem pad_example_layout :
    (recordGates padSource 5 initialAuxState).steps.map (fun s => allocs s.events) =
        [[], [5, 6, 7], []] ∧
      (recordGates padSource 5 initialAuxState).steps.map (fun s => fusions s.events) =
        [[], [(6, 0)], []] ∧
      padRows.length = 4 ∧ gateRowOf padSource padPublic 5 1 (by decide) = 2 ∧
      padRows[2]?.map (fun r => (r.kind, r.coeffs)) = some (.generic, []) ∧
      classCells padRoots padRows 6 = [(0, 0), (1, 3), (2, 0), (2, 3)] ∧
      classCells padRoots padRows 5 = [(1, 2), (2, 2)] ∧
      classCells padRoots padRows 1 = [(1, 0), (2, 1), (3, 0), (3, 1)] := by
  decide +kernel

/-! ## Its boundaries -/

/-- The table with the padding row's second cell, the Boolean's variable, set to `0`. -/
private def padSplitTable : Fin 16 → Fin wCols → K := fun i j =>
  if i.val = 2 ∧ j.val = 1 then 0 else tableOf padV padRows i j

/-- A padding row naming another gate's unwired operand keeps every constraint wired and
breaks the scope; a table altering one of its cells, every gate still holding, breaks the copy
constraint. -/
theorem pad_rejections :
    ((∀ c ∈ padReuse, c.Wired) ∧ ¬ KimchiConstraint.Wired.Scoped 20 padReuse publicVars) ∧
    ((∀ i, Index.rowSatisfies padIdx padPub padSplitTable i) ∧
      ¬ padIdx.Satisfies padPub padSplitTable) := by
  decide +kernel

end Snarky.Kimchi
