# Compiler lowering trace: design and implementation handoff

## Objective and boundary

Design a trace of Lean's existing Kimchi lowering, then use it to prove the first
source-to-row correspondence results. The eventual direction is:

```text
arbitrary table satisfying the emitted Kimchi index
  → a valuation satisfying the original source constraints
    with the same public inputs
  → existing Snarky/Pickles capstones apply
```

The witness table must be arbitrary: do not assume it came from `makeWitness`,
`reduceSolved`, or the honest prover. This is deterministic compiler correctness,
not cryptographic soundness of Kimchi or IPA, and not honest-prover completeness.

The motivation is to transfer the Pickles capstones to applications reconstructed
from exported rules and shape, once their emitted constraint systems are certified
equivalent to the original application's. The trace is internal Lean compiler data.
It does not require a new PureScript export, fixture schema, or proof format.

This phase deliberately stops before the entire compiler theorem. It must deliver:

1. A recorded lowering with a proved erasure relationship to the existing lowering.
2. Explicit structural trace validity and separate semantic interpretation.
3. Correspondence for `Basic.boolean` and `AddComplete`.
4. A small theorem from **arbitrary matrix satisfaction**, closing the semantic
   premises for a precisely restricted fragment described below.

The design below has landed in `snarky/Snarky/Kimchi/Backend/` (see section 7 for the
modules and section 8 for the checks). The declarations quoted in sections 1 to 5 are the
design signatures the implementation was elaborated from; where a landed name or shape
differs, section 6 onward states the landed one. No `sorry` or axiom was added.

## Starting point

The trace and its theorems landed on branch `formal/compiler-trace`, the wired fragment of
section 10 on `formal/wired-fragment`. Read `CLAUDE.md` and `formal/CLAUDE.md` before
touching them. Helpers stay private until a concrete consumer
needs them. The Pickles capstones, the fixture schema, the emitted rows and the wiring are
unchanged.

Relevant existing files, relative to `formal/`:

| File | Existing machinery to reuse |
| --- | --- |
| `snarky/Snarky/CVar.lean` | `CVar.reduce_val`, `CVar.ScopedBy`, affine evaluation |
| `snarky/Snarky/Constraint/Basic.lean` | `Basic.Holds`, including Booleanity |
| `snarky/Snarky/Kimchi/Constraint/Types.lean` | `KimchiRow`, generic constraints, `AuxState` |
| `snarky/Snarky/Kimchi/Constraint/Reduction.lean` | reduction operations, both interpreters, batching/cache |
| `snarky/Snarky/Kimchi/Constraint/GenericPlonk.lean` | `reduce : Basic F → m Unit` |
| `snarky/Snarky/Kimchi/Constraint/AddComplete.lean` | `AddComplete.reduce` |
| `snarky/Snarky/Kimchi/Constraint.lean` | grouped `KimchiGate`, dispatch, flattening |
| `snarky/Snarky/Kimchi/Backend/Compile.lean` | `reduceStep`, `reduceGates`, `reduceBuilt`, `gateDataOf` |
| `snarky/Snarky/Kimchi/Backend/Assemble.lean` | public rows, wiring, assembly |
| `snarky/Snarky/Kimchi/Semantics.lean` | `AddComplete.read`, `KimchiConstraint.Holds` |
| `kimchi/Kimchi/Lift.lean` | backend `rowWitness`/`cellMap` readings |
| `kimchi/Kimchi/Index/{Basic,Satisfies}.lean` | `Index`, `build?`, `Index.Satisfies` |
| `pickles/PicklesFixture/Satisfies.lean` | current fixture-only tag/index adapter |

There are no general semantic proofs of backend lowering in those compiler files.
Existing gate proofs and source-level `builder_spec_iff` are reusable; they do not
already connect arbitrary matrices to source valuations.

## 1. What the trace records

Keep `KimchiRow` and `KimchiGate` unchanged. Return provenance alongside compilation,
retaining the existing grouped gates until flattening. Do not attach arbitrary
semantic claims to individual matrix rows.

There are two different pieces of provenance:

- **Reduction operations:** how operands were reduced, before generic batching.
- **Placement:** where flushed generic rows and custom blocks occur after flattening.

Start with the following data vocabulary in namespace `Snarky.Kimchi`:
For proof signatures below, supply the ordinary field/decidable-equality instances,
and `[NeZero n]` where using `Index.Satisfies`. Implicit binders are omitted for
readability; these are interface sketches, not copy-paste compilation units.

```lean
inductive ReductionEvent (F : Type) where
  | alloc (v : Variable) (expression : AffineExpression F)
  | generic (constraint : GenericPlonkConstraint F)
  | equal (constraint : EqualsConstraint F)

structure RecordedReduction (F : Type) (α : Type) where
  result : α
  events : List (ReductionEvent F)
  rows : List (Rows F)
  nextVariable : Variable
  aux : AuxState F

def RecordedReduction.erase (r : RecordedReduction F α) :
    α × List (Rows F) × Variable × AuxState F :=
  (r.result, r.rows, r.nextVariable, r.aux)

structure RowSpan where
  first : Nat
  count : Nat

structure StepPlacement where
  genericRows : RowSpan
  customRows : RowSpan
```

An array/list of step records is in source-constraint order. Its position identifies
the source constraint; do not also store a source copy and numeric source identifier.
`customRows.count = 0` for a Basic constraint. Row spans initially count body rows,
before public rows. A shared translation adds the public-row prefix later.

Events are ordered exactly as executed. Their indices, together with the source-step
index, are stable references for later generic-equation receipts. An allocation's
expression records intended advice computation; **it is not an equation**.

Do not retain full compiler-state snapshots per event. They would duplicate large
union-find tables and turn a useful trace into an expensive execution history.

### Recording mechanism

Implement a `PlonkReductionM` interpreter wrapping the existing `PlonkBuilder`:

```lean
structure RecordingState (F : Type) where
  core : BuilderReductionState F
  eventsRev : List (ReductionEvent F)

abbrev RecordingBuilder (F : Type) := StateM (RecordingState F)

def recordReduction
    (nextVariable : Variable) (aux : AuxState F)
    (action : RecordingBuilder F α) : RecordedReduction F α := ...
```

Each operation delegates to the existing builder instance, then records its payload
and, for allocation, returned variable. Reverse once on exit, like `reduceAsBuilder`.
Run the **existing polymorphic reducers** in this interpreter. Do not copy their
algorithms or reconstruct expressions by inspecting emitted coefficient rows.

The builder instance ignores an allocation's expression today. Recording retains it
without changing allocation or assigning any extra constraint to it.

Prove erasure for the reducers actually used, not a parametricity theorem claimed
without proof for arbitrary polymorphic Lean code:

```lean
theorem record_reduceToVariable_erases (nv aux x) :
    (recordReduction nv aux (reduceToVariable x)).erase =
      reduceAsBuilder nv aux (reduceToVariable x) := ...

theorem record_boolean_erases (nv aux x) :
    (recordReduction nv aux (reduce (.boolean x))).erase =
      reduceAsBuilder nv aux (reduce (.boolean x)) := ...

theorem record_addComplete_erases (nv aux c) :
    (recordReduction nv aux c.reduce).erase =
      reduceAsBuilder nv aux c.reduce := ...
```

The interpreter types on the right and left select the two existing-algorithm
instantiations. Supply explicit type annotations in the implementation as needed.
Factor a relation between interpreter states and reusable operation/bind simulation
lemmas; the arithmetic algorithm should not be reproved separately for erasure.

## 2. Structural validity has no witness or valuation argument

Use a replay relation for the operations. It checks allocation returns the current
counter, invokes the existing builder primitive, and advances to its resulting state.
Its inputs are a start state, event list, and end state:

```lean
def EventsReplay (start : BuilderReductionState F)
    (events : List (ReductionEvent F))
    (finish : BuilderReductionState F) : Prop := ...

def RecordedReduction.finish (r : RecordedReduction F α) : BuilderReductionState F :=
  { constraints := r.rows.reverse.map Rows.row
    nextVariable := r.nextVariable
    aux := r.aux }

theorem record_boolean_replays (nv aux x) :
    let r := recordReduction nv aux (reduce (.boolean x))
    EventsReplay ⟨[], nv, aux⟩ r.events r.finish := ...
```

Give `reduceToVariable` and `AddComplete.reduce` corresponding replay lemmas.
Do not state this for arbitrary `RecordingBuilder` computations: unrestricted
`StateM` code could mutate the core without logging an event. Prove preservation
for the recording operations and their compositions used by the actual reducers.

`EventsReplay` accounts for rows, queue, cache, union-find, and counter through their
actual transitions. It does **not** establish that a particular reducer produced
those events or its return value. The reducer-specific recording definitions and
erasure/soundness lemmas supply that connection. Never accept arbitrary replayable
events as a certificate for an unrelated source constraint.

For placement, prove a literal list decomposition, not just a gate-kind check:

```text
bodyRows = prefix ++ genericRowsForThisStep ++ customBlockRows ++ suffix
genericRows.first = prefix.length
customRows.first = prefix.length + genericRowsForThisStep.length
customRows.count = customBlockRows.length
```

`reduceStep` already concatenates flushed generic rows before the custom gate.
`reduceGates` appends steps and `reduceBuilt` appends the final queue flush. Derive
placements during this fold. The final flush belongs to neither the last custom
block nor an invented extra source constraint.

The reusable slice lemma must preserve variable labels and coefficients as well as
row kinds. Later multirow proofs use an in-bounds local row and its successor;
they must establish an ordinary successor within the block, not silently use the
modular wraparound of `Fin n` addition.

## 3. Give events their deliberately limited semantic reading

Define these explicitly; do not use a predicate called `Admissible` hiding the goal.

```lean
def genericValue (V : Valuation F) (g : GenericPlonkConstraint F) : F :=
  let l := g.vl.map V |>.getD 0
  let r := g.vr.map V |>.getD 0
  let o := g.vo.map V |>.getD 0
  g.cl * l + g.cr * r + g.co * o + g.m * (l * r) + g.c

def equalsHolds (V : Valuation F) (e : EqualsConstraint F) : Prop :=
  e.cl * (e.vl.map V |>.getD 1) = e.cr * (e.vr.map V |>.getD 1)

def ReductionEvent.Holds (V : Valuation F) : ReductionEvent F → Prop
  | .alloc _ _ => True
  | .generic g => genericValue V g = 0
  | .equal e => equalsHolds V e

def ReductionFacts (V : Valuation F) (events : List (ReductionEvent F)) : Prop :=
  ∀ e ∈ events, e.Holds V
```

Notice the different `none` meanings: absent generic cells contribute zero in this
source reading; absent equality operands stand for one before multiplication by
their coefficient. Reusing one optional-variable reading for both would be wrong.

Prove these local contracts first:

```lean
theorem reduceToVariable_reads (V nv aux x)
    (hf : ReductionFacts V
      (recordReduction nv aux (reduceToVariable x)).events) :
    V (recordReduction nv aux (reduceToVariable x)).result = x.val V := ...

theorem boolean_of_reductionFacts (V nv aux x)
    (hf : ReductionFacts V
      (recordReduction nv aux (reduce (.boolean x))).events) :
    Basic.Holds V (.boolean x) := ...
```

Use `CVar.reduce_val`. A helper for `reduceAffineExpression` should read its result
`(some v, k)` as `k * V v`, and `(none, k)` as `k`. Prove it from emitted equations.
The `alloc` event must never introduce `V v = expression.val V` as a premise or rule.

For AddComplete, state the cell-layout identity first. Define a named row's reading
by evaluating each `some v` under `V` and filling `none` with zero. Then:

```text
ReductionFacts V recorded.events
  → AddComplete.cellMap (namedRowValues V recorded.result.row)
      = AddComplete.read V sourcePayload
```

Here `cellMap` is the existing backend reading in `Kimchi.Lift.Gate.AddComplete`;
`read` is the source reading in `Snarky.Kimchi`. Fully qualify them in code.
Transport the existing gate `Holds` across this equality. Do not duplicate the
seven gate equations or reprove elliptic-curve correctness.

These local lemmas are useful, but their `ReductionFacts` premises remain to be
derived from matrix satisfaction. They are not the end-to-end result of the phase.

## 4. Generic packing: the equation may be elsewhere

Prove the row-reading lemmas for one- and two-equation generic rows. The existing
double-row order is **incoming equation first, queued equation second**:

```text
columns 0,1,2 / coefficients 0..4 : incoming equation
columns 3,4,5 / coefficients 5..9 : queued equation
```

The final single flush puts the queued equation in the first half. A queue can
survive across custom gates. Never require a custom block's supporting equations
to occur before it, or within its source step's row span.

For the fragment, give each `.generic` event an eventual `(row, half)` receipt:

```lean
structure GenericReceipt where
  sourceStep : Nat
  eventIndex : Nat
  row : Nat
  half : Fin 2
```

The recording fold carries the pending event reference alongside the unchanged
existing queue. On pairing, assign receipts to both events in the order above;
on final flush, assign the pending receipt. Validate exact slot variables and
coefficients. All of the fragment's generic events need a receipt; none may remain pending
after finalization. Rows and halves are relative to the body, before public rows.

The first receipt builder is explicitly limited to the direct fragment's allocation/equality-free
event stream. If offered unsupported events, it must reject them, not silently omit
their obligations. General recording and its erasure theorem can still support those
events before general receipt certification does.

Do not require absent cells of an arbitrary table to be zero. Instead prove their
coefficients make them irrelevant. A sufficient structural condition for a generic
payload is:

```text
vl = none → cl = 0 ∧ m = 0
vr = none → cr = 0 ∧ m = 0
vo = none → co = 0
```

Prove that the fragment's generated generic equations meet this condition, and prove
the packing lemma for payloads satisfying it. Apply ordinary generic equations
only outside the public prefix; public rows use `Generic.withPublic` instead.

Equality operations are discharged by a trivial identity, a union, a pinning equation, or a
cache hit backed by an earlier pinning equation. The direct fragment below uses none; the
wired fragment of section 10 covers all four paths, with the receipts walk total over the
equations an event queues.

## 5. Recovering a valuation: a concrete structural certificate

There are 15 witness columns and only 7 permutation columns. `KimchiRow.vars`
records names in all 15, but the index does not enforce equality merely because
two names match. This distinction must appear in the first experiment.

Use cell addresses and copy paths as the first sufficient certificate:

```lean
structure Cell (n : Nat) where
  row : Fin n
  col : Fin 15

-- CopyPath is the reflexive, symmetric, transitive closure of actual wiring edges.
-- Edges only embed permutation cells (columns 0..6) and their index wiring targets.
def CopyPath (idx : Kimchi.Index F n) (a b : Cell n) : Prop := ...

def LabelsConnected (idx : Kimchi.Index F n)
    (labels : Cell n → Option Variable) : Prop :=
  ∀ a b v, labels a = some v → labels b = some v → CopyPath idx a b

def Realizes (V : Valuation F) (labels : Cell n → Option Variable)
    (table : Fin n → Fin 15 → F) : Prop :=
  ∀ c v, labels c = some v → table c.row c.col = V v

theorem copyPath_values_eq
    (hsat : Kimchi.Index.Satisfies idx pub table)
    (hpath : CopyPath idx a b) : table a.row a.col = table b.row b.col := ...

theorem exists_realizing_valuation
    (hc : LabelsConnected idx labels)
    (hsat : Kimchi.Index.Satisfies idx pub table) :
    ∃ V : Valuation F, Realizes V labels table := ...
```

Choose one occurrence of each named variable as its value; use zero for variables
with no occurrence. The theorem may be noncomputable initially. It depends only
on copy equalities, not on honest witness assignments. `LabelsConnected` is a
structural graph property of the index and compiler labels, with no table argument.

For a single occurrence in column 7 or above, reflexivity suffices. For two distinct
occurrences, an unwired column cannot participate in a copy path. Reject that case
under this first certificate. Later gate-specific determination lemmas can extend
the certificate; do not assume them now.

Public rows are included in `labels`, with their first cell naming the corresponding
public variable. Use the public conjunct of `Index.Satisfies` to derive `V v = pub i`.
Unassigned padding/masked cells have label `none`; no zero-value claim is made.

The index/row correspondence record must contain only these explicit structural facts:

- the emitted rows fit before `n - idx.zkRows`;
- gate types match under the existing kind conversion;
- coefficients match, with zero extension of the emitted coefficient lists;
- labels match the emitted `vars`, and are absent after the emitted prefix;
- public count and ordered public-row labels match the supplied public variables;
- `LabelsConnected` for those labels.

Call this proposed record `RowsInIndex`. Its fields must not contain `Realizes`,
`ReductionFacts`, source satisfaction, or an implication from `Satisfies` to any of
them. Those are conclusions of the soundness theorem, not structural validation.
For the direct fragment, derive its copy-path field from the emitted wiring. Do not make a
caller postulate it for a supposedly arbitrary application.

## 6. The first closed fragment and its theorem

The general local reducer lemmas above allow affine operands. For the first closed
matrix theorem, deliberately avoid proving the entire equality/cache/union-find
backend. Use a source list containing only:

```lean
/-- A constraint the lowering places directly: a Boolean on a bare variable, or a complete
addition whose eleven operands are bare variables. -/
def KimchiConstraint.Direct : KimchiConstraint F → Prop
  | .basic (.boolean (.var _)) => True
  | .addComplete c => ∀ x ∈ c.operands.toList, x.var?.isSome
  | _ => False
```

The operands are in AddComplete **column order**:
`x1 y1 x2 y2 x3 y3 inf sameX s infZ x21Inv`. The fragment is a predicate on the existing
constraint type, so the closed theorem quantifies over real source lists and the actual
existing reducers run on them unchanged; there is no carrier type and no embedding.

`Direct.Scoped source publicVars` is the finite, decidable condition with both of:

1. Every source constraint is `Direct`.
2. Each AddComplete operand at positions 7..10 occurs exactly once across **all**
   source operand occurrences and the ordered public-variable list.

The fragment allocates nothing, so no bound on the operands against the initial
next-variable counter is needed and none is stated; the counter parameterizes only the
lowering itself.

An auxiliary identifier cannot be shared with another auxiliary, a Boolean operand,
a coordinate, or a public variable. Coordinate/flag identifiers in positions 0..6
may repeat: copy wiring handles them. This is a sufficient restriction of the fragment,
not a claim of necessary conditions for the production circuits.

Starting from `initialAuxState`, this fragment has no allocations or equality
operations; all generic events come from Boolean constraints. It still exercises
custom blocks, generic queueing across blocks, final flush, repeated wired variables,
unwired local auxiliaries, and public rows.

The acceptance theorem, as landed in `Direct.lean`:

```lean
theorem KimchiConstraint.Direct.holds_of_satisfies {n : ℕ} [NeZero n]
    {source : List (KimchiConstraint F)} {publicVars : List Variable} {nv : Variable}
    {idx : Index F n} (hscope : KimchiConstraint.Direct.Scoped source publicVars)
    (hindex : IndexOf source publicVars nv idx) (pub : Fin idx.publicCount → F)
    (wTab : Fin n → Fin wCols → F) (hsat : idx.Satisfies pub wTab) :
    ∃ V : Valuation F, (∀ c ∈ source, KimchiConstraint.Holds V c) ∧
      ∀ i : Fin publicVars.length, V publicVars[i] = pub (hindex.publicIndex i)
```

`IndexOf` identifies the actual existing lowering/assembly output (`directGates`):
public count, gate kinds, zero-extended coefficients, and wires are exactly the
output at their corresponding positions; the rows fit in the unmasked prefix.
It leaves the remaining domain rows to the existing index invariants and carries no
connectivity premise: label connectivity is proved from the assembly algorithm
(`Wiring.lean`, `classCells_values_eq`). `publicIndex` transports the ordered index
through the public-count equality. The assembly's wire map is a hash map, which the
kernel cannot evaluate, so `IndexOf` is decided on concrete data through
`indexOf_of_classTarget`: an index matching the lowering's rows and the pure
class-based target `classTarget` (proved equal to the assembled one by `wireTarget_eq`)
agrees with the assembly.

Keep this structural index adapter small. The emitted row's gate tag is the index
model's own `GateType`, so no tag conversion exists to adapt or to prove agreement for.
Do not move all fixture parsing into the library.

This theorem is intentionally restricted. It must not be advertised as soundness
of `reduceBuilt` for arbitrary source constraints. The affine local lemmas and
recording layer remain reusable when the remaining state invariants are proved.

## 7. Modules

Under `snarky/Snarky/Kimchi/Backend/`:

| Module | Responsibility |
| --- | --- |
| `Trace.lean` | event data, recording interpreter, erasure, replay, allocation labels |
| `TraceChecks.lean` | decided recordings over `ℚ`: batching, wiring, constant cache, allocation |
| `TraceSemantics.lean` | event readings, affine/Boolean/AddComplete local lemmas |
| `RowCorrespondence.lean` | the recorded fold, its erasure, placement of each step's rows |
| `Receipts.lean` | generic receipts: location, completeness, the packing lemma |
| `Wiring.lean` | the wire map's cycles, the class-based target, class agreement |
| `Direct.lean` | the direct fragment, provenance of its rows, the closed theorem, the index lemmas |
| `DirectChecks.lean` | a decided instance invoking the closed theorem, and the boundaries |
| `Wired.lean` | the wired fragment: the class and cache folds, provenance by membership, the closed theorem |
| `WiredChecks.lean` | a decided instance with a pin, a merge, a cache hit and affine operands, and the boundaries |

Beside them, `snarky/Snarky/Kimchi/UnionFind.lean` carries the class view of the existing
union-find (`Inv`, `Same`, and the lemmas that a union joins and no operation splits).

The recording data is independent of `Kimchi.Index` and gate semantics; the proof
modules import them. Helpers are private to their modules; public results are rooted in
`snarky/roots.txt` and audited by `snarky/scripts/check_axioms.lean`. The reducers
`completelyReduce`, `constraintToCoeffs`, `emitDoubleGateRow`, `reduceAffinePoint`, the
Poseidon and EndoMul round reducers and `reducePad` were made public for the simulation
lemmas; the assembly names its wiring target (`wireTarget`), unchanged in behaviour.

## 8. Validation

Every theorem is kernel checked without `sorryAx`, new axioms, or `native_decide`
(`snarky/scripts/check_axioms.sh`). The checks are `decide +kernel` theorems, rooted
like every other result.

`TraceChecks.lean`, over `ℚ`:

- two Booleans pack with the incoming equation in the first half, and a Boolean followed by
  a complete addition outlives the custom block to be flushed after the addition's row
  (`recorded_batching`);
- an equality of two variables is discharged by wiring alone (`recorded_wiring`);
- a constant pinned twice is cached once (`recorded_constantCache`);
- a sum reduced from an occupied queue logs its allocation and packs in front of the
  waiting equation (`recorded_allocation`).

`DirectChecks.lean`, over a field of 113 elements with a domain of 16 rows: a public
prefix of two variables, a Boolean queued across a complete addition, the pair packed after
it, one equation flushed; the addition's `inf` flag is the first public variable, so a wired
operand repeats across the public row, a Boolean's cells and the addition's row; the
addition's four auxiliaries are singletons in unwired columns. The index is built from the
lowering's rows by `Index.build?`, the table satisfies it, and `direct_example_holds`
invokes the closed theorem on them. The boundaries, `direct_rejections` and
`direct_rejections_index`: an auxiliary aliased with a Boolean's variable, with a public
variable, or with another auxiliary is out of scope; each receipt is located and none is
once moved to the other half; a table zeroing the packed Boolean's two cells still satisfies
every gate but not the copy to its public row; an index with that row's coefficients
altered, or with the copy cycle through that row rerouted (still a permutation), is not the
lowering's.

Not exercised: repeated public variables (the example's are distinct), and rejections of a
shifted custom-block start or of an unflushed equation, which are not certificates here:
placements and receipts are computed from the recorded fold, and the walk is total over the
equations events queue, so `receipts_complete` locates every one.

`WiredChecks.lean`, same field and domain: a public variable pinned to a constant, the two
public-side variables merged, a complete addition whose first abscissa is a sum and whose
second ordinate is a scaled variable, a second variable hitting the constant's cache, and a
Boolean on the merged variable; the pin's row packs with the sum's intermediate, the scaled
operand's row with the Boolean. `wired_example_holds` invokes the closed theorem on the built
index and the satisfying table. The boundaries are one per premise: `wired_rejections_scope`
(a constant in an unwired slot; an unwired operand named again by an equality that writes no
cell, or by a term of the sum; a variable at the counter), `wired_rejections_table` (a table
splitting the merged class, or reading the intermediate away from its pinning cell, while
every gate holds) and `wired_rejections_index` (the packed row's coefficients altered, the
pinned variable's copy wire cut).

The closed theorem quantifies over arbitrary satisfying tables; the decided instance only
rules out an empty set of accepted examples.

Build changed modules incrementally. From `formal/`, the bounded library gate is
`lake build Snarky`; bare `lake build` there is not a useful gate. Use the snarky
axiom audit and existing style/comment/dead-code checks as applicable to changed
declarations. If executable lowering changes, run targeted constraint-system
regressions; inspect the current `check-cs` invocation/options before choosing them.
Do not launch long Pickles fixtures just for proof-only changes.

Completion means recording erases to the original implementation, the local
correspondence lemmas are proved, and the restricted matrix theorem closes without
semantic oracle premises. If a structural obstruction prevents that theorem,
provide a minimal concrete example and identify the failed field; do not quietly
add `Realizes` or source satisfaction to its assumptions.

## 9. What remains

The general compiler theorem still needs:

- a suitable treatment of repeated operands outside permutation columns, which both fragments
  exclude by `unwiredOnce`;
- EndoScalar and the multirow gates;
- Poseidon MDS and EndoMul endomorphism-parameter agreement with the index;
- whole-source-list and full index-construction correctness;
- integration with `compileWith` and its public input/output layout, with `Wired.Scoped`
  decided per application;
- certified cross-language constraint-system correspondence and application imports.

The trace solves provenance and organizes these proofs. It cannot supply equality
that the emitted constraints do not enforce. In particular, the fragment's locality
condition must be revisited against actual gadget-generated source constraints
before claiming coverage of Pickles applications.

## 10. The wired fragment

Phase 4 widened the closed theorem to `Basic` constraints over affine operands and complete
additions whose wired operands are affine, so the lowering allocates intermediates, pins
constants through the cache and fuses classes. The design decision was to annotate more and
replay less: the compiler proofs stay at the level of the log, and the union-find is seen only
through its class view.

- **The equality op logs its decision.** `.equal c o` carries the `EqualOutcome` the op took
  (`merge`, `cached`, `pinned`, `row`, `trivial`), `outcomeOf` mirrors the op's guards and
  `OutcomesFaithful` says the logged outcome is the decision at that point. The receipts walk
  is total over `ReductionEvent.queued?`, the equation an event queued, so pinning and
  unequal-coefficient rows are located like generic ones. Each outcome has a reading
  (`equalsHolds_of_merge` and the others): a merge or cache hit holds by class, a pin or row by
  its emitted equation, and a pin also yields `V v = k`.
- **The union-find through `Same`.** `fusion_root_eq` says every logged merge or cache hit
  shares a root in the roots the assembly wires through, by threading `UnionFind.Inv` from the
  empty structure. Only this joining direction is used. `pinned_of_cached` says every cache hit
  names a pin some step logged, since the lowering starts from the empty cache; order is
  irrelevant because every pin's row holds at the one valuation.
- **Provenance by membership.** `ReductionEvent.names` lists what an event writes or fuses,
  and `allocs` what a log allocates, at or above its starting counter. The `Records` walks show
  every name is a term of the operand or an allocation, a bare operand returns itself with no
  event, and an addition's row cells are its operands' variables position by position. No
  multiplicity bound is stated anywhere: a Boolean writes its input twice. For an operand of an
  unwired column, whose one occurrence is a bare operand, `unwired_not_named`,
  `unwired_of_cell` and `unwired_cell_unique` follow by counting source occurrences.
- **The valuation.** A variable reads its own unwired cell if it has one, else any cell of its
  root's class, else `0`. The permutation step `IndexOf.classCells_eq`, shared with the direct
  theorem, gives class agreement; uniqueness gives the unwired branch; no converse of the class
  view is needed.
- **The theorem.** `KimchiConstraint.Wired.holds_of_satisfies` has the direct theorem's shape
  under `Wired.Scoped nv source publicVars`: every constraint in the fragment, every named
  variable below the counter, and every operand of an unwired column occurring once among all
  terms and the public variables. Queued equations hold by receipt, with `AbsentZero` proved
  for every equation a reducer queues; a cache hit's constant is recovered from its pin's
  receipt before any event is discharged; each constraint then holds by
  `basic_of_reductionFacts` or by the addition's row read cell by cell.
