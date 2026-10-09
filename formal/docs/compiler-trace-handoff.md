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

The agreed whole-compiler interface is **checked compilation** (section 11): validate
admissibility on the reconstructed application's source constraint list and retain its
proof with the compilation result. The public lifting theorem then has no separate unwired
hypothesis. This does not claim that every unrestricted `CircuitM` program passes validation.

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

After phase 5's gate coverage, the whole-compiler work is:

- a proved admissibility checker over the completed source constraints and public variables;
  retain `unwiredOnce`, rejecting repeated unwired operands rather than changing the index;
- full index-construction correspondence, including source/index parameter agreement;
- integration with `compile`/`compileWith` and their public input/output layout, returning a
  checked compilation whose certificate discharges the general lifting theorem's premises;
- certified cross-language constraint-system correspondence and its application to imports.

Section 11 specifies this boundary and the imported-application argument. Universal
admissibility proofs for gadget composition are not a prerequisite for this plan.

After the checked-compilation wrapper, the order is: the proof-module separation of section 12,
then the typed public-input bridge, then certified imported-index correspondence and the
reconstructed-application theorem. New consumers are built against the isolated interface,
not against internals that section 12 hides.

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

Phase 5 completed the gate coverage under the same theorem statement. Every constructor is
now in `Wired`: the challenge decomposition, the scalar multiplication, the endomorphism
multiplication, the Poseidon block and the padding row joined the addition. The remaining
admissibility conditions are bare-or-empty cells in the unwired columns, `unwiredOnce`, and
the Poseidon block shape `state.length % 5 = 1`. Each gate supplies a `Placed` proof against
`KimchiConstraint.rowOperands`, an absent-coefficient proof and a reading of its rows. The
scalar multiplication, the endomorphism multiplication and the Poseidon block read their
successor row inside the block; `IndexOf.params` supplies the endomorphism coefficient and
the MDS matrix, `IndexOf.coeffs_eq` the round constants. `WiredChecks.lean` decides lowerings
of each gate with their rejections.

## 11. Phase 6: checked compilation and imported applications

### The boundary to validate

There are two compilation stages:

```text
CircuitM program reconstructed from shape + rules + environment/backend artifacts
  → compile / compileWith
  → source constraint list + allocation counter + public variable layout
  → affine reduction, equality processing, generic packing, gate expansion, wiring
  → Kimchi rows / index
```

The final backend artifact is the rows/index. The source list is the intermediate
`List (KimchiConstraint F)`, containing structured constraints such as `.basic`,
`.addComplete`, and `.endoMul`, still with affine operands. Validate this completed list,
including input checks and the constraints binding the public outputs, not just the circuit
body or the imported rules. Derive the public variable list from the existing compilation
layout, in its actual order.

Successful validation proves `KimchiConstraint.Wired.Scoped nv source publicVars` (with the
gate coverage completed in phase 5). Keep that predicate and the general
`Wired.holds_of_satisfies` theorem as the semantic foundation. Do not weaken uniqueness,
add copy wires, change gate layouts, or alter the public interface to obtain acceptance.

The checker should use two passes:

1. Count occurrences using exactly the source `termVars` and public-variable occurrences
   that `Wired.Scoped` uses. Include wired operands, affine terms, repeated appearances
   within a constraint, and public variables. Check the allocation bound as well.
2. Check that each constructor is admitted and each operand placed in an unwired column is
   a bare `.var v` (empty cells are allowed). Require the total occurrence count of each
   such `v` to be one. This detects reuse both before and after the unwired occurrence.

An efficient count map may replace repeated list scans, but its result must be proved
equivalent to the existing predicate. Preserve that predicate's affine-normalization and
operand-occurrence conventions; an independently chosen syntactic count is not the contract.
Report the offending constraint/operand/variable on rejection where practical.

Proposed signatures, with names provisional and proofs omitted:

```lean
def checkScoped (nv : Variable) (source : List (KimchiConstraint F))
    (publicVars : List Variable) : Bool

theorem checkScoped_eq_true_iff :
    checkScoped nv source publicVars = true ↔
      KimchiConstraint.Wired.Scoped nv source publicVars
```

A successful external executable run alone is not a formal certificate. For a concrete
import, the success fact must be established in Lean and fed through the checker theorem.
Use the project's kernel-checked decision/certificate path; do not introduce a new trusted
`native_decide` or an axiom equating an external check with a proof.

### Package the evidence; keep the general theorem

The following proposed backend certificate makes the intended contract explicit. It is
indexed by the source list, public variables and counter so it cannot silently certify a
different compilation. Assume the existing field instances, `open Kimchi`, and `[NeZero n]`:

```lean
structure CheckedIndex (source : List (KimchiConstraint F))
    (publicVars : List Variable) (nv n : Nat) where
  index : Kimchi.Index F n
  admissible : KimchiConstraint.Wired.Scoped nv source publicVars
  corresponds : IndexOf source publicVars nv index

theorem CheckedIndex.lift
    (c : CheckedIndex source publicVars nv n)
    (pub : Fin c.index.publicCount → F)
    (table : Fin n → Fin wCols → F)
    (hsat : c.index.Satisfies pub table) :
    ∃ V : Valuation F,
      (∀ con ∈ source, KimchiConstraint.Holds V con) ∧
      ∀ i : Fin publicVars.length,
        V publicVars[i] = pub (c.corresponds.publicIndex i)
```

The wrapper follows from the existing general lifting theorem. The substantive work is
constructing this certificate from ordinary compilation: derive `IndexOf` from the actual
index builder, including bounds, wiring, public count and parameter agreement; obtain
`admissible` from validation. Preserve the existing compiler's output exactly on success.
The checked entry point may reject a compilation but must not repair its constraints.

The whole-circuit wrapper ties `source`, `nv` and `publicVars` to `compile` or `compileWith`
of the supplied circuit. Interpreting the public equalities through their encodings is the
typed public-input bridge, which follows the isolation of section 12. Keep
`compileWith`'s returned internal cells available for the Pickles capstones. Callers should
not supply either `Wired.Scoped` or `IndexOf` manually. Public-input length is enforced by
the index-typed input, with any external list-to-vector conversion checked at the boundary.

This proves lifting for every **successfully checked compilation**, not that all programs
pass the checker. Proving private allocation/non-escape contracts for sealed gadgets and
composing them into universal admissibility is optional later work. It is not part of
phase 6 and requires no change to existing gadget APIs or their irreducibility discipline.

### Transfer to the source-language application

Use the same reconstruction and Lean compilation that generate the comparison artifact:

```text
exported shape + rule replay + shared environment/resolved backend artifacts
  → reconstructed Lean application
  → checked Lean compilation: admissibility proof + corresponding Lean index

source-language CS dump ↔ certified comparison ↔ Lean index

source-language index satisfies pub, table
  → Lean index satisfies the same pub, table
  → Lean source valuation satisfying the compiled constraints and public inputs
  → applicable Pickles capstones
```

There is no separate unwired-property check on the source-language CS dump. Admissibility
is certified on the intermediate constraints of the Lean reconstruction. The independent
source-language dump is compared to the output derived from that same Lean compilation.

Certify the comparison's connection to satisfaction: matching results imply equal
satisfaction predicates for the same public input and witness table. Check gate types,
coefficients, copy wiring, public-input layout, domain dimensions and every other parameter
read by `Index.Satisfies`, including MDS and `endoBase`. Actual equality of the relevant
index data suffices by rewriting; otherwise prove the comparison sound for these predicates.
An executable comparator reporting success without this theorem is still only a fixture
check. Existing variable-occupancy checks may remain as additional fidelity checks.

Source variable IDs may differ under consistent renaming. Those IDs are not table
coordinates: with the same row/column positions and copy wiring, no witness transformation
is needed. Row/column permutations and the machinery for transporting witnesses across
them are outside this plan. Any serialization normalization must preserve the compared
index data and the public input order.

This transfer retains the Pickles theorems' other hypotheses and collision/failure
alternatives. It establishes the recursive framework's guarantees for the imported circuit,
not the application's business semantics, correctness of its `mustVerify` choices, or
cryptographic soundness of Kimchi/IPA. It is relative to the exported artifacts and their
connection to the source implementation.

### Implementation order and acceptance checks

1. Implement and prove the checker. Reuse the existing positive and rejection examples;
   explicitly cover unwired reuse earlier and later in the list, reuse in public inputs,
   affine/non-bare unwired operands, and out-of-range variables.
2. Validate representative reconstructed applications early, before the full compiler
   wrapper is complete, to test the admissibility boundary.
   A rejection identifies a real unsupported layout or an overly restrictive predicate to
   investigate; do not assume acceptance merely because the gadgets allocate fresh witnesses.
3. Prove actual index-builder correspondence and assemble the checked compilation wrapper.
   A consumer example must invoke lifting with no explicit admissibility or `IndexOf`
   argument; its index must be the unchanged ordinary compilation output.
4. Isolate the backend proof machinery and stabilize the public checked-compilation
   interface (section 12).
5. Add the typed public-input bridge: read the ordered public variables through the input
   and output encodings of `compile`/`compileWith`, in the generic compilation layer.
6. Certify CS comparison and apply the wrapper to a reconstructed fixture. Transfer matrix
   satisfaction with the same table/public inputs and invoke the applicable capstones
   directly. Rejected comparisons must not produce a correspondence certificate.

The comparison/application integration follows the isolated interface and the typed bridge;
it need not be bundled into the same commit. Keep checks targeted to selected applications,
never `LINKS=all`.

The follow-up work is scoped in
[Imported Pickles application certification: phased plan](imported-application-certification-plan.md),
which separates application lifting, capstone composition, index equality and concrete certification.

## 12. Isolate the compiler proof machinery

This was the implementation strategy; section 12.8 records the tree it produced. Start after
phase 6's checked-compilation wrapper and its `compile`/`compileWith` consumer checks are
complete. It precedes the typed public-input readings and the imported-application theorems:
those are consumers of the backend interface, built against its isolated form.

After the gate coverage and whole-compiler theorem stabilize, separate their bespoke proof
support from the executable compiler. Consumers should use the final theorem and its stated
premises without depending on how its proof was constructed. This phase changes module
organization and visibility, not the emitted index or the theorem's semantic contract.

The dependency direction is:

```text
compiler implementation ← internal proof support ← public soundness interface ← consumers
                         (arrows mean imports)
```

The executable compiler must not import the proof-support tree. Keep executable constraint
types, reducers, assembly and union-find operations in their implementation modules. Move
proof-only additions there into the proof tree: union-find invariants and lemmas, operand
layouts, absent-cell predicates and equality-outcome lemmas, where they have no implementation
consumer. Keep any executable helper genuinely shared with production in the implementation.

Place the recording interpreter, event readings, receipts, placement/provenance arguments,
valuation recovery and per-gate correspondence in internal proof modules. Recording remains
a sidecar that runs the existing reducers and is connected to them by erasure theorems;
ordinary compilation need not generate a trace or carry proof certificates. The checked
wrapper of section 11 imports the implementation and the proof layer and retains its
certificate; the underlying compiler has no reverse dependency on that wrapper. Layout
helpers used by the executable admissibility checker must be shared without introducing
a dependency from executable code to the proof tree.

Use maximal privacy: a binding stays private until another proof module needs it. Definitions
shared across proof modules belong to an internal namespace, not the supported consumer API.
Keep decided examples and rejection checks in separate check modules. A small public module
exposes the final matrix-to-valuation theorem, the definitions needed to understand its
premises and conclusion, and the interfaces needed to discharge those premises. Substantive
admissibility restrictions remain explicit in the checked-compilation contract and rejection
conditions, rather than a separate premise callers must prove. The general lifting lemma
retains its explicit premises. Internal receipts, traces and recovery choices must not
become caller obligations.

Proof irrelevance permits consumers to use the theorem without inspecting its proof. The
trace and layouts are data, so their isolation comes from module organization and API
discipline rather than proof irrelevance. Lean imports are transitive: an internal namespace
is not a claim that shared support declarations are inaccessible to a determined consumer.

Completion checks:

- Compiler implementation modules build without importing the proof-support tree.
- A consumer imports only the public soundness module and applies the final theorem without
  naming internal proof machinery.
- Executable lowering and its index are unchanged; retain the erasure/correspondence proofs.
- The theorem's semantic assumptions and public-input conclusion are unchanged.
- Update imports, audit roots and checks after the moves; builds, axiom audits and the
  existing decided examples and rejection checks pass.

### 12.1. Freeze the result before moving its proof

The semantic contract to preserve is lifting for a successfully checked compilation, with
the same public inputs. It is not unconditional success of compilation, cryptographic
soundness, or application-rule correctness. Preserve the source counter, source constraints,
ordered public-variable list, rejection conditions, and the exact constructed index.

The checked wrapper is complete: `CheckedIndex`, `CheckedIndex.check?`, `checkBuilt?`,
`checkBuilt?_index` and `CheckedIndex.lift` in `Backend/CheckedCompile`, with decided
acceptances, exact rejections and the `compile`/`compileWith` lifts in
`Backend/CheckedCompileChecks`. The import inventory below matches the tree with the wrapper
in place.

The public-interface consumer, `Backend/Checks/CheckedCompileConsumer`, imports
`Snarky.Kimchi.Backend.CheckedCompile` and the DSL gadgets only. It:

1. Compiles a small DSL circuit once with `compile` and states its lifting, through `lift`,
   from a checked index of that compilation and a table satisfying it.
2. Does the same with `compileWith`, retaining one internal cell without publishing it.
3. States the public-input conclusion without naming `IndexOf`, `Wired.Scoped`, a trace,
   an event, a receipt, a recovered-valuation definition, or a union-find invariant. The
   public input is read in the order of the public variables, through
   `CheckedIndex.publicCount_eq` and `CheckedIndex.publicIndex`.

The consumer does not establish that its circuit passes the check or that a table satisfies
the index. Deciding either in the kernel uses internal support: the class-based wiring, since
the assembly's hash map does not reduce, and the lowering's rows to fill a table. The concrete
checks supply both. They obtain each checked index from `checkBuilt?`, decide the prover's
table against it, and apply the consumer's theorems; the `compileWith` check also fixes the
retained cell and the public layout. The consumer tests that the public interface suffices,
and the checks certify a concrete instance of it.

This consumer is the acceptance test for the public API. Keep the existing mathematical
theorems internally; callers should not have to learn their intermediate representations.

### 12.2. Proposed supported interface

Retain the names established by the wrapper unless a demonstrated consumer problem requires
a change. The intended surface is the following; ambient instances and detailed parameter
binders are omitted in these signatures:

```lean
-- Existing compilation layout, shared with ordinary compilation and fixture consumers.
def compiledPublicVars (built : Built c (β × bvar)) : List Variable

-- A checked result, indexed by the exact source, public variables, counter and domain.
-- Its internal certificate need not be a supported construction API.
CheckedIndex source publicVars nv n

-- The ordinary index and the public-position map are the consumer's accessors.
CheckedIndex.index : CheckedIndex source publicVars nv n → Index F n

def CheckedIndex.publicIndex (c : CheckedIndex source publicVars nv n) :
    Fin publicVars.length → Fin c.index.publicCount

theorem CheckedIndex.publicCount_eq (c : CheckedIndex source publicVars nv n) :
    c.index.publicCount = publicVars.length

-- Keep the wrapper's diagnostic type and checked entry points.
CheckFailure
CheckedIndex.check?
checkBuilt?

theorem CheckedIndex.lift [NeZero n]
    (c : CheckedIndex source publicVars nv n)
    (pub : Fin c.index.publicCount → F)
    (table : Fin n → Fin wCols → F)
    (hsat : c.index.Satisfies pub table) :
    ∃ V : Valuation F,
      (∀ con ∈ source, KimchiConstraint.Holds V con) ∧
      ∀ i : Fin publicVars.length, V publicVars[i] = pub (c.publicIndex i)
```

The current proposed statement uses `c.corresponds.publicIndex`. Replace that spelling by
the definitionally equal `c.publicIndex` accessor: otherwise the public theorem itself
exposes `IndexOf`. This is an interface change with the same semantic conclusion, not a new
public-input theorem. Keep a natural-number projection lemma for `publicIndex` if the
consumer needs to eliminate the transport. Do not add a family of unused accessors.

Keep `checkBuilt?_index` and the wrapper's successful-check characterization available where
the ordinary-compilation or certificate consumers use them. If their signatures expose
`compiledIndex?` or `indexOfGates?`, those functions are supporting API for those consumers;
do not claim to hide them while referring to them in a public theorem. They may remain in
their own opt-in adapter module rather than being advertised as everyday entry points.

Keep `ScopedFailure` available through `CheckFailure.scope`, including existing printable
diagnostics. The runtime checker is an intentional feature, not disposable proof scaffolding.
Conversely, users should not construct `CheckedIndex` by manually supplying its admissibility
and correspondence fields. Document those as internal certificate fields initially.

Do not introduce an opaque wrapper, existential certificate, new typeclass, or second copy
of the certificate merely to hide field names. Module organization and the accessor above
are sufficient for this phase. Lean's transitive imports still expose declarations used by
the implementation; a small supported API is not a claim of strict access control.

### 12.3. Separate definitions before moving large proofs

The current imports show the main obstacles:

```text
ScopedCheck   imports Wired
CompiledIndex imports Direct
Direct        imports Receipts and Wiring
Receipts      imports TraceSemantics and RowCorrespondence
Constraint.Types imports UnionFind, including its proof development
```

Moving `Wired.lean` into a directory called `Internal` alone does not solve these dependencies.
Extract the small definitions the checkers need before relocating the large proof modules.
The proposed file allocation is below; paths are relative to `Snarky/Kimchi/` and may be
adjusted to the completed wrapper without changing the dependency rules.

| Destination | Contents | Must not depend on |
| --- | --- | --- |
| Existing `Constraint/*`, `Backend/Assemble`, `Backend/Compile` | Production constraint data, reducers, interpreters, assembly, compilation and public-variable layout | The trace or lifting proof tree, checked wrapper, fixture modules |
| `Backend/Admissibility` | Checker-used operand layouts, occurrence definitions, `Wired`/`Scoped`, parameter agreement where appropriate, and their decidability support | Recording, receipts, valuation recovery, gate-reading proofs |
| `Backend/IndexSpec` | `directGates`, `IndexOf`, public-count transport; ordinary compilation dependencies only | Direct-fragment provenance, receipts, wiring proofs |
| `Backend/ScopedCheck` | The executable checker, diagnostics, and its reflection theorem | The general lifting theorem or traces |
| `Backend/CompiledIndex` | Gate conversion, array lookup, index construction and `compiledIndex?_indexOf` | Trace, receipts or direct-fragment soundness |
| `Backend/Internal/*` | Recording, erasure, event semantics, receipts, wiring proofs, provenance and valuation recovery; the general lifting theorem | Public `CheckedCompile` facade or fixture consumers |
| `Backend/CheckedCompile` | Checked-result packaging, checking entry points, public accessors and `lift` | Any checks/examples module |
| `Backend/Checks/*` | Decided examples, negative controls, shared fixture data and public-interface consumer | No production module may import this tree |

`Admissibility` and `IndexSpec` are shared definitions, not new supported application APIs.
Preserve existing declaration names initially to keep file moves mechanically reviewable.
The historical name `directGates` can remain during this refactor; renaming it is not needed
to establish the dependency boundary.

The desired imports, expressed as permitted dependency directions, are:

```text
implementation                     → existing DSL/constraint semantics and Kimchi types
admissibility + index specification → implementation
checker + index adapter            → shared definitions and implementation
internal lifting proofs            → shared definitions and implementation
CheckedCompile                     → checker, index adapter, internal lifting theorem
Pickles/application consumers       → CheckedCompile and ordinary application dependencies
checks                             → whichever public or internal module they exercise
```

The facade necessarily imports the proof of `lift`. Its consumers will therefore load that
proof's transitive dependencies. The goal is to keep the ordinary compiler independent of
them and to keep consumer statements independent of proof construction, not to promise a
small import closure for the theorem itself.

### 12.4. Declaration-by-declaration guidance

- **Operand layouts and occurrences.** `rowOperands`, `placedOperands`, `termVars`, and
  `unwiredVars` are executable data used by admissibility, despite having originated in a
  proof. Move their checker-required closure out of `TraceSemantics`; leave `Placed`,
  `CellOf`, placement lemmas, and reducer reading proofs in the proof tree. Check actual
  references before moving helpers from `Semantics` or individual constraint modules.
  Preserve all occurrence conventions, including Poseidon chunking and the omitted
  EndoMul fields. Do not rewrite those definitions during a file move.
- **The direct fragment.** Split `Direct.lean` so that `IndexOf` and gate definitions can
  be imported without the original restricted lifting proof. Keep its examples and theorem
  as regression coverage, but internalize them; do not delete a proof merely because the
  larger wired theorem subsumes its statement.
- **Union-find.** Keep the executable structure and `empty`, `find`, `union`, `rootOf` on
  the implementation side. Move `Inv`, `Same`, and their proof-only closure into an internal
  proof module. The current proofs unfold file-private `ensure` and `rootLoop`: private
  declarations cannot simply be referenced from the new file. Move these executable helpers
  into an implementation-detail namespace with the minimal cross-file visibility needed, or
  retain a minimal local implementation equation. Do not duplicate their algorithms or expose
  every helper as supported API. Move proof-only Mathlib imports with the proofs.
- **Equality reduction.** Classify the completed step-4 code, not an earlier revision:
  `EqualOutcome` and `outcomeOf` may be shared executable machinery if the builder uses them.
  Keep that shared machinery below the proof layer. Move outcome correctness lemmas and
  event interpretations upward. Never introduce a second runtime equality reducer to make
  the module split convenient.
- **Rows and gates.** `AbsentZero` and cell-list helpers belong with their real consumers.
  A layout helper consumed by the checker belongs in shared executable support; one used
  only to read a gate in the lifting proof belongs internally. Small pure definitions need
  not be moved out of an implementation file if production already uses them.
- **Wiring and class-based evaluation.** Keep `wireMap`/`wireTarget` in assembly. Move the
  class characterization, cycle proofs and `classGates` evaluation alternative to internal
  support. The `directGates_eq_classGates` theorem should be imported by kernel checks,
  not by the production index constructor. Retain a single gate-table/index implementation.
- **Semantic contracts.** Do not move `KimchiConstraint.Holds`, existing gate semantics,
  or the DSL's established correctness interfaces into a bespoke compiler-proof namespace.
  They are the meaning of the public conclusion and have independent consumers.
- **Compiler-facing helpers.** Some reducers were exposed for the recording proofs.
  Cross-file proof consumers still need access. Use internal naming/documentation for those
  definitions rather than marking them private and then recreating them in the proof tree.
  Maintain the existing gadget irreducibility discipline.

### 12.5. Commit sequence and stop conditions

**A. Baseline and public consumer.** Finish step 4 first. Inventory imports and references
with `rg`, record the public theorem statement and its axiom closure, and add the facade-only
consumer described above. Add `CheckedIndex.publicIndex` if needed. No large file moves yet.
Acceptance: the consumer compiles without intermediate-proof names in its source.

**B. Extract shared definitions.** Move the minimal admissibility definitions and structural
index specification out of `Wired`, `TraceSemantics`, and `Direct`. Retain names and bodies.
Rewire `ScopedCheck` and `CompiledIndex` to import them. Move the class-based testing adapter
out of the executable constructor module. Acceptance: neither checker nor index adapter
imports the general lifting proof, traces, or receipts, directly or transitively.

**C. Separate implementation-local proofs.** Split union-find and other proof-only additions
to implementation modules, using the minimal visibility adjustments described above. This
is the delicate step because private names, unfolding equations, and imports change.
Acceptance: ordinary constraint reduction and compilation build without the new proof tree;
all moved lemmas retain their statements. Review any change beyond visibility/imports
separately, rather than disguising it as a move.

**D. Relocate the sidecar proof tree.** Move Trace, RowCorrespondence, TraceSemantics, Receipts,
Wiring, Direct and Wired into `Backend/Internal/`, after the shared-definition extraction.
Keep existing declaration names in this commit. Move examples and fixture data into the
checks tree, updating their imports. Do not combine this with splitting every large proof
file into per-gate files or golfing proofs. Acceptance: the facade and both consumer examples
still compile, as do all existing internal decided checks.

**E. Tighten visibility.** Find consumers of each non-private helper outside its defining
file, and make file-local helpers private. Shared proof declarations keep their names: no
namespace migration. The `Backend/Internal` tree, the facade's documented interface and the
import-boundary gate already mark the boundary, and renaming the roughly 190 shared and
audit-rooted declarations would add little protection. A helper occurring in a public
proposition's body stays public where consumers need to name it while using that proposition;
it need not be made private for maximal privacy alone. Retain public names only for the
supported interface, existing semantic APIs, or documented implementation dependencies.

**F. Validate and document.** Run the focused and final gates below, record the final public
surface and module map, and link the facade consumer as the usage example. Old import-path
shim modules are temporary migration aids only: remove them once in-repo consumers migrate,
unless an identified external consumer requires a compatibility period. Do not import shims
from ordinary compiler modules.

Stop and report if a split would require weakening a theorem, adding a semantic assumption,
changing scope acceptance, changing index data, duplicating an algorithm, or increasing the
heartbeat/memory limits to keep a move compiling. Resolve an import cycle by extracting the
shared definition lower in the graph, not by making implementation import the proof facade.

### 12.6. Validation and performance safeguards

For each commit, build explicit changed-module targets from `formal/`, then the affected
consumers. Do not use bare workspace `lake build` as evidence of coverage. Run the full
`Snarky` target and affected Pickles/fixture targets at the final checkpoint. Inspect the
current Lake configuration and gate commands rather than assuming paths survived the moves.

Update `snarky/roots.txt`, `snarky/scripts/check_axioms.lean`, the comment and dead-code driver
imports, and `scripts/noshake.json` entries where affected. Keep the capstone and public
consumer rooted. Existing internal regression theorems remain check/audit roots; a declaration
being an audit root does not make it supported API. Do not root every unused helper to silence
dead-code reports, or shrink the audit to conceal an altered dependency.

The final validation has five parts:

1. **Semantics:** the same lifting conclusion, checker equivalence, index correspondence,
   emitted-row and padding properties, and all positive/negative kernel checks pass. The
   public consumer applies `lift` with no manually supplied `Scoped` or `IndexOf` proof.
2. **Dependencies:** check transitive imports, not just source import lines. Starting at
   ordinary `Backend.Compile`, no new internal lifting-proof or checks module is reachable.
   Starting at the checker/index adapter, no trace or general lifting theorem is reachable.
   The facade imports proofs; this is expected. `scripts/check-import-boundaries.sh`
   (`make lean-import-boundaries`, run in CI) asserts these from the import lines.
3. **Trust and hygiene:** axiom audit, style, comments, dead-code and import checks pass.
   Preserve existing standard-axiom closures; introduce no `sorry`, trusted evaluation,
   assumption standing in for a move, or new blanket linter exclusions.
4. **Runtime:** preserve `arrayTable`'s `@[noinline]` boundary and finished-array capture,
   tail-recursive array accumulation, and the scope check's bounds-before-bitset behavior.
   Preserve scope-before-index rejection order and compile the source once. Use a bounded
   native adapter probe above the old stack-overflow size, with repeated table reads, to
   detect loss of those runtime properties. Runtime erasure alone is not a performance proof.
5. **Fixtures:** do not repeat all 40 application reconstructions for a proof-only file move.
   If an executable definition or compilation path changes, use a targeted existing CS
   comparison and a representative constructor smoke test. Keep broader runs justified by
   an actual unresolved risk; no `LINKS=all`. Record the existing 40/40 scope and index runs
   as prior executable evidence, not as kernel certificates newly supplied by this refactor.

Kernel checks have substantial import memory overhead. Run expensive checks one process at
a time under the agreed limits, and keep small decisions separate when needed. Do not turn
this refactor into another application-scale kernel-evaluation experiment.

### 12.7. What this phase deliberately leaves to consumers

The backend ends at a source-satisfying valuation and equality at the ordered public variables.
Typed input/output readings belong with the generic Snarky compilation/encoding layer.
Reconstructing Pickles applications, applying application capstones, and certifying equality
of imported step/wrap indices belong to the Pickles application/import layer. Do not import
those layers back into `CheckedCompile` to make its result look application-specific.

Proof irrelevance does not make trace data disappear from the Lean environment, and private
names do not eliminate transitive imports. The deliverable is a stable, small consumer
contract and an implementation independent of bespoke lifting proofs. The proofs remain
kernel-checked in their own modules, available for maintenance without becoming caller
obligations.

### 12.8. The isolated tree

Paths are relative to `snarky/Snarky/Kimchi/`.

| Modules | Contents | Reaches no |
| --- | --- | --- |
| `Constraint/*`, `UnionFind`, `Backend/Assemble`, `Backend/Compile` | Constraint data, reducers, union-find operations, assembly, kimchi compilation (the public layout `compiledPublicVars` is in the generic `Snarky/Compile`) | internal or check module |
| `Backend/Admissibility` | Operand layouts, `occurrences`, `KimchiConstraint.Wired`, `Wired.Scoped` | internal or check module |
| `Backend/IndexSpec` | `directBuilt`, `directGates`, `ParamsAgree`, `IndexOf` | internal or check module |
| `Backend/ScopedCheck`, `Backend/CompiledIndex` | The scope checker and the index constructor with their reflection theorems | internal or check module |
| `Backend/Internal/*` | The union-find's class view, the builder's transitions and equality decision, recording, readings, receipts, wiring proofs, the direct and wired lifting theorems | check module |
| `Backend/CheckedCompile` | The facade | check module |
| `Backend/Checks/*` | Decided checks and rejections, fixture data, the witness table, the facade-only consumer | — |

The supported interface is the section of that name in the facade's module docstring;
`CheckedConsumer.compile_lifts` and `CheckedConsumer.compileWith_lifts` are the usage
example. Executable helpers made visible for proofs in other modules, each documented at its
definition: `UnionFind.ensure`, `UnionFind.rootLoop`, `handleGateBatching`, `addGenericB`,
`addEqualsB`, `bareCell` and `directBuilt`. No import-path shims were introduced.

At completion the build, axiom audit, comments, dead code, shake, lint, import boundaries and
every decided check and rejection pass, and the CS comparison matches all 97 circuits. A
native probe of the gate-table adapter, interpreted, builds and reads every row twice at
`2^14` to `2^17` rows in time linear in the rows and without stack overflow. The 40/40
application scope and index runs remain the executable evidence for the applications; this
refactor supplies no new kernel certificate for them.
