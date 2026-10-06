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

Only this document is being added now. The proposed declarations below are design
signatures, not existing or elaboration-checked Lean. Bodies marked `...` are work
items; no corresponding `sorry` or axiom should be added to the library. Names may
change during elaboration; the direction and assumptions of the contracts must not.

## Starting point for the implementing agent

Inspected at commit `82d132f9`, branch `formal/application-layout`. At writing, these
files already have unrelated working-tree changes; preserve them:

```text
.github/workflows/test.yml
formal/README.md
formal/scripts/check_tags.lean
```

Read `CLAUDE.md` and `formal/CLAUDE.md` before implementation. Use the existing
Lean skill. Keep new helpers private until a concrete consumer needs them.
Do not change the Pickles capstones, fixture schema, emitted rows, or wiring.
No commit, branch operation, PR, or full fixture run is requested by this handoff.
Never run `LINKS=all`; use explicitly selected fixtures if regression testing needs them.

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

Equality operations are a later extension to receipt certification. They may be
discharged by a trivial identity, a union, a pinning equation, or a cache hit backed
by an earlier pinning equation. The recording layer supports `.equal` now, and
the local semantic lemmas may assume its meaning. The direct fragment below uses no equality
operations. Do not report general `ReductionFacts` reconstruction as proved until
these equality paths are actually covered.

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

Define a finite, decidable `Direct.Scoped` condition with all of the following:

1. Every operand and public variable is below the initial next-variable counter.
2. Each AddComplete operand at positions 7..10 occurs exactly once across **all**
   source operand occurrences and the ordered public-variable list.
3. Every source constraint is `Direct`.

An auxiliary identifier cannot be shared with another auxiliary, a Boolean operand,
a coordinate, or a public variable. Coordinate/flag identifiers in positions 0..6
may repeat: copy wiring handles them. This is a sufficient restriction of the fragment,
not a claim of necessary conditions for the production circuits.

Starting from `initialAuxState`, this fragment has no allocations or equality
operations; all generic events come from Boolean constraints. It still exercises
custom blocks, generic queueing across blocks, final flush, repeated wired variables,
unwired local auxiliaries, and public rows.

The acceptance theorem must have this shape, with every named contract defined:

```lean
-- Proposed signature; source/public vectors and index adapters need explicit binders.
theorem Direct.holds_of_satisfies
    (hscope : Direct.Scoped nv source publicVars)
    (hindex : IndexOf source publicVars nv idx)
    (hsat : Kimchi.Index.Satisfies idx pub table) :
    ∃ V : Valuation F,
      (∀ c ∈ source, KimchiConstraint.Holds V c.toConstraint) ∧
      (∀ i : Fin publicVars.length, V publicVars[i] = pub (publicIndex hindex i)) := ...
```

`IndexOf` must identify the actual existing lowering/assembly output:
public count, gate kinds, zero-extended coefficients, and wires are exactly the
output at their corresponding positions; the rows fit in the unmasked prefix.
It can leave the remaining domain rows to the existing index invariants. It must
not include `LabelsConnected` as an unexplained premise. Prove the latter from
`Direct.Scoped` and the actual assembly algorithm, then construct `RowsInIndex`.
`publicIndex` transports the ordered index through the public-count equality.

Keep this structural index adapter small. The emitted row's gate tag is the index
model's own `GateType`, so no tag conversion exists to adapt or to prove agreement for.
Do not move all fixture parsing into the library.

This theorem is intentionally restricted. It must not be advertised as soundness
of `reduceBuilt` for arbitrary source constraints. The affine local lemmas and
recording layer remain reusable when the remaining state invariants are proved.

## 7. Work order and proposed modules

Use new modules under `snarky/Snarky/Kimchi/Backend/`:

| Module | Responsibility |
| --- | --- |
| `Trace.lean` | event data, recording interpreter, structural replay/erasure |
| `TraceSemantics.lean` | event readings, affine/Boolean/AddComplete local lemmas |
| `RowCorrespondence.lean` | slices, generic packing, copy paths, valuation recovery |
| `Direct.lean` | the direct fragment, actual assembly connection, closed theorem |

Split further only if dependencies or size justify it. Keep the recording data
independent of `Kimchi.Index` and gate semantics; the proof modules can import them.
Do not expose all new helpers through the top-level library automatically.

Implement in this order:

1. Elaborate the core data definitions and **final theorem signature**. Define
   `Direct.Scoped` and `IndexOf` concretely before proving convenience lemmas.
2. Implement recording for existing operations; prove operation simulation and
   the three erasure statements. Check empty and nonempty initial queues.
3. Define event semantics; prove affine reading, Booleanity, and AddComplete reading.
4. Add placement and generic receipts. Prove packed-row correspondence and final flush.
5. Prove copy-path equality and valuation recovery. Prove the fragment's assembly
   produces connected labels under its precise locality restriction.
6. Prove `Direct.holds_of_satisfies`, including ordered public inputs.
7. Run bounded examples and regressions below. Report exactly which general compiler
   obligations remain, without replacing any of them by an opaque assumption.

If existing private definitions obstruct a proof, prefer a narrow lemma in their
defining module over exposing all implementation helpers. If the recording instance
requires extracting a shared primitive implementation, prove erasure and retain
the same emitted rows, variable counter, queue, cache, and union-find state.

## 8. Validation and completion criteria

Formal checks are the main deliverable. Every finished theorem must be kernel
checked without `sorryAx`, new axioms, or `native_decide`.

Small regression examples must cover:

- A Boolean followed by AddComplete followed by another Boolean: the first Boolean
  remains pending across the custom block and shares a later generic row.
- One Boolean followed by AddComplete and finalization: its equation is flushed
  **after** the AddComplete row.
- Two Booleans: verify incoming/queued half order, including distinct variables.
- Repeated coordinates/flags across AddComplete rows and the public prefix.
- Singleton local auxiliary identifiers outside the seven permutation columns.
- Affine/constant/scaled expressions in the local reduction lemmas; these need
  not be in the closed direct fragment.
- A nonzero public prefix, preserving public order and repeated public variables.

Negative controls for structural certification must reject:

- a shifted custom-block start or wrong block length;
- a generic receipt assigned to the wrong half;
- an unflushed pending generic event;
- a repeated auxiliary identifier in an unwired column;
- an auxiliary identifier also appearing in a public row;
- altered coefficients or wiring that destroys a required copy path.

For coefficient/placement changes, test rejection by the structural relation/checker.
For wiring changes, choose a case where a required nontrivial connection is broken;
identity wiring for a singleton is valid and must not be rejected merely for being identity.

At least one explicit satisfying instance of the fragment should be constructed to rule out
an accidentally empty set of accepted examples. Use an existing AddComplete witness
constructor/completeness lemma when suitable. Do not require on-curve points in the
general compiler theorem: its target is the source `Holds` predicate, not an EC spec.

The closed theorem must quantify over arbitrary satisfying tables. Merely deciding
both predicates on a prover-generated table does not meet this criterion.

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

## 9. What remains after this phase

The general compiler theorem still needs:

- equality-operation receipts, constant-cache invariants, and union-find soundness;
- scope/freshness across generated intermediate variables;
- a suitable treatment of repeated operands outside permutation columns;
- other Basic cases, then EndoScalar and multirow gates;
- Poseidon MDS and EndoMul endomorphism-parameter agreement with the index;
- whole-source-list and full index-construction correctness;
- integration with `compileWith` and its public input/output layout;
- certified cross-language constraint-system correspondence and application imports.

The trace solves provenance and organizes these proofs. It cannot supply equality
that the emitted constraints do not enforce. In particular, the fragment's locality
condition must be revisited against actual gadget-generated source constraints
before claiming coverage of Pickles applications.
