# Imported Pickles application certification: phased plan

## Goal and starting point

Reconstruct an application from exported shape, rule replay, resolved backend artifacts and a
shared environment. Prove that its checked Lean compilation has the Pickles framework's
verification and handover guarantees. Certify equality with the independently imported
application indices, then transfer those guarantees to the imported indices.

This plan follows [PR #448](https://github.com/l-adic/snarky/pull/448), stacked on
[PR #444](https://github.com/l-adic/snarky/pull/444). Its starting point is `3a0efd78` on
`formal/multirow-gates`: checked matrix-to-valuation lifting, proof-module isolation and the
typed public-input bridge are implemented. Their design history is in
[compiler-trace-handoff.md](compiler-trace-handoff.md).

The shared application representation remains `Pickles.Application.Circuits D L`. The
fixture importer already produces it through `Assembled.circuits`; a future native Lean
application builder can produce the same representation. Do not introduce a second
application language or a registry describing all applications at once. Each application has
its own branches, one shared wrap circuit and interfaces to already constructed producers.

The intended argument is:

```text
shape + rule replay + backend artifacts + shared environment
  -> reconstructed Circuits D L
  -> checked compilation of each step branch and the wrap circuit
  -> arbitrary satisfying tables lift to typed application runs
  -> existing Pickles capstones apply, with their remaining assumptions

independent source-language gate dumps + actual backend metadata
  -> imported application indices
  -> certified equality with the checked Lean indices
  -> the same application guarantees for the imported indices
```

### What is imported, and what is quantified

The application certificate concerns static circuits. It does **not** require importing a
particular witness matrix. The application theorems quantify over arbitrary tables satisfying
the relevant indices at the supplied public statements. They must not assume those tables came
from the honest prover, `makeWitness`, or cached advice.

For tests, existing cached witness advice can generate concrete tables using the fixture
machinery. These demonstrate satisfying instances and exercise consumers of the theorems.
They are not an additional application export. The compiler's lowering trace is another
object entirely: it remains internal proof machinery and is not imported from PureScript.

### Semantic boundary

The result preserves the existing capstones' hypotheses, whole-message equalities, application
state projection, collision alternatives and `AccumulatorFailure` alternative. It does not
establish the business semantics of a rule, justify a rule's choice of `mustVerify = false`,
or prove a whole application's inductive derivation relation.

These phases start from matrix satisfaction. They do not add a cryptographic theorem deriving
a satisfying matrix from `kimchiVerify = true`. A later proof-level contract must identify the
intended index and verifier key. Index equality alone does not prove that a key's polynomial
commitments commit to that index. The certification path now also derives every step and wrap
key from the certified index and shared SRS, retaining this correspondence as `ApplicationKeys`.
Existing key-layout checks and dynamic `KeyBound` facts remain distinct from this check.

Certification is relative to the decoded exported artifacts and their connection to the
source-language implementation. Optional gates, lookups, sideloading and full prover-key generation
remain separate work. The current constructor and application vocabulary is the scope here.

## Existing components to reuse

Paths below are relative to `formal/`.

| Module | Existing interface |
| --- | --- |
| `snarky/Snarky/Kimchi/Backend/CheckedCompile.lean` | `CheckedIndex`, `checkBuilt?`, `lift`, public-input accessors, ordinary-output correspondence |
| `snarky/Snarky/Compile.lean` | `compiledPublicVars`, public-layout lengths, `compile_reads`, `compileWith_reads` |
| `pickles/Pickles/Application/Circuit.lean` | `Circuits`, `stepBuilt`, `wrapBuilt`, advice irrelevance |
| `pickles/Pickles/Application/Run.lean` | `StepRun`, `WrapRun`, `SourceFor`, `StepWrapLink`, `WrapStepLink` |
| `pickles/Pickles/Application/Verify.lean` | Assumption records and both `verifies_proof` capstones |
| `pickles/Pickles/Application/Handover.lean` | Both handover capstones and the application-state projection |
| `pickles/PicklesFixture/ApplicationImport.lean` | Assembly from reconstruction data independently of the circuit dump |
| `pickles/PicklesFixture/ApplicationCircuit.lean` | Checked replay rules and rule-advice irrelevance |
| `pickles/PicklesFixture/ApplicationRun.lean` | Reconstruction comparison and cached executions |
| `pickles/PicklesFixture/ApplicationVerify.lean` | Direct capstone application to connected fixture runs |
| `pickles/PicklesFixture/Manifest.lean` | Explicit applications, tags and required link/handover coverage |
| `kimchi/KimchiFixture/PS.lean` | Gate-dump parsing and the existing synthetic-domain witness adapter |

The phases below record the implementation decomposition. The current contract above and
the executable consumer document identify the public endpoints. Supply the existing Pasta instances, column notation and
the implicit context `{D : Shape} {L : Layout D} {C : Circuits D L}` as appropriate. Before
proof work in each phase, elaborate the complete types and statements. Do not add new library
axioms or leave `sorry` declarations as an implementation of the plan.

## Implemented matrix contract

[application-certification-draft.lean](application-certification-draft.lean) now elaborates
consumers of the production interface, rather than defining a second version of it.

`PicklesCorrect C I` has two lifting fields. Each accepted step/wrap matrix gives a satisfying
native run at its public statement **and the fixed matrix valuation**. That valuation follows
the compiled layout's labelled cells and equality classes. It is defined before any
connection is supplied; no arbitrary source execution or prover advice chooses it.
`PicklesCorrect.stepRun_reads` and `wrapRun_reads` preserve every observation of retained cells,
including affine expressions, proof parts, keys, masks and messages.

The universal endpoints take their arguments in this order:

1. Certificates for the participating applications' indices.
2. Arbitrary accepted matrices at typed public statements.
3. Connections expressed on those matrices through the fixed readers.
4. The original capstone assumptions.

They conclude verification or handover for proofs and messages read from those matrices.
The connection records do not assume the complete-message equality that handover proves.
No caller supplies a connection about an existential execution chosen later.

`CertifiedIndices.wrap_handover` handles Step → Wrap → Step → Wrap across two applications;
`CertifiedIndices.step_handover` handles Wrap → Step → Wrap → Step across three. The pair
endpoints retain production/consumption of accumulators, conditional verification, and the
wrap/step mask fact. Whole-message equality, accumulator failure and hash collisions retain
the original grouping. The application-state result is a projection of message equality.

A retained but unused variable need not occur in any matrix cell. The interpretation reads
unrepresented variables as zero; it does not recover an arbitrary original prover valuation.
The backend proves this fixed interpretation satisfies the source. This boundary is covered
by a regression showing two source-satisfying valuations can disagree on unused retained advice.

Imported-index equality transfers this entire contract. `certifyIndices?` uses the same
comparison and returns the same indices or located errors; its proof field now retains the
stronger lifting guarantee. Certification never requires a concrete witness chain.

## Phase 1. Checked compilation of one application

Module: `pickles/Pickles/Application/CheckedCompile.lean`.

### Interface

Keep branch domains independent. The indices cover this application's step branches and wrap
circuit; imported producers retain their own certificates.

```lean
structure ApplicationIndices (D : Shape) where
  stepSize : D.Branch → Nat
  step : (b : D.Branch) → Kimchi.Index Fp (stepSize b)
  wrapSize : Nat
  wrap : Kimchi.Index Fq wrapSize

def checkApplication (C : Circuits D L) :
    Except ApplicationFailure (CheckedApplication C)
```

Define `CheckedApplication C` from the existing `CheckedIndex` certificates for the exact
compiled source, public variables and counter of each circuit. Derive its `indices` accessor
from those certificates; do not store duplicate indices and equality proofs unnecessarily.
Scope and index correspondence remain supplied by checked compilation, not by the caller.

### Work

1. Choose canonical inert main advice and compile each circuit once with `compileWith`.
   Reuse the build for checking, index construction and subsequent comparison.
2. Reuse `stepBuilt_advice_irrel` and `wrapBuilt_advice_irrel`. For replayed rules, reuse
   `Assembled.stepBuilt_ruleAdvice_irrel` when relating cached executions to the canonical rule.
3. Keep application constructors and compilation independent of valuations. Use ordinary
   constraint types; introduce `Builder V` only in soundness proofs. The checked artifact's
   constraints and retained cells are fixed before lifting supplies a valuation.
4. Obtain actual domain sizes, generators, shifts and masked-row counts from the branch and
   wrap keys. Obtain the gate endomorphism coefficient and MDS from the appropriate shared
   field environment. Keep their origins explicit.
5. Return diagnostics locating a failure at a step branch or the wrap circuit, with its
   underlying scope/index-stage failure. Successful checking changes no circuit data.

### Tests and exit condition

- Select `NoRecursionReturn` explicitly. Construct every declared step index and its wrap
  index, and compare the ordinary compiler output with the independent fixture as before.
- Check advice changes preserve the compiled artifact, including retained cells.
- Use small decided examples to reject incorrect domain/parameter data with a located error.
- A consumer obtains the certificates without supplying `Scoped` or `IndexOf` proofs.

Exit: one reconstructed application has a checked family of its own indices. No Pickles
verification theorem is invoked by this phase.

## Phase 2. Satisfying tables give typed application runs

Module: `pickles/Pickles/Application/MatrixRun.lean`.

### Interface

Define `StepTable` and `WrapTable` to associate a typed public statement and witness table with
the corresponding index. Satisfaction must be at the encoding of that very statement, with
the public-count equality handled explicitly. Neither record contains a source valuation or
source-satisfaction premise. Positivity of the domain comes from the checked index data.

```lean
theorem CheckedApplication.lift_step
    (checked : CheckedApplication C) (b : D.Branch)
    (t : StepTable checked.indices b) :
    ∃ r : StepRun C b,
      CircuitType.Reads r.V r.cells.out t.statement ∧
      r.V = stepValuation C checked.indices b t

theorem CheckedApplication.lift_wrap
    (checked : CheckedApplication C)
    (t : WrapTable checked.indices) :
    ∃ r : WrapRun C,
      CircuitType.Reads r.V wrapStatement t.statement ∧
      r.V = wrapValuation C checked.indices t
```

### Work

Compose `CheckedIndex.lift_reading` with `compileWith_reads`. On the step side the public input type
is `Unit` and the public output is the `StepStatement`; on the wrap side the public input is
the packed wrap statement and the public output is `Unit`.

Prove the constructor identities connecting the body's output to `StepRun.cells.out` and the
retained cells to each run. Use phase 1's build invariance to establish the exact `holds` field
required by `StepRun` or `WrapRun`. Every reading concerns the same recovered valuation.

`lift_reading` retains equality to `matrixValuation`. The application valuations are opaque
to routine simplification so proofs do not unfold entire compilations. This is a mathematical
reading, not an executable witness-recovery API or equality to arbitrary prover advice.

### Tests and exit condition

- A theorem consumer obtains both kinds of run without supplying source satisfaction.
- Reuse a small decided matrix example to exercise public-count transport and the typed
  input/output conversion. Altering a pinned public value for that fixed table must fail
  satisfaction.
- Check retained cells belong to the same build and valuation as the lifted public readings.
- Use a selected cached application execution for runtime evidence of the premises, without
  turning the cached prover into a premise of the universal theorem.

Exit: arbitrary satisfying tables supply application runs with the intended typed public
statements. Their inter-run connections are still separate obligations.

## Phase 3. Apply the application capstones to lifted runs

Module: `pickles/Pickles/Application/Certification.lean`.

### Define the claim before proving it

`PicklesCorrect C indices` quantifies over arbitrary satisfying tables and obtains their
typed runs and fixed readings via phase 2.
Its matrix consumers take connections stated on the fixed matrix readings, construct the
corresponding native links, and apply the existing verification/handover implications. Do not use an unexplained predicate as a substitute for
agreeing on these quantifiers.

Its remaining hypotheses include exactly those needed at the respective connection:

- `StepWrapAssumptions` and `WrapStepAssumptions`, including Lagrange/SRS conditions;
- the producer/consumer `SourceFor` relation, selected branches and public-statement ties;
- the applicable `mustVerify`, key-binding and mask readings;
- `SgOk` for an individual conditional verification result, or later-proof acceptance for
  handover, as in the existing theorem being applied.

Assembly and typed public readings should discharge the hypotheses they actually imply.
Do not add copies of derived layout facts, but do not remove a dynamic connection merely
because both circuits belong to a compiled application. In particular, independently supplied
tables need not describe matching proof statements.

Reuse the current capstones directly:

```lean
StepWrapLink.verifies_proof
WrapStepLink.verifies_proof
StepProofHandover.handover_or_collision
WrapProofHandover.handover_or_collision
WrapProofHandover.appState_eq_or_collision
```

Retain the existing successful handover grouping: both complete messages agree, and the
earlier proof verifies or the later proof exhibits `AccumulatorFailure`; message-collision
alternatives remain outside that conjunction. Preserve the application-state projection and
its verified-slot restriction.

The endpoint is:

```lean
theorem checkedApplication_picklesCorrect
    (C : Circuits D L) (checked : CheckedApplication C) :
    PicklesCorrect C checked.indices
```

This theorem establishes the two lifting guarantees. The matrix consumer theorems retain the
remaining hypotheses above; neither the certificate nor `PicklesCorrect` asserts their validity.
State connections across producer applications using their own certificates and existing
interfaces; do not require a uniform domain or a global application registry.

### Tests and exit condition

- An application-level proof consumer starts at phase 2 and applies the capstones themselves.
  Hand-written Boolean lists duplicating their hypotheses are not an acceptance test.
- Existing `TwoPhaseChain` and `HeterogeneousPrevs` cached executions remain optional concrete
  evidence. They are not an obligation for the universal matrix theorem.
- Every supplied key, mask and internal-statement fact must concern the lifted run it is used
  with. Facts decided on a different prover valuation are not automatically transferable.
- Public consumers take only returned certificates, matrices and matrix connections; no native
  run, source-satisfaction fact or native-run connection may be an additional input.
- Audit each endpoint against its original capstone: no new axioms or erased alternatives.

Exit: the native reconstructed application's matrix-level Pickles guarantee is proved, with
all residual assumptions visible. No witness matrix needs to be exported to certify the
static application.

## Phase 4. Certified equality of indices

Module: `kimchi/Kimchi/Index/Compare.lean`, with separate check modules.

### Interface

For a common domain size and the existing field/decidable-equality instances:

```lean
def checkIndexEq (a b : Kimchi.Index F n) : Bool

theorem checkIndexEq_eq_true_iff :
    checkIndexEq a b = true ↔ a = b
```

Compare all stored data: every row's gate type, coefficients and wires, public count,
masked-row count, domain generator, shifts, endomorphism coefficient and MDS matrix.
The law fields need no data comparison; index equality uses proof irrelevance there.

The application comparator first checks the branch count and domain sizes, then compares the
dependent indices. A successful result must provide equality; retain useful failure categories
and a row/column location for table mismatches. Prove that equality transports `Satisfies`
with unchanged public values and table coordinates, handling dependent casts explicitly.

Source variable IDs are absent from `Index`. Keep `varsAgreeUpToRenaming` as an additional
fidelity check if useful; it is not part of this equality proof. Row/column permutations and
witness remapping are outside the plan.

### Tests and exit condition

- Kernel-decided equality of small independently built indices.
- Mutations of gate types, coefficients, wire targets and each metadata category are rejected;
  malformed indices may fail construction before comparison.
- Include padding-row mutations and application-level domain-size mismatches.
- A consumer transports satisfaction across the returned equality, not across an unrelated
  Boolean assertion.

Exit: successful comparison is connected by a theorem to actual index equality. This phase
does not depend on the Pickles proof machinery and can be reviewed separately.

## Phase 5. Import actual indices and transport application correctness

Modules: an adapter under `pickles/PicklesFixture/` and
`pickles/Pickles/Application/Imported.lean`.

### Independent import

Build the imported indices from the independent source-language circuit dumps and their
resolved backend metadata. Reconstruction continues to consume shape, rule replay, keys and
the shared environment. The compared imported gate table must not be generated from the Lean
reconstruction's gates.

The existing `Kimchi.Fixture.PS.build` is a witness-checking adapter: it synthesizes the
smallest fitting two-power domain, uses three masked rows and uses generator-power shifts.
Those choices do not establish identity with a deployment's actual index. On the certification
path, use the supplied keys' domain sizes, generators, shifts and masked-row counts, together
with the declared shared gate parameters. Reuse the existing parsers where appropriate.

Check raw array dimensions and bounds. Zero extension of omitted coefficient positions and
padding must have explicit, justified meanings; do not silently truncate data or repair wires.
Shared parameters remain declared environment inputs, rather than being copied from the Lean
comparison target merely to force equality. No new witness export is required.

### Transfer theorem

Native correctness is an explicit input to the transfer:

```lean
theorem importedApplication_picklesCorrect
    (C : Circuits D L)
    (native imported : ApplicationIndices D)
    (hNative : PicklesCorrect C native)
    (hMatch : imported = native) :
    PicklesCorrect C imported
```

The checked-application corollary obtains `hNative` from phase 3 and `hMatch` from phase 4.
It does not inspect the imported circuit for unwired-variable admissibility: that condition
was discharged on the Lean reconstruction, whose index now matches the imported one.

Imports continue to be resolved through reconstructed producers and `SourceFor`. When a
claim spans producer/consumer applications, use each application's corresponding certificate.
Equality of one application's indices does not certify an unrelated producer's indices.

### Verifier-key correspondence

`pickles/Pickles/KeyDerivation.lean` interpolates each index column by the proved inverse NTT
and commits its coefficients using the accelerated MSM. Each chunk restarts at the first SRS
generator. The seven permutation and fifteen coefficient columns are unmasked; the six
selector columns add the SRS blinding base once per chunk. `deriveKey` assembles the metadata
and computes the digest from the derived commitments, independently of the supplied key.

`checkKey?` checks metadata, the SRS chunk count and the shape's predecessor count, then compares
every commitment. Its success carries `KeyCorresponds`, stated against polynomial commitments.
The supplied `Key` already proves its digest equation. `certifyKeys?` checks every branch and
the wrap; `Certification` retains `ApplicationKeys` alongside the imported-index certificate.
The manifest driver certifies external producers too and blocks their dependents on failure.

`check-application-keys` defaults to three explicit manifest entries: `SimpleChainN2` for
nonchunked self recursion, `HeterogeneousPrevs` for nonchunked self plus external recursion
(including its producer), and `SelfRecursiveChunks` for chunked self recursion. `APPS` can
override that selection. Kernel checks cover inverse interpolation and located commitment
comparison. The small application driver also changes step and wrap commitments, recomputes
their digests, and requires the otherwise wellformed keys to fail against the unchanged index.

### Tests and exit condition

Run explicit selections, expanding only after the preceding case passes:

1. `NoRecursionReturn`: the complete reconstruction, checked compilation and index comparison.
2. `TwoPhaseChain`: recursion and both handover directions.
3. `HeterogeneousPrevs`: distinct producer schemas and external slots.
4. `RecurseOverChunks`: source chunk/domain metadata beyond the one-chunk default.
5. `ExampleTransaction`: the transaction/merge application and its existing tree of proofs.

Mutate an independent dump's coefficient, wire or metadata and require correspondence failure.
Retain explicit manifest selection and missing-tag/coverage failures. Keep the existing
constraint-system comparison as additional evidence where appropriate.

Exit: the universal imported-application theorem and its checked adapter are implemented;
targeted fixture runs exercise the success and rejection paths. Distinguish this from the
closed certificate for a named application in phase 6.

## Deferred experiment: kernel-certify a named imported application

This investigation was stopped in favor of the compiled `certify-application` executable.
The executable reconstructs, checks and compares selected artifacts, returning the certified
indices or located errors. Its universal theorem is kernel-checked; it does not emit a
standalone kernel proof of a named file’s parsing/checking success. The experiment below is
future work, not an obligation for matrix handover or the executable.

A universal theorem about successful checking and a successful native fixture run are
different deliverables. A closed theorem about a named imported application also needs
kernel-checked success facts for reconstruction, checked compilation and index equality.

Begin with a small serialized example and a named theorem applying phase 5 to its fixed
artifacts. Pin what those artifacts are; a theorem with the concrete success facts still
assumed is not the finished named certificate.

Then investigate bounded, compositional certificates for a real application. The earlier
monolithic kernel evaluation reached the agreed memory cap just traversing large source
lists. Do not repeat that scaling experiment, raise the cap, or silently introduce
`native_decide` or another trusted evaluator. A certificate design must also account for
reconstruction and compilation, not only equality of precomputed tables.

### Tests and exit condition

- Kernel-check the small serialized example end to end, including its success facts.
- A changed artifact cannot reuse the old certificate.
- Prototype any larger certificate mechanism under explicit resource bounds and report
  whether it closes the concrete success obligations.
- Retain native application runs as executable validation while concrete certification is
  unresolved; do not relabel them kernel-certified applications.

Exit: a named imported application's theorem invokes the universal transfer theorem with
its concrete success facts proved. Scaling this to the full transaction fixture is an
explicit task, not an automatic consequence of the earlier phases.

## Delivery and validation discipline

Implement and review one phase at a time. The first implementation target is phase 1 only.
Within a phase, begin with types and complete theorem signatures and work backward from them.
Settle the complete `PicklesCorrect` definition and its matrix consumers before phase 1, so
the checked compilation and lifting interfaces are built to supply that precise claim.

Preserve the backend facade: no consumer should need `Backend/Internal` definitions, raw
`Scoped` proofs or hand-assembled `IndexOf` proofs. Keep helpers private until a concrete
consumer requires them. JSON and fixture IO stay out of the application theorem modules.
The public consumer and regression endpoints should be rooted; do not root unused proof
milestones merely to keep them alive.

Build explicit changed-module targets and affected consumers. At phase checkpoints, run the
appropriate build, style, comments, axiom, dead-code, import-boundary, shake and lint gates.
Run meaningful small kernel decisions and the selected fixture checks stated for that phase.
Do not run `LINKS=all`; application selection comes from the manifest, never auto-discovery.
Expensive checks run one process at a time under the existing resource limits. Do not rerun
the full fixture corpus for a proof-only change without a concrete reason.

Record separately: universal kernel-checked theorems, small closed certificates, native
fixture results, and unresolved concrete-certification obligations. No proof-acceptance
soundness theorem, native `compileMulti`, or change to `compile`'s result representation is
required by these phases. The latter simplification remains issue #447.
