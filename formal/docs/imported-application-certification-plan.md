# Imported Pickles application certification: plan and current status

## Current contract

This document records the phased work following [PR #448](https://github.com/l-adic/snarky/pull/448)
and [PR #444](https://github.com/l-adic/snarky/pull/444), originally based at `3a0efd78` on
`formal/multirow-gates`. The phases below are retained as **historical design**, not the current
API or a remaining implementation checklist. Application certification was subsequently
consolidated around supplied-key correspondence; foreign-index comparison is a separate fixture
operation. The earlier compiler design history is in
[compiler-trace-handoff.md](compiler-trace-handoff.md).

Reconstruction produces `Pickles.Application.Circuits D` from exported shape, rule replay,
backend artifacts and shared setup. The canonical constructor is:

```lean
def checkApplication (C : Circuits D)
    (steps : (b : D.Branch) → StepCompilation C b)
    (wrap : WrapCompilation C) :
    Except (ApplicationFailure D) (ApplicationCertified C)
```

The caller supplies the canonical compilations in hand so each circuit is compiled once.
`ApplicationCertified` bundles the checked Step/Wrap indices, correspondence of the supplied
keys to those indices under the shared SRSs, the embedded verifiers' static setup assumptions,
and finiteness of the slot-source key commitments. Checking recomputes the Lagrange bases from
the SRSs and compares them with the supplied tables. Its constructor is private.

```text
shape + rule replay + backend artifacts + shared setup
  -> reconstructed Circuits D
  -> canonical Step/Wrap compilations
  -> checkApplication: checked indices + supplied-key correspondence + static verifier setup
  -> ApplicationCertified C
```

`certify-application` runs this path for explicitly selected manifest entries. It requires
neither independent foreign circuit dumps nor a proof cache. A returned certificate concerns
the reconstructed circuits and their supplied keys; it does not assert literal equality with
an independently exported foreign constraint system.

### Lifting and theorem consumers

`ApplicationCertified.lift_step` and `.lift_wrap` lift arbitrary satisfying tables at
`cert.indices` to satisfying circuit runs at the same public statement and the fixed
`stepValuation`/`wrapValuation`. No honest-prover or cached-advice premise is required.
Connections between supplied matrices are stated on those fixed readings before lifting.
The interpretation reads unrepresented variables as zero; it need not recover an arbitrary
original prover valuation on unused advice cells.

`matrices_stepWrap`, `matrices_wrapStep`, `matrices_wrap_handover` and
`matrices_step_handover` consume the participating applications' certificates directly.
The certificates discharge static verifier setup. Dynamic statement connections, source
relations, required-proof flags and applicable key/mask readings remain in the matrix
interfaces. The capstones retain their collision and accumulator-failure alternatives.

At the proof level, `ApplicationCertified.step_valuation_or_failure` and
`.wrap_valuation_or_failure` derive a satisfying Lean valuation with the accepted public
statement, or an explicit `KimchiFailure`, from acceptance under a certified key. Kimchi
soundness is not proved, and no probability bound is asserted by this failure predicate.
`SomeKimchiFailure` hides the particular failed index/proof at the application level.

### Key checking and optional foreign-index comparison

`kimchi/Kimchi/KeyDerivation.lean` derives commitment columns from an index and SRS using the
proved inverse NTT and accelerated MSM. `checkKey?` checks metadata and every commitment,
returning `KeyCorresponds`; `checkApplication` applies it to every Step key and the Wrap key.
`KimchiVK` itself carries the checked curve constants, domain, zero-knowledge row count and
digest equation. There is no separate Pickles key wrapper or whole-key `deriveKey` construction.

Independent gate dumps can still be compared in `PicklesFixture.ImportedIndices` using
`compareIndices?`; `compareIndices?_eq_none_iff` supplies actual index equality. The consumers
in [application-certification-draft.lean](application-certification-draft.lean) use that equality
to apply the certificate's matrix theorems to independently imported indices. This comparison
is optional and is not part of `ApplicationCertified` construction.

The old names appearing in the historical phases below have these replacements:

| Historical interface | Current interface |
| --- | --- |
| `CheckedApplication`, `PicklesCorrect`, `ApplicationKeys` | `ApplicationCertified`, its checked indices/key fields, and its lifting theorems |
| `certifyKeys?` | Key checking inside `checkApplication` |
| `CertifiedIndices`, `certifyIndices?` | Separate fixture-level `compareIndices?` and equality transport when foreign dumps are needed |
| `deriveKey`, `Pickles.KeyDerivation` | `deriveColumns` and `checkKey?` in `Kimchi.KeyDerivation` |
| `Circuits D L` | `Circuits D` |

### Scope and validation

The certificate does not establish application-rule business semantics, justify a rule's
choice of `mustVerify = false`, or prove an entire application's inductive derivation relation.
Reconstruction remains relative to the decoded exported artifacts. Optional gates, lookups,
sideloading and full prover-key generation remain separate work. The sideloading follow-up is
[sideloaded-application-certification-plan.md](sideloaded-application-certification-plan.md).

Universal kernel-checked theorems, native checker runs, and a closed kernel proof of successful
checking for a named serialized application remain distinct deliverables. The compiled
`certify-application` executable provides the second using the first; it does not emit the third.

## Historical phases

The remaining sections preserve the original matrix/index-comparison plan and its review
boundaries. Their old signatures and module names document that design; use the current
contract above and the production declarations for new work. In particular, do not restore
the removed certificate wrappers or make foreign circuit dumps a certification prerequisite.

## Phase 1. Checked compilation of one application (historical)

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

## Phase 2. Satisfying tables give typed application runs (historical)

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

## Phase 3. Apply the application capstones to lifted runs (historical)

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

## Phase 4. Certified equality of indices (historical)

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

## Phase 5. Import actual indices and transport application correctness (historical)

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

## Deferred experiment: kernel-certify a named imported application (historical)

This investigation was stopped in favor of the compiled `certify-application` executable.
The current executable reconstructs the selected applications and checks their Lean compilations,
supplied keys and static setup, returning `ApplicationCertified` or located errors. Its universal
theorems are kernel-checked; it does not emit a standalone kernel proof of a named file’s
parsing/checking success. The experiment below is
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

## Original delivery and validation discipline (historical)

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
