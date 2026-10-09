# Side-loaded Pickles application certification: implementation plan

## Goal and fixed boundary

Extend shape/rule import, application reconstruction and the certification executable to
applications whose predecessor slots receive verification keys at run time. The application
continues to have one step circuit per branch and one shared wrap circuit. Different runtime
keys are witnesses of the same circuit, not additional compiled branches or indices.

This plan builds on [PR #449](https://github.com/l-adic/snarky/pull/449) and
[imported-application-certification-plan.md](imported-application-certification-plan.md).
The starting implementation is `bbeb4b2d` on `formal/checked-application`.

**Keep the original capstones unchanged.** Existing capstone statements, proofs, assumptions
and collision/accumulator-failure alternatives are fixed contracts. Add readings and adapters
that establish their premises for the side-loaded path. Do not broaden a capstone or add an
unjustified premise to the application certificate to accommodate the implementation.

Some existing circuit-specific wrappers explicitly use known domains and static domain pins.
Direct application of those wrappers to a new circuit body is not established. Phase 1 must
identify the reusable semantic contracts and demonstrate composition with the unchanged
capstones. New side-loaded adapters may be necessary. Do not start by generalizing every
existing circuit type or editing the old capstone proofs.

The intended argument remains:

```text
shape + recorded rule operations + shared artifacts
  -> reconstructed application, including runtime VK output handles
  -> checked compilation and exact equality with independent dumped indices
  -> universal lifting of arbitrary accepted imported matrices
  -> readings of runtime keys, domains, masks, statements and accumulators
  -> existing verification and handover capstones
```

There are two distinct endpoints:

1. Certify the parent's static circuits and its own supplied step/wrap keys. Arbitrary
   satisfying parent matrices lift with their public statements and retained runtime VK cells.
2. Apply the capstones to a chain involving a particular runtime-selected producer. Supply
   that producer's certificate and connect the parent's runtime descriptor to that producer's
   independently checked key. The parent's certificate alone does not certify arbitrary
   children or enumerate a set of authorized applications.

Keep the existing `PicklesCorrect` vocabulary and fixed matrix valuation. Connections are
expressed on the supplied matrices before lifting. Whole-message equality remains a conclusion.
No honest-prover, cached-advice or particular witness-chain premise belongs in certification.

## Current implementation: established facts

Paths in this section are relative to the repository root.

| Component | Current boundary |
| --- | --- |
| `packages/pickles/src/Pickles/Dump/Shape.purs` | Already encodes `SideLoadedSource`, with a statement layout and slot width. |
| `formal/pickles/PicklesFixture/ShapeDump.lean` | Parses `sideLoaded`, then rejects it in `sourceRows`. |
| `packages/pickles/src/Pickles/Prove/RuleDump.purs` | Records allocations and source constraints; rejects a returned side-loaded VK in `prevOf`. |
| `packages/pickles/src/Pickles/Dump/Tag.purs` | Rejects side-loaded slots while assembling the reconstruction sidecar. |
| `formal/pickles/PicklesFixture/Rule.lean` | Replays local allocations/constraints; predecessor outputs have statements and flags, no VK descriptor. |
| `formal/pickles/Pickles/Application/Description.lean` | `SlotRef` has Self and External; slot sizes come from their static layouts. |
| `formal/pickles/Pickles/Application/Wiring.lean` | Resolves every slot to a static producer interface and emits a static wrap-domain pin. |
| `formal/pickles/Pickles/StepMain.lean` | `SlotSource` has Self and External; each rule output is a `PrevStatement`. |
| `formal/pickles/Pickles/FinalizeOtherProof.lean` | Models known-domain finalization only. |
| `formal/pickles/Pickles/PublicInputCommit.lean` | Already contains masked bases/corrections and their group readings; reuse where emission agrees. |
| `formal/pickles/Pickles/WrapFinalize.lean` | Already accepts `none` pins. `pinWrapDomainIndex_spec` establishes a domain only for a `some` pin. |
| `formal/pickles/Pickles/Application/Run.lean` | `SourceFor` identifies a static producer and proves exact source-width equality. |
| `formal/pickles/Pickles/Application/KeyCertification.lean` | Certifies each application's own fixed step/wrap keys against its indices and SRSs. |

The source implementation has two different dynamic domain operations:

- The step scalar finalizer uses the side-loaded domain universe `[0..16]`, including a
  16-bit ones-prefix mask and the 17 domain-selection bits.
- The step group verifier selects its public-input Lagrange basis and shift corrections
  across wrap domains `[13,14,15]`, using the runtime VK's `actualWrapDomainSize` bits.

The runtime descriptor has two length-three one-hot vectors (`maxProofsVerified` and
`actualWrapDomainSize`) and the wrap-index commitment points. Its circuit-visible fields are
not a complete ordinary `KimchiVK` record. Relating the descriptor to an ordinary checked key
is a proof obligation, not a cast.

Side-loaded predecessor proofs currently use one step chunk in PureScript. Keep that supported
boundary explicit even when the parent application's own step proofs use multiple chunks.

## Non-goals and hypotheses retained

- Optional gates, lookups and feature flags are separate work. This plan covers the existing
  gate/protocol fragment with the side-loaded path added.
- No Rust backend integration, proving-key generation or new verifier soundness assumption.
- The original SRS, Lagrange, accumulator-check and connection assumptions remain visible.
  The committed Lagrange cache supplies operational data; it does not prove mathematical
  correspondence. Extend its inventory if needed without changing that boundary.
- Rule authorization is distinct from framework faithfulness. `bindVk` records constraints
  tying a side-loaded digest to a rule-supplied expression. A JSON label or the source-language
  `BoundVk` type is not proof that a particular digest authorizes an intended child.
- Parent certification requires no runtime key value or concrete child proof. A particular
  inter-application chain supplies its selected producer and the key/statement connection.

## Phase 1. Establish composition with the unchanged capstones

Deliver a Lean-checked statement/proof skeleton before implementing serialization or circuits.
Use scratch files outside the repository until the contracts have been checked. Skeletons
may take the precise new circuit-reading lemmas as hypotheses; they must actually apply the
existing capstones and must not use `sorry` to bypass composition.

Inventory the exact existing theorem contracts used by the result, including:

- `Pickles.stepWrap_kimchiVerify`, `Pickles.wrapStep_kimchiVerify` and `wrapStep_mask`;
- `Pickles.StepWrapRun.handover_or_collision` and
  `Pickles.WrapStepRun.handover_or_collision`;
- the application verification/handover wrappers and matrix consumers.

For each, record whether it consumes abstract semantic readings or a particular compiled
circuit body. Identify the lower-level contracts a new side-loaded wrapper can discharge.
Record the declarations that must stay unchanged and verify them against the baseline after
implementation. An unchanged theorem name with changed meaning is not acceptance.

Resolve these two boundaries explicitly:

1. **Domain alignment without a static pin.** With the active branch's pin equal to `none`,
   the pin equation does not select a wrap domain. Identify what ties the receiving wrap
   domain to the runtime descriptor and the selected producer's checked key. Attempt a
   mismatched selection. Document which ties follow from satisfaction and which are ordinary
   chain-connection conditions. Do not assert the missing equality as an unexplained new
   admissibility hypothesis.
2. **Capacity versus actual producer width.** `SideLoadedMain` passes a width-0 child through
   a width-2 slot. Replace reliance on static exact-width equality with the precise padding,
   active-mask and statement-reading facts the unchanged capstones need. Check the type-level
   transports and accumulator ordering on this case.

Select a representation that preserves the compiled-source specializations and permits new
runtime-source adapters without rewriting the capstones. Keep the shape, rules, static key
artifacts and checked-index types shared where possible. A side-loaded slot has an interface
and runtime descriptor, not a fabricated compile-time child key.

Write the complete target signatures with this quantifier order:

1. Certificates/key correspondence for each participating application.
2. Arbitrary satisfying step/wrap tables and public statements.
3. Runtime-source, domain, padding, mask and statement connections on their fixed readings.
4. The original capstone assumptions.

The results must retain the original verification and handover conclusions, including their
alternative grouping. Check both handover directions, not only parent matrix lifting.

**Exit:** the composition skeleton type-checks; the required new readings have exact contracts;
the domain/width questions and representation decision are recorded. If composition needs a
change to an original capstone, report the exact obstruction and revise the design with the
user before proceeding. Do not silently implement a weaker certificate.

## Phase 2. Export and replay the side-loaded rule outputs

The existing shape JSON is sufficient for a declared side-loaded interface, for example:

```json
{
  "kind": "sideLoaded",
  "statement": { "inputFields": 1, "outputFields": 0 },
  "width": 2
}
```

Implement the Lean shape counterpart using phase 1's representation. Check field counts,
protocol width bounds, branch-local routing and the capacities used by shared wrap positions.
Side-loaded slots do not require an entry in the static compiled-import registry.

Extend the rule dump's predecessor outputs with a structured runtime VK descriptor. Encode
its one-hot fields and commitment coordinates as the same local `CVar` expressions used by
the existing rule dump. Specify constructor/field order and vector/chunk lengths alongside
the encoder and reader; follow the source descriptor's circuit encoding.

Extend `RuleDump.ofJson`, local scoping, substitution and replay to all descriptor cells.
Extend checked-rule validation so a side-loaded slot returns its required descriptor and a
compiled slot uses its declared output form. Preserve compatibility with existing sidecars.

The recorded input check and rule body already include any VK witness allocation, on-curve
checks, one-hot checks and `bindVk` equations they execute. Replay those operations once and
reconstruct the returned descriptor from their handles. Preserve the framework's existing
shared-VK allocation and the original constraint order.

Remove the refusal points in `RuleDump.purs` and `Dump/Tag.purs` after the output format is
implemented. Add source fixtures without changing the existing circuit construction merely
to make a comparison pass.

**Tests:**

- Shape round trips with self, external and side-loaded slots in one application.
- Rule round trip with a witnessed VK and `bindVk` operations.
- All returned VK cells remap through the replay's local environment.
- Reject missing descriptors, malformed dimensions, wrong statement sizes and references to
  unallocated local variables, located at the branch/slot where possible.
- Existing compiled-source rule/shape tests and reconstructed-index comparisons still pass.

**Exit:** side-loaded rules are exportable and replayable with the returned handles preserved.

## Phase 3. Implement the missing circuit paths and their readings

Keep this phase in small commits. Each new body gets its reading and a focused comparison
before integration. Reuse existing arithmetic, one-hot, masking, group and sponge lemmas.

### 3a. Runtime descriptor interpretation

Implement the typed descriptor and its reading relation to a supplied checked producer key.
Cover commitment order, one-hot metadata, supported wrap domains and the descriptor's actual
producer width versus the slot capacity. Retain its handles in the step output.

The side-loaded `digestVk` encoding uses `MinaSideLoadedVk`, commitment coordinates and the
six packed one-hot bits. Keep it distinct from the ordinary index digest. Preserve the
recorded `bindVk` behavior; any theorem claiming digest binding must follow from its equations,
not from naming the descriptor `BoundVk`.

Tests cover all supported one-hot choices and malformed descriptor outputs. If a separate
digest-binding theorem is provided, test a wrong digest against the same key/table; changing
the public digest does not itself change the compiled index.

### 3b. Side-loaded scalar finalization

Implement the source's side-loaded domain mode, including the emission order of the prefix
mask, domain-selection bits, assertion, generator selection and vanishing computation.
Prove the scalar reading needed by phase 1 against the selected producer's ordinary key.
Keep the predecessor step-chunk restriction explicit and separate from the parent's chunks.

Tests cover supported domain selections, invalid/out-of-range domain readings, prefix-mask
boundaries and the scalar-half connection. A fixed list fed to the known-domain compiler is
not automatically the same circuit: check the actual emitted rows.

### 3c. Selected public-input commitments

Implement selection across the three wrap-domain Lagrange tables, including circuit-valued
shift corrections and sealing in the source's order. Reuse the existing masked commitment
mathematics where applicable. Prove that the selected bases/corrections yield the commitment
required by the unchanged group-verifier contract.

Tests cover each wrap domain, malformed selection bits, commitment readings and a focused
constraint-dump comparison. Keep Lagrange correspondence as the existing explicit premise.

**Exit:** the new circuits have the exact readings named in phase 1, preserve the compiled
source behavior, and match focused source dumps. No capstone has been changed.

## Phase 4. Connect the readings to application and matrix consumers

Add the runtime-source adapters selected in phase 1. A connection identifies a producer using
the runtime descriptor's fixed matrix reading and that producer's certified key. It accounts
for statement layout, supported domains, actual width, slot capacity and accumulator padding.
It does not resolve the side-loaded slot through a static import key.

Establish the verification, production/consumption, masks and hash readings needed by the
original capstones. Apply those unchanged theorems through the composition skeleton. Add
parallel circuit-specific wrappers where the existing known-domain wrappers cannot apply.

Expose the runtime descriptor, selected domain and relevant retained handles through the
existing public matrix-reading boundary. Preserve the fixed valuation selected by matrix
lifting; do not introduce a later existential valuation that can change the connection.
Reuse `PicklesCorrect` and the existing index-equality transport. Connections must not take
whole-message equality or the desired verifier acceptance as premises.

**Tests:**

- Theorem consumers for both verification directions and both handover directions using
  arbitrary tables, certificates and the reviewed connections.
- Width-0 producer in a width-2 side-loaded slot, including exact padding/mask ordering.
- Runtime key/producer mismatch and domain-alignment boundaries from phase 1.
- Compiled-source consumers retain their original statements and continue to compile.
- A consumer imports the supported interface without compiler-proof internals or checks.

**Exit:** universal matrix-level side-loaded chains reach the original capstone conclusions.

## Phase 5. Integrate reconstruction, metadata and key coherence

Wire the new source mode into reconstruction and checked compilation. Side-loaded positions
carry the appropriate `none` branch pins and the candidate Lagrange tables. Preserve one
compilation per branch/wrap and one parse of each independent dump.

Continue checking the parent's own step/wrap keys against its certified indices and shared
SRSs. A producer used in a chain has its own key correspondence and certificate. Parent
reconstruction does not bake in a runtime child key, and parent certification does not require
loading a particular child witness or its proof cache.

Extend the committed Lagrange cache manifest/regeneration inputs for any newly consumed
prefixes. Share identical domain tables through the existing mechanism. Report cache failures
at reconstruction as before; mathematical correspondence remains a theorem hypothesis.

Preserve exact index comparison, strict import validation, located failures and blocked
compiled-dependency reporting. Do not add imaginary static dependencies for arbitrary runtime
children. The tests may select child and parent artifacts together to exercise a concrete chain.

**Tests:** parent checked compilation and imported-index equality; independent parent/child
key corruption; altered dumped coefficients/wires; missing tables; mixed branch kinds sharing
one wrap circuit; new sources accepted by the existing proved scope checker.

**Exit:** the certification executable can return the parent's certificate with runtime VK
handles covered by the universal lifting result and its own key correspondence retained.

## Phase 6. Representative executable and adversarial coverage

Enable dumps for the existing `SideLoadedBound` and `SideLoadedMain` scenarios and their
children. Their current test configurations have `dump: Nothing`; make the relevant compile
calls export both sidecars and independent circuit dumps. Add explicit manifest entries and
selection rather than scanning directories.

Keep the initial runtime corpus small:

1. Bound side-loaded key: `SideLoadedBound` and its child.
2. Capacity/padding boundary: `SideLoadedMain` with its width-0 child in a width-2 slot.
3. One mixed compiled/side-loaded application, including different slot kinds at the same
   shared wrap position across branches where supported.

Require the existing executable to certify those parent circuits without a proof cache. Use
cached proofs only in the optional consumer lane to exercise real matrix connections and
the original capstones. Universal theorems remain independent of these executions.

Negative controls distinguish the stage expected to reject:

- Malformed shape, wrong descriptor dimensions or unallocated local ids: import/reconstruction.
- Altered framework equations in an independent dump: located index disagreement.
- Supplied parent/child key commitments changed with a recomputed digest: key correspondence.
- Wrong runtime descriptor for a chosen producer: the runtime-source connection cannot hold.
- Wrong binding digest for the same key: the rule's binding constraints reject that witness.
- Domain mismatch: the exact satisfaction/connection boundary established in phase 1.

An intentionally unbound rule can still be framework-faithful. Its certificate must not be
reported as proving authorization of a particular child. This is a statement-boundary check,
not a reason to reject all rules lacking a business authorization policy.

Run full build, style/comments, axiom audits, dead code, import boundaries, shake and lint;
repeat existing corpus comparisons when changed executable paths justify them. Add focused
CI selections and failure checks. Introduce no new axioms or trusted evaluation sites.

**Exit:** the existing executable certifies representative side-loaded parents, and the
universal matrix consumers apply unchanged capstones to their runtime-selected, separately
certified producers. Both handover directions and the domain/width boundaries are covered.

## Handoff and completion record

For each phase, record the implemented declarations, tests, unresolved obligations and any
deviation from the reviewed signatures. Treat the phases as separate commits or small stacks.
Keep proof machinery isolated and tests outside ordinary library import closures.

The most difficult work is expected in phase 3's readings and phase 4's domain/width adapters.
Phase 1 is a feasibility and statement check, not a claim that those proofs already exist.
The completion report must identify the unchanged capstones used, the universal matrix
endpoints, the native fixture results and the remaining original assumptions. Do not equate
a passing concrete proof cache with the universal result.
