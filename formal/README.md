# Formal

<!-- archon:readme -->
<!-- Claude fills in the prose sections below. Keep the section headers. -->

## Project

A Lean 4 + Mathlib formalization of the kimchi proof system over the Pasta curves: the basic
gate set (Generic, Poseidon, AddComplete, VarBaseMul, EndoMul, EndoScalar), the
arithmetization, and the executable verifier. Gates are modelled as plain Lean predicates
over witness structures and proved faithful to Mathlib's elliptic-curve group law
(`WeierstrassCurve.Affine`). The verifier itself is a **specification** — the transcription
of proof-systems' `kimchi/src/verifier.rs`, and the anchor circuit implementations are proved
faithful to; the probabilistic soundness development this tree once carried was retired.
**The modeled fragment excludes lookups and optional gates**; recursion's old accumulators
are on the wire, validated on a deployed pickles wrap proof, and production's sub-SRS
one-chunk regime is in scope — Mina/pickles proofs are outside it only where they use
lookups or optional gates; the canonical fragment
statement is the `## Scope` section of `kimchi/Kimchi/Verifier/Kimchi.lean`'s preamble. A second library, `Snarky`, is a
deep-embedded port of the PureScript circuit-building DSL, modelling how constraint systems
are *constructed*; it is Mathlib-free by design and bridges to the verified generic-gate
checker. See [`CLAUDE.md`](CLAUDE.md) for the detailed guide: the layer stack, the gate
modelling convention, the faithfulness pattern, and the axiom discipline.

## References

See [`references/summary.md`](references/summary.md) for a description of each source.

## Structure

`formal/` is a lake workspace of standalone path-required packages; the root package is a
pure aggregator that owns no library.

- `pasta/` (lib `Pasta`) — the Pasta curve trust base: orders, GLV constants, point groups
- `poseidon/` (libs `Poseidon`, `FixtureKit`) — the Poseidon permutation and sponge, the
  `FqSponge` consumer layer, SvdW map-to-curve, and the shared JSON-fixture kit
- `bulletproof-pcs/` (lib `Bulletproof`) — the IPA polynomial commitment: the abstract
  scheme and the executable Pasta wire verifier
- `kimchi/` (libs `Kimchi`, `KimchiFixture`) — the kimchi protocol: gates, index,
  arithmetization, and the executable verifier with its body in closed form
- `snarky/` (lib `Snarky`) — the deep-embedded circuit DSL and its kimchi bridge
- `docs/` — the negative controls and standing invariants, the completeness guide, and
  why soundness is out of scope
- `scripts/` — workspace-wide gates (style, dead code, kernel replay, sorry census); each
  package additionally owns its own `scripts/` (axiom gate, fixture checks, `roots.txt`)
- `references/` — PDFs, papers, and informal notes backing the formalization
- `archon-protected.yaml` — declarations agents must not modify
- `.archon/` — agent state (not committed)

There is no `blueprint/` source directory: the in-file docstring preambles are this project's
informal layer. The root-level `blueprint.{md,html,pdf}` are stale generated artifacts from
2026-06-24 (they document `Kimchi.Gate.AddComplete.sound_point`, which no longer exists — the
live pair is `sound_point_noninf` / `sound_point_inf`).

## How to build

```bash
lake exe cache get   # download Mathlib olean cache
make lean-build      # from the parent repo root
```

`make lean-build` expands to the explicit target list, which is the build gate:

```bash
lake build Kimchi Snarky Pasta Poseidon FixtureKit Bulletproof BulletproofFixture
```

Name that list (CI adds `KimchiFixture`). **Bare `lake build` from `formal/` builds
nothing** — the root package owns no library and declares no `defaultTargets`, so it reports
`Build completed successfully (0 jobs)` while stale modules sit on disk. Per package,
`cd <pkg> && lake build` does work; all five declare `defaultTargets`.

The gates, all CI-enforced:

```bash
scripts/check-style.sh                  # the formatter contract (≤100 cols, no tabs, …)
scripts/check_sorry_census.sh           # no sorries anywhere
scripts/deadcode.sh                     # reachability from the packages' roots.txt
scripts/kernel-replay.sh                # lean4checker replays every .olean
make lean-lint                          # Batteries' env_linter suite, one process per module
make lean-shake                         # no redundant imports
*/scripts/check_axioms.sh               # per-package axiom closures (all six packages)
```

The fixture drivers (`*/scripts/check_*fixture*.sh`, `check_fq_sponge.sh`,
`check_sponge_vectors.sh`, …) validate the executable layer against data recorded from the
production Rust code.

Pickles step circuits take a predecessor step chunk count and finalize parameters for each
slot (`ncs : Fin n → Nat` and `P : Fin n → FopParams Fp`). A uniform circuit supplies constant
functions. The fixture readers retain each slot's declared count; Self slots must agree with
each other. `wrapStep_kimchiVerify` requires the selected slot's count to match the step key
being verified, without restricting the other slots.

`PICKLES_DUMP_DIR=<dir> lake exe check-slot-chunks` uses the TwoPhaseChain sidecar's key to
construct synthetic two-slot circuits at counts `[1, 2]` and `[2, 1]`, and checks reader rejection
of inconsistent Self slots. This tests construction; it supplies no mixed-chunk proof witness.
`check-tags` separately compares dumped circuits, reading each branch's unfinalized padding
from its tag's sidecar by predecessor count. Its selected `LINKS=<app>,…` mode checks cached
witnesses and applies both capstones and the handover theorems directly.

The application layout check reads only the sidecar metadata for `TwoPhaseChain` and
`HeterogeneousPrevs` (including its child tag). It checks independently described
branch/slot shapes against the dumps and exercises front padding and rejection of
widths above the protocol bound, without building circuits or running witness checks.
Synthetic cases additionally exercise shared slots with differing source widths, including
widths 0/2 and 1/2 in both branch orders. Each shared slot's capacity is the maximum source
width across branches; source widths remain unchanged. The library proves each source
width fits its assigned capacity instead of requiring equal widths at overlapping slots.

Each description covers one application. The checker first assembles the child's layout
and wiring, then supplies its exported interface to the parent; the parent does not
inspect the child's branch descriptions. `Application/Wiring.lean` derives candidate
step domains from branch keys, resolves Self/External sources, and computes the padded
wrap-domain pin matrix. It checks key layouts, chunk counts against domain sizes, and
supported wrap domains. Generic theorems establish source widths, domain selection,
live-slot pins and the branch-key layouts consumed by the existing capstones.

The same driver checks backend metadata from the application's wrap key and ordered
branch keys. Its synthetic Lagrange values suffice for layout checks. Reconstruction
derives the actual tables from the shared SRS, and cached-run capstone checks establish
their correspondence explicitly. Negative cases change key order, key layouts,
domains and chunk counts.

Source chunk counts are derived per branch-local slot. A synthetic imported interface
exercises mixed counts 2/1 without imposing an application-wide predecessor chunk count.
That is a static-wiring check, not a mixed-chunk proof fixture. The existing step circuits,
capstones and readers accept per-slot counts, so `Wiring.sourceChunks` can supply the
count family for application circuit construction.

```bash
lake build PicklesFixture.Application PicklesFixture.ApplicationImport
PICKLES_DUMP_DIR=/path/to/pickles-dumps lake env lean --run scripts/check_application_layouts.lean
```

### Reconstruction from application sidecars

`check-tags` and `check-application-shapes` reconstruct each application from its single
`shapes/<tag>.json` sidecar and the shared SRS files. The sidecar carries the shape,
input checks and rule operations, resolved keys and protocol padding. Imports resolve
against previously reconstructed producers. Lagrange tables and the padding accumulator
commitment are computed from the supplied SRS; no tables are read from circuit dumps or
an on-disk Lagrange cache.

The result retains the existing `Assembled` application and its `Setup`. Only after
assembly does the driver read `<tag>.json` to compare every step branch and the shared
wrap circuit: public-input size, gate types, coefficients, permutation wiring and cell
variable identities up to renaming. Circuit dumps contain only those comparison inputs;
keys, rule operations and padding are in the sidecar, and witness advice is in the proof cache.
`PaddedWideSlots` has zero-, two- and one-predecessor branches at width two, so its
padded branches exercise distinct entries of the unfinalized padding table.
The reconstruction reader has no circuit-dump or proof-cache argument. With `LINKS=<app>,…`,
`check-tags` also runs the reconstructed circuits on cached advice, checks source and
backend satisfaction and public inputs, and directly applies the application verification
and handover capstones. Every selected cache entry must be covered.

`pickles/PicklesFixture/Manifest.lean` is the required corpus: an explicit list of fixture
test names and all tags each must emit. Neither driver discovers applications or tags
from directories. Both default to the complete manifest. `APPLICATION_SHAPES=<app>,…`
selects a subset for reconstruction; `LINKS=<app>,…` selects a subset with cached runs.
Unknown, empty or duplicate selections fail. Every listed circuit and sidecar must exist,
checked before loading SRSs. Adding a fixture requires adding its application/tag entry
to the manifest. Other files do not add tests to the corpus.

The example's transaction application is exported by the dedicated `example-fixtures`
executable under `packages/example/bin/`. Its manifest entry is `ExampleTransaction`.
See that directory's README for generation and selected reconstruction commands.

`Chunks4`, `SideLoadedMain` and `SideLoadedBound` do not currently export application
sidecars and are outside this reconstruction corpus. Their PureScript tests remain in
the suite. Old sidecars need regeneration because wrap-padding evaluations are required.

Rule replay covers all seven exported Kimchi variants. It retains dynamic `mustVerify`
expressions, rejects out-of-scope references, and fails on missing witness allocations.
`build_replayRule_irrel` establishes that replay advice cannot change the built circuit.
The focused tests cover every constraint payload, non-contiguous input variables,
returned expressions, scope errors, witness bounds and malformed sidecars.

The loader supports Self/External slots. Side-loaded slots are rejected. Each step branch
selects its unfinalized padding from the exported table by its own predecessor count.
SRS references check curves, round counts and blinding bases; the caller supplies the
actual shared generator files.

```bash
lake build check-rule-replay check-application-inputs check-application-shapes
lake env lean --run scripts/check_application_manifest.lean
lake exe check-rule-replay
PICKLES_DUMP_DIR=/path/to/pickles-dumps lake exe check-application-inputs
PICKLES_DUMP_DIR=/path/to/pickles-dumps \
  APPLICATION_SHAPES=TwoPhaseChain,HeterogeneousPrevs,RecurseOverChunks,PaddedWideSlots \
  lake exe check-application-shapes
```

### Follow-up: backport shared slot capacities to PureScript

The Lean application layout follows OCaml's per-position maximum
(`max_local_max_proofs_verifieds` in `mina/src/lib/crypto/pickles/compile.ml`, using
`Hlist.Maxes` in `mina/src/lib/crypto/plonkish_prelude/hlist.ml`). PureScript's
`deriveWrapSlotWidths` in `packages/pickles/src/Pickles/Prove/Compile.purs` still rejects
differing source widths at a shared wrap position. Backport the more flexible layout:

- Compute per-position maxima after front-padding each branch's slot list. Preserve
  each branch-local source width, statement schema, and key; capacity is separate.
- Adapt wrap advice/challenge-stack allocation and padding to those capacities. Audit
  message hashing and scalar finalization so padding to a shared capacity preserves the
  predecessor proof's message and accumulator interpretation. OCaml's
  `pad_messages_for_next_wrap_proof` and `Wrap_hack` are reference points; confirm padding
  order through the whole path rather than changing only the width calculation.
- Add PureScript applications that share a slot between width-0/width-2 and
  width-1/width-2 sources, including reversed branch order. Export their ordinary tag
  metadata, then extend this layout check and run structural and selected link fixtures.
  The link fixtures must apply the existing capstones and handover theorems directly.

Current boundary: the Lean layout accepts these descriptions, but does not yet build
their circuits or generate their witnesses. The existing PureScript fixtures validate
the common supported subset; the mixed-width cases currently validate Lean layout
assembly only. Circuit/witness construction and its padding correspondence remain work
for the application framework and the PureScript backport. This layout change does not
alter the existing StepWrap, WrapStep, or Handover capstones.

## How to run the formalization loop

```bash
archon loop .
```

This launches the plan → prove → review loop and opens a dashboard.
