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

`PICKLES_DUMP_DIR=<dir> lake exe check-slot-chunks` uses the TwoPhaseChain dump's constants to
construct synthetic two-slot circuits at counts `[1, 2]` and `[2, 1]`, and checks reader rejection
of inconsistent Self slots. This tests construction; it supplies no mixed-chunk proof witness.
`check-tags` separately compares dumped circuits, and its selected `LINKS=<app>,…` mode checks
cached witnesses and applies both capstones and the handover theorems directly.

The application layout check reads only the tag metadata for `TwoPhaseChain` and
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

The same driver compares those assembled circuit parameters with the dumped per-slot
constants. Backend inputs are the application's wrap key and ordered branch keys, plus
Lagrange tables. Those tables occur only inside slot constants in the current schema:
the driver collects one per wrap domain and rejects disagreeing copies. Table selection
is checked; correspondence with SRS commitments remains the explicit upstream premise.
Negative cases change key order, key layout, source keys/domains/chunks, Lagrange table
selection and domain pins. This phase builds static configuration, not circuits or runs.

Source chunk counts are derived per branch-local slot. A synthetic imported interface
exercises mixed counts 2/1 without imposing an application-wide predecessor chunk count.
That is a static-wiring check, not a mixed-chunk proof fixture. The existing step circuits,
capstones and readers accept per-slot counts, so `Wiring.sourceChunks` can supply the
count family for application circuit construction. Application execution/path wrappers
remain a later phase.

```bash
lake build PicklesFixture.Application PicklesFixture.ApplicationWiring
PICKLES_DUMP_DIR=/path/to/pickles-dumps lake env lean --run scripts/check_application_layouts.lean
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
