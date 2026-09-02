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
**The modeled fragment excludes lookups, optional gates, recursion, and the sub-SRS
regime** — Mina/pickles proofs are outside it on all four axes; the canonical fragment
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
- `docs/` — design notes, the audit record, and the follow-up register
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

## How to run the formalization loop

```bash
archon loop .
```

This launches the plan → prove → review loop and opens a dashboard.
