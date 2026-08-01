# The minimum support for the locked target

Target: `deployedExtract_failure_measure_le` (`docs/locked-target.md`).

## The criterion

Not "what does the current proof reach" — reachability from our own roots certifies the
duplication, because our proof reaches our own copies. The criterion is per ingredient:

> Does ironwood already have this? If yes, import and call it. If no, we own it, and the reason
> must be stated.

## Why anything is ours at all: five absences, each verified

`grep` over the entire pinned tree (`.lake/packages/Zcash/Zcash`, `--include='*.lean'`):

| term | hits | consequence |
| --- | --: | --- |
| `glv` (case-insensitive) | **0** | no endomorphism/short-basis theory — nothing to import for the challenge domain |
| `challengeNat` | **0** | challenges are never squeezed as bounded naturals |
| `endoExpand` | **0** | no expansion map: upstream challenges *are* field elements |
| `foldHalves` | **0** | upstream folds generators with `u⁻¹` (`foldGens`), never with `u` |
| `sg` (whole word) | **0** | no notion of the final synthetic-blinding group element |

Those five zeros account for essentially every line we keep. Upstream's challenge alphabet is the
field, so its bound divides by `|F|`; ours is `2 ^ 128`, and closing that gap is not an import.
Upstream's fold convention is the inverse of kimchi's, so no upstream extraction result applies
until transported. Upstream has no `sg`, which is why the oracle domain must be a structured node
type rather than a transcript prefix — `DecodesFromPrefixes.final` has to return it.

## What we own, and why it cannot be imported

The `lines` column is `wc -l` **as of the reference-doc sweep**, not as of the audit; where the
audit's figure differed it is given after the arrow. The `why` column is the substance and is
unchanged.

| ours | lines | why ironwood cannot supply it |
| --- | --: | --- |
| `EndoChallenge.lean` | 428 | the four `expandPre` hypotheses of the target. Zero upstream hits for `glv`/`endoExpand`/`challengeNat` |
| `Convention.lean` | 138 | `foldHalves` ↔ `foldGens`: invert challenges, swap `L`/`R`. Without it no upstream extraction result applies |
| `Transcript.lean` | 519 (was 414) | our wire sponge and its absorption order — `preC` absorbs `δ` only, never `sg`, which is what forces the node domain |
| `Deployed.lean` | 970 (was ~800) | `IpaNode` + `Fintype`, `nodes`, `nodeTranscript` faithfulness, `decodesFromPrefixes_nodes`, `wireWins`, `wireWins_iff_wins`, `deployedExtract`, the target, `verifyWith_of_deferred_delta` |
| `Honest.lean` | 722 (was ~570) | upstream ships **no** wins-on-every-table companion for any of its fork games; each instantiation owes its own |
| `Prover.lean` | 161 (was ~226) | the kimchi prover shape and `kimchiProverAccept_iff_verifierAcceptsAt`, the anti-parallel-predicate pin |
| `SVector.lean` | 155 | `bPolyCoefficients` satisfies the doubling recursion; `combinedB_eq_innerProduct` |
| `Capstone.lean` | 165 | the cert layer and its exit into upstream `deployed_forking_tree` → `ipa_extractV` |
| `Schnorr.lean` | 66 | the Schnorr wrapper is kimchi-only; halo2 has no such round. This is the `+1` in the bound |
| `Adapter.lean` | 70 | `SRS ≅ URS` (`rfl`) and `openingRelationB` = upstream `IpaRelation` at `P − ρ • σ.h` |
| ~~`Triviality.lean`~~ | **deleted** (was ~139) | the vacuity results: `Prop`-level `∃`/`∨` is free over the deployed 1-dim group. The file went at step 3 of `forking-consolidation-plan.md` and the vacuity results went with it — kept here because *why* it was ours is still the record |
| `Game.lean`, the field-coupled part | ~1,380 of 2,261 | the fork recursion and realization (`u⁻¹` at the node), the extractor, `DecodesFromPrefixes`, and `verifierAcceptsAt_of_deferred_delta` |
| kimchi `Transcript`/`OracleRun`/`RunLink` | 346 (was 460) | the fq/fr prefix machinery and its faithfulness — the `m > 0` block |

"Roughly **4,700 of 6,253 lines survive**" was the estimate **as of the audit** (per-declaration,
against pinned ironwood `83a98f7f`; the same 6,253 denominator as `forking-consolidation-plan.md`'s
verdict). Measured today instead: the ten extant single-file rows sum to **3,394** lines and the
kimchi row adds **346**, so **3,740** lines are accounted for outright; the `Game.lean` row is the
only estimate left, and its field-coupled/portable split is not cheaply re-derivable from a
2,261-line file. For a denominator that *is* re-derivable: `bulletproof-pcs/Bulletproof/Forking/`
is **6,685** lines today and `kimchi/Kimchi/Verifier/Forking/` **2,375**.

Whichever number you take, the five absences above are why it is not smaller: the parts of this
development that look like duplication are mostly the parts upstream does not contain.

## What leaves, with the upstream name that replaces it

| ours | upstream |
| --- | --- |
| `scanFork` + 5 lemmas + the two `≠ none` corollaries | `nextForkChallenge` + `_isSome_of_good`/`_output_fresh`/`_output_attempt`/`_other_good_mem_rest`/`_two_more` (`Recursive.lean:242`, `:258`, `:323`, `:347`, `:285`, `:417`) |
| `PreThreeForkSuccess`, `preForkEscape`, `_subset_triple` | `ThreeForkSuccess`, `recursiveForkEscape`, `_subset_triple` (`Recursive.lean:168`, `:174`, `:179`) |
| the escape-set quartet + its measure bound | `escapesDuringC_measure_le'` (`OracleComp.lean:728`) ∘ `uniformOfFintype_toOuterMeasure_triple_le` (`Probability.lean:339`) |
| `KimchiForkReached`, `_child`, `KimchiRunHistory` | `RecursiveForkReached`, `recursiveForkReached_child`, `RecursiveRunHistory` (`Recursive.lean:1063`, `:1074`, `:780`) |
| the tape-completeness argument | `RecursiveForkTape.toCoins_complete` (`Recursive.lean:147`) |
| three copies of the `commitGen` algebra | `commitGen_{add_gen,smul_gen,add_left,smul_left,round,split}` (`CommitFold.lean:32-57`, `IpaSoundness.lean:88`) |
| `Wins` as a definition | `fsWinsFull` (`Adaptive.lean:30`) — equal at `m = 0` by `Iff.rfl` |
| `Extraction.lean`, `Knowledge.lean` | superseded in-tree by `Capstone`/`Prover`/`Deployed`; not upstream |
| kimchi `Escape.lean`, `GuardEscape.lean` | nothing — they divide by `Fintype.card C.ScalarField` for 128-bit challenges, understating the cost by ~`2 ^ 126`. Deleted as wrong, not as redundant |

## Consequence for the plan

The nine-step order in `forking-consolidation-plan.md` stands, with one change of emphasis: the
target above is the acceptance test for every step. A step that keeps the build green but moves the
target further away is a regression, and a step that deletes either anti-vacuity companion voids
the target even while the bound still compiles.

Which of the nine still bind: per that document's own status banner, steps **1, 2, 3, 6, 7 and 9
are executed** and only **4, 5 and 8** remain open — so the order constrains those three (step 8
is now settled as NOT DONE rather than unsettled: its `good`/`hgood` hoist targets exist as
`kimchiForkGoodAtU`/`_update`). The ordering constraint **3 and 4 before 7** was already violated
by execution order, 7 having landed without 4.

## The standing directive

Recorded here because it outlives any particular job spec, and because the seed that carries it to
the prover is local-only.

> Prefer a strategy derived from an ironwood import over anything written in this tree — including
> over declarations that look purpose-built for the goal. **Where a route requires going with
> ironwood instead of our own code, take it.** That is the preferred outcome, not a deviation: a
> proof that reaches its target through `Zcash.Snark.*` and leaves declarations of ours unused is a
> better result than one that consumes them, because it tells us what to delete.

Two corollaries, both load-bearing:

* Freezing a file means it cannot be *edited*. It never means it must be *used*. Routing around a
  frozen declaration is permitted and encouraged; the declarations a proof renders unnecessary are a
  deliverable, to be named so they can be deleted.
* A refuted reuse claim is worth as much as a successful one. When an ironwood route turns out not to
  work, the specific obstruction gets recorded rather than silently worked around — that is how the
  five zero-hit absences above were established, and how the `[Field F]` premise this project
  carried for weeks was eventually falsified.
