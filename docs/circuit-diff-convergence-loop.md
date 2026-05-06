# Circuit-diff convergence loop

Drive a single `pickles-circuit-diffs` fixture from a known divergence
to byte-identical with the OCaml production CS, by editing PureScript
only.

## Current state (entry point)

After the M9 cleanup pass (commit `b8607be0`) every `step_main_*` /
`wrap_main_*` fixture is sourced from production OCaml drivers
(`tools/regen_top_level_fixtures.sh` + `PICKLES_STEP_CS_DUMP` /
`PICKLES_WRAP_CS_DUMP`). The truth state of `pickles-circuit-diffs`
(2026-05-05): **82/87 pass**, 5 mismatches.

### Distribution of mismatches sorted by delta

| fixture                                | delta         | notes                                                       |
|----------------------------------------|---------------|-------------------------------------------------------------|
| `wrap_main_side_loaded_main_circuit`   | −14           | Generic-only; cached_constants 147=147 (real VK in PS).     |
| `wrap_main_tree_proof_return_circuit`  | 0 rows        | Row + kind delta zero (commit `642766e4`); coeffs differ in `choose-key` because step CS divergent. |
| `step_main_side_loaded_main_circuit`   | +25           | Sideload-related (separate domain).                         |
| `step_main_tree_proof_return_circuit`  | −25           | FOP `ft_eval0` mul-chain divergence (memory).               |
| `wrap_main_two_phase_chain_circuit`    | 0 rows        | Row + kind delta zero (commit `307293f3`); coeffs differ on dummy VK — needs `compileStepMainTwoPhaseChain` for both branches. |

Recently converged:
- `step_main_simple_chain_n2_circuit` (was +1) — fixed by `perSlotFopDomainLog2s: 16 → 15` in `StepMainSimpleChainN2.purs`.
- `wrap_main_n2_circuit` (was +4) — commit `cf352650` "byte-identical via deterministic step VK".
- `wrap_main_circuit` (was +4074) — `WrapMain.purs` `Slots2 0 1 → Slots1 1` (mpv=2 → mpv=1, matching OCaml's `Max_proofs_verified.n = N1 = 1` for Simple_chain N1) + deterministic step VK derivation. Diagnosed via `cs_label_diff.py cached_constants` showing alternating shared / PS-only runs in cached_constants insertion order, then OCaml partition-counts instrumentation confirming `total=34 constant_part=0 non_constant_part=34` (mpv=1, not 2).
- `wrap_main_add_one_return_circuit` (was +8103) — `WrapMainAddOneReturn.purs` `Slots2 0 0 → NoSlots` (mpv=2 → mpv=0, matching OCaml's `Max_proofs_verified.n = N0 = 0` for Add_one_return) + deterministic step VK + `domainLog2s: 13 → 9` (was confusing wrap-circuit domain with step-circuit domain) + lagrange lookup log2 13→9 in test setup. Required relaxing `deriveStepVKFromCompiled`'s `Add 1 lenPred len` constraint so it accepts `len = 0`.

Partial progress (row delta closed but coeffs still diverge):

- `wrap_main_tree_proof_return_circuit` (was −14): row delta 0 via `domainLog2s 13 → 15` + lagrange log2 → 15 + deterministic step VK (commit `642766e4`). Blocked on step_main_tree_proof_return_circuit's −25 (FOP ft_eval0 divergence) — once step TPR converges, the deterministic VK derivation will produce values matching OC.
- `wrap_main_two_phase_chain_circuit` (was +4088): row delta 0 via `Slots2 0 1 → Slots1 1` (commit `307293f3`). cached_constants 9=9 byte-identical. Coefficients diverge on dummy VK — needs `compileStepMainTwoPhaseChain` (currently nonexistent) compiling both make_zero and increment rules' step CSs to derive their VKs.

The +4000-gate `wrap_main_*` cluster is likely a single shared bug.
The smaller deltas are individual emission divergences. Recommended
order: convergence in delta-magnitude order, smallest first.

## Workflow

**Input:** a single fixture name `F` (e.g.
`step_main_simple_chain_n2_circuit`).

**Termination:** `F` matches OCaml byte-for-byte AND every previously
passing circuit-diff test still passes.

### Invariants (guard rails — never violate)

1. **No OCaml edits.** Only `packages/*` PS code may change. The
   `mina/` submodule is a read-only reference. The fixtures under
   `packages/pickles-circuit-diffs/circuits/ocaml/` are
   production-derived; touching them invalidates the convergence.

2. **Every PS edit requires a "blast-radius" memo before commit.**
   List every currently-passing circuit-diff test whose PS code path
   includes the edited region, and explain *why* each one does not
   exhibit the same divergence (different inputs, dead branch,
   type-app pinning, etc.). If you can't explain one, the fix is
   wrong — investigate that test instead.

3. **Every iteration must move the first-divergent-index FORWARD.**
   If it doesn't, revert and re-hypothesize. Pushing the divergence
   "up and out" is the only valid trajectory.

### Two passes

- **Pass 1: kind alignment.** Compare gate kinds only (`Generic`,
  `Poseidon`, `CompleteAdd`, etc.). Done when no kind diff exists at
  any index.
- **Pass 2: coefficient + permutation alignment.** Same kind sequence
  already; now compare coeffs and wires. Done when fixture
  byte-matches.

## Per-iteration loop (same shape both passes)

### Step 1 — Snapshot

```sh
PATH="…" npx spago test -p pickles-circuit-diffs -- --example "F"
```

Read `packages/pickles-circuit-diffs/circuits/results/F.json`.
Compute:

- **Pass 1 metric:** smallest `i` where `ps[i].kind != oc[i].kind`.
- **Pass 2 metric:** smallest `i` where
  `(ps[i].kind, ps[i].coeffs, ps[i].wires) != (oc[i].kind, oc[i].coeffs, oc[i].wires)`.

Call this index `i*`. If `i*` doesn't exist for the active pass,
advance to next pass or terminate.

### Step 2 — Bilateral localization

Extract **both sides' label context** at `i*`:

- **PS:** `ps[i*].context` from the comparison JSON. Walk backward
  until the longest-common-prefix label changes — that delimits the
  PS code block emitting at `i*`.
- **OCaml:** `oc[i*].context` from
  `packages/pickles-circuit-diffs/circuits/ocaml/F_gate_labels.jsonl`.
  Same backward walk.

Form a **block hypothesis** — the smallest PS code region whose label
appears at `i*` but is NOT shared by `i*-1`. That's where the
divergent emission lives.

### Step 3 — Cross-side correspondence

Find the OCaml source at the labels OCaml's context names (typically
file/line strings like
`"src/lib/crypto/pickles/step_verifier.ml:457"`). Read that OCaml
block as the reference. The PS edit must produce the same gate
sequence that block produces.

### Step 4 — Diagnose the divergence shape

Three exhaustive cases at `i*` for Pass 1:

| case                 | PS at `i*`             | OCaml at `i*`             | hypothesis                                                                |
|----------------------|------------------------|---------------------------|---------------------------------------------------------------------------|
| **A. Extra in PS**   | gate K                 | gate K' (later)           | PS emits something OCaml omits — usually an extra `seal`, `mul_`, or eager allocation |
| **B. Missing in PS** | gate K (later)         | gate K'                   | PS skips an emission OCaml does — often optimization / reordering         |
| **C. Wrong kind**    | gate K                 | gate K' (different prim)  | PS uses a different primitive — different `mul_` vs `square_`, different `addFast` mode, etc. |

For Pass 2 (kinds match), only case D applies: **same kind at `i*`
but different coeffs/wires** → wrong constant, wrong scaling, swapped
operand order, or wrong permutation cycle.

### Step 5 — Blast-radius memo

List every PS file the candidate fix would touch. For each, run:

```sh
grep -rn "<that function/identifier>" packages/pickles-circuit-diffs/test/
grep -rn "<that function/identifier>" packages/*/src/  # callers
```

For each currently-passing fixture whose PS code path includes the
touched region:

- Record the fixture name.
- Identify why the fixture's inputs don't trigger the divergent
  branch (= type-app pinned to the working shape; mode dispatch hits
  a different case; the primitive is shared but called with different
  sizing; etc.).
- If the explanation is "the test was matching the synthetic dump
  that hid the divergence" — **STOP**. The fix is real but the test
  guarantee was never real; mark that fixture as "expected to
  fail/change" and proceed.

### Step 6 — Apply fix

Smallest possible PS edit. No reformatting, no refactor, no
abstraction. If the fix needs a new primitive variant, add it as a
**new** exported function — don't change the existing one (keeps
blast radius zero on already-passing tests).

### Step 7 — Verify

```sh
PATH="…" npx spago build -p pickles-circuit-diffs   # type-check
PATH="…" npx spago test -p pickles-circuit-diffs    # full suite
```

Three checks:

1. **`F`'s `i*` advanced strictly forward.** Compare new `i*` to the
   iteration-start `i*`. If equal or smaller → revert via
   `git checkout`, return to step 4 with a different hypothesis.
2. **Previously-passing tests in the blast-radius memo still pass.**
   If any regressed → revert. The memo's "why this test doesn't see
   the bug" reasoning was wrong; either the fix is wrong or the
   regressed test was matching the same bug for a different reason.
3. **No new test failures outside `F` and the memo.** If yes → the
   change has a wider blast radius than the memo predicted; revert.

If all three checks pass → commit:

```
<fixture> <pass>.iter <n>: <one-line fix description>

i* advanced from <old> to <new>.

Blast radius (passing tests still passing):
- <fixture A>: <why not affected>
- <fixture B>: <why not affected>
…
```

### Step 8 — Repeat

Go back to Step 1 with the new state.

## Pass transition

When Step 1's Pass 1 metric returns "no kind diffs":

1. Re-run the full suite once more to confirm.
2. Update memory with: `"Pass 1 done for F at commit <hash>. Kinds
   aligned; entering Pass 2."`
3. Switch the metric to Pass 2 and continue from Step 1.

## Termination

When Step 1's Pass 2 metric returns "no diffs":

1. Final full-suite run. If all passing tests still pass and `F` now
   matches → fixture converged.
2. Memory update: `"F byte-identical at commit <hash> after <n>
   iterations across both passes."`
3. Move on to the next fixture (smallest delta first, per the
   prioritization above).

## Scope discipline

- **Don't conflate fixtures.** One fixture per iteration loop. If a
  fix for `F` happens to converge another fixture as a side effect,
  note it in the commit but don't change the active target until `F`
  is done.
- **Don't speculate on multiple `i*` at once.** Only the lowest.
  Higher-index divergences may be symptoms of the lowest one and
  disappear on their own.
- **Memory entry per pass completion**, not per iteration. Iterations
  live in the commit log only.

## When stuck

- **First response when out of ideas: ADD MORE LABELS, on BOTH sides.**
  If the bilateral localization in Step 2 yields a label scope that's
  too coarse to pin down the divergent emission (e.g. a 30-row block
  that contains a single +1 you can't explain), the answer is almost
  never "stare harder at the source" — it is "narrow the labels until
  the divergence localizes to a single emission site on each side".
  Add `with_label "<descriptive name>"` around the suspect OCaml
  region and a matching `label "<same name>"` around the PS region,
  regenerate the OCaml fixture (`tools/regen_top_level_fixtures.sh`),
  re-run the PS test, and re-inspect with `tools/cs_label_diff.py`.
  Iterate label-density until each side reports the divergence inside
  a label whose body is small enough to read in one glance. The
  step_main_simple_chain_n2 +1 was unblocked by labels around
  `Pseudo.Domain.to_domain.vanishing_polynomial`'s squaring loop;
  `bp_assert_iter_<i>_if` / `_eq` labels around the bp_assert region
  proved decisively that OC's `Field.if_` was emitting zero gates per
  iteration. Both findings would have been guesses without the labels.
- If two consecutive iterations both fail Step 7 check 1 (`i*`
  doesn't advance), the block hypothesis is wrong. Add labels to
  widen the bilateral localization, then re-run.
- If the candidate fix requires touching a primitive (e.g.,
  `Snarky.Circuit.Kimchi.EndoMul.endo`) AND the blast-radius memo
  can't explain why other tests don't see it, the bug is in the
  primitive itself — but the existing tests were comparing against a
  synthetic dump that *also had* the bug. Surface this finding to the
  human before proceeding (echo of the M9 iter D situation).

## Interacting with the OCaml side

**Default to merlin/LSP, not naive file reads.** The `mina/` submodule
is large and many module paths route through functor applications that
are invisible without type resolution. Reading the source as text will
mislead you about which `Field.t`, which `Impl`, which functor
instantiation is in scope at a given line. Use the LSP tooling instead
— we are already in the nix shell when this loop runs.

Order of preference:

1. **`tools/merlin_type.sh <file> <line> <col>`** — first stop for any
   "what is the type of this expression here?" question. Use this
   before opening the file in Read; it tells you which field/curve is
   live and which functor instantiation supplies the operation.
2. **`mcp__ocamllsp__hover` / `mcp__ocamllsp__definition` /
   `mcp__ocamllsp__references`** — for navigation. `definition` jumps
   through `include`/functor to the real source. `references` finds
   every call site of an identifier across the submodule. Both are
   far more reliable than `grep` for OCaml because they understand
   scope.
3. **`mcp__ocamllsp__diagnostics`** — verify a file builds cleanly
   after edits. Use this as the inner loop when adding labels to
   OCaml; it surfaces type errors faster than `dune build`.
4. **Direct `Read` on `.ml` / `.mli`** — only after merlin has located
   the precise file and line, OR when you need to see the full body
   of a function whose signature merlin has already given you. Never
   open an unfamiliar OCaml file with Read as your first step.

**Why this matters for the convergence loop**: the labels on both
sides have to name the *same logical region of the circuit*. If you
guess the OCaml emission site from naive file reading, you frequently
end up labeling the wrong functor instantiation (e.g. labeling
`Field.Checked.equal` in the wrong `Impl`) and the OC fixture comes
back with no rows under your new label. Merlin tells you exactly
which `Impl` is in scope before you place the `with_label`, so the
first regeneration produces useful data.

## Tooling reference

- **Diagnostic dumps:**
  - `KIMCHI_STEP_CS_DUMP=/tmp/ps_step_cs_%c.json` (PS step CS)
  - `KIMCHI_WRAP_CS_DUMP=/tmp/ps_wrap_cs_%c.json` (PS wrap CS)
  - `KIMCHI_STEP_LABELS_DUMP=/tmp/ps_step_labels_%c.txt` (PS row→label)
  - `PICKLES_STEP_CS_DUMP=/tmp/ocaml_step_%c` and
    `PICKLES_WRAP_CS_DUMP=/tmp/ocaml_wrap_%c` (OCaml side, for
    spot-checking `tools/regen_top_level_fixtures.sh`'s output).
- **Comparison output:** `packages/pickles-circuit-diffs/circuits/results/<F>.json`
  has both PS and OCaml gates side-by-side after a test run.
- **Manifest summary:** `packages/pickles-circuit-diffs/circuits/results/manifest.jsonl`
  lists `match` / `mismatch` per fixture.

### `tools/cs_label_diff.py` — CS label diff CLI

A subcommand-driven explorer over the comparison JSON + OCaml gate-label
fixture. This is the primary inspection interface for every step of the
loop after Step 1. The script auto-resolves three files from the
fixture name:

- `packages/pickles-circuit-diffs/circuits/results/<F>.json` (PS+OC gates)
- `packages/pickles-circuit-diffs/circuits/ocaml/<F>_gate_labels.jsonl` (per-row OC label stack)
- `packages/pickles-circuit-diffs/circuits/ocaml/<F>_labels.jsonl` (per-constraint OC events)

```sh
python3 tools/cs_label_diff.py FIXTURE SUBCOMMAND [ARGS]
```

`FIXTURE` is the bare name (no extension), e.g.
`step_main_simple_chain_n2_circuit`.

#### Step 1 (snapshot): `totals`

```sh
python3 tools/cs_label_diff.py F totals
```

Prints row counts (PS / OC / delta) and a per-kind breakdown
(`Generic`, `Poseidon`, `CompleteAdd`, …). The delta-by-kind table
localizes which gate kind is over- or under-emitting before you even
open the JSON. Run this after every iteration to confirm direction.

#### Steps 2 + 4 (localize divergence): `find_shift` and `generic_stream_diff`

`find_shift [START [LIMIT]] [--coeffs]` — walks PS and OC in lockstep
and reports the FIRST structural shift. Default compares gate **kind**
only (Pass 1 metric); add `--coeffs` to also flag content diffs
(kinds align, coeffs differ — Pass 2 metric). For Generic kinds it
performs **half-level alignment**: Generic is the only gate that packs
2 halves per row, so a single extra emission upstream shifts subsequent
half-pairings even though kinds keep matching. Distinguishes:

- half-level shift (Generic packing offset)
- row-level insertion (non-Generic kind diff)
- content diff (kinds align, coeffs differ)

`generic_stream_diff [--kind-only] [LO [HI]]` — walks the **entire**
Generic-half emission stream in parallel and reports EVERY structural
insertion/deletion, with running cumulative balance. Each event prints
which side is ahead, the coeffs of the extra half, and the row's label
context. With `--kind-only` it skips pure coefficient diffs (different
constants in the same gate kind shape) — what you want during Pass 1.

Use them together: `find_shift` for the first divergence to drive a
single iteration; `generic_stream_diff` to see how the imbalance
accumulates across the whole circuit (e.g. "+2 PS extras both inside
`domain-vanishing-poly`" → per-FOP constant offset, fixable upstream
in one place).

#### Step 2 (bilateral localization): `ps_label`, `oc_label`, `pair_count`

`ps_label LABEL` / `oc_label LABEL` — print every row whose context
contains LABEL. Use to enumerate the rows belonging to a hypothesised
emission block on each side.

`pair_count [LABEL]` — per top-level-context-prefix row counts (PS vs
OC). When the suite is broadly aligned, this surfaces which top-level
scopes carry the delta. With LABEL it filters to rows tagged with that
label.

`seals [LO HI]` — rows tagged with any 'seal' label. Sealing is one of
the most common sources of +1/-1 emission divergence — use this to
quickly enumerate seal sites near a suspected divergence.

`cached_constants [--depth N] [--limit N] [--samples K] [--field fp|fq] [--side ps|oc|both]`
— compare the PS vs OC cached_constants tables. Each entry is a
constant value that was materialized into a Variable via an
`assert_equal_constant` Generic gate. Both sides ship a
`<F>_cached_constants.json` (OC dump) and the comparison JSON's
`purescript.cachedConstants` field (PS dump). The handler:

  1. Canonicalizes every value modulo the field (Fp for `step_main_*`,
     Fq for `wrap_main_*`; auto-detected from fixture name).
  2. Reports totals and the set diff (PS-only / OC-only / shared).
  3. For each extra value, scans Generic gates for the
     `assert_equal_constant` half-pattern (`[cl≠0, 0, 0, 0, cc≠0]` →
     value = `-cc/cl mod field`) and bins the matched rows by their
     label-prefix at depth `--depth`.

Read this BEFORE staring at row coefficients — a delta in cached
constants is the cleanest possible signal for "PS materialized a
constant where OC kept it algebraic" or "OC pre-summed a chain where
PS folds it in-circuit". A typical wrap_main_circuit run shows ~140
PS-extras concentrated in `public-input-commit > add_fast`, which
isolates the divergence to one block before any per-row inspection.

#### Step 4 (diagnose): `rows`, `gate_kinds`, `trace_var`

`rows LO HI` — side-by-side dump of PS vs OC rows in [LO, HI]. Prints
kind, coeffs (both halves for Generic), and the tail of each row's
label context. The default first stop after `find_shift` returns an
index.

`gate_kinds LO HI` — kind histogram inside [LO, HI]. Cheaper than
`rows` when you want a count rather than full coeffs. Note: same
total halves on both sides means same emission count, NOT "aligned"
— for alignment use `find_shift` / `generic_stream_diff`.

`trace_var ROW COL [--side ps|oc]` — walks the wire equivalence cycle
from the given (row, col). Useful in Pass 2 when kinds and coeffs
match but wires don't — follow each side's cycle to compare topology
and find where the variable identities diverge.

#### Conventions

- Default side is `ps` for `ps_label`, `oc` for `oc_label`. Use
  `--side ps|oc` where the command supports it (`trace_var`).
- Generic emission stream order: per row, R-half first then L-half.
  This mirrors OCaml's `pending_generic_gate` queue — R is the half
  emitted earlier (queued), L is the later half that closes the row.
- A cumulative `+N` on PS-side from `generic_stream_diff` means PS has
  N more Generic halves than OC. Halves come in pairs, so +2 halves
  typically equals +1 row delta in `totals`.

#### When the tool gives a false positive

Every shift it reports has a concrete reason. If a reported shift
doesn't survive Step 7's "i* advanced strictly forward" check, the
likely causes are:

- The two halves at the divergent row encode the **same constraint**
  with negated coefficients (e.g. PS Square `[0,0,-1,1,0]` vs OC R1CS
  `[0,0,1,-1,0]` — the kimchi backend emits different sign conventions
  for `assert_square` vs `assert_r1cs`). `--kind-only` already
  collapses these by shape (zero/nonzero pattern).
- A primitive choice difference upstream (PS `square_` vs OC's local
  `let square x = x * x in` Mul) puts the extra half in a different
  context than `find_shift`'s top match. Cross-check with
  `generic_stream_diff` and inspect ALL reported events — the per-FOP
  pattern usually surfaces.
