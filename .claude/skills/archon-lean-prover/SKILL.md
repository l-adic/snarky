---
name: archon-lean-prover
description: Run the Archon autonomous Lean prover (the archon-docker wrapper) to discharge `sorry`s in formal/, then pull the proofs back and verify them. Use when handing sorried Lean proof obligations to the containerized plan→prove→review loop.
---

# Archon Lean prover (archon-docker)

Archon is an autonomous Lean 4 proving loop that runs in a container against a **copy** of
`formal/` (your repo is mounted read-only). It is good for **sorry-discharge where the statements
are already correct and the proofs are mechanical**. It is *not* good where the risk is in the
statement — write and validate those yourself first.

The wrapper lives at `~/code/l-adic/archon-docker/`. **Read its docs before doing anything** — they
are complete, so do NOT reverse-engineer `entrypoint.sh` from first principles (that wasted a lot of
time once):

- `archon-docker/README.md` — the authoritative guide (isolation model, seed, helper, env vars).
- `archon-docker/archon.sh` — helper; the command list is the header comment (lines 3–24).
- `archon-docker/.env.example` — env vars.

## The flow

Run everything from `archon-docker/`. `ARCHON_PROJECT` defaults to `../snarky/formal`.

```bash
cd ~/code/l-adic/archon-docker
./archon.sh doctor                              # verify toolchain/auth/seed
./archon.sh init --harness claude-code --force  # bootstrap NON-interactively (see gotcha)
./archon.sh loop                                # plan→prove→review, dashboard at :8080
```

Then pull the work back (below) and **verify it yourself** — never trust "0 sorries" or an agent's
"complete" self-report.

## Starting a NEW job: reset the state per task, keep the build cache

`.archon/` is **one task's session state** — `PROGRESS.md`, `TO_USER.md` ("Project COMPLETE"),
`PROJECT_STATUS.md`'s knowledge base, `task_done.md`, iteration numbering. Reusing it for a new
task contaminates the planner: it burns its cycle reconciling the old task's COMPLETE state with
the new sorries, and stale notices can trip stage detection later. **Do NOT surgically edit the
old state** (e.g. `sed` the stage line in `PROGRESS.md`) — that leaves everything else stale.
The per-task flow, verified end to end:

```bash
docker stop $(docker ps -q --filter ancestor=archon-lean:local)  # end the old loop
# 1. write the NEW .archon-seed/{USER_HINTS.md,archon-protected.yaml}; commit the scaffold
# 2. drop the old task state + the seed marker, keeping the copy and .lake:
docker compose run --rm -T --no-deps --entrypoint sh archon -c \
  "rm -rf /work/project/.archon && rm -f /work/.seeded"
./archon.sh doctor                               # re-seed source + seed files (rsync skips .lake)
./archon.sh init --harness claude-code --force   # FRESH bootstrap; auto-detects stage
./archon.sh loop
```

`init` is merge-based: with declarations + sorries present it prints
`Stage detection: prover` and advances past `init` itself — no manual stage edit needed.
**Verify fresh state before `loop`:** `.archon/logs/` empty, no `TO_USER.md`, `USER_HINTS.md`
names the new target, sorry count as expected.

**Blueprint/DAG panes** (dashboard) are populated only if the image has `leanblueprint` on PATH
at `init` time (in the image since archon-docker `ad3f507`; before that, init reported
"leanblueprint scaffolding (disabled by options)" — meaning the binary was absent — and the
panes stayed empty on every job). With the scaffold in place, run `./archon.sh dag` before
`loop` to have the blueprint chapters written; `dag` runs on the Claude backend — the
"informal agent" API-key warning in the loop banner concerns a different optional helper.

## Per-project seed: `formal/.archon-seed/` (gitignored)

The container maps these into the work copy on first seed (README has the table):

- `USER_HINTS.md` → `<work>/.archon/USER_HINTS.md` — **the binding task spec**. Write: THE JOB
  (sorry-discharge, not statement edits), the exact target list, a *worked proof template* if you
  have one, hard constraints (no `sorry`/`admit`/`native_decide`/new `axiom`/`set_option linter`),
  and acceptance gates (`lake build Kimchi` 0-sorry, `check_axioms.sh` unchanged).
- `archon-protected.yaml` → freeze list. **Listed = frozen, unlisted = editable.** Freeze
  everything except the files you want Archon to touch (explicit-list pattern — see the git history
  of this file for a worked example that freezes all of kimchi except three modules).
- `references/` → read-only material Archon may consult (e.g. ironwood modules a design mirrors).

## Model — do NOT override

Upstream forces the loop model; `<work>/.archon/config.json` shows `claude-opus-4-8[1m]`, which is
**correct**. Do not try to set `ARCHON_MODEL` to something else — that only causes churn.

## Pull the work back and verify

The work is already on disk in `archon-docker/work/project/` (persistent bind mount). To review and
apply onto `formal/`:

```bash
cd ~/code/l-adic/archon-docker
# full diff of what Archon changed (entrypoint chatter is on stderr; -T keeps stdout clean):
docker compose run --rm -T archon bash -lc \
  "cd /work/project && git --no-pager diff HEAD -- <files>" > /tmp/w.patch

# apply onto the real repo — from the SNARKY REPO ROOT, with --directory=formal:
cd ~/code/l-adic/snarky
git apply --directory=formal /tmp/w.patch
```

**Why `--directory=formal`:** the patch paths are `kimchi/...` (relative to `formal/`), but
`formal/` is a *subdirectory* of the snarky git repo. `git apply` resolves paths from the repo root,
so applying from `cd formal` fails **silently** (`--stat` reports "0 files changed" and nothing
changes). `--directory=formal` (or `./archon.sh apply`, which prepends `$ARCHON_SUBDIR`) fixes it.

Then, from `formal/`, verify — this is the real acceptance, not the sorry count:

```bash
grep -rc sorry kimchi/Kimchi/Verifier/<...>/*.lean          # expect 0
grep -rnE "admit|native_decide|^\s*axiom|set_option[[:space:]]+linter" <files>   # expect none
lake build Kimchi                                            # clean, 0 sorry warnings
bash kimchi/scripts/check_axioms.sh                          # SAME 48-root closure as before
# and #print axioms on the new capstones — expect only [propext, Classical.choice, Quot.sound]
```

## Gotchas (each of these cost real time)

- **`init` is interactive.** Bare `./archon.sh init` prompts for an engine (`[1] Claude Code`
  default) and, under `nohup`, aborts on EOF. Always pass `--harness claude-code --force` (`--force`
  also skips the re-init overwrite prompt). `init --help` lists the flags.
- **Bootstrap files are under `.archon/`, not the project root.** `PROGRESS.md`, `AGENTS.md`,
  `prompts/` land in `work/project/.archon/`. They read as "missing" at root — don't panic. The
  doctor's "3 errors" about them are just the pre-`init` state; `init` clears them.
- **Seed the work copy AFTER committing your scaffold.** The seed rsyncs the working tree at seed
  time; if you seed before committing/writing the sorried files, Archon works on stale source.
- **Re-sync without re-fetching Mathlib.** The documented refresh (`rm -rf work/*; doctor`)
  re-downloads the multi-GB Mathlib cache. The entrypoint's re-seed rsync **excludes `.lake`**, so
  to refresh source + `.archon-seed` while keeping `work/project/.lake`, remove only the seed
  marker: `docker compose run --rm --no-deps --entrypoint sh archon -c "rm -f /work/.seeded"` then
  `./archon.sh doctor`. Mid-job source refresh only — for a **new task**, also drop `.archon` and
  re-`init` (see "Starting a NEW job" above).
- **Empty re-seed bricked the entrypoint silently (fixed in archon-docker `516e56b`).** On images
  older than that fix: a re-seed with no source changes made the baseline `git commit` exit 1
  ("nothing to commit"), `set -e` killed the entrypoint before `.seeded` was written and before
  `archon` ever ran — every retry printed only the seed lines and exited 1 with no error. Escape:
  `--entrypoint sh … -c "touch /work/.seeded"`, rerun; or rebuild the image (`./archon.sh build`).
- **Never `pkill -f "archon.sh …"`.** The pattern matches your own running shell command and kills
  it (exit 143/144, output lost). Stop containers with `docker stop <cid>` or `docker compose down`;
  find the loop container via `docker ps -q --filter ancestor=archon-lean:local`.
- **Stop the loop when the sorry count hits 0.** It otherwise churns empty iterations (default 10),
  each spawning paid agents, since everything else is frozen. `docker stop $(docker ps -q --filter
  ancestor=archon-lean:local)`.
- **Root-owned files.** `work/` and `out/` are written by the container as root; `./archon.sh chown`
  to reclaim for local editing (reading is fine without it).

## De-risking the handoff (the important discipline)

Before seeding, prove **one representative goal by hand** in the scaffold (e.g. the first bridge of a
family). That validates the statements are true — so Archon gets known-true goals, not conjectures —
and gives it a worked template to copy in `USER_HINTS.md`. A wrong statement is the failure mode
(the model will happily "prove" a weakened one); a proven exemplar prevents it.
