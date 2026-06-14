# Plan: decouple from `mina` + thread the blinder RNG

Status: planned (not started). Target: a branch off `main`, separate from the
`p2p-mesh` feature PR.

## Why

`main` (and our `wasmy`) pull in the entire **`mina` OCaml monorepo** essentially
only to get the proof-systems **Rust** crates at `mina/src/lib/crypto/proof-systems/`.
Vendoring proof-systems as its own top-level submodule lets us drop the heavy
`mina` clone.

Coupled to this is **determinism**. The deterministic blinder RNG — the thing
that makes our PureScript proofs byte-identical to mina's OCaml proofs (the
"circuits/proofs correspond exactly" guarantee) — lives **inside** proof-systems,
on both the napi side and the kimchi-stubs (OCaml FFI) side. It is currently
driven by an environment variable, so it is native-only and not controllable
from the browser. When we own proof-systems standalone we must keep those two
RNGs in sync; while we're there we should thread the seed through the stack so
the wasm/app path can (a) run the same byte-identity checks the native path does
and (b) switch to real randomness for production zero-knowledge.

## Current state (verified in the code, correcting an earlier note)

The blinder RNG is **already deterministic on every backend** — it is NOT OsRng:

- `proof-systems/kimchi-napi/src/proof.rs:819` passes `&mut make_rng()` to
  `ProverProof::create_recursive`.
- `make_rng()` (`kimchi-napi/src/deterministic_rng.rs`) builds a `ChaCha20Rng`
  seeded from `KIMCHI_DETERMINISTIC_SEED`, defaulting to **`42`**; it never falls
  back to OsRng (unparseable env value = fatal).
- The OCaml side has a **sister module** `kimchi-stubs/src/deterministic_rng.rs`
  with the same `DEFAULT_SEED = 42`, kept in lockstep — so napi-side and
  OCaml-side draw identical blinder bytes and proofs are byte-reproducible across
  PureScript ⟷ mina.

In the browser, `std::env::var` returns `Err` (no env) → seed `42` →
**the wasm proofs are already deterministic and byte-identical** to native and to
mina. (My earlier "the wasm build uses OsRng / browser runs aren't byte-identical"
described the *old kimchi-wasm adapter*; the napi-wasip1 build does not behave
that way. The "self-consistent but not byte-identical run" caveat in the example
docs is about **block generation** — `randomSampleOne`/`Math.random` in
`genGenesisLedger`/`genValidSignedTransaction` picking different transactions each
run — not the prover. Fix that caveat in CLAUDE.md.)

`getrandom` already carries the `js` feature (`Cargo.toml`), so OsRng *would* work
in wasm if we chose to use it.

So determinism exists; the real gaps are about **control**:

1. The seed is env-var-driven → unreachable from the browser, stuck on `42`.
2. A fixed seed means predictable blinders → **not real zero-knowledge**. Fine for
   byte-identity tests, a privacy hole for production. There is currently no way
   to say "secure randomness here, fixed seed there".
3. The byte-identity / transcript-diff verification is native-only precisely
   because the seed isn't threadable on the wasm path.

## Part A — vendor proof-systems, drop `mina`

1. Add `proof-systems` as a **top-level submodule** = the l-adic standalone fork
   (the same crates extracted out of mina, plus the wasm-support patches). Our
   `wasmy` already pins `21e730a7d` (mina's proof-systems commit `92bd6a7e` + the
   wasm patches); re-confirm it tracks whatever commit main's mina is currently
   pinned at so the crates stay byte-identical.
2. Repoint the four crate paths in the **root `Cargo.toml`**:
   `mina/src/lib/crypto/proof-systems/*` → `proof-systems/*`
   (`kimchi`, `mina-curves`, `mina-poseidon`, `poly-commitment`).
3. Repoint `PS_DIR` in `packages/kimchi-napi/build.sh` and `build-wasm.sh`.
4. Repoint CI SRS-cache key paths in `.github/workflows/test.yml`
   (`mina/src/lib/crypto/proof-systems/srs/*.srs`) and `make fetch-srs`.
5. Drop `mina` from `.gitmodules` — **pending** the `.claude/skills/` check: those
   skills reference mina's OCaml pickles/kimchi-stubs for analysis/translation.
   They are dev-only tooling; decide whether to keep `mina` solely for them, point
   them at the standalone `proof-systems` (which also has kimchi-stubs), or drop
   them.

Caveats: keep the standalone fork in sync with mina's pinned proof-systems
commit; verify SRS files live under `proof-systems/srs/` in the fork; confirm no
other build/test path reads from `mina/`.

## Part B — extract the blinder RNG from env-global to an app-settable control

Thread an explicit RNG choice app → deps → prover, working in native **and** wasm:

- **proof-systems / kimchi-napi (Rust):** add a napi setter, e.g.
  `caml_set_blinder_rng(seed: Option<…>)`, storing into a thread-safe cell
  (`OnceLock`/`Mutex`/thread-local). `make_rng()` consults the cell first, then
  the env var, then the default. `Some(seed)` → `ChaCha20Rng` (deterministic);
  `None` → **OsRng** (re-introduced as an *explicit* secure mode; works in wasm
  via getrandom-js). Mirror the same setter in **kimchi-stubs** so the OCaml side
  stays in lockstep and the byte-identity tests still pass.
- **snarky-kimchi (PureScript FFI):** expose
  `setBlinderRng :: BlinderRng -> Effect Unit` where
  `BlinderRng = Deterministic Seed | Secure`, wrapping the napi export. This is
  the "thread it through the dependencies" seam.
- **pickles:** proving is sequential, so set-before-prove is sufficient — no
  signature change. Thread a seed per prove-call only if we want it fully
  explicit.
- **example / app (PureScript + JS):** a `provingRng` config set once at startup —
  `Secure` for real privacy, `Deterministic seed` for verification (exposed as a
  browser URL flag). The P2P/privacy pages set it before any prove.

Policy decision to make: the default when nothing is set. Either keep `42`
(back-compat: existing byte-identity tests rely on it) or default to `Secure` with
deterministic as an explicit opt-in (safer). Recommend: keep `42` as the test
default but make `Secure` reachable and use it in any "production" app path.

Payoff: secure production randomness becomes reachable from the browser, AND the
wasm/browser path can run the same byte-identity checks the native path does
(closing the "transcript-diff is native-only" gap).

## Part C — (adjacent) seed the example block generator

For fully reproducible *runs* (not just proofs), the example's block generation
uses `randomSampleOne` (`Math.random`) in `Simulation/{Genesis,Block}.purs`.
Replace with a seeded `Test.QuickCheck.Gen.evalGen`/`runGen` driven by an app
seed, so a given (RNG-seed, block-seed) reproduces a run end-to-end. This is
app-level randomness, distinct from the prover RNG — do it only if reproducible
demo runs are wanted.

## Verification

- Run the existing transcript-diff / witness-parity / byte-identity tests on the
  **wasm** backend (deterministic mode), confirming the wasm port matches mina
  bit-for-bit — currently only done natively.
- In `Secure` mode, assert proofs still *verify* (`verifyBatch`) but are NOT
  reproducible across runs (blinders differ) — i.e. real zero-knowledge restored.
- Native + existing suites unchanged when the default seed stays `42`.

## Open questions / risks

- Does main's `mina` pin still match the l-adic fork's base commit? If mina moved,
  rebase the fork onto the new proof-systems commit before repointing.
- The `.claude/skills` OCaml dependency on `mina` (Part A step 5) — keep, redirect,
  or drop.
- Concurrency: a global blinder-RNG cell is fine because proving is sequential
  here (per-process, one proof at a time). If parallel proving is ever added,
  switch to a per-call seed parameter instead of a global.
- Don't forget the CLAUDE.md correction (the stale OsRng caveat above).
