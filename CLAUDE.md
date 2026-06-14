# Snarky

PureScript zero-knowledge circuit library with a Rust cryptography backend.

## Prerequisites

- Node.js 23
- Rust stable toolchain

## Project Initialization

```bash
# Install dependencies and build the kimchi-napi native binding
npm install

# Download SRS files (required for snarky-kimchi and pickles tests)
make fetch-srs

# Generate linearization code (required to build pickles)
make gen-linearization
```

## Build & Test

```bash
# Build everything
npx spago build

# Type-check only (no JS codegen) — fast compiler feedback
# Use this routinely after edits instead of full builds
npx purs compile -g corefn $(npx spago sources -p <package> 2>/dev/null) --json-errors

# Type-check a package including its tests (exclude other packages' test files)
npx purs compile -g corefn $(npx spago sources -p <package> 2>/dev/null | grep -v '/test/') packages/<package>/test/**/*.purs --json-errors

# Test a specific package
npx spago test -p snarky-kimchi

# Test with pattern matching (run only tests matching string)
npx spago test -p snarky-kimchi -- --example "VarBaseMul"

# Build with strict checking (warnings as errors, clean up spago.yaml)
npx spago build --pedantic-packages --strict
```

## Formatting & Linting

```bash
# Format and lint everything
make lint

# Or individually:
npx purs-tidy format-in-place 'packages/*/src/**/*.purs' 'packages/*/test/**/*.purs'
cargo fmt --all
cargo clippy --workspace --all-targets -- -D warnings
```

## Documentation is Local

**PureScript libraries** — All dependencies have full source in `.spago/p/`. When uncertain about a function, look it up:
```
.spago/p/prelude-7.0.0/src/...
.spago/p/transformers-6.1.0/src/...
```

**Spago documentation** — Spago is installed as an npm dev dependency. Its README has extensive documentation:
```
node_modules/spago/README.md
```

**Project conventions** — See `.claude/skills/project-developer-guide/` for testing patterns, FFI conventions, and other project-specific practices.

## Project Structure

### Crypto Backend
- **kimchi-napi** — Rust napi-rs crate exposing upstream proof-systems (kimchi/arkworks) as the `kimchi-napi` node module

### Core
- **snarky** — Circuit-building DSL
- **curves** — Prime field and elliptic curve types/classes
- **sized-vector** — Type-level sized vectors

### Backends
- **snarky-kimchi** — Kimchi proving system backend (Pasta curves)
- **snarky-bulletproofs** — Bulletproofs backend (Pasta curves)
- **snarky-groth16** — Groth16 backend (BN254)

### Crypto Primitives
- **poseidon** — Poseidon hash function
- **random-oracle** — Random oracle / sponge construction
- **schnorr** — Schnorr signatures

### Higher-Level
- **pickles** — Pickles recursive proof system
- **merkle-tree** — Merkle tree circuits

### Infrastructure
- **snarky-test-utils** — Testing utilities for circuits
- **pickles-codegen** — Code generation for pickles linearization

### Example
- **example** — A block-pipeline simulation: the `example` library
  (`packages/example/src`, a root-workspace package) + the application
  frontends in `packages/example/app/{terminal,web}` (a nested
  purs-backend-es workspace → `app/output-es/`). Runs natively or, in the
  browser, over the wasm backend.

## Example app in the browser

`packages/example/app/web` is a Vite + react-basic app over the shared
`app/output-es` build. Proving is synchronous, so it always runs in a **Web
Worker** over the wasm backend; the wasm rayon pool needs `SharedArrayBuffer`,
which needs the page cross-origin isolated — `vite.config.mjs` sends COOP/COEP
(and `public/coi-serviceworker.js` / `public/_headers` cover deployed hosts).
Three pages (one vite multi-page build):

- **Full pipeline** (`/`, `Snarky.Example.Web.Engine`) — the whole one-block
  flow in-browser: SRS + compile, genesis, block, base + merge proofs, verify.
- **Privacy split** (`/private.html`, `Snarky.Example.WebBase`) — the client
  proves each transaction's BASE proof **locally** (private witnesses stay on
  device), then POSTs only proofs + public ledger statements to a native merge
  server (`web/merge-server.mjs` → `Snarky.Example.MergeServer`, `POST /merge`
  proxied to `:8099` by vite) that reduces them to a verified block root. The
  base proof is the privacy boundary; merges only touch public data, so an
  untrusted server can do them. Cross-backend parity holds (VK is a pure
  function of circuit + SRS). Shared merge-tree primitives in
  `Snarky.Example.Merge`; proofs serialize via `Snarky.Example.Snark.LeafCodec`.
- **Serverless P2P mesh** (`/p2p.html`, `Snarky.Example.P2P.*`) — the pipeline
  split across a **decentralized WebRTC mesh** of browsers on the same static
  site (no server). A peer is **base** (generates its OWN block from private
  transactions and proves that block's base proofs) or **merge** (proves ready
  merge slots of any block) — exclusive roles. It is **multi-block**: each base
  prover owns a block (keyed by its root content-address), so N base provers
  prove N blocks in parallel with merge provers helping all. **No coordinator**:
  peers derive each block's merge DAG from its public leaf statements and gossip
  a globally content-addressed job-board (`Have`/`Claim`/`Request`/`Deliver`,
  keyed by `stmtKey`), self-assigning the lowest ready node; duplicate work is
  idempotent and **trustless** (every received proof is `verifyBatch`'d before
  being merged on). Proving is **manual/stepped** ("prove next" → one proof);
  the work-trees label each node with the id of the peer that proved it. The
  prover runs in a worker RPC service (`Snarky.Example.P2P.ProverService`); the
  main thread owns the transport + gossip state machine
  (`Snarky.Example.P2P.Node`) + the SVG. Transports are pluggable
  (`Snarky.Example.P2P.Transport`, `t=` URL hash): `bc` (BroadcastChannel,
  same-browser), `manual` (copy-paste SDP), `trystero` (WebRTC over public Nostr
  relays). Proofs cross peers as `String` wires (never a witness) and cache in
  IndexedDB by `stmtKey`. A **headless browser in merge mode replaces an HTTP
  merge server** (`tools/run_p2p_merge_peer.sh`). Base proving is single-owner
  per block (witnesses are never shared). Running several provers on one machine
  wants `#threads=N` so the wasm compiles don't thrash one CPU.

Launchers: `tools/run_simulation{,_web,_private,_p2p}.sh`; multi-config mesh
tests: `node tools/p2p_mesh_test.mjs <roles> [threads]` (e.g.
`base,base,merge`). The wasm shared-memory cap is sized to ~2.5 GiB
(`kimchi-napi/package.json` `maximumMemory`) so the browser doesn't OOM across
reloads; determinism caveat: the browser uses OsRng (no
`KIMCHI_DETERMINISTIC_SEED`).
