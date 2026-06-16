# P2P star worker-pool — implementation plan

**Branch:** `p2p-pool` (from `origin/main`). **Scope:** web application only. This
**replaces** the wasm-thread worker pool (PoC on branch `wasm-pool`, PR #151 +
follow-ups), which proved *less* efficient than one full-core prover per machine
("do it yourself"). We keep the wasm-pool branch only as a source of ideas/files
— it has little merge value of its own.

Reference branches:
- `wasm-pool` — the worker-pool PoC (Engine `runWith`, `Prover.buildProver`,
  browser web-worker backend). Cherry-pick 2 files from here.
- `p2p-mesh` — PR #148, the p2p/WebRTC infrastructure (no worker pool; a
  hand-rolled decentralized gossip prover). Pull its **networking tier verbatim**;
  drop its coordination layer.

---

## Goal / topology (locked decisions)

A **star** (hub-and-spoke) over the #148 WebRTC transport:

- **One coordinator** = the block producer. It **proves nothing**: it generates
  the block, farms *every* `WorkItem` (base AND merge) to the pool, collects
  results, and verifies the root proof.
- **N worker peers** = each a single full-core wasm prover running `proveItem`
  (handles `Base` and `Merge` identically). Parallelism comes from *N machines
  each at full speed*, not one machine core-splitting across N wasm instances.

Locked with the user:
- **Star, not decentralized pull-mesh.** The coordinator owns assignment; this
  reuses our `runPool` reliability and deletes #148's claim/TTL/gossip.
- **No base/merge distinction.** #148 kept base proofs local (privacy boundary —
  base jobs carry the tx witness). We farm everything; **nothing is private in
  this demo** (a future design problem, explicitly out of scope).
- **One block producer** for the first cut. Multi-coordinator (a shared worker
  set serving several blocks) is a later v2.

---

## Baseline: what's already on `main` (verified)

The swappable-backend architecture landed in #151 and **is on main**:

- `packages/example/src/Snarky/Example/Snark/Pool.purs` — `runPool` (timeout →
  reassign, at-most-once via atomic `claim`, reclaim/respawn dead worker,
  feeder/dispatcher/`free`/`ready` queues). `WorkerBackend { name, spawn :: Aff Worker }`,
  `Worker { id, run :: job -> Aff result, terminate }`.
- `Snark/Worker.purs` — `type SnarkBackend d = Env d -> WorkerBackend (WorkItem d) Proof`;
  `proveItem :: CompiledTx d -> WorkItem d -> Effect Proof` (dispatches `Base`/`Merge`);
  `localSnarkBackend`.
- `Snark/Work.purs` — `WorkItem d = Base (BaseJob d) | Merge MergeJob`, with
  `encodeWorkItem`/`decodeWorkItem` (BOTH base and merge round-trip as strings;
  base witness `Mask d = SparseLedger …` already has `Read/WriteForeign` in
  `packages/merkle-tree/.../Sparse/Mask.purs`). The stale comment at `Work.purs`
  header saying "Base … Mask codec (pending)" is WRONG — fix it.
- `Snark/Manager.purs` — `mkManager`/`startNode` already take
  `backend :: SnarkBackend d`, `poolSize :: Int`, `jobTimeout :: Milliseconds`.
  Pushes base leaves onto the work queue; reactively enqueues merges as children
  land (DAG sequencing handled here). `submitBlock`.
- `Simulation.purs` — `mkSimulation` config record includes `backend`, `poolSize`,
  `jobTimeout`. Builds SRS + compiles the circuit once → `Env`.
- `Pickles/Prove/SerializeProof.purs` (in the **pickles** package) —
  `encodeCompiledProof` / `decodeCompiledProof {pallasSrs,vestaSrs|r} String`.
- Web app (single in-process prover = the "performant single" case):
  `app/web/src/Main.purs` (`Snarky.Example.Web.Main`, React UI, `runApp`),
  `app/web/src/Worker.purs` (`Web.Worker.startEngine`), `Web.Engine`
  (`runSimulation`, `ScanView`, `TxView`), `worker-entry.js`, `main.js`,
  COI plumbing (`public/coi-serviceworker.js`), vite config (kimchi-napi
  wasi-browser alias, COOP/COEP headers).

So the **coordinator pipeline already exists on main**; p2p only injects a new
`SnarkBackend`. `Engine.Depth = 4` (ledger depth).

---

## Provenance — what to pull, from where

| Source | Files / items | How |
|---|---|---|
| **main** (baseline) | pool core, `WorkItem`+codecs, `Manager`/`Simulation` (backend seam), `SerializeProof`, React UI, COI | branch point — untouched |
| **wasm-pool** (cherry-pick) | `packages/example/src/Snarky/Example/Prover.purs` (`buildProver` = worker-peer compute core); the `runWith` backend-parameterization of the engine | `git show wasm-pool:…/Prover.purs`; port `runWith` into main's `Web.Engine` |
| **p2p-mesh #148** (pull verbatim) | `app/web/p2p-rtc.js`, `p2p-transport-{trystero,broadcast,manual}.js`, `p2p.js` (COI gate), `app/web/src/P2P/Transport.purs` + `Transport.js`; `p2p-worker.js` shell; trystero dep + `VITE_METERED_API_KEY` define + `public/_headers`; `tools/p2p_mesh_test.mjs`, `tools/run_p2p_merge_peer.sh` (adapt) | `git checkout p2p-mesh -- <files>` |
| **NEW** | dispatch `Protocol`, `p2pSnarkBackend`, worker-peer loop, coordinator/worker entries, slim boot | write fresh |

**Dropped from #148 (coordination layer the pool replaces — NOT networking):**
`Node.purs` (gossip/claim/TTL/`mayTake`/Have/Request/Deliver), `Dag.purs`,
`Cache.purs`, `LocalDriver.purs`, `ProverService.purs` (split base/merge RPCs),
`ProverClient.purs`, #148's gossip `Protocol.purs`, the gossip role/SDP UI.

`buildProver` (wasm-pool) for reference — the worker-peer compute core:
```purescript
buildProver :: { chain :: String, depth :: Int } -> Effect (String -> Effect String)
buildProver { chain, depth } = reifyType depth (buildProverAt chain)
buildProverAt :: forall d. Reflectable d Int => String -> Proxy d -> Effect (String -> Effect String)
buildProverAt chain _ = do
  config <- mkConfig (chainIdFromTag chain)
  env <- mkEnv @d mempty config
  pure \encoded -> case decodeWorkItem env encoded :: Either _ (WorkItem d) of
    Left err   -> throw ("prover: decodeWorkItem failed: " <> show err)
    Right item -> encodeCompiledProof <$> proveItem env.compiledTx item
```

#148 Transport interface (what every transport implements; pull verbatim):
```
{ myId: string,
  broadcast(msg: string): void,
  sendTo(peer: string, msg: string): void,
  onMessage(handler: (from, msg) => void): void,
  onPeer(handler: (peerId) => void): void }     // JOIN only — see "onPeerLeave gap"
```
`Transport.purs` exposes: `myId`, `broadcast`, `sendTo`, `onMessage`, `onPeer`.
Chunking (proof wires exceed the ~256KB SCTP limit) lives in `p2p-rtc.js`
(`sendChunked`/`recvChunked`, 48KB frames) and is transport-internal: trystero
chunks itself; manual uses `sendChunked`; broadcast is in-process (unlimited).
So the backend sends/receives whole strings and is chunking-agnostic.

---

## New modules (signatures)

### 1. `app/web/src/P2P/Protocol.purs` — dispatch protocol
Replaces #148's 6-variant gossip vocab with a 4-variant dispatch protocol.
```purescript
data Msg
  = Join   { peerId :: String, fingerprint :: String }  -- worker → coord: available
  | Assign { jobId :: String, work :: String }          -- coord → worker: encodeWorkItem
  | Result { jobId :: String, proof :: String }         -- worker → coord: encodeCompiledProof
  | Reject { jobId :: String, reason :: String }        -- worker → coord: verify/decode failed
encodeMsg :: Msg -> String
decodeMsg :: String -> Either MultipleErrors Msg
```
`fingerprint` = build/circuit compatibility check (carry #148's idea); coordinator
ignores a `Join` whose fingerprint ≠ its own.

### 2. `app/web/src/P2P/Backend.purs` — coordinator side
A `SnarkBackend` whose workers are remote peers. Mirrors wasm-pool's
`webWorkerSnarkBackend` but the channel is `transport.sendTo` (not `postMessage`).
```purescript
p2pSnarkBackend :: Transport -> Int -> SnarkBackend Depth
-- \env -> { name: "p2p peer", spawn: dequeue joinQueue }   -- spawn blocks until a Join arrives
-- a remote Worker:
--   id        = peerId
--   run job   = do jobId <- fresh
--                  reply <- AVar.empty ; register pending jobId reply
--                  sendTo transport peerId (encodeMsg (Assign {jobId, work: encodeWorkItem job}))
--                  AVar.take reply        -- Result → decodeCompiledProof env ; Reject → throw
--   terminate = drop peerId from registry
```
Shared state (set up once when the backend is built, before `runPool`):
- `pending :: Ref (Map jobId (AVar (Either String Proof)))` — reply correlation
  (same pattern as `webWorkerSnarkBackend`).
- `joinQueue :: AsyncQueue (Worker (WorkItem Depth) Proof)` — fed by `onPeer` +
  the `Join` handshake; `spawn` dequeues it.
- `transport.onMessage` routes `Result`/`Reject` to the matching AVar by `jobId`.
Decode uses `env.{pallasSrs,vestaSrs}` (already on the `Env`).

### 3. `app/web/src/P2P/WorkerPeer.purs` (+ thin JS entry) — worker side
```purescript
runWorkerPeer :: Transport -> Effect Unit
-- prove <- buildProver { chain, depth: reflect Depth }
-- broadcast Join { peerId: myId, fingerprint }
-- onMessage: Assign {jobId, work} ->
--    try (prove work) >>= case _ of
--      Right proof -> sendTo coord (Result {jobId, proof})
--      Left  err   -> sendTo coord (Reject {jobId, reason: message err})
```
Reuses wasm-pool `Prover.buildProver`/`proveItem` — base & merge identical.

### 4. Engine generalization — port `runWith` into `Web.Engine`
main's `Web.Engine.runSimulation` runs the whole sim in one in-process worker.
Add the backend parameter (the wasm-pool generalization):
```purescript
runWith :: SnarkBackend Depth -> Int -> Milliseconds -> EngineCallbacks -> Effect Unit
runSimulation = runWith localSnarkBackend 1 (Milliseconds …)   -- main's path, unchanged
```
Coordinator calls `runWith (p2pSnarkBackend transport poolSize) poolSize timeout cb`.

### 5. Entries & glue
- `p2p-worker.js` (from #148): keep the wasm-boot / rayon-thread / log-forward
  shell; replace its method set (`seed`/`genBlock`/`proveLeaf`/`merge`/`verify`)
  with one path that drives `runWorkerPeer`.
- `p2p-coordinator.js` (new, small): boot wasm (needed for decode + verify), pick
  transport, `runWith (p2pSnarkBackend …)`, render the tree from the existing
  `ScanView`.
- `p2p.js` COI gate (verbatim) + a slimmed `p2p-boot.js`: role toggle
  (coordinator | worker) + transport picker; strip all gossip UI. Keep manual-SDP
  signaling UI only if we want the 2-peer manual transport for cross-machine demos.
- transports + `p2p-rtc.js` verbatim. vite: trystero dep, `VITE_METERED_API_KEY`
  define, `public/_headers`, kimchi-napi wasi-browser alias (already on main).

---

## Implementation order (each step builds / type-checks)

1. **Branch + networking tier.** (Branch already created.)
   `git checkout p2p-mesh -- app/web/p2p-rtc.js app/web/p2p-transport-*.js
   app/web/p2p.js app/web/src/P2P/Transport.purs app/web/src/P2P/Transport.js`;
   add trystero dep + vite bits + `_headers`. Transports compile standalone.
2. **Worker compute core.** Copy `Prover.purs` from `wasm-pool`. Type-checks
   against main's `Work`/`Worker`.
3. **`Protocol.purs`** (new, standalone).
4. **`Backend.purs`** — `p2pSnarkBackend`. Type-check against `runPool`'s
   `WorkerBackend`/`Worker` (contract is on main).
5. **`WorkerPeer.purs`** + worker entry — `Assign → proveItem → Result`.
6. **Engine `runWith`** generalization + **coordinator entry**.
7. **Slim `p2p-boot.js`** (role + transport) + COI gate.
8. **Milestone A — BroadcastChannel, headless.** Drive coordinator + 2 worker
   contexts in one Chrome (bc transport + the playwright harness used for the
   wasm pool). Proves `Assign`/`Result`, chunking, **timeout→reassign**,
   **reclaim** — before any WebRTC. (Analogue of #148's `LocalDriver` de-risk,
   but exercising the real pool.) Target: `root proof verified`.
9. **Milestone B — Trystero, cross-tab / cross-machine.** Same code, WebRTC;
   verify TURN probe + a full merge tree to `root verified`.
10. **Lint/format/commit** (`make lint`).

Type-check loop (fast):
`npx purs compile -g corefn $(npx spago sources -p example 2>/dev/null) --json-errors`

---

## Deferred refinements (NOT v1; call out, don't block)

- **Dynamic membership.** v1 uses `spawn = dequeue joinQueue`, so `poolSize` means
  "wait for N peers, then go" (launch N workers, set `poolSize = N`). This needs
  **zero change to `runPool`**. Growing/shrinking live (start at 1, add as peers
  join) is a later small change: `WorkerBackend.spawn :: Aff Worker` → a
  membership-aware source, or a pool variant tolerating size-0 + late joins.
- **`onPeerLeave` gap.** The `Transport` interface has `onPeer` (join) but no
  leave hook. v1 reclaims a dead worker via the **job timeout we already have**
  (correct, just not instant — a vanished worker never replies, timeout fires,
  job reassigns). v2 adds one field to `Transport` (trystero exposes
  `room.onPeerLeave` natively; manual via datachannel `onclose`; broadcast via
  heartbeat) → a disconnect rejects the pending reply and drops the peer from the
  free queue immediately.

## Build-time knobs (decide later, not now)
- `poolSize` (= expected worker count for v1).
- Coordinator-also-a-worker: the pool's `free` queue is heterogeneous, so adding
  one in-process worker (`localSnarkBackend`'s worker) alongside the remote ones
  is trivial — but it contradicts "farm everything out", so **off by default**.

## Notes / gotchas
- Coordinator must still compile the circuit (mkSimulation) — needed for
  `verifyBatch` (verifier VK) and proof decode (SRS) — even though it proves
  nothing.
- Star = coordinator is a bandwidth hub + SPOF. Acceptable: it's already special
  (the only peer with the block/witnesses). Noted, not mitigated in v1.
- The proof wire is large (a `MergeJob` embeds two `CompiledProof`s in, one out);
  all of it flows through the coordinator's uplink. Same data #148 moved, but
  star-shaped. Chunking (p2p-rtc.js) handles framing.
- Fix the stale `Work.purs` header comment about the "pending" Mask codec.
