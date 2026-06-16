# example web frontend

The browser frontend for the example simulation: a **P2P proving app**. One
**coordinator** generates a block and runs the one-block pipeline (SRS, circuit
compile, base + merge proofs, root verification) over a *dynamic* worker pool;
**worker peers** join to parallelize the proving. The coordinator's pool always
includes its own in-process prover, so a lone coordinator with no peers proves
the whole block itself — there's no separate single-machine app.

The UI is react-basic (`src/P2P/Main.purs`): a channel name + two buttons
(**Start experiment** = coordinator, **Join as worker** = prover) and a peer
table. The only JS→PS call is `main()`; everything else crosses via `foreign
import` (`src/P2P/Main.js`), and the transport tier stays internal JS.

## Run

One-time prerequisite — build the wasm backend:

```
npm run build:wasm -w kimchi-napi
```

Then, from `packages/example/` (or via `tools/run_p2p_pool.sh`):

```
npm run p2p       # dev: vite dev server (COOP/COEP set, --host) → /index.html
npm run bundle    # prod: optimized bundle -> web/dist/
npm run preview   # prod: serve the built bundle
```

Cross-origin isolation (COOP `same-origin` + COEP `require-corp`) is required for
the SharedArrayBuffer-backed rayon thread pool; the dev server sets both, and any
production host must do the same (`p2p.js` falls back to a coi-serviceworker on
hosts that can't, e.g. GitHub Pages).

## Using it

Open `/index.html`, enter a channel name, then on one machine click **Start
experiment** and on the others **Join as worker** (same channel). The
coordinator's pool is dynamic — it starts immediately and uses whatever workers
join (add more anytime), so there's no peer count to enter.

- A lone coordinator proves the block itself (its in-process worker).
- The default transport is **Trystero** (serverless WebRTC over public Nostr
  relays) for cross-machine use; append `#t=bc` for same-browser tabs.

The pieces:

- `src/P2P/Main.purs` — the react-basic UI + the transport↔worker relay.
- `src/P2P/Worker.purs` — the prover worker's PS entry (`main`): runs the
  coordinator or a worker peer.
- `src/P2P/Backend.purs` — `p2pSnarkBackend` / `runCoordinator`: a `SnarkBackend`
  over a `Dynamic` pool (first worker = the coordinator's in-process prover, the
  rest = remote peers); reuses the `runPool` reliability (timeout → reassign,
  at-most-once). Tracks the peer table.
- `src/P2P/WorkerPeer.purs` — `runWorkerPeer`: compile once, prove each `Assign`.
- `src/P2P/Protocol.purs` — the Join/Assign/Result/Reject dispatch messages.
- `src/P2P/Transport.purs` + `p2p-transport-*.js` / `p2p-rtc.js` / `p2p-bridge.js`
  — the transport tier (from #148): BroadcastChannel, Trystero (WebRTC), manual
  SDP, plus the worker-side bridge.

The transport runs on the **main thread** (it stays responsive while the worker
proves, and WebRTC's `RTCPeerConnection` isn't constructable in a Worker); it's
bridged into the prover worker over `postMessage` (`p2p-bridge.js`), so the
PureScript is transport-host-agnostic.

## Headless tests

From the repo root:

```
tools/run_p2p_pool.sh --test 2     # 1 coordinator + 2 peers over BroadcastChannel
tools/run_p2p_pool.sh --webrtc     # 1 coordinator + 1 peer over a REAL WebRTC
                                   #   data channel (manual SDP, harness-driven)
```

Trystero depends on public Nostr relays, so it's human-tested cross-machine
rather than part of these deterministic checks.
