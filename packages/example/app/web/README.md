# example web frontend

Browser frontend for the example simulation: runs the full one-block
pipeline (SRS, circuit compile, base + merge proofs, root verification)
in a Web Worker over the wasm kimchi backend, rendering the scan-state
tree and block transactions with react-basic.

## Run

One-time prerequisite — build the wasm backend:

```
npm run build:wasm -w kimchi-napi
```

Then, from `packages/example/` (or via `tools/run_simulation_web.sh`):

```
npm run dev       # dev: vite dev server (COOP/COEP set) on http://localhost:5173
npm run bundle    # prod: optimized bundle -> web/dist/
npm run preview   # prod: serve the built bundle
```

Cross-origin isolation (COOP `same-origin` + COEP `require-corp`) is
required for the SharedArrayBuffer-backed rayon thread pool; the dev
server sets both, and any production host must do the same.

## P2P star worker-pool (`/p2p.html`)

A second entry distributes the proving across machines. One **coordinator**
(the block producer) proves nothing itself — it generates the block, farms
*every* base and merge job to the connected worker peers, and verifies the
root proof. Each **worker peer** is a single full-core wasm prover answering
the coordinator's assignments. Parallelism comes from N machines each at full
speed, over the #148 WebRTC transport (`trystero`) or, for same-browser tabs,
`BroadcastChannel`.

Open `/p2p.html`, pick a role + transport + session: run one coordinator and
N peers in the same session. The pieces:

- `src/P2P/Protocol.purs` — the Join/Assign/Result/Reject dispatch messages.
- `src/P2P/Backend.purs` — `p2pSnarkBackend` / `runCoordinator`: a `SnarkBackend`
  whose workers are remote peers; reuses the `runPool` reliability (timeout →
  reassign, at-most-once) unchanged.
- `src/P2P/WorkerPeer.purs` — `runWorkerPeer`: compile once, then prove each
  `Assign` (base and merge identically).
- `src/P2P/Transport.purs` + `p2p-transport-*.js` / `p2p-rtc.js` — the transport
  tier (pulled from #148): BroadcastChannel, Trystero (WebRTC), manual SDP.

The transport runs on the **main thread** (it stays responsive while the worker
proves, and WebRTC's `RTCPeerConnection` isn't constructable in a Worker); it is
bridged into the prover worker over `postMessage` (`p2p-bridge.js`). The
PureScript is transport-host-agnostic.

Headless tests — from the repo root:

```
tools/run_p2p_pool.sh --test 2     # Milestone A: 1 coordinator + 2 peers over
                                   # BroadcastChannel, to a verified root
tools/run_p2p_pool.sh --webrtc     # Milestone B: 1 coordinator + 1 peer over a
                                   # REAL WebRTC data channel (manual SDP,
                                   # harness-driven signaling), to a verified root
```

Trystero (serverless WebRTC over public Nostr relays) is the cross-machine
many-peer transport: pick it in the UI and share the session code. It depends on
public relays, so it's human-tested rather than part of the deterministic CI
checks above.
