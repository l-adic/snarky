// FFI for Snarky.Example.Web.P2P.Main. Signatures are dictated by the PS
// `foreign import`s. The transport tier and the worker-spawn module are internal
// app JS reached via the `@webjs` vite alias (app/web/), so this FFI — which is
// compiled into output-es/ — can import them regardless of its own location.
import { mkTransport } from "@webjs/p2p-mk-transport.js";
import { initIce } from "@webjs/p2p-rtc.js";
import { spawnWorker as makeWorker } from "@webjs/p2p-spawn.js";

// Construct the prover Web Worker. The `new Worker(new URL(...))` literal lives
// in p2p-spawn.js (app/web/) so the URL resolves relative to that dir.
export const spawnWorker = () => makeWorker();

// Build the real transport on the main thread (async for trystero), priming the
// TURN credentials for WebRTC transports first, then resolve it via `cont`.
export const connectTransport = (kind, channel, cont) => {
  (async () => {
    if (kind === "trystero" || kind === "manual") {
      try { await initIce(); } catch {}
    }
    const t = await mkTransport(kind, channel);
    try { window.__transport = t; } catch {} // manual-SDP signaling / tests
    cont(t);
  })();
};

// Mirror a value onto `window` (the headless harness polls window.__p2pVerified
// / __p2pPhase / __p2pPeers). Guarded so it is a no-op in any non-window context.
export const setWindowProp = (k) => (v) => () => {
  try { window[k] = v; } catch {}
};
