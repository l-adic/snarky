// FFI for Snarky.Example.Web.P2P.Main. Signatures are dictated by the PS
// `foreign import`s. The transport tier and the worker-spawn module are internal
// app JS reached via the `@webjs` vite alias (app/web/), so this FFI — which is
// compiled into output-es/ — can import them regardless of its own location.
import { mkTransport, initIce } from "@webjs/transport";
import { spawnWorker as makeWorker } from "@webjs/p2p-spawn.js";

// Construct the prover Web Worker. The `new Worker(new URL(...))` literal lives
// in p2p-spawn.js (app/web/) so the URL resolves relative to that dir.
export const spawnWorker = () => makeWorker();

// Build the real transport on the main thread (async for trystero), priming the
// TURN credentials for the WebRTC transport first, then resolve it via `cont`.
export const connectTransport = (kind, channel, cont) => {
  (async () => {
    if (kind === "trystero") {
      try { await initIce(); } catch {}
    }
    const t = await mkTransport(kind, channel);
    cont(t);
  })();
};

// Run `eff` when the page is unloaded. `pagehide` is the reliable signal (it
// fires on tab close / navigation, and unlike `unload` is bfcache-friendly).
export const onPageHide = (eff) => () => {
  window.addEventListener("pagehide", () => eff(), { once: true });
};
