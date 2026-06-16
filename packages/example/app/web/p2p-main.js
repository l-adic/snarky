import "./styles.css";
// Thin entry for the P2P proving UI: the react-basic app lives in PureScript
// (Snarky.Example.Web.P2P.Main); this file supplies only the irreducibly-JS
// pieces it can't construct itself — the worker (vite needs the literal
// `new Worker(new URL(...))` to bundle its graph) and the transport factory (the
// BroadcastChannel / WebRTC / trystero modules) — plus the URL-hash defaults.
import { runP2pApp } from "../output-es/Snarky.Example.Web.P2P.Main/index.js";
import { mkTransport } from "./p2p-mk-transport.js";
import { initIce } from "./p2p-rtc.js";

function hashParams() {
  const raw = location.hash.replace(/^#/, "");
  const p = {};
  for (const part of raw.split("&")) {
    if (!part) continue;
    const [k, v] = part.split("=");
    p[k] = v === undefined ? true : decodeURIComponent(v);
  }
  return p;
}
const params = hashParams();

runP2pApp({
  spawnWorker: () => new Worker(new URL("./p2p-worker.js", import.meta.url), { type: "module" }),
  // Build the real transport on the main thread (async for trystero); for WebRTC
  // transports prime the TURN credentials first. Resolves it back to PureScript.
  connectTransport: (kind, channel, cont) => {
    (async () => {
      if (kind === "trystero" || kind === "manual") {
        try { await initIce(); } catch {}
      }
      const t = await mkTransport(kind, channel);
      window.__transport = t; // manual-SDP signaling / tests
      cont(t);
    })();
  },
  channel: params.session || "snarky-p2p",
  transport: params.t || "trystero",
  // Auto-start a role on mount for the headless harness / launchers.
  autoRole: params.auto || params.role ? (params.role === "peer" ? "peer" : "coordinator") : null,
  threads: params.threads ? +params.threads : null,
})();
