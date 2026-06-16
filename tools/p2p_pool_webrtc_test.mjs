#!/usr/bin/env node
// Headless integration test for the P2P star worker-pool over a REAL WebRTC data
// channel (Milestone B). Uses the manual-SDP transport so signaling is
// deterministic (no Nostr relay / no external discovery): the harness itself
// copy-pastes the offer/answer between the two tabs. This validates the leg the
// main-thread-transport bridge unblocked — RTCPeerConnection on the main thread,
// an RTCDataChannel, and sendChunked/recvChunked framing for proof wires that
// exceed the ~256KB SCTP message limit — coordinator + 1 worker peer to a
// verified block root.
//
// Manual SDP is exactly 2 peers (one data channel), so this is 1 coordinator
// (offerer) + 1 peer (answerer), poolSize 1. (Trystero is the cross-machine,
// many-peer transport; it's wired and human-testable but depends on public
// relays, so it's not part of this deterministic CI check.)
//
// Prereqs: a static server for the BUILT app on $URL (vite preview sends the
// COOP/COEP headers the wasm rayon pool needs):
//     npm run bundle -w example-app
//     npx vite preview --config packages/example/app/web/vite.config.mjs --port 4173
//
// Usage: node tools/p2p_pool_webrtc_test.mjs [threads]
import { spawn } from "node:child_process";
import os from "node:os";
import fs from "node:fs";

const THREADS = process.argv[2] || "4";
const URL = process.env.URL || "http://localhost:4173";
const CDP = +(process.env.CDP || 9457);
const SESSION = "p2pwebrtc-" + Math.floor(Date.now() % 1e7);
const CHROME =
  process.env.CHROME ||
  os.homedir() + "/.cache/ms-playwright/chromium-1169/chrome-linux/chrome";
const sleep = (ms) => new Promise((r) => setTimeout(r, ms));

async function rpc(ws, method, params = {}) {
  return await new Promise((res, rej) => {
    const s = new WebSocket(ws);
    const to = setTimeout(() => { try { s.close(); } catch {} rej(new Error("rpc timeout")); }, 20000);
    s.onopen = () => s.send(JSON.stringify({ id: 1, method, params }));
    s.onmessage = (e) => { const d = JSON.parse(e.data); if (d.id === 1) { clearTimeout(to); s.close(); res(d.result); } };
    s.onerror = (e) => { clearTimeout(to); rej(e); };
  });
}
// awaitPromise so we can call the transport's async signaling methods directly.
const evalIn = async (ws, expr) =>
  (await rpc(ws, "Runtime.evaluate", { expression: expr, returnByValue: true, awaitPromise: true }))?.result?.value;
const J = async () => await (await fetch(`http://localhost:${CDP}/json`)).json();
const logsOf = (ws) => evalIn(ws, "Array.from(document.querySelectorAll('.log-line .log-text')).map(e=>e.textContent).join('\\n')");

// 1. launch a dedicated headless Chromium with remote debugging.
const profile = fs.mkdtempSync(os.tmpdir() + "/p2p-webrtc-test-");
const chrome = spawn(
  CHROME,
  ["--headless=new", "--disable-gpu", "--no-first-run", "--no-default-browser-check",
    "--no-sandbox", "--user-data-dir=" + profile, "--remote-debugging-port=" + CDP, "about:blank"],
  { stdio: "ignore" },
);
process.on("exit", () => { try { chrome.kill(); } catch {} try { fs.rmSync(profile, { recursive: true, force: true }); } catch {} });
for (let i = 0; i < 30; i++) { try { await fetch(`http://localhost:${CDP}/json/version`); break; } catch { await sleep(1000); } }
const ver = await (await fetch(`http://localhost:${CDP}/json/version`)).json();
const brpc = (m, p = {}) => rpc(ver.webSocketDebuggerUrl, m, p);

// 2. open the coordinator (offerer) + one peer (answerer).
const base = `${URL}/p2p.html`;
async function tabFor(match) {
  const ts = (await J()).filter((t) => (t.url || "").includes(match));
  return ts[ts.length - 1]?.webSocketDebuggerUrl;
}
await brpc("Target.createTarget", { url: `${base}#role=coordinator&session=${SESSION}&t=manual&poolSize=1&threads=${THREADS}&auto=1` });
await sleep(500);
await brpc("Target.createTarget", { url: `${base}#role=peer&session=${SESSION}&t=manual&threads=${THREADS}&auto=1` });
console.log(`launched coordinator + 1 peer over manual WebRTC, session ${SESSION} (threads=${THREADS})`);

// 3. wait for both tabs' main-thread transports, then hand-wire the WebRTC
//    connection (offer → answer → apply). __transport is set in p2p-boot once
//    mkManualTransport() returns.
const coord = await (async () => { for (let i = 0; i < 60; i++) { const w = await tabFor("role=coordinator"); if (w && (await evalIn(w, "!!window.__transport"))) return w; await sleep(1000); } throw new Error("coordinator transport never appeared"); })();
const peer = await (async () => { for (let i = 0; i < 60; i++) { const w = await tabFor("role=peer"); if (w && (await evalIn(w, "!!window.__transport"))) return w; await sleep(1000); } throw new Error("peer transport never appeared"); })();
console.log("both transports up — exchanging SDP…");
const offer = await evalIn(coord, "window.__transport.createOffer()");
if (!offer) throw new Error("createOffer returned nothing");
const answer = await evalIn(peer, `window.__transport.acceptOffer(${JSON.stringify(offer)})`);
if (!answer) throw new Error("acceptOffer returned nothing");
await evalIn(coord, `window.__transport.acceptAnswer(${JSON.stringify(answer)})`);
console.log("SDP exchanged — WebRTC data channel negotiated; driving…");

// 4. poll the coordinator for verification.
const t0 = Date.now(), ts = () => ((Date.now() - t0) / 1000) | 0;
const DEADLINE = +(process.env.DEADLINE || 1500);
let last = "";
while (ts() < DEADLINE) {
  let verified, phase, tail;
  try {
    verified = await evalIn(coord, "window.__p2pVerified");
    phase = await evalIn(coord, "window.__p2pPhase");
    tail = ((await logsOf(coord)) || "").split("\n")[0];
  } catch {}
  const summary = `phase=${phase ?? "-"}  ${tail ?? ""}`;
  if (summary !== last) { console.log(`[t+${ts()}s] ${summary}`); last = summary; }
  if (verified === true) { console.log(`\nblock root proof verified over WebRTC ✓  (t+${ts()}s)\nPASS`); process.exit(0); }
  if (verified === false || phase === "failed") { console.log(`\nFAIL: coordinator reported failure (phase=${phase})`); process.exit(1); }
  await sleep(3000);
}
console.log("FAIL: timeout");
process.exit(2);
