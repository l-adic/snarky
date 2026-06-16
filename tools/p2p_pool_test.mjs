#!/usr/bin/env node
// Headless integration test for the P2P star worker-pool (Milestone A).
//
// Opens, in ONE headless Chromium over the BroadcastChannel transport (no
// WebRTC, no infra), a coordinator tab + N worker-peer tabs in a shared session,
// and asserts the coordinator verifies the block root proof. This exercises the
// real pool end-to-end: Join handshake, Assign/Result over the transport,
// base+merge dispatch to remote peers, and (if a peer stalls) timeout→reassign.
//
// Prereqs: a static server for the BUILT app on $URL. Easiest:
//     npm run bundle -w example-app           # build web/dist (both entries)
//     npx vite preview --config packages/example/app/web/vite.config.mjs --port 4173
//   (vite preview sends the COOP/COEP headers the wasm rayon pool needs.)
// Or the dev server: `cd packages/example/app && npm run p2p` (default :5173).
//
// Usage:
//     node tools/p2p_pool_test.mjs [peers] [threads]
//   peers    number of worker-peer tabs (default 2); coordinator poolSize = peers
//   threads  rayon threads per tab (default 2 — keep low so N+1 wasm instances
//            share one CPU without thrashing)
import { spawn } from "node:child_process";
import os from "node:os";
import fs from "node:fs";

const PEERS = Math.max(1, +(process.argv[2] || 2));
const THREADS = process.argv[3] || "2";
const URL = process.env.URL || "http://localhost:4173";
const CDP = +(process.env.CDP || 9455);
const SESSION = "p2ppool-" + Math.floor(Date.now() % 1e7);
const CHROME =
  process.env.CHROME ||
  os.homedir() + "/.cache/ms-playwright/chromium-1169/chrome-linux/chrome";
const sleep = (ms) => new Promise((r) => setTimeout(r, ms));

async function rpc(ws, method, params = {}) {
  return await new Promise((res, rej) => {
    const s = new WebSocket(ws);
    const to = setTimeout(() => { try { s.close(); } catch {} rej(new Error("rpc timeout")); }, 10000);
    s.onopen = () => s.send(JSON.stringify({ id: 1, method, params }));
    s.onmessage = (e) => { const d = JSON.parse(e.data); if (d.id === 1) { clearTimeout(to); s.close(); res(d.result); } };
    s.onerror = (e) => { clearTimeout(to); rej(e); };
  });
}
const evalIn = async (ws, expr) => (await rpc(ws, "Runtime.evaluate", { expression: expr, returnByValue: true }))?.result?.value;
const J = async () => await (await fetch(`http://localhost:${CDP}/json`)).json();
const logsOf = (ws) => evalIn(ws, "Array.from(document.querySelectorAll('.log-line .log-text')).map(e=>e.textContent).join('\\n')");

// 1. launch a dedicated headless Chromium with remote debugging.
const profile = fs.mkdtempSync(os.tmpdir() + "/p2p-pool-test-");
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

// 2. open the peer tabs first (so they're compiling + announcing), then the
//    coordinator. All compile in parallel; the coordinator's pool waits for N
//    Joins before dispatching, which the peers satisfy as they finish compiling.
const base = `${URL}/p2p.html`;
async function tabFor(match) {
  const ts = (await J()).filter((t) => (t.url || "").includes(match));
  return ts[ts.length - 1]?.webSocketDebuggerUrl;
}
for (let i = 0; i < PEERS; i++) {
  await brpc("Target.createTarget", { url: `${base}#role=peer&session=${SESSION}&t=bc&threads=${THREADS}&auto=1` });
  await sleep(500);
}
await brpc("Target.createTarget", { url: `${base}#role=coordinator&session=${SESSION}&t=bc&poolSize=${PEERS}&threads=${THREADS}&auto=1` });
console.log(`launched 1 coordinator + ${PEERS} peer(s), session ${SESSION} (threads=${THREADS}) — driving…`);

// 3. poll the coordinator tab for verification.
const t0 = Date.now(), ts = () => ((Date.now() - t0) / 1000) | 0;
const DEADLINE = +(process.env.DEADLINE || 1200);
let last = "";
while (ts() < DEADLINE) {
  const coordWs = await tabFor("role=coordinator");
  if (coordWs) {
    let verified, phase, tail;
    try {
      verified = await evalIn(coordWs, "window.__p2pVerified");
      phase = await evalIn(coordWs, "window.__p2pPhase");
      tail = ((await logsOf(coordWs)) || "").split("\n")[0];
    } catch {}
    const summary = `phase=${phase ?? "-"}  ${tail ?? ""}`;
    if (summary !== last) { console.log(`[t+${ts()}s] ${summary}`); last = summary; }
    if (verified === true) { console.log(`\nblock root proof verified ✓  (t+${ts()}s)\nPASS`); process.exit(0); }
    if (verified === false || phase === "failed") { console.log(`\nFAIL: coordinator reported failure (phase=${phase})`); process.exit(1); }
  }
  await sleep(3000);
}
console.log("FAIL: timeout");
process.exit(2);
