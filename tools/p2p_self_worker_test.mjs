#!/usr/bin/env node
// Definitive headless test that the COORDINATOR'S OWN spawned prover contributes.
//
// The coordinator runs its own prover as a nested Web Worker (prover.js) — the
// first worker of the Dynamic pool, shown as "self" in the peer table. This test
// asserts that worker actually completes jobs, in two regimes:
//
//   peers=0  the self worker is the ONLY prover, so it must do EVERY job and the
//            root must verify (a stall here is fatal — nothing to reassign to).
//   peers≥1  the self worker proves ALONGSIDE remote peers, so it must complete
//            at least one job (completed > 0) — i.e. it is not starved/stalled
//            while the peers do all the work.
//
// Over BroadcastChannel in one headless Chromium (no WebRTC/infra), same vehicle
// as p2p_pool_test.mjs. PASS = root verified AND self.completed meets the bar.
// It also reports the self-vs-remote completion split and any pool job timeouts
// (a symptom of self-worker flakiness even when the run self-heals).
//
// Prereqs: the BUILT app served on $URL with COOP/COEP (vite preview):
//     npm run bundle -w example-app
//     npx vite preview --config packages/example/app/web/vite.config.mjs --port 4173
//   or just use the runner:  tools/run_p2p_pool.sh --self-worker [peers]
//
// Usage:
//     node tools/p2p_self_worker_test.mjs [peers] [threads]
//   peers    remote peer tabs besides the coordinator's self worker (default 0)
//   threads  rayon threads per tab (default 2)
import { spawn } from "node:child_process";
import os from "node:os";
import fs from "node:fs";

const PEERS = Math.max(0, +(process.argv[2] || 0));
const THREADS = process.argv[3] || "2";
const URL = process.env.URL || "http://localhost:4173";
const CDP = +(process.env.CDP || 9456);
const DEADLINE = +(process.env.DEADLINE || 1200);
const SESSION = "p2pself-" + Math.floor(Date.now() % 1e7);
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
const profile = fs.mkdtempSync(os.tmpdir() + "/p2p-self-test-");
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

// 2. open the remote peers (if any) first so they compile in parallel, then the
//    coordinator. With peers=0 it's a lone coordinator: the self worker alone.
const base = `${URL}/index.html`;
const tabFor = async (match) => {
  const ts = (await J()).filter((t) => (t.url || "").includes(match));
  return ts[ts.length - 1]?.webSocketDebuggerUrl;
};
for (let i = 0; i < PEERS; i++) {
  await brpc("Target.createTarget", { url: `${base}#role=peer&session=${SESSION}&t=bc&threads=${THREADS}&auto=1` });
  await sleep(500);
}
await brpc("Target.createTarget", { url: `${base}#role=coordinator&session=${SESSION}&t=bc&threads=${THREADS}&auto=1` });
console.log(`[self-worker test] 1 coordinator + ${PEERS} remote peer(s), session ${SESSION} (threads=${THREADS})`);
console.log(`  bar: ${PEERS === 0 ? "self must prove EVERY job + root verifies" : "self.completed > 0 (contributes alongside peers)"}\n`);

// 3. poll the coordinator: track the self worker's completion, the remote split,
//    and pool timeouts; decide PASS/FAIL once the root verifies (or we time out).
const t0 = Date.now(), ts = () => ((Date.now() - t0) / 1000) | 0;
const parsePeers = (j) => { try { return JSON.parse(j || "[]"); } catch { return []; } };
const selfOf = (ps) => ps.find((p) => p.id === "self");
let last = "";
let maxSelf = 0;
while (ts() < DEADLINE) {
  const coordWs = await tabFor("role=coordinator");
  if (coordWs) {
    let verified, phase, peers, log;
    try {
      verified = await evalIn(coordWs, "window.__p2pVerified");
      phase = await evalIn(coordWs, "window.__p2pPhase");
      peers = parsePeers(await evalIn(coordWs, "JSON.stringify(window.__p2pPeers||[])"));
      log = (await logsOf(coordWs)) || "";
    } catch {}
    peers = peers || [];
    const self = selfOf(peers);
    if (self) maxSelf = Math.max(maxSelf, self.completed);
    const remote = peers.filter((p) => p.id !== "self");
    const remoteDone = remote.reduce((a, p) => a + p.completed, 0);
    const timeouts = (log.match(/timed out/g) || []).length;
    const summary =
      `phase=${phase ?? "-"}  self=${self ? self.status + ":" + self.completed : "absent"}` +
      `  remoteDone=${remoteDone}  timeouts=${timeouts}`;
    if (summary !== last) { console.log(`[t+${ts()}s] ${summary}`); last = summary; }

    if (verified === true) {
      const finalTimeouts = (log.match(/timed out/g) || []).length;
      console.log(
        `\nroot verified ✓ at t+${ts()}s — self.completed=${maxSelf}, remoteDone=${remoteDone}, ` +
        `pool timeouts=${finalTimeouts}`,
      );
      // peers=0: the self worker is the ONLY prover, so it must prove every job
      // AND never time out (a timeout there is the self worker stalling on itself
      // — pure waste, the symptom we are guarding against).
      // peers≥1: it must merely contribute (completed > 0); a timeout that hands a
      // slow self job to a faster peer is legitimate load-balancing, not a failure.
      if (maxSelf <= 0) {
        console.log(`FAIL: root verified but the coordinator's own worker completed 0 jobs (starved/stalled).`);
        process.exit(1);
      }
      if (PEERS === 0 && finalTimeouts > 0) {
        console.log(`FAIL: lone self worker timed out ${finalTimeouts}×on itself (flaky/slow — it should never stall).`);
        process.exit(1);
      }
      console.log(`PASS: the coordinator's own worker contributed (${maxSelf} job(s)).`);
      process.exit(0);
    }
    if (verified === false || phase === "failed") { console.log(`\nFAIL: coordinator reported failure (phase=${phase})`); process.exit(1); }
  }
  await sleep(3000);
}
console.log(`\nFAIL: timeout after ${DEADLINE}s (self.completed peaked at ${maxSelf}; the self worker stalled).`);
process.exit(2);
