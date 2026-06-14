#!/usr/bin/env node
// Headless multi-config integration test for the P2P proving mesh. Opens one
// tab per role in a single headless Chrome (BroadcastChannel transport — the
// sandboxed-WebRTC-free vehicle that exercises the full gossip Node), auto-
// clicks "prove next" as work becomes available, and asserts:
//   * the block root verifies,
//   * all MERGE peers report the SAME "prove next" count at every poll
//     (the count reflects global network state, not just local proofs).
//
// Prereqs: the dev server running on $URL (default http://localhost:5173):
//     cd packages/example/app && npm run p2p
//
// Usage:
//     node tools/p2p_mesh_test.mjs [roles] [threads]
//   roles    comma list of base|merge (default "base,merge,merge"); capped at 5
//   threads  rayon threads per tab (default 4 — keep low so N provers fit one CPU)
//
// Examples:
//     node tools/p2p_mesh_test.mjs base,merge
//     node tools/p2p_mesh_test.mjs base,merge,merge,merge 3
import { spawn } from "node:child_process";
import os from "node:os";
import fs from "node:fs";

// Test-suite bounds (CPU), not app limits: merge provers are capped at 2 (so
// the merge work splits without piling on too many heavy wasm tabs).
const MAX_MERGE = 2;
let mergeSeen = 0;
const ROLES = (process.argv[2] || "base,merge,merge")
  .split(",").map((s) => s.trim())
  .filter((r) => (r === "merge" ? ++mergeSeen <= MAX_MERGE : true));
const THREADS = process.argv[3] || (ROLES.length >= 4 ? "2" : "4"); // keep N provers within one CPU
const URL = process.env.URL || "http://localhost:5173";
const CDP = 9444;
const SESSION = "test-" + Math.floor(Date.now() % 1e7);
const CHROME = process.env.CHROME || "/Applications/Google Chrome.app/Contents/MacOS/Google Chrome";
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
const J = async () => (await (await fetch(`http://localhost:${CDP}/json`)).json());

// 1. launch a dedicated headless Chrome
const profile = fs.mkdtempSync(os.tmpdir() + "/p2p-test-");
const chrome = spawn(CHROME, ["--headless=new", "--disable-gpu", "--no-first-run", "--no-default-browser-check",
  "--user-data-dir=" + profile, "--remote-debugging-port=" + CDP, "about:blank"], { stdio: "ignore" });
process.on("exit", () => { try { chrome.kill(); } catch {} try { fs.rmSync(profile, { recursive: true, force: true }); } catch {} });
for (let i = 0; i < 30; i++) { try { await fetch(`http://localhost:${CDP}/json/version`); break; } catch { await sleep(1000); } }
const ver = await (await fetch(`http://localhost:${CDP}/json/version`)).json();
const brpc = (m, p = {}) => rpc(ver.webSocketDebuggerUrl, m, p);

// 2. open one tab per role SEQUENTIALLY — wait for each to compile (and, for a
// base, generate its block) before opening the next, so N heavy wasm compiles
// don't thrash one CPU. (Several provers still run concurrently while proving.)
async function newestTab() {
  const ts = (await J()).filter((t) => (t.url || "").includes(`session=${SESSION}`));
  return ts[ts.length - 1]?.webSocketDebuggerUrl;
}
async function waitReady(role) {
  const ready = role === "base" ? /generated block/ : /compiled; fingerprint/;
  for (let i = 0; i < 90; i++) {
    const ws = await newestTab();
    if (ws) { try { if (ready.test(await evalIn(ws, "Array.from(document.querySelectorAll('.log-line .log-text')).map(e=>e.textContent).join('\\n')") || "")) return; } catch {} }
    await sleep(2000);
  }
}
for (const role of ROLES) {
  await brpc("Target.createTarget", { url: `${URL}/p2p.html#mode=${role}&session=${SESSION}&t=bc&threads=${THREADS}` });
  await sleep(800);
  await waitReady(role);
  console.log(`  ${role} ready`);
}
console.log(`config [${ROLES.join(", ")}], session ${SESSION} — driving…`);

const EXPECT_BLOCKS = ROLES.filter((r) => r === "base").length; // one block per base prover
const SNAP = `JSON.stringify((()=>{const n=document.getElementById('next');return{
  role:(location.hash.match(/mode=(\\w+)/)||[])[1],
  step:n&&!n.disabled?((n.textContent.match(/\\((\\d+)/)||[0,0])[1]|0):0,
  raw:n?n.textContent:'-',
  verified:Array.from(document.querySelectorAll('.log-line .log-text')).map(e=>(e.textContent.match(/block (\\S+) root proof verified/)||[])[1]).filter(Boolean)
}})())`;

const t0 = Date.now(), ts = () => ((Date.now() - t0) / 1000) | 0;
const DEADLINE = Math.max(900, EXPECT_BLOCKS * 360); // scale with the number of blocks
let last = "", samples = 0, agreed = 0;
const verifiedBlocks = new Set();
while (ts() < DEADLINE) {
  const tabs = (await J()).filter((t) => (t.url || "").includes(`session=${SESSION}`));
  const states = [], mergeSteps = [];
  for (const tb of tabs) {
    let s; try { s = JSON.parse(await evalIn(tb.webSocketDebuggerUrl, SNAP)); } catch { s = {}; }
    states.push(`${s.role}:${s.raw}`);
    (s.verified || []).forEach((b) => verifiedBlocks.add(b));
    if (s.role === "merge") mergeSteps.push(s.step);
    if (s.step > 0) { try { await evalIn(tb.webSocketDebuggerUrl, "globalThis.__node && globalThis.__node.step()"); } catch {} }
  }
  if (mergeSteps.length > 1) { samples++; if (Math.max(...mergeSteps) === Math.min(...mergeSteps)) agreed++; }
  const summary = states.join(" | ") + `  [verified ${verifiedBlocks.size}/${EXPECT_BLOCKS}]`;
  if (summary !== last) { console.log(`[t+${ts()}s] ${summary}`); last = summary; }
  if (verifiedBlocks.size >= EXPECT_BLOCKS) {
    const consistent = samples === 0 || agreed === samples;
    console.log(`\nall ${EXPECT_BLOCKS} block root(s) verified ✓   merge-count consistency: ${agreed}/${samples} polls agreed`);
    console.log(consistent ? "PASS" : "FAIL (merge peers disagreed on the count)");
    process.exit(consistent ? 0 : 1);
  }
  await sleep(3000);
}
console.log("FAIL: timeout");
process.exit(2);
