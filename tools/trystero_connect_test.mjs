#!/usr/bin/env node
// Trystero/WebRTC connectivity regression test via Playwright Chromium.
//
// Headless Chrome over CDP has NO WebRTC/UDP, so the mesh tests only ever
// exercised the BroadcastChannel transport — which is why a trystero API
// breakage (0.25 changed makeAction to return an object, not a [send,get]
// pair; onPeerJoin became an assignable property) went unnoticed. Playwright
// Chromium DOES have a real WebRTC stack, so two contexts pointed at the same
// trystero session must discover each other over public Nostr relays and open
// a data channel. We assert both peers log "peer connected: <id>".
//
// This does NOT prove (it would need ~minutes + lots of memory); it only
// checks transport wiring, which is what keeps silently breaking.
//
// One-time setup:   npm i -D playwright && npx playwright install chromium
// Run against a PRODUCTION preview (tools/run_simulation_safari.sh → :4173):
//     tools/run_simulation_safari.sh --no-build   # terminal 1 (after a bundle)
//     node tools/trystero_connect_test.mjs        # terminal 2
//   optional arg: a base URL (default http://localhost:4173)
import { chromium } from "playwright";

const BASE = process.argv[2] || "http://localhost:4173";
const DEADLINE = Number(process.env.DEADLINE || 45) * 1000;
// A fresh session each run so stale peers on the relay don't interfere. No
// Date.now()/Math.random() restriction here (plain node script, not a workflow).
const SESSION = "ci-" + Date.now().toString(36);

const browser = await chromium.launch({
  args: ["--use-fake-ui-for-media-stream", "--use-fake-device-for-media-stream"],
});

// Two independent browser contexts = two independent peers (separate WebRTC
// stacks, separate trystero selfIds).
async function mkPeer(role) {
  const ctx = await browser.newContext();
  const page = await ctx.newPage();
  const logs = [];
  page.on("console", (m) => logs.push(m.text()));
  page.on("pageerror", (e) => logs.push("PAGEERROR: " + e.message));
  // The `&${role}` hash sets mode=base|merge, which AUTOSTARTS the mesh on
  // load (joining the trystero room) — no click needed; the buttons are hidden.
  const url = `${BASE}/p2p.html#session=${SESSION}&t=trystero&${role}`;
  await page.goto(url, { waitUntil: "domcontentloaded" });
  return { ctx, page, logs };
}

const peerConnected = (page) =>
  page.evaluate(() =>
    Array.from(document.querySelectorAll(".log-line .log-text")).some((e) =>
      /peer connected:/.test(e.textContent)
    )
  );

const base = await mkPeer("base");
const merge = await mkPeer("merge");

const t0 = Date.now();
let ok = false;
while (Date.now() - t0 < DEADLINE) {
  const [b, m] = await Promise.all([peerConnected(base.page), peerConnected(merge.page)]);
  if (b && m) {
    ok = true;
    break;
  }
  await base.page.waitForTimeout(1500);
}

const elapsed = ((Date.now() - t0) / 1000) | 0;
if (ok) {
  console.log(`PASS: peers connected over trystero/WebRTC in ${elapsed}s ✓`);
  await browser.close();
  process.exit(0);
}

console.log(`FAIL: peers did not connect within ${DEADLINE / 1000}s`);
for (const [name, p] of [["base", base], ["merge", merge]]) {
  console.log(`--- ${name} logs ---`);
  for (const l of p.logs.slice(-12)) console.log("  " + l);
}
await browser.close();
process.exit(1);
