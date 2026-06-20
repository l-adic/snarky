// One-off headless-browser smoke test for the web prover's idbSyncCache path.
//
// Serves the built web bundle (dist/, with COOP/COEP for SharedArrayBuffer),
// drives a lone coordinator to a verified block root in real chromium, and
// asserts the SRS Lagrange bases got persisted to IndexedDB by the in-process
// prover worker (which uses idbSyncCache). Run AFTER `vite build`:
//
//   node tools/web-smoke.mjs
//
// Requires playwright + its chromium (`npm i -D playwright && npx playwright
// install chromium`). Not wired into CI — heavy; the Node fake-indexeddb test
// (Test.Snarky.Srs.IdbSyncSpec) is the CI-resident coverage of the same FFI.
import { chromium } from "playwright";
import { spawn } from "node:child_process";
import { fileURLToPath } from "node:url";

const appDir = fileURLToPath(new URL("../packages/example/app", import.meta.url));
const PORT = 4317;
const APP_URL = `http://localhost:${PORT}/index.html#t=bc`;
const PROVE_TIMEOUT_MS = 20 * 60 * 1000;

const log = (...a) => console.log("[smoke]", ...a);

async function waitForServer(url, tries = 60) {
  for (let i = 0; i < tries; i++) {
    try {
      const r = await fetch(url);
      if (r.ok) return;
    } catch {}
    await new Promise((r) => setTimeout(r, 500));
  }
  throw new Error("preview server never came up");
}

const preview = spawn(
  "npx",
  ["vite", "preview", "--config", "web/vite.config.mjs", "--port", String(PORT), "--strictPort"],
  { cwd: appDir, stdio: "inherit" },
);

let browser;
const cleanup = () => {
  try { browser?.close(); } catch {}
  try { preview.kill("SIGTERM"); } catch {}
};
process.on("exit", cleanup);

try {
  await waitForServer(`http://localhost:${PORT}/`);
  log("preview server up");

  browser = await chromium.launch({ headless: true });
  const page = await browser.newPage();
  page.on("console", (m) => console.log("  [browser]", m.text()));
  page.on("pageerror", (e) => console.log("  [browser ERROR]", e.message));

  await page.goto(APP_URL, { waitUntil: "load" });
  const coi = await page.evaluate(() => self.crossOriginIsolated);
  log("crossOriginIsolated =", coi);
  if (!coi) throw new Error("not cross-origin isolated — SharedArrayBuffer unavailable");

  log("clicking Start experiment (lone coordinator)…");
  await page.getByRole("button", { name: "Start experiment" }).click();

  log(`waiting up to ${PROVE_TIMEOUT_MS / 60000} min for verified root…`);
  await page.getByText("block root proof verified").waitFor({ timeout: PROVE_TIMEOUT_MS });
  log("✓ block root proof verified");

  // The in-process prover persists bases through idbSyncCache → assert the DB
  // holds the SRS cache entries (a basis key, not just generators).
  const keys = await page.evaluate(
    () =>
      new Promise((res, rej) => {
        const req = indexedDB.open("snarky-srs-cache", 1);
        req.onsuccess = () => {
          const r = req.result.transaction("srs", "readonly").objectStore("srs").getAllKeys();
          r.onsuccess = () => res(r.result);
          r.onerror = () => rej(r.error);
        };
        req.onerror = () => rej(req.error);
      }),
  );
  log("IndexedDB SRS cache keys:", keys);
  const bases = keys.filter((k) => /-d\d+$/.test(k));
  if (bases.length === 0) throw new Error("no Lagrange-basis entries persisted to IndexedDB");
  log(`✓ ${bases.length} Lagrange-basis entries persisted:`, bases.join(", "));

  log("SMOKE TEST PASSED");
  cleanup();
  process.exit(0);
} catch (e) {
  console.error("[smoke] FAILED:", e.message);
  cleanup();
  process.exit(1);
}
