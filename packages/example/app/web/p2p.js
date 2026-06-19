import "./styles.css";
// P2P entry LOADER — gates the real bootstrap (p2p-main.js) on cross-origin
// isolation.
//
// On GitHub Pages there are no COOP/COEP response headers, so the page is NOT
// cross-origin isolated on first load; the coi-serviceworker (registered in
// <head>) installs and RELOADS the page to make it isolated. Importing the
// prover graph before that reload spins up the wasm worker pool and shares a
// SharedArrayBuffer with the worker, which throws:
//   "Failed to execute 'postMessage' on 'Worker': SharedArrayBuffer transfer
//    requires self.crossOriginIsolated".
// So on the first, not-yet-isolated load we show a notice and do nothing else
// (no worker, no wasm) — the service worker reloads us, and the isolated
// reload dynamically imports the real entry. Locally (vite dev/preview) the
// COOP/COEP headers make the very first load isolated, so this imports
// immediately with no reload.
const panel = (html) => {
  const app = document.getElementById("app");
  if (app)
    app.innerHTML =
      '<div style="min-height:100vh;display:flex;flex-direction:column;align-items:center;' +
      "justify-content:center;gap:1rem;font-family:ui-monospace,Menlo,monospace;color:#e2e8f0;" +
      'background:#0f172a;padding:2rem;text-align:center;line-height:1.6">' + html + "</div>";
};

if (globalThis.crossOriginIsolated) {
  try { sessionStorage.removeItem("coiTries"); } catch {}
  import("./p2p-main.js");
} else {
  panel("Enabling secure context (SharedArrayBuffer)…<br>one moment, reloading.");
  // Watchdog: the coi-serviceworker reloads to gain cross-origin isolation, but
  // on Safari the SW can be "active but not controlling" after a reload, so it
  // may take a couple of attempts (the SW's own loop-guard is overridden in the
  // page <head> to retry up to a cap). If we're STILL not isolated after that —
  // Private Browsing, content blockers, or a stale SW — stop spinning and offer
  // a manual reset (unregister the SW + reload) instead of hanging forever.
  setTimeout(() => {
    if (globalThis.crossOriginIsolated) return;
    panel(
      "<div>Couldn’t enable a secure context (SharedArrayBuffer).</div>" +
        '<div style="color:#94a3b8;font-size:13px">This page needs cross-origin isolation for the wasm prover. ' +
        "It can fail in Private Browsing or with content blockers.</div>" +
        '<button id="coi-reset" style="background:#0ea5e9;color:#fff;border:none;border-radius:8px;' +
        'padding:0.6rem 1.2rem;font:inherit;cursor:pointer">Reset &amp; retry</button>',
    );
    const btn = document.getElementById("coi-reset");
    if (btn)
      btn.onclick = async () => {
        try {
          const regs = await navigator.serviceWorker.getRegistrations();
          await Promise.all(regs.map((r) => r.unregister()));
        } catch {}
        try { sessionStorage.removeItem("coiTries"); } catch {}
        location.reload();
      };
  }, 10000);
}
