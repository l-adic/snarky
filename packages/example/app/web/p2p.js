import "./styles.css";
// P2P entry LOADER — gates the real bootstrap (p2p-boot.js) on cross-origin
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
if (globalThis.crossOriginIsolated) {
  import("./p2p-boot.js");
} else {
  const app = document.getElementById("app");
  if (app)
    app.innerHTML =
      '<div style="min-height:100vh;display:flex;align-items:center;justify-content:center;' +
      "font-family:ui-monospace,Menlo,monospace;color:#e2e8f0;background:#0f172a;padding:2rem;" +
      'text-align:center;line-height:1.6">Enabling secure context (SharedArrayBuffer)…<br>' +
      "one moment, reloading.</div>";
}
