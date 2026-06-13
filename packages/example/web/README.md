# example-simulation-web

Browser frontend for the example simulation — the second package of
the `example-simulation` spago workspace, sharing the simulation
source (`packages/example`) and the workspace's purs-backend-es output
with the node TUI package.

```
tools/run_simulation_web.sh           # vite dev server
tools/run_simulation_web.sh --build   # production bundle -> dist/
```

## Current state: scaffold

The page renders the scan-state tree through the SAME pure
`renderScanState` the terminal display uses, inside a react-basic
component (entry: `web/src/Main.purs`, `Snarky.Example.Web.Main`).

Node-only FFI reached through the shared source is aliased to stubs in
`vite.config.mjs`:

| stub | replaced by (next steps) |
|---|---|
| `kimchi-napi` | the wasm backend: `packages/kimchi-napi/wasm/kimchi-napi.wasi-browser.js` — run inside a dedicated Web Worker, `initThreadPool(navigator.hardwareConcurrency - 1)` |
| `node:crypto` | Web Crypto / pure-JS digest for pasta-runtime's `createHash` use |
| `log-update`  | nothing — TUI-only; react renders the tree here |

The dev server already sends `Cross-Origin-Opener-Policy: same-origin`
and `Cross-Origin-Embedder-Policy: require-corp`: cross-origin
isolation is required for the SharedArrayBuffer-backed rayon thread
pool when the wasm backend lands, and any production host must do the
same.

## Next steps

1. Replace the `<pre>` with a real react tree-diagram component,
   subscribed to the snark manager's `onProgress` hook (the same hook
   the TUI's reporter plugs into).
2. Run the actual simulation in-browser: wasm kimchi backend in a Web
   Worker, SRS computed in-browser (`createCRS` — no filesystem
   needed), the page driving blocks through the pipeline.
