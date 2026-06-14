# example web frontend

Browser frontend for the example simulation: runs the full one-block
pipeline (SRS, circuit compile, base + merge proofs, root verification)
in a Web Worker over the wasm kimchi backend, rendering the scan-state
tree and block transactions with react-basic.

## Run

One-time prerequisite — build the wasm backend:

```
npm run build:wasm -w kimchi-napi
```

Then, from `packages/example/` (or via `tools/run_simulation_web.sh`):

```
npm run dev       # dev: vite dev server (COOP/COEP set) on http://localhost:5173
npm run bundle    # prod: optimized bundle -> web/dist/
npm run preview   # prod: serve the built bundle
```

Cross-origin isolation (COOP `same-origin` + COEP `require-corp`) is
required for the SharedArrayBuffer-backed rayon thread pool; the dev
server sets both, and any production host must do the same.
