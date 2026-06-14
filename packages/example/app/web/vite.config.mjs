// Vite config for the browser simulation app.
//
// - root = this directory (index.html + main.js + worker-entry.js);
//   the PS module graph is imported from the workspace's shared
//   ../output-es build.
// - COOP/COEP headers: cross-origin isolation is REQUIRED for the
//   SharedArrayBuffer-backed rayon thread pool of the wasm kimchi
//   backend.
// - node builtins (Buffer, process, fs, ...) reached through FFI files
//   are handled by the standard vite-plugin-node-polyfills. The ONLY
//   custom mapping is app-specific: `kimchi-napi` resolves to the
//   wasm32-wasip1-threads browser loader (built by `napi build` into
//   packages/kimchi-napi/wasm/), and `module`'s createRequire (the CJS
//   interop our kimchi FFI files use) hands that loader back.
// - target esnext: the wasm loader uses top-level await.
import { defineConfig } from "vite";
import { nodePolyfills } from "vite-plugin-node-polyfills";
import { fileURLToPath } from "node:url";

const here = (p) => fileURLToPath(new URL(p, import.meta.url));

const aliases = [
  { find: "kimchi-napi", replacement: here("../../../kimchi-napi/wasm/kimchi-napi.wasi-browser.js") },
  { find: "module", replacement: here("stubs/node-module.js") },
];

export default defineConfig({
  root: here("."),
  // Served from "/" locally (dev/preview). GitHub Pages serves the repo
  // under a subpath (https://l-adic.github.io/snarky/), so the deploy
  // build sets VITE_BASE=/snarky/ to prefix asset URLs accordingly.
  base: process.env.VITE_BASE ?? "/",
  plugins: [nodePolyfills({ exclude: ["module"], overrides: { fs: "memfs" } })],
  resolve: { alias: aliases },
  // Flow a build-time KIMCHI_WASM_POOL_SIZE override into the bundled
  // worker: the kimchi-napi wasm-pool-config module reads this env ref to
  // derive MAX_RAYON_THREADS, so the worker's rayon cap stays consistent
  // with the pre-spawned pool size baked into the wasm loader.
  define: {
    "process.env.KIMCHI_WASM_POOL_SIZE": JSON.stringify(process.env.KIMCHI_WASM_POOL_SIZE ?? ""),
  },
  build: {
    target: "esnext",
    outDir: here("dist"),
    emptyOutDir: true,
    rollupOptions: {
      // Pages: full pipeline (index.html), the privacy split (private.html),
      // and the serverless P2P proving mesh (p2p.html).
      input: { main: here("index.html"), private: here("private.html"), p2p: here("p2p.html") },
    },
  },
  worker: {
    format: "es",
    plugins: () => [nodePolyfills({ exclude: ["module"], overrides: { fs: "memfs" } })],
  },
  server: {
    headers: {
      "Cross-Origin-Opener-Policy": "same-origin",
      "Cross-Origin-Embedder-Policy": "require-corp",
    },
    fs: {
      allow: [here("../../../..")],
    },
    // The privacy page's worker POSTs base proofs to a same-origin /merge,
    // which we proxy to the native merge server (web/merge-server.mjs).
    proxy: {
      "/merge": "http://localhost:8099",
    },
  },
  preview: {
    headers: {
      "Cross-Origin-Opener-Policy": "same-origin",
      "Cross-Origin-Embedder-Policy": "require-corp",
    },
  },
});
