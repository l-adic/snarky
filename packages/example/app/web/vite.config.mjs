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
  // The PS FFI (compiled into output-es/) reaches the app's internal JS modules
  // here in app/web/ through this alias, so its imports don't depend on the
  // output-es layout.
  { find: "@webjs", replacement: here(".") },
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
    // Two entry pages over one shared output-es build:
    //   index.html  the single-instance simulation app
    //   p2p.html    the P2P star worker-pool (coordinator + worker peers)
    rollupOptions: {
      input: {
        main: here("index.html"),
        p2p: here("p2p.html"),
      },
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
  },
  preview: {
    headers: {
      "Cross-Origin-Opener-Policy": "same-origin",
      "Cross-Origin-Embedder-Policy": "require-corp",
    },
  },
});
