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
  { find: "kimchi-napi", replacement: here("../../kimchi-napi/wasm/kimchi-napi.wasi-browser.js") },
  { find: "module", replacement: here("stubs/node-module.js") },
];

export default defineConfig({
  root: here("."),
  plugins: [nodePolyfills({ exclude: ["module"], overrides: { fs: "memfs" } })],
  resolve: { alias: aliases },
  build: {
    target: "esnext",
    outDir: here("dist"),
    emptyOutDir: true,
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
      allow: [here("../../..")],
    },
  },
  preview: {
    headers: {
      "Cross-Origin-Opener-Policy": "same-origin",
      "Cross-Origin-Embedder-Policy": "require-corp",
    },
  },
});
