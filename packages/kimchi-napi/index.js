// Loads the platform-appropriate kimchi-napi .node native module.
// The .node file is produced by `npm run build` (build.sh in this
// directory), which invokes `cargo build -p kimchi-napi --release`
// inside the in-tree proof-systems submodule and copies the resulting
// cdylib here under the platform-suffixed name below.

// KIMCHI_BACKEND=wasm loads the wasm32-wasip1-threads build instead
// (same API surface; built by `napi build --target wasm32-wasip1-threads`
// into ./wasm). The rayon pool on wasm defaults to 1 thread (wasi's
// available_parallelism reports 1), so we size it explicitly here —
// REQUIRED for multi-threaded proving.
if (process.env.KIMCHI_BACKEND === "wasm") {
  const k = require("./wasm/kimchi-napi.wasi.cjs");
  // rayon pool size. Default IN NODE is the full core count: our napi
  // calls are synchronous, so the main JS thread is blocked (asleep)
  // during every Rust phase — it donates its core to the pool rather than
  // contending with it (cores-1 measured ~8% prove wall). When several wasm
  // instances run at once (the worker_threads pool), that full count
  // oversubscribes — so KIMCHI_WASM_RAYON_THREADS overrides it, letting the
  // launcher hand each instance cores/poolSize for an even split. (The
  // browser is the opposite regime and sizes its own pool via wasm-pool-config.)
  const rayon = Number(process.env.KIMCHI_WASM_RAYON_THREADS) || require("os").cpus().length;
  k.initThreadPool(rayon);
  module.exports = k;
  return;
}

const { platform, arch } = process;
let file = null;

switch (platform) {
  case "linux":
    if (arch === "x64") file = "./kimchi-napi.linux-x64-gnu.node";
    else if (arch === "arm64") file = "./kimchi-napi.linux-arm64-gnu.node";
    break;
  case "darwin":
    if (arch === "x64") file = "./kimchi-napi.darwin-x64.node";
    else if (arch === "arm64") file = "./kimchi-napi.darwin-arm64.node";
    break;
}

if (file === null) {
  throw new Error(
    `kimchi-napi: unsupported host ${platform}-${arch}. Add a case in index.js and build.sh for this platform.`,
  );
}

module.exports = require(file);
