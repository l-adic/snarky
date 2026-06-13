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
  // Full core count IN NODE: our napi calls are synchronous, so the
  // main JS thread is blocked (asleep) during every Rust phase — it
  // donates its core to the pool rather than contending with it.
  // Measured: cores-1 costs ~8% prove wall here. The BROWSER is the
  // opposite regime — the UI thread keeps running concurrently, so the
  // browser init should use navigator.hardwareConcurrency - 1.
  k.initThreadPool(require("os").cpus().length);
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
