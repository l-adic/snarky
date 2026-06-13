// Post-processes the napi-CLI-generated browser loader
// (wasm/kimchi-napi.wasi-browser.js) after `napi build`:
//
//   instantiateNapiModuleSync  ->  await instantiateNapiModule
//   + reuseWorker: { size: 16 }   (pre-spawned thread-worker pool)
//
// WHY: rayon's thread spawn blocks the calling worker until its threads
// check in, but nested workers' module scripts load via the PARENT
// thread's event loop — the blocked thread. Deadlock. The pre-spawned
// pool creates and loads the workers during module init (event loop
// free), so later thread-spawns reuse them without loading anything.
// emnapi requires the ASYNC instantiate for pool mode ("Synchronous
// loading is not supported with worker pool"); the loader already runs
// under top-level await, so the change is mechanical.
//
// Idempotent; run after every wasm build (see package.json build:wasm).
import fs from "node:fs";
import url from "node:url";
import { POOL_SIZE } from "./wasm-pool-config.mjs";

const file = url.fileURLToPath(new URL("./wasm/kimchi-napi.wasi-browser.js", import.meta.url));
let src = fs.readFileSync(file, "utf8");

if (src.includes("reuseWorker")) {
  console.log("[patch-wasi-browser] already patched");
  process.exit(0);
}

src = src.replace(
  "  instantiateNapiModuleSync as __emnapiInstantiateNapiModuleSync,",
  "  instantiateNapiModule as __emnapiInstantiateNapiModule,",
);
src = src.replace(
  "} = __emnapiInstantiateNapiModuleSync(__wasmFile, {",
  `} = await __emnapiInstantiateNapiModule(__wasmFile, {\n  reuseWorker: { size: ${POOL_SIZE} },`,
);
if (!src.includes("reuseWorker")) {
  console.error("[patch-wasi-browser] PATTERNS NOT FOUND — napi CLI output changed, update this script");
  process.exit(1);
}
fs.writeFileSync(file, src);
console.log("[patch-wasi-browser] patched: async instantiate + pre-spawned worker pool");
