// Post-processes the napi-CLI-generated browser loader
// (wasm/kimchi-napi.wasi-browser.js) after `napi build` to inject a
// pre-spawned thread-worker pool:
//
//   await instantiateNapiModule(__wasmFile, {
// +   reuseWorker: { size: <POOL_SIZE> },
//     ...
//
// WHY a pool: rayon's thread spawn blocks the calling worker until its
// threads check in, but nested workers' module scripts load via the
// PARENT thread's event loop — the blocked thread. Deadlock. The
// pre-spawned pool creates and loads the workers during module init
// (event loop free), so later thread-spawns reuse them without loading
// anything.
//
// WHY a patch (and not just config): napi-rs exposes the ASYNC
// instantiate as first-class config — `napi.wasm.browser.asyncInit` in
// package.json — which is why this script no longer swaps
// instantiateNapiModuleSync; the CLI already emits `await
// instantiateNapiModule` (pool mode requires the async instantiate:
// "Synchronous loading is not supported with worker pool"). But the
// CLI's BROWSER loader template has no notion of `reuseWorker` at all
// (only the node loader hardcodes it), so the pool option itself must
// be injected here. Upstream feature request would remove the need.
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

// Anchor on the async instantiate the CLI emits when
// `napi.wasm.browser.asyncInit` is set; inject the pool option.
const anchor = "} = await __emnapiInstantiateNapiModule(__wasmFile, {";
if (!src.includes(anchor)) {
  console.error(
    "[patch-wasi-browser] anchor not found — expected `await __emnapiInstantiateNapiModule`. " +
      "Is `napi.wasm.browser.asyncInit` still set in package.json? Has the napi CLI output changed?",
  );
  process.exit(1);
}
src = src.replace(anchor, `${anchor}\n  reuseWorker: { size: ${POOL_SIZE} },`);
fs.writeFileSync(file, src);
console.log("[patch-wasi-browser] patched: injected pre-spawned worker pool (reuseWorker)");
