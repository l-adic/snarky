// SRS builder with an IndexedDB lagrange-basis cache. Rebuilds the g-vector
// fresh (deterministic, ~1s) and caches only the lagrange bases (~12 MB) so a
// reload restores them via set_lagrange_basis instead of warming (~33s).
//
// Depths/domains mirror Snarky.Example.Env.mkConfig exactly:
//   vesta / Fp (step): depth 2^16, warm 2^13 (base step) + 2^15 (merge step)
//   pallas / Fq (wrap): depth 2^15, warm 2^14 (override_wrap_domain)
// These are the only domains the transaction-snark program commits over
// (measured by instrumenting the prover), so the cache stays minimal — a
// reload restores ~3 bases instead of warming the old 12-domain superset.
import { createRequire } from "module";

const require = createRequire(import.meta.url);
const k = require("kimchi-napi");

const VESTA = { side: "fp", depth: 1 << 16, domains: [13, 15] };
const PALLAS = { side: "fq", depth: 1 << 15, domains: [14] };

const log = (m) => { try { console.log("[SrsCache] " + m); } catch {} };
const hasIDB = () => typeof indexedDB !== "undefined";

function openDB() {
  return new Promise((res, rej) => {
    const r = indexedDB.open("snarky-srs", 1);
    r.onupgradeneeded = () => r.result.createObjectStore("srs");
    r.onsuccess = () => res(r.result);
    r.onerror = () => rej(r.error);
  });
}
async function idbGet(key) {
  const db = await openDB();
  return new Promise((res, rej) => {
    const t = db.transaction("srs", "readonly").objectStore("srs").get(key);
    t.onsuccess = () => res(t.result ?? null);
    t.onerror = () => rej(t.error);
  });
}
async function idbPut(key, val) {
  const db = await openDB();
  return new Promise((res, rej) => {
    const tx = db.transaction("srs", "readwrite");
    tx.objectStore("srs").put(val, key);
    tx.oncomplete = () => res();
    tx.onerror = () => rej(tx.error);
  });
}

// One domain's basis = one commitment per lagrange polynomial; for domain
// <= srs depth each is a single curve point. Pack to a flat Uint8Array.
function packBasis(polys) {
  const n = polys.length;
  const buf = new Uint8Array(4 + n * 65);
  new DataView(buf.buffer).setUint32(0, n, true);
  let off = 4;
  for (const p of polys) {
    if (p.unshifted.length !== 1) throw new Error("SrsCache: expected single-point lagrange comm");
    const pt = p.unshifted[0];
    buf.set(pt.x.subarray(0, 32), off);
    buf.set(pt.y.subarray(0, 32), off + 32);
    buf[off + 64] = pt.infinity ? 1 : 0;
    off += 65;
  }
  return buf;
}
// `WasmF{p,q}PolyComm` is a napi CLASS (not a plain object): its fields are
// `#[napi(skip)]` and it has a `#[napi(constructor)]`. `set_lagrange_basis`
// unwraps each element as that class, so we must hand back real instances
// (a plain `{ unshifted, shifted }` fails with "Unwrap … from class failed").
// The point objects (`WasmG{Vesta,Pallas}`) are `#[napi(object)]`, so plain
// `{ x, y, infinity }` is fine for them; under emnapi/wasm the byte fields
// marshal from Uint8Array (no distinct Buffer type in wasm).
function unpackBasis(buf, PolyComm) {
  const dv = new DataView(buf.buffer, buf.byteOffset, buf.byteLength);
  const n = dv.getUint32(0, true);
  const polys = new Array(n);
  let off = 4;
  for (let i = 0; i < n; i++) {
    const pt = { x: buf.slice(off, off + 32), y: buf.slice(off + 32, off + 64), infinity: buf[off + 64] === 1 };
    polys[i] = new PolyComm([pt], undefined);
    off += 65;
  }
  return polys;
}

async function buildOne(cfg) {
  const create = cfg.side === "fp" ? k.caml_fp_srs_create : k.caml_fq_srs_create;
  const getLB = cfg.side === "fp" ? k.caml_fp_srs_get_lagrange_basis : k.caml_fq_srs_get_lagrange_basis;
  const setLB = cfg.side === "fp" ? k.caml_fp_srs_set_lagrange_basis : k.caml_fq_srs_set_lagrange_basis;
  const PolyComm = cfg.side === "fp" ? k.WasmFpPolyComm : k.WasmFqPolyComm;

  const srs = create(cfg.depth); // deterministic g-vector, ~1s
  const key = `srs-${cfg.side}-${cfg.depth}`;

  let cached = null;
  if (hasIDB()) { try { cached = await idbGet(key); } catch { cached = null; } }

  // Per-domain: restore from cache if present, else warm (and re-cache).
  // Keeps a partial/stale cache (e.g. from a build with different domains)
  // correct — any missing domain is just warmed lazily.
  const store = cached || {};
  let restored = 0, warmed = 0, dirty = false;
  for (const d of cfg.domains) {
    if (store[d]) {
      setLB(srs, 1 << d, unpackBasis(store[d], PolyComm));
      restored++;
    } else {
      store[d] = packBasis(getLB(srs, 1 << d)); // getLB warms + returns
      warmed++; dirty = true;
    }
  }
  if (dirty && hasIDB()) {
    try { await idbPut(key, store); } catch (e) { log("cache write failed: " + e); }
  }
  log(`${cfg.side} lagrange basis: restored ${restored}, warmed ${warmed}` + (hasIDB() ? "" : " (no cache)"));
  return { srs, size: cfg.depth };
}

// EffectFnAff form: (onError, onSuccess) => canceler
export const buildCachedSrsImpl = (onError, onSuccess) => {
  (async () => {
    const vestaSrs = await buildOne(VESTA);
    const pallasSrs = await buildOne(PALLAS);
    return { pallasSrs, vestaSrs };
  })().then(onSuccess, onError);
  return (_c, _oce, ocs) => ocs();
};
