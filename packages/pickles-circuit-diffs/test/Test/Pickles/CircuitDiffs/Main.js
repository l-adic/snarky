// kimchi-napi-backed SRS query helpers for the circuit-diff suite.
//
// PS-side types: `pallas*` ops here take a `CRS VestaG` (Vesta SRS, used by
// Pallas-field/Fq-circuits) and return `AffinePoint Fq` (Vesta point coords).
// `vesta*` ops take `CRS PallasG` and return `AffinePoint Fp`.
//
// The CRS values are `{srs, size}` wrappers from snarky-kimchi's Impl
// modules — `srs` is the underlying `WasmF{p,q}Srs` from kimchi-napi.
//
// kimchi-napi returns curve points as `NapiG{Pallas,Vesta}` objects with
// 32-byte LE buffers for x/y; we decode via `pasta-runtime` fields.

import { createRequire } from 'module';
import { Fp, Fq } from 'pasta-runtime';

const require = createRequire(import.meta.url);
const k = require('kimchi-napi');

const fpFromBytes = (b) => Fp.fromBytesLE(b instanceof Uint8Array ? b : new Uint8Array(b));
const fqFromBytes = (b) => Fq.fromBytesLE(b instanceof Uint8Array ? b : new Uint8Array(b));

// `pallas*` ops use a Vesta SRS (PS-side `CRS VestaG`); coords land in Fq.
export const pallasSrsBlindingGenerator = (crs) => {
  const h = k.caml_fp_srs_h(crs.srs);
  return { x: fqFromBytes(h.x), y: fqFromBytes(h.y) };
};

export const vestaSrsBlindingGenerator = (crs) => {
  const h = k.caml_fq_srs_h(crs.srs);
  return { x: fpFromBytes(h.x), y: fpFromBytes(h.y) };
};

// Lagrange-basis commitment lookups. kimchi-napi exposes the lookup as a
// `PolyComm` over the appropriate curve; we expose the first `unshifted`
// chunk (which is the whole comm for non-chunked VKs).
export const pallasSrsLagrangeCommitmentAt = (crs) => (domainLog2) => (i) => {
  const domainSize = 1 << domainLog2;
  const pc = k.caml_fp_srs_lagrange_commitment(crs.srs, domainSize, i);
  const p = pc.unshifted[0];
  return { x: fqFromBytes(p.x), y: fqFromBytes(p.y) };
};

export const vestaSrsLagrangeCommitmentAt = (crs) => (domainLog2) => (i) => {
  const domainSize = 1 << domainLog2;
  const pc = k.caml_fq_srs_lagrange_commitment(crs.srs, domainSize, i);
  const p = pc.unshifted[0];
  return { x: fpFromBytes(p.x), y: fpFromBytes(p.y) };
};
