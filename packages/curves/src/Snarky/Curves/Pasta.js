// Pure-JS Pasta scalar-field and curve operations, backed by the vendored
// o1js implementations in `PastaField.js` and `PastaCurve.js`.
//
// Runtime representations exposed to PureScript (PS treats them as opaque
// foreign types, so the JS rep can change freely without touching .purs
// files):
//
//   PallasScalarField :: bigint                       (Fq, modulus Q)
//   VestaScalarField  :: bigint                       (Fp, modulus P)
//   PallasG           :: { x: bigint, y: bigint, z: bigint }   (Jacobian)
//   VestaG            :: { x: bigint, y: bigint, z: bigint }
//
// Previously these were opaque `napi::External<Fp>` / `Pallas` handles
// returned by the `snarky-crypto` crate. Migrating to BigInt + the
// PastaCurve.js projective rep is the foundational step for the kimchi-napi
// swap — the upstream binding takes/returns 32-byte LE buffers, which we
// convert at the FFI boundary using `Fp.toBytesLE / fromBytesLE`.
//
// Two test-only / placeholder paths still call into `snarky-crypto` via thin
// bigint↔External conversion shims: `_pallasBW19Params` / `_vestaBW19Params`
// (curve constants in a parametrization PastaCurve doesn't expose) and
// `_pallasGroupMap` / `_vestaGroupMap` (BW19 hash-to-curve; PastaCurve's
// GroupMapPallas uses Shallue-vdW — different math, different output).
// Both are slated for replacement/removal in a later slice; until then they
// preserve byte-for-byte compatibility with existing tests.

import { createRequire } from 'module';
import {
  Fp,
  Fq,
  P,
  Q,
  Pallas,
  Vesta,
  pallasEndoBase,
  pallasEndoScalar,
  vestaEndoBase,
  vestaEndoScalar,
  projectiveZero,
  projectiveFromAffine,
} from 'pasta-runtime';

const require = createRequire(import.meta.url);
const napi = require('snarky-crypto');
// `pasta-runtime` is an npm workspace package (packages/pasta-runtime/) that
// bundles the vendored o1js field + curve + Poseidon JS. Importing by name
// (rather than via a relative `./PastaField.js` path) sidesteps spago's
// foreign-js copy step, which doesn't track sibling-file dependencies and
// would leave `output/<Module>/foreign.js` with broken imports.

// ============================================================================
// SHIMS — bigint↔snarky-crypto External, for the few remaining test-only
// snarky-crypto callsites (`_pallas/vestaBW19Params`, `_pallas/vestaGroupMap`)
// kept until BW19 hash-to-curve is removed/replaced.
// ============================================================================

const toFpExt = (b) => napi.vestaScalarfieldFromBigint(b);   // Fp ext (= VestaScalarField in snarky-crypto naming)
const fromFpExt = (e) => napi.vestaScalarfieldToBigint(e);
const toFqExt = (b) => napi.pallasScalarfieldFromBigint(b);  // Fq ext (= PallasScalarField)
const fromFqExt = (e) => napi.pallasScalarfieldToBigint(e);

// ============================================================================
// PALLAS — scalar field = Fq, base field = Fp
// ============================================================================

// Pallas scalar-field operations (Fq, modulus Q)
export const _pallasZero = () => 0n;
export const _pallasOne = () => 1n;
export const _pallasMul = (x) => (y) => Fq.mul(x, y);
export const _pallasAdd = (x) => (y) => Fq.add(x, y);
export const _pallasSub = (x) => (y) => Fq.sub(x, y);
export const _pallasDiv = (x) => (y) => {
  const r = Fq.div(x, y);
  if (r === undefined) throw new Error("_pallasDiv: division by zero");
  return r;
};
export const _pallasInvert = (x) => {
  const r = Fq.inverse(x);
  if (r === undefined) throw new Error("_pallasInvert: not invertible (zero?)");
  return r;
};
export const _pallasEq = (x) => (y) => Fq.equal(x, y);
export const _pallasToString = (x) => x.toString();
export const _pallasRand = (seed) =>
  // Match snarky-crypto's seed-based RNG so tests stay deterministic.
  // For now, use the snarky-crypto path via shim until we drop the crate.
  fromFqExt(napi.pallasScalarfieldRand(seed));
export const _pallasFromBigInt = (x) => Fq.fromBigint(x);
export const _pallasModulus = () => Q;
export const _pallasToBigInt = (x) => Fq.toBigint(x);
export const _pallasPow = (base) => (exponent) => Fq.power(base, exponent);
export const _pallasScalarFieldFromHexLe = (hex) => Fq.fromHexLE(hex);
export const _pallasScalarFieldToHexLe = (x) => Fq.toHexLE(x);

// Pallas Weierstrass parameters — y^2 = x^3 + 5 in Fp (Pallas.base = Fp).
export const _pallasWeierstrassA = () => Pallas.a;
export const _pallasWeierstrassB = () => Pallas.b;

// Pallas group element operations (PallasG = projective Jacobian in Fp)
export const _pallasGroupAdd = (p1) => (p2) => Pallas.add(p1, p2);
export const _pallasGroupIdentity = () => projectiveZero;
export const _pallasGroupGenerator = () => Pallas.one;
export const _pallasGroupRand = (seed) => {
  // Derive a random group element via seeded-scalar * G. Stays test-only.
  const s = fromFqExt(napi.pallasScalarfieldRand(seed));
  return Pallas.scale(Pallas.one, s);
};
export const _pallasGroupEq = (p1) => (p2) => Pallas.equal(p1, p2);
export const _pallasGroupToString = (g) => {
  const a = Pallas.toAffine(g);
  if (a.infinity) return "(infinity)";
  return `(${a.x.toString()}, ${a.y.toString()})`;
};
export const _pallasGroupNeg = (g) => Pallas.negate(g);
export const _pallasGroupScale = (scalar) => (g) => Pallas.scale(g, scalar);

// `toAffine` returns `Nothing` for the identity, `Just [x, y]` otherwise.
export function _pallasToAffine(just, nothing, value) {
  const aff = Pallas.toAffine(value);
  if (aff.infinity) return nothing;
  return just([aff.x, aff.y]);
}

export function _pallasFromAffine({ x, y }) {
  return projectiveFromAffine({ x, y, infinity: false });
}

// ============================================================================
// VESTA — scalar field = Fp, base field = Fq
// ============================================================================

export const _vestaScalarFieldZero = () => 0n;
export const _vestaScalarFieldOne = () => 1n;
export const _vestaScalarFieldAdd = (x) => (y) => Fp.add(x, y);
export const _vestaScalarFieldMul = (x) => (y) => Fp.mul(x, y);
export const _vestaScalarFieldSub = (x) => (y) => Fp.sub(x, y);
export const _vestaScalarFieldDiv = (x) => (y) => {
  const r = Fp.div(x, y);
  if (r === undefined) throw new Error("_vestaScalarFieldDiv: division by zero");
  return r;
};
export const _vestaScalarFieldInvert = (x) => {
  const r = Fp.inverse(x);
  if (r === undefined) throw new Error("_vestaScalarFieldInvert: not invertible (zero?)");
  return r;
};
export const _vestaScalarFieldEq = (x) => (y) => Fp.equal(x, y);
export const _vestaScalarFieldToString = (x) => x.toString();
export const _vestaScalarFieldRand = (seed) =>
  fromFpExt(napi.vestaScalarfieldRand(seed));
export const _vestaScalarFieldFromBigInt = (x) => Fp.fromBigint(x);
export const _vestaScalarFieldToBigInt = (x) => Fp.toBigint(x);
export const _vestaScalarFieldPow = (base) => (exponent) => Fp.power(base, exponent);
export const _vestaScalarFieldModulus = () => P;
export const _vestaScalarFieldFromHexLe = (hex) => Fp.fromHexLE(hex);
export const _vestaScalarFieldToHexLe = (x) => Fp.toHexLE(x);

// Vesta Weierstrass parameters — y^2 = x^3 + 5 in Fq (Vesta.base = Fq).
export const _vestaWeierstrassA = () => Vesta.a;
export const _vestaWeierstrassB = () => Vesta.b;

// Vesta group element operations (VestaG = projective Jacobian in Fq)
export const _vestaGroupAdd = (p1) => (p2) => Vesta.add(p1, p2);
export const _vestaGroupIdentity = () => projectiveZero;
export const _vestaGroupGenerator = () => Vesta.one;
export const _vestaGroupRand = (seed) => {
  const s = fromFpExt(napi.vestaScalarfieldRand(seed));
  return Vesta.scale(Vesta.one, s);
};
export const _vestaGroupEq = (p1) => (p2) => Vesta.equal(p1, p2);
export const _vestaGroupToString = (g) => {
  const a = Vesta.toAffine(g);
  if (a.infinity) return "(infinity)";
  return `(${a.x.toString()}, ${a.y.toString()})`;
};
export const _vestaGroupNeg = (g) => Vesta.negate(g);
export const _vestaGroupScale = (scalar) => (g) => Vesta.scale(g, scalar);

export function _vestaToAffine(just, nothing, value) {
  const aff = Vesta.toAffine(value);
  if (aff.infinity) return nothing;
  return just([aff.x, aff.y]);
}

export function _vestaFromAffine({ x, y }) {
  return projectiveFromAffine({ x, y, infinity: false });
}

// ============================================================================
// ENDOMORPHISM CONSTANTS
//
// Per `endo_base` / `endo_scalar` memory note, two distinct uses:
//   _pallasEndoBase   : Pallas.endo_base() ∈ Fp — step's cs.endo (EndoMul gate)
//   _pallasEndoScalar : Pallas.endo_scalar() ∈ Fq — step scalar-challenge expansion
//   _vestaEndoBase    : Vesta.endo_base()  ∈ Fq — wrap's cs.endo
//   _vestaEndoScalar  : Vesta.endo_scalar() ∈ Fp — wrap scalar-challenge expansion
//
// PS-side return types stay `VestaScalarField` / `PallasScalarField`; values
// are now plain bigints from PastaCurve's constants.
// ============================================================================

export const _pallasEndoBase = () => pallasEndoBase;
export const _pallasEndoScalar = () => pallasEndoScalar;
export const _vestaEndoBase = () => vestaEndoBase;
export const _vestaEndoScalar = () => vestaEndoScalar;

// ============================================================================
// SQUARE ROOTS / QUADRATIC RESIDUE
// ============================================================================

export const _pallasIsSquare = (x) => Fq.isSquare(x);
export const _pallasSqrt = (just) => (nothing) => (x) => {
  if (!Fq.isSquare(x)) return nothing;
  return just(Fq.sqrt(x));
};

export const _vestaScalarFieldIsSquare = (x) => Fp.isSquare(x);
export const _vestaScalarFieldSqrt = (just) => (nothing) => (x) => {
  if (!Fp.isSquare(x)) return nothing;
  return just(Fp.sqrt(x));
};

// ============================================================================
// BW19 GROUPMAP PARAMETERS + HASH-TO-CURVE (test-only)
//
// PastaCurve's `GroupMapPallas` implements Shallue–van de Woestijne; the
// snarky-crypto FFI uses Brier–Walliams 2019 (`BWParameters`). These produce
// different points for the same input. The PS-side `_pallasGroupMap` /
// `_vestaGroupMap` callers are test-only, so we keep snarky-crypto-backed
// BW19 here with bigint↔External shims, and revisit when the test consumer
// is rewritten against the in-circuit GroupMap.
// ============================================================================

export const _pallasBW19Params = () => {
  // snarky-crypto returns Array<External<Fp>>; convert each.
  const raw = napi.pallasBw19Params();
  return raw.map(fromFpExt);
};

export const _vestaBW19Params = () => {
  const raw = napi.vestaBw19Params();
  return raw.map(fromFqExt);
};

// Pallas / Vesta group maps: input `t : BaseField`, output `[x, y]` in
// BaseField. snarky-crypto's `pallas_group_map` / `vesta_group_map` return a
// `(External<F>, External<F>)` tuple of affine coords directly (NOT an
// External<Group>); the napi-rs bridge surfaces that tuple as a JS Array of
// length 2. PallasBaseField = VestaScalarField = Fp; VestaBaseField =
// PallasScalarField = Fq.
export const _pallasGroupMap = (t) => {
  const xy = napi.pallasGroupMap(toFpExt(t));
  return [fromFpExt(xy[0]), fromFpExt(xy[1])];
};

export const _vestaGroupMap = (t) => {
  const xy = napi.vestaGroupMap(toFqExt(t));
  return [fromFqExt(xy[0]), fromFqExt(xy[1])];
};

