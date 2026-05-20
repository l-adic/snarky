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
// PastaCurve.js projective rep was the foundational step for the kimchi-napi
// swap — the upstream binding takes/returns 32-byte LE buffers, which we
// convert at the FFI boundary using `Fp.toBytesLE / fromBytesLE`.

import { createHash } from 'node:crypto';
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

// `pasta-runtime` is an npm workspace package (packages/pasta-runtime/) that
// bundles the vendored o1js field + curve + Poseidon JS. Importing by name
// (rather than via a relative `./PastaField.js` path) sidesteps spago's
// foreign-js copy step, which doesn't track sibling-file dependencies and
// would leave `output/<Module>/foreign.js` with broken imports.

// ============================================================================
// DETERMINISTIC SEEDED RNG — for QuickCheck `Arbitrary` over scalar fields
// and group elements. Maps `seed: Int` → 32 LE bytes via SHA-256, then
// reduces mod p. Distribution bias from 256-bit hash → ~254-bit prime is
// ≈ 2^-252, negligible for QuickCheck input generation. Same-seed
// reproducibility is what matters for test repro.
// ============================================================================

function seedToBytes32(seed) {
  const buf = Buffer.alloc(4);
  buf.writeInt32LE(seed | 0);
  return createHash('sha256').update(buf).digest();
}

const seedToFq = (seed) => Fq.fromBigint(Fq.fromBytesLE(seedToBytes32(seed)));
const seedToFp = (seed) => Fp.fromBigint(Fp.fromBytesLE(seedToBytes32(seed)));

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
export const _pallasRand = (seed) => seedToFq(seed);
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
export const _pallasGroupRand = (seed) => Pallas.scale(Pallas.one, seedToFq(seed));
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
export const _vestaScalarFieldRand = (seed) => seedToFp(seed);
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
export const _vestaGroupRand = (seed) => Vesta.scale(Vesta.one, seedToFp(seed));
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
// BW19 GROUPMAP PARAMETERS — production, consumed by
// `Snarky.Circuit.Kimchi.GroupMap.groupMapParams` via `HasBW19.bw19Params`.
//
// Port of `BWParameters::setup()` from `proof-systems/groupmap/src/lib.rs:
// 134-163`, specialized to A=0 short-Weierstrass curves (Pallas / Vesta).
// Returns `[u, fu, sqrt(-3u^2 - u/2)·(1/2), sqrt(-3u^2), (3u^2)^-1]`
// — the same 5-tuple shape the PS-side `bw19Params` instance expects.
//
// The corresponding hash-to-curve (`pallas_group_map` / `vesta_group_map`)
// was deleted alongside this slice — it was only referenced by a Rust-FFI
// parity test that's no longer needed (`Test.Snarky.Circuit.Kimchi
// .GroupMap` was the sole consumer, and it cross-checked the in-circuit
// Shallue-vdW against the Rust BW19 — two different algorithms; the test
// fundamentally couldn't pass anyway and was test-only scaffolding).
// ============================================================================

// Find the smallest x ≥ 1 such that the curve equation at x is nonzero.
// For Pallas / Vesta (A=0, B=5), `x=1` works: `1^3 + 5 = 6 ≠ 0`.
function bw19Setup(F, curveB) {
  // u = smallest i ≥ 1 with i^3 + curveB ≠ 0 in F. For Pallas/Vesta this is 1.
  let u = 1n;
  let fu = F.add(F.power(u, 3n), curveB);
  while (F.equal(fu, 0n)) {
    u = u + 1n;
    fu = F.add(F.power(u, 3n), curveB);
  }
  const threeUSquared = F.mul(F.power(u, 2n), 3n);
  const invThreeUSquared = F.inverse(threeUSquared);
  const sqrtNegThreeUSquared = F.sqrt(F.negate(threeUSquared));
  const twoInv = F.inverse(2n);
  const sqrtNegThreeUSquaredMinusUOver2 = F.mul(F.sub(sqrtNegThreeUSquared, u), twoInv);
  return [u, fu, sqrtNegThreeUSquaredMinusUOver2, sqrtNegThreeUSquared, invThreeUSquared];
}

// Both Pasta curves have COEFF_A=0, COEFF_B=5. The 5-tuple is cached on
// first access — `bw19Setup` is deterministic and pure.
let _pallasBW19ParamsCache = null;
let _vestaBW19ParamsCache = null;

// Pallas's BASE field is Fp (= o1js naming, = VestaScalarField in
// snarky-crypto naming). The PS-side `HasBW19 PallasBaseField PallasG`
// instance reads these as `VestaScalarField` values (same prime).
export const _pallasBW19Params = () => {
  if (_pallasBW19ParamsCache === null) _pallasBW19ParamsCache = bw19Setup(Fp, Pallas.b);
  return _pallasBW19ParamsCache;
};

// Vesta's BASE field is Fq (= PallasScalarField in snarky-crypto naming).
export const _vestaBW19Params = () => {
  if (_vestaBW19ParamsCache === null) _vestaBW19ParamsCache = bw19Setup(Fq, Vesta.b);
  return _vestaBW19ParamsCache;
};

