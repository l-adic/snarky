// Parity harness for PastaCurve.js.
//
// Verifies that the vendored projective curve arithmetic produces
// affine-coordinate results identical to the existing arkworks-backed FFI
// in `snarky-crypto`. Comparison is at the affine level — projective
// representations are not canonical (different (X,Y,Z) can encode the
// same point), so both sides are normalized via `.toAffine()` before
// comparing the (x, y) coordinates as BigInts.
//
// Run:  node packages/curves/test/curve-parity-harness.mjs
// Exit: 0 on success; non-zero with a diagnostic message on first mismatch.

import { createRequire } from "module";
import {
  Pallas,
  Vesta,
  GroupMapPallas,
  pallasGeneratorProjective,
  vestaGeneratorProjective,
  pallasEndoBase,
  pallasEndoScalar,
  vestaEndoBase,
  vestaEndoScalar,
  projectiveZero,
} from "../src/Snarky/Curves/PastaCurve.js";

const require = createRequire(import.meta.url);
const crypto = require("snarky-crypto");

const N_ADD = 500;
const N_SCALE = 100;
const N_GROUPMAP = 200;

let failures = 0;
function fail(msg) {
  console.error("  FAIL: " + msg);
  failures++;
}

// ----------------------------------------------------------------------------
// Bridges: FFI External <-> our projective representation
// ----------------------------------------------------------------------------

// Convert an FFI external curve point to our affine {x, y, infinity}.
// `pallasGroupToAffine` returns `null` (infinity) or `[xExt, yExt]` where the
// coordinate Externals are the curve's base field. Pasta cycle: Pallas base =
// Vesta scalar = modulus P, Vesta base = Pallas scalar = modulus Q.
function ffiToAffineP(ext) {
  const r = crypto.pallasGroupToAffine(ext);
  if (r === null || r === undefined) return { x: 0n, y: 0n, infinity: true };
  return {
    x: BigInt(crypto.vestaScalarfieldToBigint(r[0])),
    y: BigInt(crypto.vestaScalarfieldToBigint(r[1])),
    infinity: false,
  };
}
function ffiToAffineV(ext) {
  const r = crypto.vestaGroupToAffine(ext);
  if (r === null || r === undefined) return { x: 0n, y: 0n, infinity: true };
  return {
    x: BigInt(crypto.pallasScalarfieldToBigint(r[0])),
    y: BigInt(crypto.pallasScalarfieldToBigint(r[1])),
    infinity: false,
  };
}

// Convert an affine point to our projective.
function affineToProj(affine) {
  if (affine.infinity) return projectiveZero;
  return { x: affine.x, y: affine.y, z: 1n };
}

// Compare affine points by coordinate.
function affineEq(a, b) {
  if (a.infinity && b.infinity) return true;
  if (a.infinity !== b.infinity) return false;
  return a.x === b.x && a.y === b.y;
}
function affineFmt(a) {
  return a.infinity ? "INF" : `(${a.x}, ${a.y})`;
}

// ----------------------------------------------------------------------------
// Step 1: constants match the FFI
// ----------------------------------------------------------------------------
{
  // generators
  const genFFI_P = ffiToAffineP(crypto.pallasGroupGenerator());
  const ourGenP = Pallas.toAffine({ ...pallasGeneratorProjective, z: 1n });
  if (!affineEq(genFFI_P, ourGenP)) {
    fail(`Pallas generator mismatch: FFI=${affineFmt(genFFI_P)}, JS=${affineFmt(ourGenP)}`);
  }
  const genFFI_V = ffiToAffineV(crypto.vestaGroupGenerator());
  const ourGenV = Vesta.toAffine({ ...vestaGeneratorProjective, z: 1n });
  if (!affineEq(genFFI_V, ourGenV)) {
    fail(`Vesta generator mismatch: FFI=${affineFmt(genFFI_V)}, JS=${affineFmt(ourGenV)}`);
  }

  // endo constants — these return field Externals; convert via the matching
  // field's *ToBigint per the Pasta cycle:
  //   pallasEndoBase   :: VestaScalarField (= Pallas base, modulus P)  → vestaScalarfieldToBigint
  //   pallasEndoScalar :: PallasScalarField (modulus Q)                → pallasScalarfieldToBigint
  //   vestaEndoBase    :: PallasScalarField (= Vesta base, modulus Q)  → pallasScalarfieldToBigint
  //   vestaEndoScalar  :: VestaScalarField (modulus P)                 → vestaScalarfieldToBigint
  const endoBaseFFI_P = BigInt(crypto.vestaScalarfieldToBigint(crypto.pallasEndoBase()));
  if (endoBaseFFI_P !== pallasEndoBase) fail(`Pallas endoBase mismatch: FFI=${endoBaseFFI_P}, JS=${pallasEndoBase}`);
  const endoScalarFFI_P = BigInt(crypto.pallasScalarfieldToBigint(crypto.pallasEndoScalar()));
  if (endoScalarFFI_P !== pallasEndoScalar) fail(`Pallas endoScalar mismatch: FFI=${endoScalarFFI_P}, JS=${pallasEndoScalar}`);
  const endoBaseFFI_V = BigInt(crypto.pallasScalarfieldToBigint(crypto.vestaEndoBase()));
  if (endoBaseFFI_V !== vestaEndoBase) fail(`Vesta endoBase mismatch: FFI=${endoBaseFFI_V}, JS=${vestaEndoBase}`);
  const endoScalarFFI_V = BigInt(crypto.vestaScalarfieldToBigint(crypto.vestaEndoScalar()));
  if (endoScalarFFI_V !== vestaEndoScalar) fail(`Vesta endoScalar mismatch: FFI=${endoScalarFFI_V}, JS=${vestaEndoScalar}`);

  // Weierstrass params (a should be 0, b should be 5 for both)
  const aFFI_P = BigInt(crypto.vestaScalarfieldToBigint(crypto.pallasGroupWeierstrassA()));
  if (aFFI_P !== 0n) fail(`Pallas Weierstrass a mismatch: FFI=${aFFI_P}, JS=0`);
  const bFFI_P = BigInt(crypto.vestaScalarfieldToBigint(crypto.pallasGroupWeierstrassB()));
  if (bFFI_P !== 5n) fail(`Pallas Weierstrass b mismatch: FFI=${bFFI_P}, JS=5`);
  const aFFI_V = BigInt(crypto.pallasScalarfieldToBigint(crypto.vestaGroupWeierstrassA()));
  if (aFFI_V !== 0n) fail(`Vesta Weierstrass a mismatch: FFI=${aFFI_V}, JS=0`);
  const bFFI_V = BigInt(crypto.pallasScalarfieldToBigint(crypto.vestaGroupWeierstrassB()));
  if (bFFI_V !== 5n) fail(`Vesta Weierstrass b mismatch: FFI=${bFFI_V}, JS=5`);

  if (failures === 0) console.log("✓ constants match FFI (generators, endo, Weierstrass)");
  if (failures) process.exit(1);
}

// ----------------------------------------------------------------------------
// Step 2-N: group ops parity
// ----------------------------------------------------------------------------
function runCurve(label, Curve, ffiOps, rand, scalarRand, toAffineFFI) {
  console.log(`\n── ${label} ──`);

  // Add / sub / negate / equal
  for (let i = 0; i < N_ADD; i++) {
    const aExt = rand(2 * i);
    const bExt = rand(2 * i + 1);
    const aAff = toAffineFFI(aExt);
    const bAff = toAffineFFI(bExt);
    const aProj = affineToProj(aAff);
    const bProj = affineToProj(bAff);

    // sanity: FFI points must be on our curve
    if (!Curve.isOnCurve(aProj)) {
      fail(`#${i} FFI point not on JS curve: ${affineFmt(aAff)}`);
      return;
    }

    // add
    {
      const sumFFI = toAffineFFI(ffiOps.add(aExt, bExt));
      const sumJS = Curve.toAffine(Curve.add(aProj, bProj));
      if (!affineEq(sumFFI, sumJS)) {
        fail(`add #${i}: a=${affineFmt(aAff)}, b=${affineFmt(bAff)}, FFI=${affineFmt(sumFFI)}, JS=${affineFmt(sumJS)}`);
        return;
      }
    }
    // double via add(a, a)
    {
      const doubleFFI = toAffineFFI(ffiOps.add(aExt, aExt));
      const doubleJS = Curve.toAffine(Curve.double(aProj));
      if (!affineEq(doubleFFI, doubleJS)) {
        fail(`double #${i}: a=${affineFmt(aAff)}, FFI=${affineFmt(doubleFFI)}, JS=${affineFmt(doubleJS)}`);
        return;
      }
    }
    // negate
    {
      const negFFI = toAffineFFI(ffiOps.neg(aExt));
      const negJS = Curve.toAffine(Curve.negate(aProj));
      if (!affineEq(negFFI, negJS)) {
        fail(`negate #${i}: a=${affineFmt(aAff)}, FFI=${affineFmt(negFFI)}, JS=${affineFmt(negJS)}`);
        return;
      }
    }
    // equal: a == a, a != b (assuming a, b are different random points)
    {
      const aEqA = ffiOps.eq(aExt, aExt);
      const aEqB = ffiOps.eq(aExt, bExt);
      if (aEqA !== Curve.equal(aProj, aProj)) {
        fail(`eq(a,a) #${i}: FFI=${aEqA}, JS=${Curve.equal(aProj, aProj)}`);
        return;
      }
      if (aEqB !== Curve.equal(aProj, bProj)) {
        fail(`eq(a,b) #${i}: FFI=${aEqB}, JS=${Curve.equal(aProj, bProj)}`);
        return;
      }
    }
  }
  console.log(`  ✓ add/double/negate/equal on ${N_ADD} samples`);

  // Scalar multiplication
  for (let i = 0; i < N_SCALE; i++) {
    const pExt = rand(3 * i + 100000);
    const sBig = scalarRand(i);
    const pProj = affineToProj(toAffineFFI(pExt));

    const sgFFI_ext = ffiOps.scale(sBig, pExt);
    const sgFFI = toAffineFFI(sgFFI_ext);
    const sgJS = Curve.toAffine(Curve.scale(pProj, sBig));
    if (!affineEq(sgFFI, sgJS)) {
      fail(`scale #${i}: s=${sBig}, FFI=${affineFmt(sgFFI)}, JS=${affineFmt(sgJS)}`);
      return;
    }
  }
  console.log(`  ✓ scale on ${N_SCALE} samples`);
}

runCurve(
  "Pallas",
  Pallas,
  {
    add: (a, b) => crypto.pallasGroupAdd(a, b),
    neg: (a) => crypto.pallasGroupNeg(a),
    eq: (a, b) => crypto.pallasGroupEq(a, b),
    // FFI's pallasGroupScale signature: (point, scalar)
    scale: (sBig, p) => crypto.pallasGroupScale(p, crypto.pallasScalarfieldFromBigint(sBig)),
  },
  (seed) => crypto.pallasGroupRand(seed),
  (i) => BigInt(crypto.pallasScalarfieldToBigint(crypto.pallasScalarfieldRand(i + 7777777))),
  ffiToAffineP,
);

runCurve(
  "Vesta",
  Vesta,
  {
    add: (a, b) => crypto.vestaGroupAdd(a, b),
    neg: (a) => crypto.vestaGroupNeg(a),
    eq: (a, b) => crypto.vestaGroupEq(a, b),
    scale: (sBig, p) => crypto.vestaGroupScale(p, crypto.vestaScalarfieldFromBigint(sBig)),
  },
  (seed) => crypto.vestaGroupRand(seed),
  (i) => BigInt(crypto.vestaScalarfieldToBigint(crypto.vestaScalarfieldRand(i + 7777777))),
  ffiToAffineV,
);

// ----------------------------------------------------------------------------
// Step: GroupMapPallas parity vs FFI's _pallasGroupMap
// ----------------------------------------------------------------------------
// GroupMapPallas: pointwise equality vs FFI's pallasGroupMap is NOT expected.
// Our vendored impl is the o1js SHALLUE–VAN DE WOESTIJNE construction; the
// FFI uses kimchi's BW19 (BWParameters). Both produce points on the same
// curve, but for a given input they produce *different* points — and
// `_pallasGroupMap` is test-only in our PS layer anyway. We instead verify
// the WEAKER (still load-bearing) property that the decoded JS point lies on
// the Pallas curve — i.e. our GroupMap is a correct hash-to-curve, even if
// not the same one the FFI uses.
function runGroupMapPallas() {
  console.log("\n── GroupMapPallas (Shallue–vdW; on-curve only, no FFI pointwise parity) ──");
  function fieldToGroupJS(t) {
    const xs = GroupMapPallas.potentialXs(t);
    for (const x of xs) {
      const p = GroupMapPallas.tryDecode(x);
      if (p !== undefined) return p;
    }
    return undefined;
  }
  let decoded = 0;
  for (let i = 0; i < N_GROUPMAP; i++) {
    const tExt = crypto.vestaScalarfieldRand(i + 12345);
    const tBig = BigInt(crypto.vestaScalarfieldToBigint(tExt));
    const pt = fieldToGroupJS(tBig);
    if (pt === undefined) continue; // not every t decodes; that's expected for SwvW
    decoded++;
    // verify y^2 = x^3 + b on Pallas (a = 0, b = 5)
    const proj = { x: pt.x, y: pt.y, z: 1n };
    if (!Pallas.isOnCurve(proj)) {
      fail(`groupMap #${i}: decoded point not on Pallas: (${pt.x}, ${pt.y}) (t=${tBig})`);
      return;
    }
  }
  console.log(`  ✓ fieldToGroup on ${decoded}/${N_GROUPMAP} samples (rest were non-decodable t's, expected for SwvW)`);
}
runGroupMapPallas();

if (failures > 0) {
  console.error(`\n✗ ${failures} parity failure(s)`);
  process.exit(1);
}

console.log("\n✓ PastaCurve parity OK");
