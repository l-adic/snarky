// Parity harness for PastaField.js.
//
// Verifies that every public op in `Snarky/Curves/PastaField.js` produces
// the same canonical integer (and the same canonical 32-byte LE encoding)
// as the existing arkworks-backed FFI in `snarky-crypto`. The harness is
// the load-bearing artifact that lets us trust the pure-JS field before
// any consumer is rewired to use it.
//
// Run:  node packages/curves/test/parity-harness.mjs
// Exit: 0 on success; non-zero with a diagnostic message on first mismatch.
//
// Iteration counts are tuned so the whole harness finishes in seconds.
// Bump N or N_POW locally if you want a longer soak.

import { createRequire } from "module";
import * as PF from "../src/Snarky/Curves/PastaField.js";

// snarky-crypto's package.json points `main` at the .node directly, which
// Node's ESM loader can't open. Bridge through createRequire (CommonJS).
const require = createRequire(import.meta.url);
const crypto = require("snarky-crypto");

const N = 5000;       // basic ops
const N_INV = 1000;   // inverse / div are slower
const N_POW = 200;    // power is the slowest (large exponents)

let failures = 0;
function fail(msg) {
  console.error("  FAIL: " + msg);
  failures++;
}

// ----------------------------------------------------------------------------
// Step 1: constants match the FFI's modulus oracles.
// ----------------------------------------------------------------------------
// Note: this build of `snarky-crypto` marshals `napi::BigInt` returns to
// JS as decimal strings (not native BigInt). Coerce with `BigInt(...)` at
// every bridge point.
{
  const fpFromFFI = BigInt(crypto.vestaScalarfieldModulus());
  const fqFromFFI = BigInt(crypto.pallasScalarfieldModulus());
  if (fpFromFFI !== PF.P) fail(`P (Vesta scalar / Pallas base) mismatch: FFI=${fpFromFFI}, JS=${PF.P}`);
  if (fqFromFFI !== PF.Q) fail(`Q (Pallas scalar / Vesta base) mismatch: FFI=${fqFromFFI}, JS=${PF.Q}`);
  if (failures === 0) console.log("✓ moduli match FFI");
  if (failures) process.exit(1);
}

// ----------------------------------------------------------------------------
// Helpers: bridge between (BigInt, JS field) and (External, FFI).
// ----------------------------------------------------------------------------
function makeBridge(label, randFFI, fromBig, toBig, ops, hexOps, JSField) {
  // randFFI(seed): External -> sample value, deterministic in `seed`
  // fromBig(b): BigInt -> External
  // toBig(e):   External -> BigInt
  // ops:        { add, sub, mul, div, invert, pow, eq } operating on Externals
  // hexOps:     { toHex, fromHex } (External -> hex string, etc.)
  // JSField:    the corresponding PastaField specialization
  return { label, randFFI, fromBig, toBig, ops, hexOps, JSField };
}

const pallasScalar = makeBridge(
  "PallasScalar (Fq)",
  (seed) => toBig_pallas(crypto.pallasScalarfieldRand(seed)),
  (b) => crypto.pallasScalarfieldFromBigint(b),
  toBig_pallas,
  {
    add: crypto.pallasScalarfieldAdd,
    sub: crypto.pallasScalarfieldSub,
    mul: crypto.pallasScalarfieldMul,
    div: crypto.pallasScalarfieldDiv,
    invert: crypto.pallasScalarfieldInvert,
    pow: crypto.pallasScalarfieldPow,
    eq: crypto.pallasScalarfieldEq,
  },
  {
    toHex: crypto.pallasScalarFieldToHexLe ?? crypto.pallasScalarfieldToHexLe,
    fromHex: crypto.pallasScalarFieldFromHexLe ?? crypto.pallasScalarfieldFromHexLe,
  },
  PF.PallasScalar,
);

const vestaScalar = makeBridge(
  "VestaScalar (Fp)",
  (seed) => toBig_vesta(crypto.vestaScalarfieldRand(seed)),
  (b) => crypto.vestaScalarfieldFromBigint(b),
  toBig_vesta,
  {
    add: crypto.vestaScalarfieldAdd,
    sub: crypto.vestaScalarfieldSub,
    mul: crypto.vestaScalarfieldMul,
    div: crypto.vestaScalarfieldDiv,
    invert: crypto.vestaScalarfieldInvert,
    pow: crypto.vestaScalarfieldPow,
    eq: crypto.vestaScalarfieldEq,
  },
  {
    toHex: crypto.vestaScalarFieldToHexLe ?? crypto.vestaScalarfieldToHexLe,
    fromHex: crypto.vestaScalarFieldFromHexLe ?? crypto.vestaScalarfieldFromHexLe,
  },
  PF.VestaScalar,
);

function toBig_pallas(ext) {
  return BigInt(crypto.pallasScalarfieldToBigint(ext));
}
function toBig_vesta(ext) {
  return BigInt(crypto.vestaScalarfieldToBigint(ext));
}

// ----------------------------------------------------------------------------
// Step 2: binary ops (add, sub, mul, div) — N samples.
// Step 3: unary ops (invert, square) — N_INV samples.
// Step 4: pow with moderate exponents — N_POW samples.
// Step 5: encoding round-trip (toHexLE / fromHexLE).
// ----------------------------------------------------------------------------
function runBridge(b) {
  console.log(`\n── ${b.label} ──`);

  // Binary ops
  for (let i = 0; i < N; i++) {
    const aBig = b.randFFI(2 * i);
    const bBig = b.randFFI(2 * i + 1);
    const aExt = b.fromBig(aBig);
    const bExt = b.fromBig(bBig);

    // add
    {
      const jsResult = b.JSField.add(aBig, bBig);
      const ffiResult = b.toBig(b.ops.add(aExt, bExt));
      if (jsResult !== ffiResult) {
        fail(`add #${i}: a=${aBig}, b=${bBig}, js=${jsResult}, ffi=${ffiResult}`);
        return;
      }
    }
    // sub
    {
      const jsResult = b.JSField.sub(aBig, bBig);
      const ffiResult = b.toBig(b.ops.sub(aExt, bExt));
      if (jsResult !== ffiResult) {
        fail(`sub #${i}: a=${aBig}, b=${bBig}, js=${jsResult}, ffi=${ffiResult}`);
        return;
      }
    }
    // mul
    {
      const jsResult = b.JSField.mul(aBig, bBig);
      const ffiResult = b.toBig(b.ops.mul(aExt, bExt));
      if (jsResult !== ffiResult) {
        fail(`mul #${i}: a=${aBig}, b=${bBig}, js=${jsResult}, ffi=${ffiResult}`);
        return;
      }
    }
    // eq (both equal and not-equal paths)
    {
      const eqJS = b.JSField.equal(aBig, aBig);
      const eqFFI = b.ops.eq(aExt, aExt);
      if (eqJS !== eqFFI) {
        fail(`eq(a,a) #${i}: a=${aBig}, js=${eqJS}, ffi=${eqFFI}`);
        return;
      }
      const neqJS = b.JSField.equal(aBig, bBig);
      const neqFFI = b.ops.eq(aExt, bExt);
      if (neqJS !== neqFFI) {
        fail(`eq(a,b) #${i}: a=${aBig}, b=${bBig}, js=${neqJS}, ffi=${neqFFI}`);
        return;
      }
    }
  }
  console.log(`  ✓ add/sub/mul/eq on ${N} samples`);

  // div + invert + square
  for (let i = 0; i < N_INV; i++) {
    let aBig = b.randFFI(3 * i + 1000000);
    let bBig = b.randFFI(3 * i + 1 + 1000000);
    if (bBig === 0n) bBig = 1n;
    const aExt = b.fromBig(aBig);
    const bExt = b.fromBig(bBig);

    // invert
    {
      const jsResult = b.JSField.inverse(bBig);
      const ffiResult = b.toBig(b.ops.invert(bExt));
      if (jsResult !== ffiResult) {
        fail(`invert #${i}: x=${bBig}, js=${jsResult}, ffi=${ffiResult}`);
        return;
      }
      // a*invert(a) === 1
      const product = b.JSField.mul(bBig, jsResult);
      if (product !== 1n) {
        fail(`mul(a, invert(a)) != 1 #${i}: a=${bBig}, got ${product}`);
        return;
      }
    }
    // div
    {
      const jsResult = b.JSField.div(aBig, bBig);
      const ffiResult = b.toBig(b.ops.div(aExt, bExt));
      if (jsResult !== ffiResult) {
        fail(`div #${i}: a=${aBig}, b=${bBig}, js=${jsResult}, ffi=${ffiResult}`);
        return;
      }
    }
    // square via mul
    {
      const jsResult = b.JSField.square(aBig);
      const ffiResult = b.toBig(b.ops.mul(aExt, aExt));
      if (jsResult !== ffiResult) {
        fail(`square #${i}: a=${aBig}, js=${jsResult}, ffi=${ffiResult}`);
        return;
      }
    }
  }
  console.log(`  ✓ invert/div/square on ${N_INV} samples`);

  // power — small/moderate exponents to keep it cheap, but include some
  // large exponents to exercise the full square-and-multiply loop.
  for (let i = 0; i < N_POW; i++) {
    const baseBig = b.randFFI(4 * i + 2000000);
    // mix of small and large exponents
    const exp = i % 4 === 0 ? BigInt(i) : b.randFFI(4 * i + 1 + 2000000);
    const baseExt = b.fromBig(baseBig);

    const jsResult = b.JSField.power(baseBig, exp);
    const ffiResult = b.toBig(b.ops.pow(baseExt, exp));
    if (jsResult !== ffiResult) {
      fail(`pow #${i}: base=${baseBig}, exp=${exp}, js=${jsResult}, ffi=${ffiResult}`);
      return;
    }
  }
  console.log(`  ✓ power on ${N_POW} samples`);

  // hex LE 32 codec round-trip and cross-check against FFI's hex format
  for (let i = 0; i < N_INV; i++) {
    const xBig = b.randFFI(5 * i + 3000000);
    const xExt = b.fromBig(xBig);

    // JS toHexLE -> FFI fromHexLE -> toBig should equal xBig
    const jsHex = b.JSField.toHexLE(xBig);
    const fromJSHex = b.toBig(b.hexOps.fromHex(jsHex));
    if (fromJSHex !== xBig) {
      fail(`hex codec: JS toHexLE not parsed back to same BigInt by FFI fromHex #${i}: x=${xBig}, jsHex=${jsHex}, fromHex=${fromJSHex}`);
      return;
    }

    // FFI toHexLE -> JS fromHexLE should equal xBig
    const ffiHex = b.hexOps.toHex(xExt);
    const fromFFIHex = b.JSField.fromHexLE(ffiHex);
    if (fromFFIHex !== xBig) {
      fail(`hex codec: FFI toHexLE not parsed back to same BigInt by JS fromHex #${i}: x=${xBig}, ffiHex=${ffiHex}, fromHex=${fromFFIHex}`);
      return;
    }

    // Both sides produce the same hex
    if (jsHex !== ffiHex) {
      fail(`hex codec strings differ #${i}: x=${xBig}, js="${jsHex}", ffi="${ffiHex}"`);
      return;
    }
  }
  console.log(`  ✓ toHexLE / fromHexLE on ${N_INV} samples`);
}

runBridge(pallasScalar);
runBridge(vestaScalar);

if (failures > 0) {
  console.error(`\n✗ ${failures} parity failure(s)`);
  process.exit(1);
}

console.log("\n✓ PastaField parity OK");
