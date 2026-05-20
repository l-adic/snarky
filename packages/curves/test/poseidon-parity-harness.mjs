// Parity harness for PastaPoseidon.js.
//
// Two-way validation:
//   (1) Permutation byte-for-byte vs kimchi-napi's caml_pasta_fp_poseidon_block_cipher.
//       This is the upstream-aligned reference (Mina's Rust permutation,
//       compiled into the same proof-systems we'll consume in slice 3.3+).
//   (2) Full sponge `Poseidon.hash(input)` vs snarky-crypto's pallas_poseidon_hash.
//       Cross-checks that our sponge construction on top of the permutation
//       also matches the Mina convention (zero-padding, rate-2 absorb, take
//       state[0] as the digest).
//
// Run:  node packages/curves/test/poseidon-parity-harness.mjs
// Exit: 0 on success; non-zero with a diagnostic on first mismatch.

import { createRequire } from "module";
import { Poseidon } from "../src/Snarky/Curves/PastaPoseidon.js";
import {
  Fp,
  bigintToBytes32LE,
  bytes32LEToBigint,
} from "../src/Snarky/Curves/PastaField.js";

const require = createRequire(import.meta.url);
const crypto = require("snarky-crypto");
const kimchiNapi = require("kimchi-napi");

const STATE = 3;          // Kimchi Poseidon state size
const FIELD_BYTES = 32;   // 32-byte LE canonical encoding

const N_PERM = 1000;      // permutation samples vs kimchi-napi
const N_HASH = 500;       // hash samples vs crypto-provider; varied input lengths

let failures = 0;
function fail(msg) {
  console.error("  FAIL: " + msg);
  failures++;
}

// ----------------------------------------------------------------------------
// Helpers: BigInt state <-> 96-byte Uint8Array (3 * 32 bytes LE).
// kimchi-napi's caml_pasta_fp_poseidon_block_cipher takes/returns this shape.
// ----------------------------------------------------------------------------
function stateToBytes(state) {
  const out = new Uint8Array(STATE * FIELD_BYTES);
  for (let i = 0; i < STATE; i++) {
    out.set(bigintToBytes32LE(state[i]), i * FIELD_BYTES);
  }
  return out;
}
function bytesToState(bytes) {
  if (bytes.byteLength !== STATE * FIELD_BYTES) {
    throw new Error(`bytesToState: expected ${STATE * FIELD_BYTES} bytes, got ${bytes.byteLength}`);
  }
  const out = [];
  for (let i = 0; i < STATE; i++) {
    out.push(bytes32LEToBigint(bytes.slice(i * FIELD_BYTES, (i + 1) * FIELD_BYTES)));
  }
  return out;
}

// Deterministic random Fp value via the FFI's rand. (Pallas base = Vesta scalar = modulus P.)
function randFp(seed) {
  return BigInt(crypto.vestaScalarfieldToBigint(crypto.vestaScalarfieldRand(seed)));
}

// ----------------------------------------------------------------------------
// Part 1: permutation parity vs kimchi-napi
// ----------------------------------------------------------------------------
console.log("── permutation vs kimchi-napi.caml_pasta_fp_poseidon_block_cipher ──");
for (let i = 0; i < N_PERM; i++) {
  const initial = [randFp(3 * i), randFp(3 * i + 1), randFp(3 * i + 2)];

  // Reference: kimchi-napi expects/returns Uint8Array of 96 bytes (3 × 32 LE).
  const inBytes = stateToBytes(initial);
  const outBytes = kimchiNapi.caml_pasta_fp_poseidon_block_cipher(inBytes);
  const refState = bytesToState(outBytes);

  // Ours: permute a mutable copy.
  const ourState = [...initial];
  Poseidon.permutation(ourState);

  for (let k = 0; k < STATE; k++) {
    if (ourState[k] !== refState[k]) {
      fail(`perm #${i} state[${k}]: init=${initial[k]}, ref=${refState[k]}, ours=${ourState[k]}`);
      process.exit(1);
    }
  }
}
console.log(`  ✓ permutation on ${N_PERM} random 3-element states`);

// ----------------------------------------------------------------------------
// Part 2: full hash parity vs snarky-crypto.pallas_poseidon_hash
// ----------------------------------------------------------------------------
console.log("\n── Poseidon.hash vs snarky-crypto.pallasPoseidonHash ──");
const empty = Poseidon.hash([]);
const emptyFFI = BigInt(crypto.vestaScalarfieldToBigint(crypto.pallasPoseidonHash([])));
if (empty !== emptyFFI) {
  fail(`hash([]) mismatch: ours=${empty}, ffi=${emptyFFI}`);
}

for (let i = 0; i < N_HASH; i++) {
  // Varied input length: cycle through 1..10 elements.
  const len = (i % 10) + 1;
  const inputBigs = [];
  const inputExts = [];
  for (let k = 0; k < len; k++) {
    const ext = crypto.vestaScalarfieldRand(7 * i + k + 4242);
    inputExts.push(ext);
    inputBigs.push(BigInt(crypto.vestaScalarfieldToBigint(ext)));
  }
  const ours = Poseidon.hash(inputBigs);
  const ffi = BigInt(crypto.vestaScalarfieldToBigint(crypto.pallasPoseidonHash(inputExts)));
  if (ours !== ffi) {
    fail(`hash(len=${len}) #${i}: ours=${ours}, ffi=${ffi}`);
    process.exit(1);
  }
}
console.log(`  ✓ Poseidon.hash on ${N_HASH} samples (varied input lengths) + empty input`);

if (failures > 0) {
  console.error(`\n✗ ${failures} parity failure(s)`);
  process.exit(1);
}

console.log("\n✓ PastaPoseidon parity OK");
