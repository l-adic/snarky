// BLAKE2b-256 via `blakejs`. Node's built-in `createHash('blake2b512')`
// is 64-byte output with no digest-size parameter — truncating that
// gives a DIFFERENT value than running BLAKE2b with `digest_size = 32`
// from the start (BLAKE2b mixes the digest length into the IV).
// `blakejs.blake2b(input, key, outlen)` does the init-time
// parameterization correctly, matching OCaml's
// `Digestif.Make_BLAKE2B { digest_size = 32 }` (see
// `mina/src/lib/crypto/blake2/blake2.ml:9`).

import * as blakejs from "blakejs";

const blake2b256Bytes = (str) => {
  // `blakejs.blake2b` accepts string OR Uint8Array; for the bit-packed
  // byte-string we feed (latin-1 chars in [0..255]), interpret each
  // char as a single byte to match OCaml `String.init`-of-`Char.of_int`
  // round-tripping (rather than letting blakejs apply UTF-8 encoding).
  const bytes = new Uint8Array(str.length);
  for (let i = 0; i < str.length; i++) bytes[i] = str.charCodeAt(i) & 0xff;
  return Array.from(blakejs.blake2b(bytes, undefined, 32));
};

export const blake2b256 = blake2b256Bytes;

export const blake2b256Bits = (str) => {
  const bytes = blake2b256Bytes(str);
  const bits = [];
  for (const byte of bytes) {
    for (let i = 0; i < 8; i++) {
      bits.push(((byte >> i) & 1) === 1);
    }
  }
  return bits;
};
