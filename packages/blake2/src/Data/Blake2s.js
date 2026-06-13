// BLAKE2s-256 via `blakejs` (pure JS — works in node AND the browser;
// node's createHash("blake2s256") is node-only). blake2s with
// outlen 32 is exactly blake2s256: the digest size is mixed into the
// IV at init, and 32 is what node used too, so values are identical.
import blakejs from "blakejs";

const blake2s256Bytes = (str) => {
  // Interpret each char as a single byte (latin-1), matching the
  // byte-string convention used by the Blake2b sibling module.
  const bytes = new Uint8Array(str.length);
  for (let i = 0; i < str.length; i++) bytes[i] = str.charCodeAt(i) & 0xff;
  return Array.from(blakejs.blake2s(bytes, undefined, 32));
};

export const blake2s256Bits = (str) => {
  const bytes = blake2s256Bytes(str);
  const bits = [];
  for (const byte of bytes) {
    for (let i = 0; i < 8; i++) {
      bits.push(((byte >> i) & 1) === 1);
    }
  }
  return bits;
};
