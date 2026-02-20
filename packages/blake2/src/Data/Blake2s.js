import { createHash } from "node:crypto";

export const blake2s256Bytes = (str) => {
  const h = createHash("blake2s256");
  h.update(str);
  return Array.from(h.digest());
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
