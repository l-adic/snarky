// blakejs is CJS — default-import gives module.exports (the `{ blake2bHex, … }`
// object); a named import does NOT work here. 16-byte (128-bit) digest, hex.
import blakejs from "blakejs";

export const srsFingerprint = (bytes) => blakejs.blake2bHex(bytes, undefined, 16);
