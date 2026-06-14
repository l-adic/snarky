// Mina-style compressed public-key address (base58check), matching
// MinaProtocol/mina's `non_zero_curve_point` compressed format — the
// `B62q…` string shown by Mina explorers and the GraphQL API.
//
//   base58check( [0xCB, 0x01, 0x01] ++ x_LE(32) ++ [parity(y)] )
//
// The compressed point is { x, is_odd = parity(y) } (the least
// significant bit of y); x is the 32-byte little-endian field encoding
// (exactly what `toHexLe` emits). The three prefix bytes are the
// base58-check version (0xCB = non_zero_curve_point_compressed), the
// non_zero_curve_point bin_prot version (0x01) and the compressed_poly
// bin_prot version (0x01). base58check appends the standard
// double-sha256 4-byte checksum.
import { sha256 } from "@noble/hashes/sha2.js";
import { base58check, hex } from "@scure/base";

const b58check = base58check(sha256);

// [base58 version, non_zero_curve_point version, compressed_poly version]
const VERSION_PREFIX = Uint8Array.of(0xcb, 0x01, 0x01);

// xHexLe, yHexLe :: little-endian hex of the affine coordinates.
export const pubkeyToBase58 = (xHexLe) => (yHexLe) => {
  const x = hex.decode(xHexLe);
  const isOdd = hex.decode(yHexLe)[0] & 1;
  const data = new Uint8Array(VERSION_PREFIX.length + x.length + 1);
  data.set(VERSION_PREFIX, 0);
  data.set(x, VERSION_PREFIX.length);
  data[data.length - 1] = isOdd;
  return b58check.encode(data);
};
