// Mina-style compressed public-key address (base58check), matching
// MinaProtocol/mina's `non_zero_curve_point` compressed format — the
// `B62q…` string shown by Mina explorers and the GraphQL API.
//
//   base58( [0xCB, 0x01, 0x01] ++ x_LE(32) ++ [parity(y)] ++ checksum )
//
// where the compressed point is { x, is_odd = parity(y) } (the least
// significant bit of y), x is the 32-byte little-endian field encoding
// (exactly what `toHexLe` emits), the three prefix bytes are the
// base58-check version (0xCB = non_zero_curve_point_compressed), the
// non_zero_curve_point bin_prot version (0x01) and the compressed_poly
// bin_prot version (0x01), and the checksum is the first 4 bytes of
// sha256(sha256(version ++ payload)).
import { sha256 } from "@noble/hashes/sha2.js";

const ALPHABET = "123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz";
// [base58 version, non_zero_curve_point version, compressed_poly version]
const VERSION_PREFIX = [0xcb, 0x01, 0x01];

// Little-endian hex (a fixed 32-byte field, as `toHexLe` emits) -> bytes.
function hexToBytes(hex) {
  const out = new Uint8Array(hex.length / 2);
  for (let i = 0; i < out.length; i++) {
    out[i] = parseInt(hex.slice(2 * i, 2 * i + 2), 16);
  }
  return out;
}

// base58 of a byte array; leading zero bytes become leading '1's.
function base58(bytes) {
  let n = 0n;
  for (const b of bytes) n = (n << 8n) | BigInt(b);
  let s = "";
  while (n > 0n) {
    s = ALPHABET[Number(n % 58n)] + s;
    n = n / 58n;
  }
  for (let i = 0; i < bytes.length && bytes[i] === 0; i++) s = ALPHABET[0] + s;
  return s;
}

// xHexLe, yHexLe :: little-endian hex of the affine coordinates.
export const pubkeyToBase58 = (xHexLe) => (yHexLe) => {
  const x = hexToBytes(xHexLe);
  const isOdd = hexToBytes(yHexLe)[0] & 1;
  const versioned = new Uint8Array(VERSION_PREFIX.length + x.length + 1);
  versioned.set(VERSION_PREFIX, 0);
  versioned.set(x, VERSION_PREFIX.length);
  versioned[versioned.length - 1] = isOdd;
  const checksum = sha256(sha256(versioned)).slice(0, 4);
  const full = new Uint8Array(versioned.length + 4);
  full.set(versioned, 0);
  full.set(checksum, versioned.length);
  return base58(full);
};
