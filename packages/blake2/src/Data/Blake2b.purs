-- | BLAKE2b-256 hash. Same algorithm as OCaml's `Blake2.digest_string`
-- | from `mina/src/lib/crypto/blake2/blake2.ml`, which configures
-- | `Digestif.Make_BLAKE2B { digest_size = 32 }`. Used by
-- | `Data.Schnorr.Derive` for Mina-compatible deterministic nonce
-- | derivation.
-- |
-- | NOTE: This is **NOT** Blake2b-512-truncated. Blake2b mixes the
-- | requested digest size into the IV, so the 32-byte output here is
-- | distinct from `take 32 (Blake2b-512 m)`. Node's built-in
-- | `createHash('blake2b512')` doesn't expose digest-size
-- | parameterization, so we use the `blakejs` npm package, which does.
module Data.Blake2b
  ( blake2b256
  , blake2b256Bits
  ) where

-- | BLAKE2b-256 of a byte-string (UTF-8 / latin-1 byte interpretation),
-- | returned as an `Array Int` of 32 byte-valued ints (0..255).
foreign import blake2b256 :: String -> Array Int

-- | BLAKE2b-256 returned as 256 bits LSB-first per byte (matches the
-- | `(c lsr i) land 1` ordering Mina's `Blake2.string_to_bits` uses).
foreign import blake2b256Bits :: String -> Array Boolean
