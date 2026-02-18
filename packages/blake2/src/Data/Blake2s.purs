-- | BLAKE2s-256 hash via Node.js built-in crypto module.
module Data.Blake2s
  ( blake2s256Bytes
  , blake2s256Bits
  ) where

-- | Hash a string with BLAKE2s-256, returning 32 bytes as integers (0-255).
foreign import blake2s256Bytes :: String -> Array Int

-- | Hash a string with BLAKE2s-256, returning 256 bits (LSB-first per byte).
-- |
-- | Each byte is expanded to 8 bits with bit 0 (LSB) first, matching
-- | OCaml's `Digestif.to_raw_string` -> `Char.to_int` -> `(c lsr i) land 1` ordering
-- | used in `mina/src/lib/pickles/ro.ml`.
foreign import blake2s256Bits :: String -> Array Boolean
