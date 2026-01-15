module Test.Snarky.Example.Utils (chooseBigInt) where

import Prelude

import Control.Monad.Gen (chooseInt)
import Data.Array ((..))
import Data.Foldable (foldl)
import Data.Maybe (Maybe(..))
import Data.Traversable (for)
import JS.BigInt (BigInt)
import JS.BigInt as BigInt
import Test.QuickCheck.Gen (Gen)

--------------------------------------------------------------------------------

-- | Generate a random BigInt in the range [a, b] (inclusive)
chooseBigInt :: BigInt -> BigInt -> Gen BigInt
chooseBigInt a b
  | a > b = chooseBigInt b a
  | otherwise = (\x -> x + a) <$> chooseBigInt' (b - a)

-- | Generate a random BigInt in the range [0, range] (inclusive)
chooseBigInt' :: BigInt -> Gen BigInt
chooseBigInt' range =
  case BigInt.toInt range of
    -- Common case: range fits in Int32
    Just n -> BigInt.fromInt <$> chooseInt 0 n
    -- Large range: generate random bits and mod
    Nothing -> do
      let
        numBits = bitLength range
        numChunks = (numBits + 30) / 31 -- 31 bits per chunk (safe Int)
      -- Generate random 31-bit chunks
      chunks <- for (1 .. numChunks) \_ -> BigInt.fromInt <$> chooseInt 0 0x7FFFFFFF
      -- Combine chunks into a single BigInt
      let randomBits = foldlChunks chunks
      -- Mod by (range + 1) to get value in [0, range]
      pure $ randomBits `mod` (range + BigInt.fromInt 1)
  where
  -- Combine chunks: each chunk contributes 31 bits
  foldlChunks :: Array BigInt -> BigInt
  foldlChunks =
    let
      base = BigInt.fromInt 0x40000000 * BigInt.fromInt 2 -- 2^31
    in
      foldl (\acc chunk -> acc * base + chunk) (BigInt.fromInt 0)

  -- Count bits needed to represent n
  bitLength :: BigInt -> Int
  bitLength n
    | n <= BigInt.fromInt 0 = 0
    | otherwise = 1 + bitLength (n / BigInt.fromInt 2)
