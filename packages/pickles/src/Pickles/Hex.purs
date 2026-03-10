module Pickles.Hex
  ( parseHex
  ) where

import Prelude

import Data.Maybe (Maybe(..))
import Effect.Exception.Unsafe (unsafeThrow)
import JS.BigInt as BigInt
import Snarky.Curves.Class (class PrimeField, fromBigInt)

-- | Parse hex string to field element.
parseHex :: forall f. Partial => PrimeField f => String -> f
parseHex hex = case fromBigInt <$> BigInt.fromString hex of
  Nothing -> unsafeThrow $ "Failed to parse Hex to BigInt: " <> hex
  Just a -> a