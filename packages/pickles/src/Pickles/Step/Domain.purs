-- | Step-side domain-related circuit helpers.
-- |
-- | Reference: step_verifier.ml, Pseudo.Domain.to_domain.
module Pickles.Step.Domain
  ( buildPow2PowsArray
  ) where

import Prelude

import Data.Array as Array
import Data.Maybe (Maybe(..))
import Snarky.Circuit.DSL (class CircuitM, FVar, Snarky, square_)

-- | Build the runtime `pow2_pows` table = `[x, x^2, x^4, ..., x^(2^maxLog2)]`
-- | as an Array of length `maxLog2 + 1`. Emits exactly `maxLog2`
-- | Square constraints (one per consecutive squaring step).
-- |
-- | Mirrors OCaml `Pseudo.Domain.to_domain`'s
-- | `vanishing_polynomial`'s pow2_pows array build
-- | (`pseudo.ml:119-123`). Used by multi-domain dispatch where the
-- | runtime `maxLog2` is determined by the maximum log2 across the
-- | slot's possible domains.
buildPow2PowsArray
  :: forall f c t m
   . CircuitM f c t m
  => FVar f
  -> Int
  -> Snarky c t m (Array (FVar f))
buildPow2PowsArray x maxLog2 = go [ x ] maxLog2
  where
  go acc i
    | i <= 0 = pure acc
    | otherwise = case Array.last acc of
        Nothing -> pure acc -- unreachable: acc is non-empty
        Just lastV -> do
          sq <- square_ lastV
          go (Array.snoc acc sq) (i - 1)
