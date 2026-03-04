-- | Domain-related circuit computations for the Step verifier.
-- |
-- | Provides in-circuit computation of domain vanishing polynomial and
-- | power-of-two exponentiation using Square constraints, matching OCaml's
-- | `step_verifier.ml` domain handling.
-- |
-- | Reference: step_verifier.ml pow2_pow, Pseudo.Domain.to_domain vanishing_polynomial
module Pickles.Step.Domain
  ( pow2PowSquare
  , domainVanishingPoly
  ) where

import Prelude

import Safe.Coerce (coerce)
import Snarky.Circuit.DSL (class CircuitM, Bool(..), BoolVar, FVar, Snarky, const_, mul_, seal, square_, sub_)

-- | Compute x^(2^n) using Square constraints.
-- |
-- | Matches OCaml's step_verifier.ml `pow2_pow` which uses `Field.square`.
-- | Generates exactly `n` Square constraints.
pow2PowSquare
  :: forall f c t m
   . CircuitM f c t m
  => FVar f
  -> Int
  -> Snarky c t m (FVar f)
pow2PowSquare x n = go x n
  where
  go acc i
    | i <= 0 = pure acc
    | otherwise = do
        sq <- square_ acc
        go sq (i - 1)

-- | Compute domain vanishing polynomial for a single known domain.
-- |
-- | Matches OCaml's `Pseudo.Domain.to_domain` vanishing_polynomial:
-- |   pow2_pows via Field.square, choose (mask), subtract one, seal.
-- |
-- | For a single-element unique_domains (like our [16] case):
-- |   mask = (which_bit :> t) * pow2_pows.(log2_size)
-- |   result = seal (mask - one)
-- |
-- | Generates: `log2Size` Square constraints + 1 R1CS (mul for mask) + 1 R1CS (seal).
domainVanishingPoly
  :: forall f c t m
   . CircuitM f c t m
  => BoolVar f
  -> FVar f
  -> Int -- ^ log2 domain size (e.g. 16)
  -> Snarky c t m (FVar f)
domainVanishingPoly whichBit x log2Size = do
  -- 1. Compute pow2_pows via Field.square (log2Size Square constraints)
  zetaToN <- pow2PowSquare x log2Size
  -- 2. mask: (which_bit :> t) * zetaToN (1 R1CS mul)
  masked <- mul_ (coerce whichBit) zetaToN
  -- 3. seal (masked - one): exists + assertEqual (1 R1CS equal)
  seal (masked `sub_` const_ one)
