-- | Power-of-two exponentiation by repeated squaring. Emits one
-- | `square_` constraint per bit of the exponent. Used in both step-
-- | and wrap-side `finalize_other_proof` paths to compute zeta^(2^n).
-- |
-- | Reference: OCaml `step_verifier.ml`'s `pow2_pow`.
module Pickles.Util.Pow2
  ( pow2PowSquare
  ) where

import Prelude

import Snarky.Circuit.DSL (class BasicSystem, FVar, Snarky, square_)
import Snarky.Curves.Class (class PrimeField)

-- | Compute x^(2^n) using Square constraints.
-- |
-- | Matches OCaml's step_verifier.ml `pow2_pow` which uses `Field.square`.
-- | Generates exactly `n` Square constraints.
pow2PowSquare
  :: forall f c r
   . PrimeField f
  => BasicSystem f c
  => FVar f
  -> Int
  -> Snarky f c r (FVar f)
pow2PowSquare x n = go x n
  where
  go acc i
    | i <= 0 = pure acc
    | otherwise = do
        sq <- square_ acc
        go sq (i - 1)
