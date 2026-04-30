-- | Domain-related circuit computations for the Step verifier.
-- |
-- | Provides in-circuit computation of domain vanishing polynomial and
-- | power-of-two exponentiation using Square constraints, matching OCaml's
-- | `step_verifier.ml` domain handling.
-- |
-- | Reference: step_verifier.ml pow2_pow, Pseudo.Domain.to_domain vanishing_polynomial
module Pickles.Step.Domain
  ( pow2PowSquare
  , buildPow2PowsArray
  , domainVanishingPoly
  , domainVanishingPolyMulti
  ) where

import Prelude

import Data.Array as Array
import Data.Fin (Finite)
import Data.Maybe (Maybe(..))
import Data.Reflectable (class Reflectable)
import Data.Vector (Vector)
import Data.Vector as Vector
import Pickles.Pseudo as Pseudo
import Prim.Int (class Add, class Compare)
import Prim.Ordering (LT)
import Safe.Coerce (coerce)
import Snarky.Circuit.DSL (class CircuitM, Bool(..), BoolVar, FVar, Snarky, const_, label, mul_, seal, square_, sub_)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Curves.Class (class PrimeField)

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
domainVanishingPoly whichBit x log2Size = label "domain-vanishing-poly" do
  -- 1. Compute pow2_pows via Field.square (log2Size Square constraints)
  zetaToN <- pow2PowSquare x log2Size
  -- 2. mask: (which_bit :> t) * zetaToN (1 R1CS mul)
  masked <- mul_ (coerce whichBit) zetaToN
  -- 3. seal (masked - one): exists + assertEqual (1 R1CS equal)
  label "seal_domain_vanishing" $ seal (masked `sub_` const_ one)

-- | Multi-domain vanishing polynomial: dispatches over `n` possible
-- | per-branch domains via Pseudo.choose.
-- |
-- | Mirrors OCaml `Pseudo.Domain.to_domain`'s `vanishing_polynomial`
-- | method (`pseudo.ml:118-127`), which builds a `pow2_pows` table up
-- | to `max_log2`, picks `pow2_pows.(log2_size d)` per branch via
-- | mask, subtracts one, and seals.
-- |
-- | Constraint count for n branches:
-- |   - `maxLog2 - 1` Square constraints (from `buildPow2Pows`)
-- |   - `n` Generic gates from `Pseudo.mask` (each entry b * x where x
-- |     is non-constant)
-- |   - 1 Generic gate from `seal`
-- |
-- | Single-branch (n=1) emits the same gate count as
-- | `domainVanishingPoly` provided that the type-level `maxLog2`
-- | equals the runtime `log2Size + 1` (so `Square` count matches).
-- |
-- | Reference: `mina/src/lib/crypto/pickles/pseudo/pseudo.ml:118-127`
domainVanishingPolyMulti
  :: forall @maxLog2 _maxPred n f t m
   . CircuitM f (KimchiConstraint f) t m
  => PrimeField f
  => Reflectable n Int
  => Reflectable maxLog2 Int
  => Add 1 _maxPred maxLog2
  => Add _maxPred 1 maxLog2
  => Compare 0 n LT
  => Vector n (BoolVar f)
  -> Vector n (Finite maxLog2)
  -> FVar f
  -> Snarky (KimchiConstraint f) t m (FVar f)
domainVanishingPolyMulti whichBits log2s x = label "domain-vanishing-poly" do
  -- 1. Compute pow2_pows = [x, x^2, ..., x^(2^(maxLog2-1))]
  --    via maxLog2-1 Square constraints.
  pow2Pows <- Pseudo.buildPow2Pows @maxLog2 x
  -- 2. choose: ∑ b_i * pow2_pows[log2_i] (n R1CS muls + linear sum)
  zetaToN <- Pseudo.choose whichBits log2s (\log2 -> Vector.index pow2Pows log2)
  -- 3. seal (zetaToN - one): 1 Generic gate
  label "seal_domain_vanishing" $ seal (zetaToN `sub_` const_ one)
