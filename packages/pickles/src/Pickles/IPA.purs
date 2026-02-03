-- | IPA (Inner Product Argument) verification circuits.
-- |
-- | This module provides in-circuit implementations for verifying IPA opening proofs
-- | as used in the Kimchi/Pickles proving system.
-- |
-- | The key operations are:
-- | - Challenge extraction from L/R commitment pairs via Fiat-Shamir
-- | - Verification that b = bPoly(challenges, zeta) + evalscale * bPoly(challenges, zetaOmega)
-- |
-- | Reference: wrap_verifier.ml in mina/src/lib/pickles
module Pickles.IPA
  ( -- Types
    LrPair
  , BCorrectInput
  -- Challenge extraction (returns 128-bit scalar challenges)
  , extractScalarChallenge
  , extractScalarChallenges
  -- Verification
  , bCorrect
  , bCorrectCircuit
  ) where

import Prelude

import Data.Reflectable (class Reflectable)
import Data.Traversable (traverse)
import Data.Vector (Vector)
import Pickles.Commitments (ComputeBInput, computeB, computeBCircuit)
import Pickles.Sponge (SpongeM, absorbPoint, squeezeScalarChallenge)
import Poseidon (class PoseidonField)
import Snarky.Circuit.DSL (class CircuitM, BoolVar, FVar, Snarky, equals_)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Curves.Class (class FieldSizeInBits, class PrimeField)
import Snarky.Data.EllipticCurve (AffinePoint)
import Snarky.Data.SizedF (SizedF)

-------------------------------------------------------------------------------
-- | Types
-------------------------------------------------------------------------------

-- | A pair of L and R commitment points from an IPA round.
-- | These are curve points on the commitment curve (the "other" curve in the 2-cycle).
type LrPair f = { l :: AffinePoint f, r :: AffinePoint f }

-- | Input type for bCorrect / bCorrectCircuit.
-- | Extends ComputeBInput with the expected b value for verification.
type BCorrectInput n f = ComputeBInput n f (expectedB :: f)

-------------------------------------------------------------------------------
-- | Challenge Extraction (In-Circuit)
-------------------------------------------------------------------------------

-- | Extract a single 128-bit scalar challenge from an L/R pair.
-- |
-- | This is the core Fiat-Shamir operation for IPA:
-- | 1. Absorb L point (x, y coordinates)
-- | 2. Absorb R point (x, y coordinates)
-- | 3. Squeeze 128-bit scalar challenge
-- |
-- | The result is a 128-bit scalar challenge, NOT a full field element.
-- | In pickles, the endo mapping to full field happens separately when needed.
-- | This matches the OCaml `squeeze_scalar` + `Bulletproof_challenge.unpack`.
extractScalarChallenge
  :: forall f t m
   . PrimeField f
  => FieldSizeInBits f 255
  => PoseidonField f
  => CircuitM f (KimchiConstraint f) t m
  => LrPair (FVar f)
  -> SpongeM f (KimchiConstraint f) t m (SizedF 128 (FVar f))
extractScalarChallenge { l, r } = do
  -- Absorb L and R points into the sponge
  absorbPoint l
  absorbPoint r
  -- Squeeze 128-bit scalar challenge (no endo mapping here)
  squeezeScalarChallenge

-- | Extract all 128-bit scalar challenges from a vector of L/R pairs.
-- |
-- | This processes all IPA rounds sequentially, building up the
-- | scalar challenge vector. The endo mapping to full field elements
-- | happens separately, outside this function.
-- |
-- | The number of rounds `n` equals the SRS log size (e.g., 16 for 2^16 SRS).
extractScalarChallenges
  :: forall n f t m
   . PrimeField f
  => FieldSizeInBits f 255
  => PoseidonField f
  => CircuitM f (KimchiConstraint f) t m
  => Vector n (LrPair (FVar f))
  -> SpongeM f (KimchiConstraint f) t m (Vector n (SizedF 128 (FVar f)))
extractScalarChallenges pairs = traverse extractScalarChallenge pairs

-------------------------------------------------------------------------------
-- | Verification
-------------------------------------------------------------------------------

-- | Pure version of b correctness check.
-- |
-- | Verifies: b == bPoly(challenges, zeta) + evalscale * bPoly(challenges, zetaOmega)
-- |
-- | This is the "b_correct" check from wrap_verifier.ml.
bCorrect
  :: forall n f
   . Reflectable n Int
  => PrimeField f
  => BCorrectInput n f
  -> Boolean
bCorrect input@{ expectedB } =
  let
    computedB = computeB input.challenges { zeta: input.zeta, zetaOmega: input.zetaOmega, evalscale: input.evalscale }
  in
    computedB == expectedB

-- | Circuit version of b correctness check.
-- |
-- | Computes b = bPoly(challenges, zeta) + evalscale * bPoly(challenges, zetaOmega)
-- | and returns a boolean constraint for equality with expected value.
-- |
-- | This is the in-circuit version of the "b_correct" check.
bCorrectCircuit
  :: forall n f c t m
   . Reflectable n Int
  => PrimeField f
  => CircuitM f c t m
  => BCorrectInput n (FVar f)
  -> Snarky c t m (BoolVar f)
bCorrectCircuit input@{ expectedB } = do
  computedB <- computeBCircuit input
  computedB `equals_` expectedB
