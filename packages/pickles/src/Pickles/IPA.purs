-- | IPA (Inner Product Argument) verification circuits.
-- |
-- | This module provides in-circuit implementations for verifying IPA opening proofs
-- | as used in the Kimchi/Pickles proving system.
-- |
-- | The key operations are:
-- | - Challenge extraction from L/R commitment pairs via Fiat-Shamir
-- | - bPoly: The challenge polynomial from the IPA protocol
-- | - computeB: Combines bPoly evaluations at zeta and zeta*omega
-- | - Verification that b = bPoly(challenges, zeta) + evalscale * bPoly(challenges, zetaOmega)
-- |
-- | Reference: wrap_verifier.ml in mina/src/lib/pickles
module Pickles.IPA
  ( -- Types
    LrPair
  , BPolyInput
  , ComputeBInput
  , BCorrectInput
  -- Challenge polynomial
  , bPoly
  , bPolyCircuit
  -- Combined b evaluation
  , computeB
  , computeBCircuit
  -- Challenge extraction (returns 128-bit scalar challenges)
  , extractScalarChallenges
  -- Verification
  , bCorrect
  , bCorrectCircuit
  ) where

import Prelude

import Data.Fin (getFinite)
import Data.Foldable (foldM, product)
import Data.Reflectable (class Reflectable)
import Data.Traversable (for)
import Data.Vector (Vector)
import Data.Vector as Vector
import JS.BigInt as BigInt
import Pickles.Sponge (SpongeM, absorbPoint, squeezeScalarChallenge)
import Poseidon (class PoseidonField)
import Snarky.Circuit.CVar as CVar
import Snarky.Circuit.DSL (class CircuitM, BoolVar, FVar, Snarky, equals_)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Curves.Class (class FieldSizeInBits, class PrimeField, pow)
import Snarky.Data.EllipticCurve (AffinePoint)
import Snarky.Data.SizedF (SizedF)

-------------------------------------------------------------------------------
-- | Types
-------------------------------------------------------------------------------

-- | A pair of L and R commitment points from an IPA round.
-- | These are curve points on the commitment curve (the "other" curve in the 2-cycle).
type LrPair f = { l :: AffinePoint f, r :: AffinePoint f }

-- | Input type for bPoly circuit tests.
type BPolyInput d f = { challenges :: Vector d f, x :: f }

-- | Input type for computeB and related circuits.
-- | Open row type to allow extension (e.g., adding expectedB for bCorrect).
type ComputeBInput d f r =
  { challenges :: Vector d f
  , zeta :: f
  , zetaOmega :: f
  , evalscale :: f
  | r
  }

-- | Input type for bCorrect / bCorrectCircuit.
-- | Extends ComputeBInput with the expected b value for verification.
type BCorrectInput n f = ComputeBInput n f (expectedB :: f)

-------------------------------------------------------------------------------
-- | Challenge Polynomial (b_poly)
-------------------------------------------------------------------------------

-- | The challenge polynomial from the IPA protocol.
-- |
-- | Computes: b_poly(chals, x) = prod_{i=0}^{k-1} (1 + chals[i] * x^{2^{k-1-i}})
-- |
-- | This is "step 8: Define the univariate polynomial" of appendix A.2 of
-- | https://eprint.iacr.org/2020/499
-- |
-- | The `d` parameter is the number of IPA rounds (= domain log2), which equals
-- | the length of the challenges vector.
bPoly :: forall d f. Reflectable d Int => PrimeField f => Vector d f -> f -> f
bPoly chals x =
  let
    -- powTwos[i] = x^{2^i}
    powTwos :: Vector d f
    powTwos = Vector.generate \i ->
      pow x (BigInt.pow (BigInt.fromInt 2) (BigInt.fromInt (getFinite i)))

    -- Reverse to get [x^{2^{d-1}}, ..., x^4, x^2, x]
    -- Then zip with chals to compute (1 + chal * pow) for each pair
    terms :: Vector d f
    terms = Vector.zipWith (\c p -> one + c * p) chals (Vector.reverse powTwos)
  in
    product terms

-- | Circuit version of bPoly using iterative squaring (O(k) multiplications).
-- |
-- | For recursive verification where each multiplication is a constraint.
-- | Computes in a single pass over reversed challenges - no intermediate arrays.
bPolyCircuit
  :: forall d f c t m
   . Reflectable d Int
  => PrimeField f
  => CircuitM f c t m
  => BPolyInput d (FVar f)
  -> Snarky c t m (FVar f)
bPolyCircuit { challenges: chals, x } = do
  -- Iterate over reversed challenges: [c_{k-1}, ..., c_1, c_0]
  -- Powers naturally go x, x², x⁴, ... as we square each iteration
  -- term_i = 1 + c_{k-1-i} * x^{2^i}
  { product: prod } <- foldM
    ( \{ product: p, currPower } c -> do
        -- term = 1 + c * currPower
        cp <- pure c * pure currPower
        let term = CVar.add_ (CVar.const_ one) cp
        -- product *= term
        newProduct <- pure p * pure term
        -- currPower = currPower²
        newPower <- pure currPower * pure currPower
        pure { product: newProduct, currPower: newPower }
    )
    { product: CVar.const_ one, currPower: x }
    (Vector.reverse chals)

  pure prod

-------------------------------------------------------------------------------
-- | Combined b evaluation
-------------------------------------------------------------------------------

-- | Compute the combined b value at two evaluation points.
-- |
-- | This combines bPoly evaluations: b(zeta) + evalscale * b(zeta*omega)
-- |
-- | Corresponds to lines 201-210 of poly-commitment/src/ipa.rs in SRS::verify.
computeB
  :: forall d f
   . Reflectable d Int
  => PrimeField f
  => Vector d f
  -> { zeta :: f, zetaOmega :: f, evalscale :: f }
  -> f
computeB chals { zeta, zetaOmega, evalscale } =
  bPoly chals zeta + evalscale * bPoly chals zetaOmega

-- | Circuit version of computeB.
-- |
-- | Combines bPolyCircuit evaluations: b(zeta) + evalscale * b(zeta*omega)
computeBCircuit
  :: forall d f c t m r
   . Reflectable d Int
  => PrimeField f
  => CircuitM f c t m
  => ComputeBInput d (FVar f) r
  -> Snarky c t m (FVar f)
computeBCircuit { challenges, zeta, zetaOmega, evalscale } = do
  bZeta <- bPolyCircuit { challenges, x: zeta }
  bZetaOmega <- bPolyCircuit { challenges, x: zetaOmega }
  scaledB <- pure evalscale * pure bZetaOmega
  pure $ CVar.add_ bZeta scaledB

-------------------------------------------------------------------------------
-- | Challenge Extraction (In-Circuit)
-------------------------------------------------------------------------------

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
extractScalarChallenges pairs = for pairs \{ l, r } -> do
  -- Absorb L and R points into the sponge
  absorbPoint l
  absorbPoint r
  -- | The result is a 128-bit scalar challenge, NOT a full field element.
  -- | In pickles, the endo mapping to full field happens separately when needed.
  -- | This matches the OCaml `squeeze_scalar` + `Bulletproof_challenge.unpack`.
  squeezeScalarChallenge

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
