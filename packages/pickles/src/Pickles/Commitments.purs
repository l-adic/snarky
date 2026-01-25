-- | IPA commitment verification functions.
-- |
-- | This module provides PureScript implementations of the IPA (Inner Product Argument)
-- | polynomial commitment verification functions, translated from the Rust proof-systems
-- | crate's poly-commitment module.
-- |
-- | Key functions:
-- | - `bPoly`: The challenge polynomial from the IPA protocol
-- | - `computeB`: Combines bPoly evaluations at zeta and zeta*omega
-- | - `combinedInnerProduct`: Batch all polynomial evaluations
module Pickles.Commitments
  ( bPoly
  , computeB
  , combinedInnerProduct
  , CombinedInnerProductInput
  , NumEvals
  ) where

import Prelude

import Data.Foldable (foldl, product)
import Data.Reflectable (class Reflectable)
import Data.Vector (Vector)
import Data.Vector as Vector
import Pickles.Linearization.FFI (PointEval)
import Snarky.Curves.Class (class PrimeField)

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
    -- Build pow_twos where pow_twos[i] = x^{2^i} by repeated squaring
    -- pow_twos = [x, x^2, x^4, ..., x^{2^{k-1}}]
    powTwos :: Vector d f
    powTwos = Vector.scanl (\acc _ -> acc * acc) x chals

    -- Reverse to get [x^{2^{k-1}}, ..., x^4, x^2, x]
    -- Then zip with chals to compute (1 + chal * pow) for each pair
    terms :: Vector d f
    terms = Vector.zipWith (\c p -> one + c * p) chals (Vector.reverse powTwos)
  in
    product terms

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

-------------------------------------------------------------------------------
-- | Combined Inner Product
-------------------------------------------------------------------------------

-- | Number of polynomial evaluations for non-recursive, non-lookup circuits:
-- | public (1) + ft (1) + Z (1) + index (6) + witness (15) + coefficient (15) + sigma (6) = 45
type NumEvals = 45

-- | Input for combined inner product computation.
-- | Contains all polynomial evaluations in the order expected by the verifier.
type CombinedInnerProductInput f =
  { polyscale :: f -- v: polynomial batching scalar
  , evalscale :: f -- u: evaluation point batching scalar
  , evals :: Vector NumEvals (PointEval f) -- polynomial evaluations in order
  }

-- | Compute the combined inner product of all polynomial evaluations.
-- |
-- | This batches all polynomial evaluations using:
-- |   sum_i (polyscale^i * (eval_zeta[i] + evalscale * eval_zeta_omega[i]))
-- |
-- | Corresponds to `combined_inner_product` in poly-commitment/src/commitment.rs:520.
-- |
-- | For non-recursive, non-lookup circuits, the polynomial order is:
-- | 1. public_evals (1)
-- | 2. ft (1)
-- | 3. Z (1)
-- | 4. Index: Generic, Poseidon, CompleteAdd, VarBaseMul, EndoMul, EndoMulScalar (6)
-- | 5. Witness: 0..14 (15)
-- | 6. Coefficient: 0..14 (15)
-- | 7. Sigma: 0..5 (6)
combinedInnerProduct :: forall f. Semiring f => CombinedInnerProductInput f -> f
combinedInnerProduct { polyscale, evalscale, evals } =
  let
    -- For each polynomial: polyscale^i * (eval_zeta + evalscale * eval_zeta_omega)
    -- We accumulate (result, polyscale^i) through the fold
    step { result, scale } eval =
      let
        term = eval.zeta + evalscale * eval.omegaTimesZeta
      in
        { result: result + scale * term
        , scale: scale * polyscale
        }

    init = { result: zero, scale: one }
  in
    (foldl step init evals).result
