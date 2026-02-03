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
-- | - `combinedInnerProductCircuit`: In-circuit version for recursive verification
module Pickles.Commitments
  ( bPoly
  , bPolyCircuit
  , computeB
  , computeBCircuit
  , combinedInnerProduct
  , combinedInnerProductCircuit
  , BPolyInput
  , ComputeBInput
  , CombinedInnerProductInput
  , NumEvals
  ) where

import Prelude

import Data.Fin (getFinite)
import Data.Foldable (foldM, foldl, product)
import Data.Reflectable (class Reflectable)
import Data.Vector (Vector)
import Data.Vector as Vector
import JS.BigInt as BigInt
import Pickles.Linearization.FFI (PointEval)
import Snarky.Circuit.CVar as CVar
import Snarky.Circuit.DSL (class CircuitM, FVar, Snarky)
import Snarky.Curves.Class (class PrimeField, pow)

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
-- | Circuit versions of bPoly / computeB
-------------------------------------------------------------------------------

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
  { product } <- foldM
    ( \{ product, currPower } c -> do
        -- term = 1 + c * currPower
        cp <- pure c * pure currPower
        let term = CVar.add_ (CVar.const_ one) cp
        -- product *= term
        newProduct <- pure product * pure term
        -- currPower = currPower²
        newPower <- pure currPower * pure currPower
        pure { product: newProduct, currPower: newPower }
    )
    { product: CVar.const_ one, currPower: x }
    (Vector.reverse chals)

  pure product

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

-------------------------------------------------------------------------------
-- | Circuit-level Combined Inner Product
-------------------------------------------------------------------------------

-- | Compute the combined inner product in-circuit.
-- |
-- | This is the circuit version for recursive verification, using the
-- | Semiring/Ring instances for `Snarky c t m (FVar f)` to express
-- | the arithmetic naturally.
-- |
-- | Computes: sum_i (polyscale^i * (eval_zeta[i] + evalscale * eval_zeta_omega[i]))
combinedInnerProductCircuit
  :: forall f c t m
   . PrimeField f
  => CircuitM f c t m
  => CombinedInnerProductInput (FVar f)
  -> Snarky c t m (FVar f)
combinedInnerProductCircuit { polyscale, evalscale, evals } = do
  -- We accumulate { result, scale } where scale = polyscale^i
  -- For each eval: result += scale * (eval.zeta + evalscale * eval.omegaTimesZeta)
  --                scale *= polyscale
  let
    step { result, scale } eval = do
      -- evalscale * eval.omegaTimesZeta
      evalscaleTimesOmega <- pure evalscale * pure eval.omegaTimesZeta
      -- eval.zeta + evalscale * eval.omegaTimesZeta
      let term = CVar.add_ eval.zeta evalscaleTimesOmega
      -- scale * term
      scaledTerm <- pure scale * pure term
      -- result + scale * term
      let newResult = CVar.add_ result scaledTerm
      -- scale * polyscale
      newScale <- pure scale * pure polyscale
      pure { result: newResult, scale: newScale }

    init = { result: CVar.const_ zero, scale: CVar.const_ one }

  { result } <- foldM step init evals
  pure result
