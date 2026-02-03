-- | Polynomial commitment batching functions.
-- |
-- | This module provides functions for batching polynomial evaluations
-- | as used in the Kimchi/Plonk verifier.
-- |
-- | Key functions:
-- | - `combinedInnerProduct`: Batch all polynomial evaluations
-- | - `combinedInnerProductCircuit`: In-circuit version for recursive verification
module Pickles.Commitments
  ( combinedInnerProduct
  , combinedInnerProductCircuit
  , CombinedInnerProductInput
  , NumEvals
  ) where

import Prelude

import Data.Foldable (foldM, foldl)
import Data.Vector (Vector)
import Pickles.Linearization.FFI (PointEval)
import Snarky.Circuit.CVar as CVar
import Snarky.Circuit.DSL (class CircuitM, FVar, Snarky)
import Snarky.Curves.Class (class PrimeField)

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
