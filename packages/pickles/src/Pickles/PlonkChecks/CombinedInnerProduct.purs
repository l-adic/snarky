-- | Combined inner product check for PLONK verification.
-- |
-- | This module provides the `combined_inner_product_correct` check from `step_main`:
-- | 1. Compute ftEval0 in-circuit
-- | 2. Build evaluation vector with computed ftEval0
-- | 3. Compute combined inner product in-circuit
-- |
-- | Reference: mina/src/lib/pickles/step_main.ml (combined_inner_product_correct)
module Pickles.PlonkChecks.CombinedInnerProduct
  ( CombinedInnerProductCheckInput
  , combinedInnerProductCheckCircuit
  ) where

import Prelude

import Data.Vector (Vector, (:<))
import Data.Vector as Vector
import Pickles.Commitments (combinedInnerProductCircuit)
import Pickles.Linearization.FFI (PointEval)
import Pickles.Linearization.Types (LinearizationPoly)
import Pickles.PlonkChecks.FtEval (ftEval0Circuit)
import Pickles.PlonkChecks.GateConstraints (GateConstraintInput)
import Pickles.PlonkChecks.Permutation (PermutationInput)
import Poseidon (class PoseidonField)
import Snarky.Circuit.DSL (class CircuitM, FVar, Snarky)
import Snarky.Curves.Class (class HasEndo, class PrimeField)

-------------------------------------------------------------------------------
-- | Types
-------------------------------------------------------------------------------

-- | Input for the combined inner product check.
-- |
-- | This contains everything needed to:
-- | 1. Compute ftEval0 (from permInput, gateInput, publicEvalForFt)
-- | 2. Build the 45-element evaluation vector
-- | 3. Compute the combined inner product
type CombinedInnerProductCheckInput f =
  { -- Inputs for ftEval0 computation
    permInput :: PermutationInput f
  , gateInput :: GateConstraintInput f
  , publicEvalForFt :: f -- public input poly eval at zeta (for ftEval0)
  -- Other evaluation witnesses
  , publicPointEval :: PointEval f -- public input poly evals (zeta, zeta*omega)
  , ftEval1 :: f -- ft poly eval at zeta*omega (witness)
  , zEvals :: PointEval f -- Z poly evals
  , indexEvals :: Vector 6 (PointEval f) -- selector poly evals
  , witnessEvals :: Vector 15 (PointEval f) -- witness column evals
  , coeffEvals :: Vector 15 (PointEval f) -- coefficient column evals
  , sigmaEvals :: Vector 6 (PointEval f) -- sigma poly evals
  -- Batching scalars
  , polyscale :: f -- v: polynomial batching scalar
  , evalscale :: f -- u: evaluation point batching scalar
  }

-------------------------------------------------------------------------------
-- | Circuit computation
-------------------------------------------------------------------------------

-- | Compute the combined inner product in-circuit with ftEval0 computed in-circuit.
-- |
-- | This implements the `combined_inner_product_correct` check:
-- | 1. Compute ftEval0 in-circuit using permutation and gate constraints
-- | 2. Build evaluation vector with computed ftEval0
-- | 3. Compute combined inner product in-circuit
-- | 4. Return the result for comparison against expected value
combinedInnerProductCheckCircuit
  :: forall f f' c t m
   . PrimeField f
  => PoseidonField f
  => HasEndo f f'
  => CircuitM f c t m
  => LinearizationPoly f
  -> CombinedInnerProductCheckInput (FVar f)
  -> Snarky c t m (FVar f)
combinedInnerProductCheckCircuit linPoly input = do
  -- 1. Compute ftEval0 in-circuit
  ftEval0Computed <- ftEval0Circuit linPoly
    { permInput: input.permInput
    , gateInput: input.gateInput
    , publicEval: input.publicEvalForFt
    }

  -- 2. Build ft PointEval with computed ftEval0 and witness ftEval1
  let ftPointEval = { zeta: ftEval0Computed, omegaTimesZeta: input.ftEval1 }

  -- 3. Build full 45-element evaluation vector
  -- Order: public (1) + ft (1) + z (1) + index (6) + witness (15) + coeff (15) + sigma (6)
  let
    allEvals :: Vector 45 (PointEval (FVar f))
    allEvals =
      (input.publicPointEval :< ftPointEval :< input.zEvals :< Vector.nil)
        `Vector.append` input.indexEvals
        `Vector.append` input.witnessEvals
        `Vector.append` input.coeffEvals
        `Vector.append` input.sigmaEvals

  -- 4. Compute combined inner product in-circuit
  combinedInnerProductCircuit
    { polyscale: input.polyscale
    , evalscale: input.evalscale
    , evals: allEvals
    }
