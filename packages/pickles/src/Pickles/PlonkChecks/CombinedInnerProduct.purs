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
  , BatchingScalars
  , combinedInnerProductCheckCircuit
  , EvalOpt(..)
  , hornerCombine
  , buildEvalList
  ) where

import Prelude

import Data.Array as Array
import Data.Foldable (foldM)
import Data.Maybe (fromJust)
import Data.Tuple (Tuple(..))
import Data.Vector (Vector, (:<))
import Data.Vector as Vector
import Partial.Unsafe (unsafePartial)
import Pickles.Commitments (combinedInnerProductCircuit)
import Pickles.Linearization.FFI (class LinearizationFFI, PointEval)
import Pickles.Linearization.Types (LinearizationPoly)
import Pickles.PlonkChecks.FtEval (ftEval0Circuit)
import Pickles.PlonkChecks.GateConstraints (GateConstraintInput)
import Pickles.PlonkChecks.Permutation (PermutationInput)
import Poseidon (class PoseidonField)
import Snarky.Circuit.DSL (class CircuitM, BoolVar, FVar, Snarky, add_, if_)
import Snarky.Curves.Class (class HasEndo, class PrimeField)

-------------------------------------------------------------------------------
-- | Types
-------------------------------------------------------------------------------

-- | Input for the combined inner product check.
-- |
-- | This contains the evaluation data needed to:
-- | 1. Compute ftEval0 (from permInput, gateInput, publicEvalForFt)
-- | 2. Build the 45-element evaluation vector
-- |
-- | Note: polyscale (xi) and evalscale (r) are NOT included here because they
-- | are derived from the sponge in the verification circuit, not provided as
-- | witness data. See plonkChecksCircuit for how they're derived and passed in.
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
  }

-- | Batching scalars derived from the Fiat-Shamir sponge.
-- |
-- | These are computed by squeezing the sponge after absorbing all evaluations:
-- | - polyscale (xi/v): first squeeze, used for polynomial batching
-- | - evalscale (r/u): second squeeze, used for evaluation point batching
type BatchingScalars f =
  { polyscale :: f -- xi/v: polynomial batching scalar
  , evalscale :: f -- r/u: evaluation point batching scalar
  }

-------------------------------------------------------------------------------
-- | Circuit computation
-------------------------------------------------------------------------------

-- | Compute the combined inner product in-circuit with ftEval0 computed in-circuit.
-- |
-- | This implements the `combined_inner_product_correct` check:
-- | 1. Compute ftEval0 in-circuit using permutation and gate constraints
-- | 2. Build evaluation vector with computed ftEval0
-- | 3. Compute combined inner product in-circuit using derived batching scalars
-- | 4. Return the result for comparison against expected value
-- |
-- | Uses precomputed alpha powers for gate constraint evaluation, matching
-- | OCaml's scalars_env approach.
combinedInnerProductCheckCircuit
  :: forall f f' g c t m r
   . PrimeField f
  => PoseidonField f
  => HasEndo f f'
  => CircuitM f c t m
  => LinearizationFFI f g
  => { linearizationPoly :: LinearizationPoly f, domainLog2 :: Int | r }
  -> FVar f -- ^ zeta (expanded)
  -> BatchingScalars (FVar f)
  -> CombinedInnerProductCheckInput (FVar f)
  -> Snarky c t m (FVar f)
combinedInnerProductCheckCircuit params zeta scalars input = do
  -- 1. Compute ftEval0 using monadic gate constraint evaluation
  ftEval0Computed <- ftEval0Circuit params zeta
    { permInput: input.permInput
    , gateInput: input.gateInput
    , publicEval: input.publicEvalForFt
    }

  -- 2. Build ft PointEval
  let ftPointEval = { zeta: ftEval0Computed, omegaTimesZeta: input.ftEval1 }

  -- 3. Build full 45-element evaluation vector
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
    { polyscale: scalars.polyscale
    , evalscale: scalars.evalscale
    , evals: allEvals
    }

-------------------------------------------------------------------------------
-- | Horner-scheme CIP computation
-------------------------------------------------------------------------------

-- | Evaluation in the Horner fold: either always present (Just) or masked (Maybe).
-- |
-- | Matches OCaml's `Pcs_batch.combine_split_evaluations` which uses
-- | `Shifted_value.of_cvar` for always-present and `if_` for masked evaluations.
data EvalOpt f
  = EvalJust (FVar f)
  | EvalMaybe (BoolVar f) (FVar f)

-- | Horner fold matching OCaml's `Pcs_batch.combine_split_evaluations`.
-- |
-- | Takes the polynomial batching scalar (xi) and a flat evaluation list.
-- | Reverses the list, initializes from head, folds with mul_and_add:
-- |   Just fx → fx + xi * acc
-- |   Maybe (b, fx) → if b then (fx + xi * acc) else acc
-- |
-- | Reference: step_verifier.ml:1060-1121 (combine ~ft ~sg_evals)
hornerCombine
  :: forall f c t m
   . CircuitM f c t m
  => FVar f
  -> Array (EvalOpt f)
  -> Snarky c t m (FVar f)
hornerCombine xi evals = do
  let
    reversed = Array.reverse evals
    initVal = unsafePartial $ fromJust $ Array.head reversed
    rest = unsafePartial $ fromJust $ Array.tail reversed
    initResult = case initVal of
      EvalJust x -> x
      EvalMaybe _ x -> x -- unreachable in practice: init is always Just
  foldM
    ( \acc opt -> case opt of
        EvalJust fx -> do
          xiAcc <- pure xi * pure acc
          pure (add_ fx xiAcc)
        EvalMaybe b fx -> do
          xiAcc <- pure xi * pure acc
          let then_ = add_ fx xiAcc
          if_ b then_ acc
    )
    initResult
    rest

-- | Build the flat evaluation list matching OCaml's combine function.
-- |
-- | Order: sg_evals, public_input, ft_eval, z, 6 selectors, 15 w, 15 coeff, 6 s.
-- | This matches `Evals.In_circuit.to_list` order for always-present fields.
buildEvalList
  :: forall f
   . Array (Tuple (BoolVar f) (FVar f)) -- ^ sg_evals [(keep, eval)]
  -> FVar f -- ^ public_input
  -> FVar f -- ^ ft_eval
  -> Array (FVar f) -- ^ always-present evals (43: z, 6 sel, 15 w, 15 coeff, 6 s)
  -> Array (EvalOpt f)
buildEvalList sgEvals pub ft evals =
  map (\(Tuple keep eval) -> EvalMaybe keep eval) sgEvals
    <> [ EvalJust pub, EvalJust ft ]
    <> map EvalJust evals
