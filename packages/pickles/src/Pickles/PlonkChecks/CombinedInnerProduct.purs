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
  , buildEvalListUnmasked
  ) where

import Prelude

import Data.Array.NonEmpty (NonEmptyArray)
import Data.Array.NonEmpty as NEA
import Data.Foldable (foldM)
import Data.Tuple (Tuple(..))
import Data.Vector (Vector, (:<))
import Data.Vector as Vector
import Pickles.Commitments (combinedInnerProductCircuit)
import Pickles.Linearization.FFI (class LinearizationFFI, PointEval)
import Pickles.Linearization.Types (LinearizationPoly)
import Pickles.PlonkChecks.FtEval (ftEval0Circuit)
import Pickles.PlonkChecks.GateConstraints (GateConstraintInput)
import Pickles.PlonkChecks.Permutation (PermutationInput)
import Poseidon (class PoseidonField)
import Prim.Int (class Add)
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
  -> NonEmptyArray (EvalOpt f)
  -> Snarky c t m (FVar f)
hornerCombine xi evals = do
  let
    reversed = NEA.reverse evals
    { head: initVal, tail: rest } = NEA.uncons reversed
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
-- | Order: sg_evals(n), public_input, ft_eval, z+index+witness+coeff+sigma (43).
-- | This matches `Evals.In_circuit.to_list` order for always-present fields.
buildEvalList
  :: forall n f _l
   . Add 1 _l n
  => { sgEvals :: Vector n (Tuple (BoolVar f) (FVar f))
     , publicInput :: FVar f
     , ftEval :: FVar f
     , evals :: Vector 43 (FVar f)
     }
  -> NonEmptyArray (EvalOpt f)
buildEvalList x =
  let
    sgEvals = map (\(Tuple keep eval) -> EvalMaybe keep eval) (NEA.fromFoldable1 x.sgEvals)
    others = NEA.cons' (EvalJust x.publicInput) [ EvalJust x.ftEval ]
    evals = map EvalJust $ NEA.fromFoldable1 x.evals
  in
    NEA.concat $ NEA.cons' sgEvals [ others, evals ]

-- | Build evaluation list with all sg_evals unmasked (EvalJust).
-- |
-- | Used by the Wrap FOP where all previous proofs are always present
-- | (no proofs-verified mask).
buildEvalListUnmasked
  :: forall n f _l
   . Add 1 _l n
  => { sgEvals :: Vector n (FVar f)
     , publicInput :: FVar f
     , ftEval :: FVar f
     , evals :: Vector 43 (FVar f)
     }
  -> NonEmptyArray (EvalOpt f)
buildEvalListUnmasked x =
  let
    sgEvals = map EvalJust $ NEA.fromFoldable1 x.sgEvals
    others = NEA.cons' (EvalJust x.publicInput) [ EvalJust x.ftEval ]
    evals = map EvalJust $ NEA.fromFoldable1 x.evals
  in
    NEA.concat $ NEA.cons' sgEvals [ others, evals ]
