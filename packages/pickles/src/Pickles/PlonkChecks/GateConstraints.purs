-- | In-circuit gate constraint verification for Kimchi/PLONK proofs.
-- |
-- | This module provides the core constraint checking circuit that verifies
-- | the Kimchi gate equations are satisfied. It evaluates the linearization
-- | polynomial (constraint AST) using in-circuit variables and asserts the
-- | result equals zero.
-- |
-- | The constraint polynomial is a complex expression combining:
-- | - Witness polynomial evaluations (15 columns × 2 rows)
-- | - Coefficient polynomial evaluations (15 columns)
-- | - Gate selector evaluations (Poseidon, Generic, VarBaseMul, etc.)
-- | - Protocol challenges (alpha, beta, gamma, jointCombiner)
-- | - Domain-dependent values (Lagrange basis, vanishing polynomial)
module Pickles.PlonkChecks.GateConstraints
  ( GateConstraintInput
  -- Re-exported helpers for building environments
  , buildEvalPoint
  , buildChallenges
  ) where

import Prelude

import Data.Fin (Finite, unsafeFinite)
import Data.Reflectable (class Reflectable)
import Data.Vector (Vector, (!!))
import Effect.Exception.Unsafe (unsafeThrow)
import Pickles.Linearization.Env (EvalPoint)
import Pickles.Linearization.FFI (PointEval)
import Pickles.Linearization.Types (CurrOrNext(..), GateType(..))

-------------------------------------------------------------------------------
-- | Input Types
-------------------------------------------------------------------------------

-- | Input record for gate constraint verification.
-- | All sizes are statically known from Kimchi protocol parameters:
-- | - 15 witness columns, each with evaluations at zeta and zeta*omega
-- | - 15 coefficient columns = 15 evaluations (at zeta only)
-- | - 6 gate types, each with evaluations at zeta and zeta*omega
-- |
-- | Use as `GateConstraintInput (F f)` for values or
-- | `GateConstraintInput (FVar f)` for circuit variables.
type GateConstraintInput f =
  { -- Wire polynomial evaluations at zeta and zeta*omega
    witnessEvals :: Vector 15 (PointEval f)
  , -- Coefficient polynomial evaluations at zeta
    coeffEvals :: Vector 15 f
  , -- Gate selector evaluations at zeta and zeta*omega
    indexEvals :: Vector 6 (PointEval f)
  , -- Protocol challenges from Fiat-Shamir transcript
    alpha :: f
  , beta :: f
  , gamma :: f
  , jointCombiner :: f
  , -- Domain-dependent values (precomputed from zeta)
    vanishesOnZk :: f
  , -- UnnormalizedLagrangeBasis(zkRows=false, offset=0)
    lagrangeFalse0 :: f
  , -- UnnormalizedLagrangeBasis(zkRows=true, offset=-1)
    lagrangeTrue1 :: f
  }

-------------------------------------------------------------------------------
-- | Helper Functions
-------------------------------------------------------------------------------

-- | Build EvalPoint from input vectors.
-- | Maps column lookups to the appropriate vector elements.
buildEvalPoint
  :: forall a
   . { witnessEvals :: Vector 15 (PointEval a)
     , coeffEvals :: Vector 15 a
     , indexEvals :: Vector 6 (PointEval a)
     , defaultVal :: a
     }
  -> EvalPoint a
buildEvalPoint { witnessEvals, coeffEvals, indexEvals, defaultVal } =
  let
    pointEvalAt :: forall n. Reflectable n Int => Vector n (PointEval a) -> Finite n -> CurrOrNext -> a
    pointEvalAt v col row =
      let
        a = v !! col
      in
        case row of
          Curr -> a.zeta
          Next -> a.omegaTimesZeta
  in
    { witness: \row col -> pointEvalAt witnessEvals col row
    , coefficient: \col -> coeffEvals !! col
    , index: \row gt ->
        let
          idx = unsafeFinite @6
          -- Gate order matches Kimchi verifier's column ordering:
          -- Generic, Poseidon, CompleteAdd, VarBaseMul, EndoMul, EndoMulScalar
          -- See kimchi/src/verifier.rs lines 485-490
          -- Only these 6 gate types are supported; others require additional FFI support.
          gateIdx = case gt of
            Generic -> idx 0
            Poseidon -> idx 1
            CompleteAdd -> idx 2
            VarBaseMul -> idx 3
            EndoMul -> idx 4
            EndoMulScalar -> idx 5
            _ -> unsafeThrow $ "buildEvalPoint: unsupported gate type " <> show gt
        in
          pointEvalAt indexEvals gateIdx row
    , lookupAggreg: \_ -> defaultVal
    , lookupSorted: \_ _ -> defaultVal
    , lookupTable: \_ -> defaultVal
    , lookupRuntimeTable: \_ -> defaultVal
    , lookupRuntimeSelector: \_ -> defaultVal
    , lookupKindIndex: \_ -> defaultVal
    }

-- | Build Challenges from input values.
-- | The UnnormalizedLagrangeBasis calls in the linearization are:
-- |   { zkRows: false, offset: 0 }
-- |   { zkRows: true, offset: -1 }
buildChallenges
  :: forall a r
   . { alpha :: a
     , beta :: a
     , gamma :: a
     , jointCombiner :: a
     , vanishesOnZk :: a
     , lagrangeFalse0 :: a
     , lagrangeTrue1 :: a
     | r
     }
  -> { alpha :: a
     , beta :: a
     , gamma :: a
     , jointCombiner :: a
     , vanishesOnZeroKnowledgeAndPreviousRows :: a
     , unnormalizedLagrangeBasis :: { zkRows :: Boolean, offset :: Int } -> a
     }
buildChallenges { alpha, beta, gamma, jointCombiner, vanishesOnZk, lagrangeFalse0, lagrangeTrue1 } =
  { alpha
  , beta
  , gamma
  , jointCombiner
  , vanishesOnZeroKnowledgeAndPreviousRows: vanishesOnZk
  , unnormalizedLagrangeBasis: \{ zkRows: zk, offset } ->
      if not zk && offset == 0 then lagrangeFalse0
      else if zk && offset == (-1) then lagrangeTrue1
      else lagrangeFalse0
  }

-------------------------------------------------------------------------------
-- | Core Circuit Functions

