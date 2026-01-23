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
  , checkGateConstraints
  , evaluateGateConstraints
  -- Re-exported helpers for building environments
  , buildEvalPoint
  , buildChallenges
  , parseHex
  ) where

import Prelude

import Data.Array as Array
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Vector (Vector, toUnfoldable)
import JS.BigInt as BigInt
import Partial.Unsafe (unsafeCrashWith)
import Pickles.Linearization.Env (Challenges, EvalPoint, circuitEnv)
import Pickles.Linearization.FFI (PointEval)
import Pickles.Linearization.Interpreter (evaluate)
import Pickles.Linearization.Types (CurrOrNext(..), GateType(..), PolishToken)
import Poseidon (class PoseidonField)
import Snarky.Circuit.CVar (CVar(..))
import Snarky.Circuit.DSL (class CircuitM, FVar, Snarky)
import Snarky.Circuit.DSL.Assert (assertEqual_)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Curves.Class (class HasEndo, class PrimeField, fromBigInt)

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
    witnessArr = toUnfoldable witnessEvals :: Array (PointEval a)
    coeffArr = toUnfoldable coeffEvals :: Array a
    indexArr = toUnfoldable indexEvals :: Array (PointEval a)

    pointEvalAt :: Array (PointEval a) -> Int -> CurrOrNext -> a
    pointEvalAt arr idx row = fromMaybe defaultVal do
      pe <- Array.index arr idx
      pure case row of
        Curr -> pe.zeta
        Next -> pe.omegaTimesZeta
  in
    { witness: \row col -> pointEvalAt witnessArr col row
    , coefficient: \col ->
        fromMaybe defaultVal (Array.index coeffArr col)
    , index: \row gt ->
        let
          gateIdx = case gt of
            Poseidon -> 0
            Generic -> 1
            VarBaseMul -> 2
            EndoMul -> 3
            EndoMulScalar -> 4
            CompleteAdd -> 5
            _ -> 0
        in
          pointEvalAt indexArr gateIdx row
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
  :: forall a
   . { alpha :: a
     , beta :: a
     , gamma :: a
     , jointCombiner :: a
     , vanishesOnZk :: a
     , lagrangeFalse0 :: a
     , lagrangeTrue1 :: a
     }
  -> Challenges a
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

-- | Parse hex string to field element.
parseHex :: forall f. PrimeField f => String -> f
parseHex hex = case fromBigInt <$> BigInt.fromString hex of
  Nothing -> unsafeCrashWith $ "Failed to parse Hex to BigInt: " <> hex
  Just a -> a

-------------------------------------------------------------------------------
-- | Core Circuit Functions
-------------------------------------------------------------------------------

-- | Evaluate the gate constraint polynomial in-circuit.
-- | Returns the computed value as a circuit variable.
-- |
-- | This computes the linearization polynomial but does NOT assert it equals zero.
-- | Use `checkGateConstraints` for the full constraint check.
evaluateGateConstraints
  :: forall f f' t m
   . PrimeField f
  => PoseidonField f
  => HasEndo f f'
  => CircuitM f (KimchiConstraint f) t m
  => Array PolishToken
  -> GateConstraintInput (FVar f)
  -> Snarky (KimchiConstraint f) t m (FVar f)
evaluateGateConstraints tokens input =
  let
    evalPoint = buildEvalPoint
      { witnessEvals: input.witnessEvals
      , coeffEvals: input.coeffEvals
      , indexEvals: input.indexEvals
      , defaultVal: Const zero
      }

    challenges = buildChallenges
      { alpha: input.alpha
      , beta: input.beta
      , gamma: input.gamma
      , jointCombiner: input.jointCombiner
      , vanishesOnZk: input.vanishesOnZk
      , lagrangeFalse0: input.lagrangeFalse0
      , lagrangeTrue1: input.lagrangeTrue1
      }

    env = circuitEnv evalPoint challenges parseHex
  in
    evaluate tokens env

-- | Check that the gate constraints are satisfied.
-- |
-- | This is the core constraint checking circuit for Kimchi/PLONK verification.
-- | It evaluates the linearization polynomial using the provided witness values
-- | and asserts the result equals zero.
-- |
-- | A valid proof will satisfy this constraint; an invalid proof will not.
checkGateConstraints
  :: forall f f' t m
   . PrimeField f
  => PoseidonField f
  => HasEndo f f'
  => CircuitM f (KimchiConstraint f) t m
  => Array PolishToken
  -> GateConstraintInput (FVar f)
  -> Snarky (KimchiConstraint f) t m Unit
checkGateConstraints tokens input = do
  result <- evaluateGateConstraints tokens input
  assertEqual_ result (Const zero)
