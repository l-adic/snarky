module Snarky.Constraint.Kimchi.Poseidon
  ( PoseidonConstraint
  , eval
  ) where

import Prelude

import Data.Array as Array
import Data.Foldable (and, foldl)
import Data.Maybe (Maybe(..))
import Data.Traversable (traverse)
import Data.Tuple (Tuple(..))
import Type.Proxy (Proxy(..))
import Poseidon.Class (class PoseidonField, getRoundConstants, getMdsMatrix, sbox)
import Snarky.Circuit.CVar (Variable)
import Snarky.Circuit.CVar as CVar
import Snarky.Circuit.Types (F(..), FVar)
import Snarky.Curves.Class (class PrimeField)
import Snarky.Data.Vector (Vector)
import Snarky.Data.Vector as Vector
import Snarky.Data.Fin (Finite, unsafeFinite)

-- | Poseidon constraint following Mina reference implementation
-- | Represents a complete Poseidon computation with witness table  
-- | Contains 56 states: initial + 55 rounds (Kimchi configuration)
type PoseidonConstraint f =
  { state :: Vector 56 (Vector 3 (FVar f)) -- Witness table: [initial_state, round_0_out, ..., round_54_out]
  }

-- | Validates that the Poseidon witness table represents a valid state progression
-- | Each transition must follow: next_state = poseidon_round(current_state, round_constants)
eval
  :: forall f m
   . PoseidonField f
  => PrimeField f
  => Applicative m
  => (Variable -> m f)
  -> PoseidonConstraint f
  -> m Boolean
eval lookup constraint = ado
  -- Evaluate all states in the witness table
  allStates <- traverse (evaluateState lookup) constraint.state

  -- Validate each round transition (55 total rounds)
  let roundChecks = map (validateRoundTransition allStates) (Array.range 0 54)

  -- All round constraints must be satisfied
  in and roundChecks

-- | Validates a single round transition in the Poseidon witness table
validateRoundTransition
  :: forall f
   . PoseidonField f
  => PrimeField f
  => Vector 56 (Vector 3 (F f)) -- All evaluated states
  -> Int -- Round number (0-54)
  -> Boolean
validateRoundTransition allStates round =
  let
    inputState = Vector.index allStates (unsafeFinite round)
    outputState = Vector.index allStates (unsafeFinite (round + 1))

    -- Apply S-box operation: sbox(x) = x^7 to each element
    sboxInputs = map (\(F x) -> sbox x) inputState

    -- Get round constants for this specific round  
    roundConstants = getRoundConstants (Proxy :: Proxy f) round

    -- Validate that output equals the expected Poseidon round result
    expected = computeRoundOutput sboxInputs roundConstants
  in
    map (\(F x) -> x) outputState == map (\(F x) -> x) expected

-- | Computes the expected output for a Poseidon round
-- | Formula: output[j] = roundConstants[j] + Σ(MDS[j][i] * sboxInputs[i])
computeRoundOutput
  :: forall f
   . PoseidonField f
  => PrimeField f
  => Vector 3 f -- S-box applied inputs
  -> Vector 3 f -- Round constants  
  -> Vector 3 (F f) -- Expected output
computeRoundOutput sboxInputs roundConstants =
  let
    mdsMatrix = getMdsMatrix (Proxy :: Proxy f)

    -- Compute output[j] = roundConstants[j] + Σ(MDS[j][i] * sboxInputs[i])
    computeElement :: Finite 3 -> F f
    computeElement j =
      let
        roundConstant = Vector.index roundConstants j
        mdsRow = Vector.index mdsMatrix j

        -- Compute MDS row dot product with S-box inputs
        mdsSum = foldl (\acc (Tuple mdsCoeff sboxInput) -> acc + mdsCoeff * sboxInput) zero
          (Vector.zip mdsRow sboxInputs)

        expectedOutput = roundConstant + mdsSum
      in
        F expectedOutput
  in
    Vector.generate computeElement

-- | Helper function to evaluate a 3-element state vector
evaluateState
  :: forall f m
   . PrimeField f
  => Applicative m
  => (Variable -> m f)
  -> Vector 3 (FVar f)
  -> m (Vector 3 (F f))
evaluateState lookup stateVec =
  traverse (\var -> F <$> CVar.eval lookup var) stateVec