module Snarky.Circuit.Kimchi.Poseidon
  ( poseidonHash
  , poseidonConstraintCircuit
  ) where

import Prelude

import Data.Array as Array
import Data.Newtype (unwrap)
import Data.Traversable (traverse)
import Poseidon.Class (class PoseidonField, fullRound)
import Snarky.Circuit.DSL (AsProverT, Snarky, addConstraint, exists, readCVar)
import Snarky.Circuit.DSL.Monad (class CircuitM)
import Snarky.Circuit.Types (F(..), FVar)
import Snarky.Constraint.Kimchi (KimchiConstraint(KimchiPoseidon))
import Snarky.Curves.Class (class PrimeField)
import Snarky.Data.Fin (Finite, getFinite, unsafeFinite)
import Snarky.Data.Vector (Vector)
import Snarky.Data.Vector as Vector

-- | Simple Poseidon hash witness (for backwards compatibility)
poseidonHash
  :: forall f t m
   . PoseidonField f
  => PrimeField f
  => CircuitM f (KimchiConstraint f) t m
  => Vector 3 (FVar f) -- Fixed-size 3-element input
  -> Snarky t m (FVar f) -- Hash result
poseidonHash inputState = do
  -- Use the full constraint circuit and return just the final result
  result <- poseidonConstraintCircuit inputState
  pure (Vector.index result (unsafeFinite 2)) -- Return last element as hash

-- | Creates a Poseidon constraint circuit following mina/src/lib/pickles/sponge_inputs.ml
-- | This implements the actual constraint that validates the full Poseidon computation
poseidonConstraintCircuit
  :: forall f t m
   . PoseidonField f
  => PrimeField f
  => CircuitM f (KimchiConstraint f) t m
  => Vector 3 (FVar f) -- Input state
  -> Snarky t m (Vector 3 (FVar f)) -- Output state (after 55 rounds)
poseidonConstraintCircuit inputState = do
  -- Witness all 56 states: initial + 55 round outputs
  witnessTable <- witnessAllRounds inputState

  -- Create the Poseidon constraint: Impl.assert_ (Poseidon { state = witnessTable })
  let constraint = KimchiPoseidon { state: witnessTable }
  addConstraint constraint

  -- Return the final output state (state 55)
  pure (Vector.index witnessTable (unsafeFinite 55))

-- | Witness all Poseidon round states (56 total: initial + 55 rounds)
-- | This creates the witness table that the constraint will validate
witnessAllRounds
  :: forall f t m
   . PoseidonField f
  => PrimeField f
  => CircuitM f (KimchiConstraint f) t m
  => Vector 3 (FVar f) -- Input state
  -> Snarky t m (Vector 56 (Vector 3 (FVar f))) -- Complete witness table
witnessAllRounds initialState = do
  -- Read initial state values
  let
    m :: AsProverT f m (Vector 56 (Vector 3 (F f)))
    m = do
      initialValuesF <- traverse readCVar initialState
      let
        initialValues = map unwrap initialValuesF

        -- Compute state at position i: state[0] = initial, state[i] = after i rounds
        computeState :: Finite 56 -> Vector 3 (F f)
        computeState i =
          if getFinite i == 0 then initialValuesF -- Initial state (already F-wrapped)
          else
            let
              rounds = Array.range 0 (getFinite i - 1)
              finalState = Array.foldl (\state round -> fullRound state round) initialValues rounds
            in
              map F finalState

      pure (Vector.generate computeState)

  -- Compute all round states using Vector.scanl
  allStates <- exists m
  pure @(Snarky t m) allStates -- Convert to circuit variables