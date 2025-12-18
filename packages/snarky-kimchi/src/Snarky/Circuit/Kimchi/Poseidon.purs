module Snarky.Circuit.Kimchi.Poseidon
  ( poseidonHash
  , poseidonConstraintCircuit
  ) where

import Prelude

import Data.Traversable (traverse)
import Poseidon.Class (class PoseidonField, fullRound)
import Safe.Coerce (coerce)
import Snarky.Circuit.DSL (AsProverT, Snarky, addConstraint, exists, readCVar)
import Snarky.Circuit.DSL.Monad (class CircuitM)
import Snarky.Circuit.Types (F(..), FVar)
import Snarky.Constraint.Kimchi (KimchiConstraint(KimchiPoseidon))
import Snarky.Curves.Class (class PrimeField)
import Snarky.Data.Fin (getFinite, unsafeFinite)
import Snarky.Data.Vector (Vector)
import Snarky.Data.Vector as Vector

poseidonHash
  :: forall f t m
   . PoseidonField f
  => PrimeField f
  => CircuitM f (KimchiConstraint f) t m
  => Vector 3 (FVar f)
  -> Snarky t m (FVar f)
poseidonHash inputState = do
  result <- poseidonConstraintCircuit inputState
  pure (Vector.index result (unsafeFinite 2))

poseidonConstraintCircuit
  :: forall f t m
   . PoseidonField f
  => PrimeField f
  => CircuitM f (KimchiConstraint f) t m
  => Vector 3 (FVar f)
  -> Snarky t m (Vector 3 (FVar f))
poseidonConstraintCircuit inputState = do
  witnessTable <- witnessAllRounds inputState
  let constraint = KimchiPoseidon { state: witnessTable }
  addConstraint constraint
  pure (Vector.index witnessTable (unsafeFinite 55))

witnessAllRounds
  :: forall f t m
   . PoseidonField f
  => PrimeField f
  => CircuitM f (KimchiConstraint f) t m
  => Vector 3 (FVar f)
  -> Snarky t m (Vector 56 (Vector 3 (FVar f)))
witnessAllRounds initialState = do
  let
    m :: AsProverT f m (Vector 56 (Vector 3 (F f)))
    m = do
      initialValues <- traverse readCVar initialState
      let
        rounds = Vector.generate (\i -> \state -> fullRound state (getFinite i))
        roundOutputs = Vector.scanl (\state roundFn -> roundFn state) (coerce initialValues) rounds
        allStates = (coerce initialValues) Vector.:< roundOutputs
      pure (map (map F) allStates)
  allStates <- exists m
  pure @(Snarky t m) allStates