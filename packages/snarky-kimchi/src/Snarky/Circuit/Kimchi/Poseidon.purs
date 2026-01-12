module Snarky.Circuit.Kimchi.Poseidon
  ( poseidon
  ) where

import Prelude

import Data.Fin (getFinite, unsafeFinite)
import Data.Traversable (traverse)
import Data.Vector (Vector)
import Data.Vector as Vector
import Poseidon.Class (class PoseidonField, fullRound)
import Safe.Coerce (coerce)
import Snarky.Circuit.DSL (Snarky, addConstraint, exists, readCVar)
import Snarky.Circuit.DSL.Monad (class CircuitM)
import Snarky.Circuit.Types (F(..), FVar)
import Snarky.Constraint.Kimchi (KimchiConstraint(KimchiPoseidon))

poseidon
  :: forall f t m
   . PoseidonField f
  => CircuitM f (KimchiConstraint f) t m
  => Vector 3 (FVar f)
  -> Snarky (KimchiConstraint f) t m (Vector 3 (FVar f))
poseidon initialState = do
  state <- exists do
    initialValues <- traverse readCVar initialState
    let
      rounds = Vector.generate (\i -> \state -> fullRound state (getFinite i))
      roundOutputs = Vector.scanl (\state roundFn -> roundFn state) (coerce initialValues) rounds
      allStates = (coerce initialValues) Vector.:< roundOutputs
    pure (map (map F) allStates)
  addConstraint $ KimchiPoseidon { state }
  pure $ Vector.index state (unsafeFinite 55)