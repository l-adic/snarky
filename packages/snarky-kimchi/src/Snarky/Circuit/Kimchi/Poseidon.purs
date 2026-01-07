module Snarky.Circuit.Kimchi.Poseidon
  ( poseidon
  ) where

import Prelude

import Data.Traversable (traverse)
import Poseidon.Class (class PoseidonField, fullRound)
import Safe.Coerce (coerce)
import Snarky.Circuit.DSL (Snarky, addConstraint, exists, readCVar)
import Snarky.Circuit.DSL.Monad (class CircuitM)
import Snarky.Circuit.Types (F(..), FVar)
import Snarky.Constraint.Kimchi (KimchiConstraint(KimchiPoseidon))
import Snarky.Data.Fin (getFinite, unsafeFinite)
import Snarky.Data.Vector (Vector)
import Snarky.Data.Vector as Vector

poseidon
  :: forall f t m
   . PoseidonField f
  => CircuitM f (KimchiConstraint f) t m
  => Vector 3 (FVar f)
  -> Snarky (KimchiConstraint f) t m (FVar f)
poseidon initialState = do
  state <- exists do
    initialValues <- traverse readCVar initialState
    let
      rounds = Vector.generate (\i -> \state -> fullRound state (getFinite i))
      roundOutputs = Vector.scanl (\state roundFn -> roundFn state) (coerce initialValues) rounds
      allStates = (coerce initialValues) Vector.:< roundOutputs
    pure (map (map F) allStates)
  addConstraint $ KimchiPoseidon { state }
  pure $
    (Vector.index (Vector.index state (unsafeFinite 55)) (unsafeFinite 2))