module Snarky.Circuit.Kimchi.Poseidon
  ( poseidon
  ) where

import Prelude

import Data.Fin (getFinite, unsafeFinite)
import Data.Traversable (traverse)
import Data.Vector (Vector)
import Data.Vector as Vector
import Poseidon (class PoseidonField, fullRound)
import Safe.Coerce (coerce)
import Snarky.Circuit.DSL (class CircuitM, F(..), FVar, Snarky, addConstraint, exists, readCVar)
import Snarky.Constraint.Kimchi (KimchiConstraint(KimchiPoseidon))

poseidon
  :: forall f t m
   . PoseidonField f
  => CircuitM f (KimchiConstraint f) t m
  => Vector 3 (FVar f)
  -> Snarky (KimchiConstraint f) t m (Vector 3 (FVar f))
poseidon initialState = do
  -- Witness only the 55 round outputs (not the initial state).
  -- OCaml's block_cipher does t.(0) <- init after witnessing, overwriting row 0
  -- with the actual input CVars. We achieve the same by prepending the original
  -- initialState outside exists.
  roundOutputs <- exists do
    initialValues <- traverse readCVar initialState
    let
      rounds = Vector.generate (\i -> \state -> fullRound state (getFinite i))
    pure $ map (map F) $ Vector.scanl (\state roundFn -> roundFn state) (coerce initialValues) rounds
  let state = initialState Vector.:< roundOutputs
  addConstraint $ KimchiPoseidon { state }
  pure $ Vector.index state (unsafeFinite 55)