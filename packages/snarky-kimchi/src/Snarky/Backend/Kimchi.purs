module Snarky.Backend.Kimchi where

import Prelude

import Data.Foldable (foldl)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Tuple (Tuple(..))
import Partial.Unsafe (unsafeCrashWith)
import Snarky.Circuit.CVar (Variable)
import Snarky.Curves.Class (class PrimeField)

placeWitness
  :: forall f r
   . PrimeField f
  => { wireAssignments :: Map Variable (Array (Tuple Int Int))
     , varAssignments :: Map Variable f
     | r
     }
  -> Map (Tuple Int Int) f
placeWitness { wireAssignments, varAssignments } =
  foldl
    ( \acc (Tuple var positions) ->
        foldl
          ( \m pos ->
              case Map.lookup var varAssignments of
                Nothing -> unsafeCrashWith $ "placeWitness failed, missing var in varAssignments: " <> show var
                Just value -> Map.insert pos value m
          )
          acc
          positions
    )
    Map.empty
    (Map.toUnfoldable wireAssignments :: Array _)
