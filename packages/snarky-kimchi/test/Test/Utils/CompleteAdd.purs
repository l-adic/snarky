module Test.Utils.CompleteAdd where

import Prelude

import Data.Foldable (foldl)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Tuple (Tuple(..))
import Snarky.Circuit.CVar (Variable)
import Snarky.Curves.Pasta (PallasBaseField, VestaBaseField)

-- | Verify that a witness row satisfies the Pallas complete addition constraints
foreign import verifyPallasCompleteAdd :: Array PallasBaseField -> Boolean

-- | Verify that a witness row satisfies the Vesta complete addition constraints  
foreign import verifyVestaCompleteAdd :: Array VestaBaseField -> Boolean

placeWitness
  :: forall f
   . Map Variable (Tuple Int Int)
  -> Map Variable f
  -> Map (Tuple Int Int) f
placeWitness wireAssignments valueAssignments = 
  foldl
    ( \acc (Tuple var value) -> 
        case Map.lookup var wireAssignments of
          Nothing -> acc
          Just (Tuple row col) -> Map.insert (Tuple row col) value acc
    )
    Map.empty
    (Map.toUnfoldable valueAssignments :: Array _)