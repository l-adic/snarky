module Snarky.Backend.Kimchi where

import Prelude

import Data.Array ((:))
import Data.Array as Array
import Data.FoldableWithIndex (foldlWithIndex)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Set (Set)
import Data.Tuple (Tuple(..))
import Data.UnionFind (UnionFindData)
import Snarky.Circuit.CVar (Variable)
import Snarky.Constraint.Kimchi.Wire (GateKind(..), KimchiRow)
import Snarky.Curves.Class (class PrimeField)
import Snarky.Data.Fin (getFinite)
import Snarky.Data.Vector ((:<))
import Snarky.Data.Vector as Vector

placeVariables
  :: forall f
   . Array (KimchiRow f)
  -> Map Variable (Array (Tuple Int Int))
placeVariables rows =
  foldlWithIndex
    ( \i acc row ->
        foldlWithIndex
          ( \j m mVar -> case mVar of
              Nothing -> m
              Just var -> Map.insertWith append var [ Tuple i (getFinite j) ] m
          )
          acc
          row.variables
    )
    Map.empty
    rows

makePublicInputRows
  :: forall f
   . PrimeField f 
  => Array Variable
  -> Array (KimchiRow f)
makePublicInputRows = 
  map
  (\var -> 
      { kind: GenericPlonkGate
      , coeffs: one : Array.replicate 9 zero
      , variables: Just var :< Vector.generate (const Nothing)
      }
  )

type BuilderInput f =
  { gates :: Array (KimchiRow f)
  , publicInputs :: Array Variable
  , internalVariables :: Set Variable
  , unionFind :: UnionFindData Variable
  }

-- placeWitness
--   :: forall f r
--    . PrimeField f
--   => { wireAssignments :: Map Variable (Array (Tuple Int Int))
--      , varAssignments :: Map Variable f
--      | r
--      }
--   -> Map (Tuple Int Int) f
-- placeWitness { wireAssignments, varAssignments } =
--   foldl
--     ( \acc (Tuple var positions) ->
--         foldl
--           ( \m pos ->
--               case Map.lookup var varAssignments of
--                 Nothing -> unsafeCrashWith $ "placeWitness failed, missing var in varAssignments: " <> show var
--                 Just value -> Map.insert pos value m
--           )
--           acc
--           positions
--     )
--     Map.empty
--     (Map.toUnfoldable wireAssignments :: Array _)
