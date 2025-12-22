module Test.Utils.AddComplete where

import Prelude

import Data.Array (all, catMaybes, mapWithIndex)
import Data.Foldable (foldl)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Tuple (Tuple(..))
import Partial.Unsafe (unsafeCrashWith)
import Snarky.Circuit.CVar (Variable)
import Snarky.Constraint.Kimchi.Wire (GateKind(..), KimchiRow)
import Snarky.Curves.Class (class PrimeField)
import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Pasta (PallasBaseField, VestaBaseField)
import Snarky.Curves.Vesta as Vesta
import Snarky.Data.Fin (getFinite)
import Snarky.Data.Vector (Vector)
import Snarky.Data.Vector as Vector

foreign import verifyPallasCompleteAdd :: Vector 15 PallasBaseField -> Boolean

foreign import verifyVestaCompleteAdd :: Vector 15 VestaBaseField -> Boolean

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

class PrimeField f <= VerifyAddComplete f where
  verifyAddComplete :: Vector 15 f -> Boolean

instance VerifyAddComplete Pallas.BaseField where
  verifyAddComplete = verifyPallasCompleteAdd

instance VerifyAddComplete Vesta.BaseField where
  verifyAddComplete = verifyVestaCompleteAdd

verify
  :: forall f
   . VerifyAddComplete f
  => { wireAssignments :: Map Variable (Array (Tuple Int Int))
     , varAssignments :: Map Variable f
     , rows :: Array (KimchiRow f)
     }
  -> Boolean
verify arg@{ rows } =
  let
    ecAddRows = catMaybes $
      mapWithIndex
        ( \i { kind } -> case kind of
            AddCompleteGate -> Just i
            _ -> Nothing
        )
        rows
    witnessMatrix = placeWitness arg

    witnessRows :: Array (Vector 15 f)
    witnessRows =
      map
        ( \row ->
            Vector.generate \col ->
              case Map.lookup (Tuple row (getFinite col)) witnessMatrix of
                Just a -> a
                Nothing -> zero

        )
        ecAddRows
  in
    all verifyAddComplete witnessRows