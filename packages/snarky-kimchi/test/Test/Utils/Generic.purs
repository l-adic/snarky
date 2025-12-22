module Test.Utils.Generic where

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
import Snarky.Curves.Pasta (PallasScalarField, VestaScalarField)
import Snarky.Curves.Vesta as Vesta
import Snarky.Data.Fin (getFinite)
import Snarky.Data.Vector (Vector)
import Snarky.Data.Vector as Vector

foreign import verifyPallasGeneric :: Vector 15 PallasScalarField -> Vector 15 PallasScalarField -> Boolean

foreign import verifyVestaGeneric :: Vector 15 VestaScalarField -> Vector 15 VestaScalarField -> Boolean

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

class PrimeField f <= VerifyGeneric f where
  verifyGeneric :: Vector 15 f -> Vector 15 f -> Boolean

instance VerifyGeneric Pallas.ScalarField where
  verifyGeneric = verifyPallasGeneric

instance VerifyGeneric Vesta.ScalarField where
  verifyGeneric = verifyVestaGeneric

verify
  :: forall f
   . VerifyGeneric f
  => { wireAssignments :: Map Variable (Array (Tuple Int Int))
     , varAssignments :: Map Variable f
     , rows :: Array (KimchiRow f)
     }
  -> Boolean
verify arg@{ rows } =
  let
    genericRowsWithCoeffs = catMaybes $
      mapWithIndex
        ( \i { kind, coeffs } -> case kind of
            GenericPlonkGate -> Just (Tuple i coeffs)
            _ -> Nothing
        )
        rows
    witnessMatrix = placeWitness arg

    results = map
      ( \(Tuple rowIndex coeffs) ->
          let
            witness :: Vector 15 f
            witness = Vector.generate \col ->
              case Map.lookup (Tuple rowIndex (getFinite col)) witnessMatrix of
                Just a -> a
                Nothing -> zero
          in
            verifyGeneric coeffs witness
      )
      genericRowsWithCoeffs
  in
    all identity results