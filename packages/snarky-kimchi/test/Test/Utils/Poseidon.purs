module Test.Utils.Poseidon where

import Prelude

import Data.Array (all, catMaybes, mapWithIndex, (!!), (:))
import Data.Array as Array
import Data.Foldable (foldl)
import Data.List (List(..))
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..), fromJust)
import Data.Tuple (Tuple(..))
import Debug (trace)
import Partial.Unsafe (unsafeCrashWith, unsafePartial)
import Snarky.Circuit.CVar (Variable)
import Snarky.Constraint.Kimchi.Wire (GateKind(..), KimchiRow)
import Snarky.Curves.Class (class PrimeField)
import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Pasta (PallasScalarField, VestaScalarField)
import Snarky.Curves.Vesta as Vesta
import Snarky.Data.Fin (getFinite)
import Snarky.Data.Vector (Vector)
import Snarky.Data.Vector as Vector
import Type.Proxy (Proxy(..))

foreign import verifyPallasPoseidon :: { row :: Vector 15 PallasScalarField, nextRow :: Vector 15 PallasScalarField, coeffs :: Vector 15 PallasScalarField } -> Boolean

foreign import verifyVestaPoseidon :: { row :: Vector 15 VestaScalarField, nextRow :: Vector 15 VestaScalarField, coeffs :: Vector 15 VestaScalarField } -> Boolean

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

class PrimeField f <= VerifyPoseidon f where
  verifyPoseidon :: { row :: Vector 15 f, nextRow :: Vector 15 f, coeffs :: Vector 15 f } -> Boolean

instance VerifyPoseidon Pallas.ScalarField where
  verifyPoseidon { row, nextRow, coeffs } = verifyPallasPoseidon { row, nextRow, coeffs }

instance VerifyPoseidon Vesta.ScalarField where
  verifyPoseidon { row, nextRow, coeffs } = verifyVestaPoseidon { row, nextRow, coeffs }

verify
  :: forall f
   . VerifyPoseidon f
  => { wireAssignments :: Map Variable (Array (Tuple Int Int))
     , varAssignments :: Map Variable f
     , rows :: Array (KimchiRow f)
     }
  -> Boolean
verify arg@{ rows } =
  let
    poseidonRowIndices = catMaybes $
      mapWithIndex
        ( \i { kind } -> case kind of
            PoseidonGate -> Just i
            Zero -> Just i
            _ -> Nothing
        )
        rows
    witnessMatrix = placeWitness arg

    witnessRowsWithCoeffs :: Vector 12 { witnessRow :: Vector 15 f, coeffs :: Vector 15 f }
    witnessRowsWithCoeffs = unsafePartial $ fromJust $ Vector.toVector (Proxy @12) $
      map
        ( \rowIndex ->
            let
              witnessRow = Vector.generate \col ->
                case Map.lookup (Tuple rowIndex (getFinite col)) witnessMatrix of
                  Just a -> a
                  Nothing -> zero
              coeffs = case rows !! rowIndex of
                Just kimchiRow -> kimchiRow.coeffs
                Nothing -> unsafeCrashWith "Missing kimchi row"
            in
              { witnessRow, coeffs }
        )
        poseidonRowIndices

    pairs = pairRowsWithCoeffs (Array.toUnfoldable $ Vector.unVector witnessRowsWithCoeffs)
    res = map verifyPoseidon pairs
  in
    trace res \_ -> all identity res
  where
  pairRowsWithCoeffs (Cons { witnessRow: row, coeffs: coeffs1 } (Cons { witnessRow: nextRow } Nil)) =
    [ { row, nextRow, coeffs: coeffs1 } ]
  pairRowsWithCoeffs (Cons { witnessRow: row, coeffs: coeffs1 } (Cons next@{ witnessRow: nextRow } rest)) =
    { row, nextRow, coeffs: coeffs1 } : pairRowsWithCoeffs (Cons next rest)
  pairRowsWithCoeffs _ = unsafeCrashWith "Expected at least two poseidon rows"