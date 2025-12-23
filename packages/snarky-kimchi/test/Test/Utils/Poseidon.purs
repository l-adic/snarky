module Test.Utils.Poseidon where

import Prelude

import Data.Array (catMaybes, mapWithIndex)
import Data.Function.Uncurried (Fn2, Fn3, runFn2, runFn3)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..), fromJust)
import Data.Tuple (Tuple(..))
import Partial.Unsafe (unsafePartial)
import Poseidon (class PoseidonField, getRoundConstants)
import Snarky.Circuit.CVar (Variable)
import Snarky.Constraint.Kimchi.Wire (GateKind(..), KimchiRow)
import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Vesta as Vesta
import Snarky.Data.Fin (getFinite)
import Snarky.Data.Vector (Vector)
import Snarky.Data.Vector as Vector
import Type.Proxy (Proxy(..))
import Snarky.Backend.Kimchi (placeWitness)

foreign import data PallasPoseidonVerifier :: Type

foreign import makePallasPoseidonVerifier
  :: Fn3 (Vector 55 (Vector 3 Pallas.ScalarField)) Int Int PallasPoseidonVerifier

foreign import verifyPallasPoseidonGadget
  :: Fn2 PallasPoseidonVerifier (Vector 12 (Vector 15 Pallas.ScalarField)) Boolean

foreign import data VestaPoseidonVerifier :: Type

foreign import makeVestaPoseidonVerifier
  :: Fn3 (Vector 55 (Vector 3 Pallas.BaseField)) Int Int VestaPoseidonVerifier

foreign import verifyVestaPoseidonGadget
  :: Fn2 VestaPoseidonVerifier (Vector 12 (Vector 15 Vesta.ScalarField)) Boolean

class PoseidonField f <= PoseidonVerifier f v | f -> v where
  makeVerifier
    :: Proxy f
    -> { firstRow :: Int
       , lastRow :: Int
       }
    -> v
  verify :: v -> Vector 12 (Vector 15 f) -> Boolean

instance PoseidonVerifier Pallas.ScalarField PallasPoseidonVerifier where
  makeVerifier _ { firstRow, lastRow } =
    let
      roundConstaints = Vector.generate $ \i ->
        getRoundConstants (Proxy @Vesta.BaseField) (getFinite i)
    in
      runFn3 makePallasPoseidonVerifier roundConstaints firstRow lastRow
  verify v w = runFn2 verifyPallasPoseidonGadget v w

instance PoseidonVerifier Vesta.ScalarField VestaPoseidonVerifier where
  makeVerifier _ { firstRow, lastRow } =
    let
      roundConstaints = Vector.generate $ \i ->
        getRoundConstants (Proxy @Pallas.BaseField) (getFinite i)
    in
      runFn3 makeVestaPoseidonVerifier roundConstaints firstRow lastRow
  verify v w = runFn2 verifyVestaPoseidonGadget v w

_verify
  :: forall f v
   . PoseidonVerifier f v
  => { wireAssignments :: Map Variable (Array (Tuple Int Int))
     , varAssignments :: Map Variable f
     , rows :: Array (KimchiRow f)
     }
  -> Boolean
_verify arg@{ rows } =
  let
    poseidonRowIndices :: Array Int
    poseidonRowIndices = catMaybes $
      mapWithIndex
        ( \i { kind } -> case kind of
            PoseidonGate -> Just i
            Zero -> Just i
            _ -> Nothing
        )
        rows

    verifier = makeVerifier (Proxy @f) { firstRow: 0, lastRow: 11 }
    witnessMatrix = placeWitness arg

    witness :: Vector 12 (Vector 15 f)
    witness = unsafePartial $ fromJust $ Vector.toVector (Proxy @12) $
      map
        ( \rowIndex ->
            Vector.generate \col ->
              case Map.lookup (Tuple rowIndex (getFinite col)) witnessMatrix of
                Just a -> a
                Nothing -> zero
        )
        poseidonRowIndices

  in
    verify verifier witness