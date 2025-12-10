module Snarky.Backend.Bulletproof.Types
  ( CRS
  , Witness
  , Statement
  , Circuit
  , Proof
  , CircuitDimensions
  , Entry(..)
  , CircuitMatrix
  , CircuitVector
  , CircuitGates(..)
  , CircuitWitness(..)
  , GatesWitness
  , Gates
  , Vector
  , Matrix
  , toCircuitGates
  , toCircuitWitness
  , nextPowerOf2
  ) where

import Prelude

import Data.Array as Array
import Data.Map (Map)
import Data.Map as Map
import Data.Newtype (class Newtype)
import Data.Tuple (Tuple(..))
import Foreign (unsafeToForeign)
import Simple.JSON (class WriteForeign)
import Snarky.Curves.Class (class PrimeField)

foreign import data CRS :: Type -> Type
foreign import data Witness :: Type -> Type
foreign import data Statement :: Type -> Type
foreign import data Circuit :: Type -> Type
foreign import data Proof :: Type -> Type

type Vector f = Map Int f
type Matrix f = Array (Vector f)

type CircuitDimensions =
  { n :: Int
  , m :: Int
  , q :: Int
  }

newtype Entry f = Entry (Tuple Int f)

derive instance Functor Entry

derive instance Newtype (Entry f) _
derive newtype instance Show f => Show (Entry f)

instance WriteForeign (Entry f) where
  writeImpl (Entry (Tuple i f)) = unsafeToForeign [ unsafeToForeign i, unsafeToForeign f ]

type CircuitVector f = Array (Entry f)

type CircuitMatrix f = Array (CircuitVector f)

type GatesWitness f =
  { al :: Array f
  , ar :: Array f
  , ao :: Array f
  , v :: Array f
  }

type Gates f =
  { wl :: Matrix f
  , wr :: Matrix f
  , wo :: Matrix f
  , wv :: Matrix f
  , c :: Array f
  }

-- Padded FFI-ready types
newtype CircuitWitness f = CircuitWitness
  { al :: Array f
  , ar :: Array f
  , ao :: Array f
  , v :: Array f
  }

derive instance Functor CircuitWitness
derive instance Newtype (CircuitWitness f) _

newtype CircuitGates f = CircuitGates
  { dimensions :: { n :: Int, m :: Int, q :: Int }
  , weightsLeft :: CircuitMatrix f
  , weightsRight :: CircuitMatrix f
  , weightsOutput :: CircuitMatrix f
  , weightsAuxiliary :: CircuitMatrix f
  , constants :: CircuitVector f
  }

derive instance Functor CircuitGates
derive instance Newtype (CircuitGates f) _

nextPowerOf2 :: Int -> Int
nextPowerOf2 k =
  let
    go power acc
      | acc >= k = acc
      | otherwise = go (power + 1) (acc * 2)
  in
    if k <= 1 then 1 else go 1 1

toCircuitWitness
  :: forall f
   . PrimeField f
  => GatesWitness f
  -> Int
  -> CircuitWitness f
toCircuitWitness witness n =
  let
    paddedN = nextPowerOf2 n
    padArray arr =
      let
        currentLength = Array.length arr
        paddingNeeded = paddedN - currentLength
      in
        if paddingNeeded > 0 then arr <> Array.replicate paddingNeeded zero
        else arr
  in
    CircuitWitness
      { al: padArray witness.al
      , ar: padArray witness.ar
      , ao: padArray witness.ao
      , v: witness.v
      }

toCircuitGates
  :: forall f
   . PrimeField f
  => Gates f
  -> { q :: Int, n :: Int, m :: Int }
  -> CircuitGates f
toCircuitGates gates { q, n, m } =
  let
    paddedN = nextPowerOf2 n

    mapToEntries :: Map Int f -> Array (Entry f)
    mapToEntries sparseMap =
      map (\(Tuple i v) -> Entry (Tuple i v)) (Map.toUnfoldable $ Map.filter (\x -> x /= zero) sparseMap)

    mapToEntriesNeg :: Map Int f -> Array (Entry f)
    mapToEntriesNeg sparseMap =
      map (\(Tuple i v) -> Entry (Tuple i (negate v))) (Map.toUnfoldable $ Map.filter (\x -> x /= zero) sparseMap)

  in
    CircuitGates
      { dimensions: { n: paddedN, m, q }
      , weightsLeft: map mapToEntries gates.wl
      , weightsRight: map mapToEntries gates.wr
      , weightsOutput: map mapToEntries gates.wo
      , weightsAuxiliary: map mapToEntriesNeg gates.wv
      , constants:
          Array.filter (\(Entry (Tuple _ f)) -> f /= zero) $
            Array.mapWithIndex (\i c -> Entry (Tuple i (negate c))) gates.c
      }