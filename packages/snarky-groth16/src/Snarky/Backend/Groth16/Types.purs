module Snarky.Backend.Groth16.Types
  ( ProvingKey
  , VerifyingKey
  , Proof
  , R1CSDimensions
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
  ) where

import Prelude

import Data.Map (Map)
import Data.Map as Map
import Data.Newtype (class Newtype)
import Data.Tuple (Tuple(..))
import Foreign (unsafeToForeign)
import Simple.JSON (class WriteForeign)
import Snarky.Curves.Class (class PrimeField)

-- Foreign data types for Groth16 components
foreign import data ProvingKey :: Type -> Type
foreign import data VerifyingKey :: Type -> Type
foreign import data Proof :: Type -> Type

type Vector f = Map Int f
type Matrix f = Array (Vector f)

type R1CSDimensions =
  { numConstraints :: Int -- Number of R1CS constraints
  , numVariables :: Int -- Total variables (instance + witness) 
  , numInputs :: Int -- Number of public instance variables
  }

newtype Entry f = Entry (Tuple Int f)

derive instance Functor Entry

derive instance Newtype (Entry f) _
derive newtype instance Show f => Show (Entry f)

instance WriteForeign (Entry f) where
  writeImpl (Entry (Tuple i f)) = unsafeToForeign [ unsafeToForeign i, unsafeToForeign f ]

type CircuitVector f = Array (Entry f)

type CircuitMatrix f = Array (CircuitVector f)

type GatesWitness f = Array f -- Full witness: [1, public..., private...]

type Gates f =
  { a :: Matrix f -- A matrix for R1CS constraints
  , b :: Matrix f -- B matrix for R1CS constraints  
  , c :: Matrix f -- C matrix for R1CS constraints
  , publicInputIndices :: Array Int -- Which positions in witness are public
  }

-- FFI-ready types for witness data
newtype CircuitWitness f = CircuitWitness (Array f) -- Full witness array

derive instance Newtype (CircuitWitness f) _

-- FFI-ready types for R1CS circuit data
newtype CircuitGates f = CircuitGates
  { dimensions :: R1CSDimensions
  , matrixA :: CircuitMatrix f
  , matrixB :: CircuitMatrix f
  , matrixC :: CircuitMatrix f
  , publicInputIndices :: Array Int
  }

derive instance Newtype (CircuitGates f) _

toCircuitWitness
  :: forall f
   . PrimeField f
  => GatesWitness f
  -> CircuitWitness f
toCircuitWitness gatesWitness = CircuitWitness gatesWitness

toCircuitGates
  :: forall f
   . PrimeField f
  => Gates f
  -> R1CSDimensions
  -> CircuitGates f
toCircuitGates gates dimensions =
  let
    mapToEntries :: Map Int f -> Array (Entry f)
    mapToEntries sparseMap =
      map (\(Tuple i v) -> Entry (Tuple i v)) (Map.toUnfoldable $ Map.filter (\x -> x /= zero) sparseMap)

  in
    CircuitGates
      { dimensions
      , matrixA: map mapToEntries gates.a
      , matrixB: map mapToEntries gates.b
      , matrixC: map mapToEntries gates.c
      , publicInputIndices: gates.publicInputIndices
      }