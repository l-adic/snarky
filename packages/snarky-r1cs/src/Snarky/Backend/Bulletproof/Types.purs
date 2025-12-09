module Snarky.Backend.Bulletproof.Types
  ( CRS
  , Witness
  , Statement
  , Circuit
  , Proof
  , CircuitDimensions
  , Entry(..)
  , Matrix
  , Vector
  ) where

import Prelude (class Show)

import Data.Newtype (class Newtype)
import Data.Tuple (Tuple(..))
import Foreign (unsafeToForeign)
import Simple.JSON (class WriteForeign)

-- Opaque types for circuit components
foreign import data CRS :: Type
foreign import data Witness :: Type
foreign import data Statement :: Type
foreign import data Circuit :: Type
foreign import data Proof :: Type

-- Circuit dimensions
type CircuitDimensions =
  { n :: Int -- multiplication gates (will be padded to power of 2)
  , m :: Int -- public inputs
  , q :: Int -- constraints
  }

-- Representation types (generic over field type)
newtype Entry f = Entry (Tuple Int f)

derive instance Newtype (Entry f) _
derive newtype instance Show f => Show (Entry f)

-- WriteForeign instance for FFI compatibility
instance WriteForeign (Entry f) where
  writeImpl (Entry (Tuple i f)) = unsafeToForeign [ unsafeToForeign i, unsafeToForeign f ]

type Matrix f = Array (Array (Entry f))
type Vector f = Array (Entry f)

