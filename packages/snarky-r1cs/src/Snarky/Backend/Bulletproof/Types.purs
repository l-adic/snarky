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
  , CircuitGates
  ) where

import Prelude

import Data.Map (Map)
import Data.Newtype (class Newtype)
import Data.Tuple (Tuple(..))
import Foreign (unsafeToForeign)
import Simple.JSON (class WriteForeign)

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

type CircuitGates f =
  { dimensions :: { n :: Int, m :: Int, q :: Int }
  , weightsLeft :: CircuitMatrix f
  , weightsRight :: CircuitMatrix f
  , weightsOutput :: CircuitMatrix f
  , weightsAuxiliary :: CircuitMatrix f
  , constants :: CircuitVector f
  }