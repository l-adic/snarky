module Snarky.Example.Types.PublicKey
  ( PublicKey(..)
  ) where

import Prelude

import Data.Generic.Rep (class Generic)
import Data.Newtype (class Newtype)
import Data.Tuple.Nested (Tuple2, tuple2, uncurry2)
import Snarky.Circuit.DSL (class AssertEqual, class CheckedType, class CircuitType, F(..), FVar, assertEq, check, fieldsToValue, fieldsToVar, isEqual, sizeInFields, valueToFields, varToFields)
import Snarky.Circuit.RandomOracle (class Hashable)
import Snarky.Data.EllipticCurve (AffinePoint)
import Test.QuickCheck (class Arbitrary)
import Type.Proxy (Proxy(..))

-- | PublicKey type - a single field element representing a public key
newtype PublicKey f = PublicKey (AffinePoint f)

derive instance Newtype (PublicKey f) _
derive instance Generic (PublicKey f) _
derive newtype instance Show f => Show (PublicKey f)
derive newtype instance Eq f => Eq (PublicKey f)
derive newtype instance Ord f => Ord (PublicKey f)
derive newtype instance Arbitrary f => Arbitrary (PublicKey f)
derive instance Functor PublicKey

-- | Route through an explicit `Tuple2 (x, y)` so the coordinate layout
-- | is fixed and visible, rather than the record's RowList order.
instance CircuitType f a var => CircuitType f (PublicKey a) (PublicKey var) where
  sizeInFields pf _ = sizeInFields pf (Proxy @(Tuple2 a a))
  valueToFields (PublicKey pk) = valueToFields (tuple2 pk.x pk.y)
  fieldsToValue fs = uncurry2 (\x y -> PublicKey { x, y }) (fieldsToValue @_ @(Tuple2 a a) fs)
  varToFields (PublicKey pk) = varToFields @_ @(Tuple2 a a) (tuple2 pk.x pk.y)
  fieldsToVar fs = uncurry2 (\x y -> PublicKey { x, y }) (fieldsToVar @_ @(Tuple2 a a) fs)

instance CheckedType f c var => CheckedType f c (PublicKey var) where
  check (PublicKey pk) = check (tuple2 pk.x pk.y)

instance AssertEqual f c var => AssertEqual f c (PublicKey var) where
  assertEq (PublicKey a) (PublicKey b) = assertEq (tuple2 a.x a.y) (tuple2 b.x b.y)
  isEqual (PublicKey a) (PublicKey b) = isEqual (tuple2 a.x a.y) (tuple2 b.x b.y)

-- | Flatten via the `CircuitType` field representation, so the hash
-- | layout always matches the circuit serialization order.
instance Hashable (PublicKey (F f)) (F f) where
  toHashInput x = map F (valueToFields x)

instance Hashable (PublicKey (FVar f)) (FVar f) where
  toHashInput = varToFields @_ @(PublicKey (F f))
