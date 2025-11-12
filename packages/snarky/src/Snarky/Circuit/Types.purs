module Snarky.Circuit.Types
  ( Variable(..)
  , Bool(..)
  , class FieldEncoded
  , valueToFields
  , fieldsToValue
  , sizeInFields
  , FieldElem(..)
  , UnChecked(..)
  , class ConstrainedType
  , varToFields
  , fieldsToVar
  , check
  ) where

import Prelude

import Data.Array (foldMap)
import Data.Array as Array
import Data.Maybe (fromJust)
import Data.Newtype (class Newtype)
import Data.Reflectable (class Reflectable, reflectType)
import Data.Tuple (Tuple(..))
import Partial.Unsafe (unsafePartial)
import Safe.Coerce (coerce)
import Snarky.Circuit.CVar (CVar)
import Snarky.Circuit.Constraint.Class (class R1CSSystem, boolean)
import Snarky.Curves.Types (class PrimeField)
import Snarky.Data.Vector (Vector, toVector, unVector)
import Test.QuickCheck (class Arbitrary)
import Type.Proxy (Proxy(..))

newtype Variable = Variable Int

derive newtype instance Eq Variable
derive newtype instance Show Variable
derive newtype instance Ord Variable

newtype Bool a = Bool a

derive newtype instance Eq a => Eq (Bool a)
derive newtype instance Show a => Show (Bool a)
derive newtype instance Ord a => Ord (Bool a)
derive instance Newtype (Bool a) _

class FieldEncoded f a where
  valueToFields :: a -> Array f
  fieldsToValue :: Array f -> a
  sizeInFields :: Proxy a -> Int

instance FieldEncoded f Unit where
  valueToFields _ = mempty
  fieldsToValue _ = unit
  sizeInFields _ = 0

instance PrimeField f => FieldEncoded f Boolean where
  valueToFields b = Array.singleton $ if b then one @f else zero
  fieldsToValue a =
    let
      b = unsafePartial fromJust $ Array.head a
    in
      b == one
  sizeInFields _ = 1

instance (FieldEncoded f a, FieldEncoded f b) => FieldEncoded f (Tuple a b) where
  valueToFields (Tuple a b) = valueToFields @f @a a <> valueToFields @f @b b
  fieldsToValue fs =
    let
      { before: as, after: bs } = Array.splitAt (sizeInFields @f (Proxy @a)) fs
    in
      Tuple (fieldsToValue @f @a as) (fieldsToValue @f @b bs)
  sizeInFields _ = sizeInFields @f @a (Proxy @a) + sizeInFields @f @b (Proxy @b)

chunk :: forall a. Int -> Array a -> Array (Array a)
chunk n arr
  | n <= 0 = []
  | Array.null arr = []
  | otherwise =
      let
        current = Array.take n arr
        rest = Array.drop n arr
      in
        [ current ] <> chunk n rest

instance (FieldEncoded f a, Reflectable n Int) => FieldEncoded f (Vector n a) where
  valueToFields as = foldMap valueToFields (unVector as)
  fieldsToValue as =
    let
      chunks = chunk (sizeInFields @f (Proxy @a)) as
      vals = fieldsToValue <$> chunks
    in
      unsafePartial $ fromJust $ toVector (Proxy @n) vals
  sizeInFields _ = reflectType (Proxy @n) * sizeInFields @f (Proxy @a)

class FieldEncoded f a <= ConstrainedType f a c var | f a -> var c, c -> f, var -> f where
  varToFields :: var -> Array (CVar f Variable)
  fieldsToVar :: Array (CVar f Variable) -> var
  check :: var -> Array c

instance (PrimeField f, R1CSSystem (CVar f Variable) c) => ConstrainedType f Boolean c (CVar f (Bool Variable)) where
  varToFields var = Array.singleton $ coerce var
  fieldsToVar a = coerce $ unsafePartial fromJust $ Array.head a
  check :: CVar f (Bool Variable) -> Array c
  check var = Array.singleton $ boolean (coerce var)

instance (ConstrainedType f a c avar) => ConstrainedType f (Tuple a Unit) c avar where
  varToFields av = varToFields @f @a av
  fieldsToVar vs = fieldsToVar @f @a vs
  check a = check @f @a a

else instance (ConstrainedType f a c avar, ConstrainedType f b c bvar) => ConstrainedType f (Tuple a b) c (Tuple avar bvar) where
  varToFields (Tuple av bv) = varToFields @f @a av <> varToFields @f @b bv
  fieldsToVar vs =
    let
      { before: avs, after: bvs } = Array.splitAt (sizeInFields @f (Proxy @a)) vs
    in
      Tuple (fieldsToVar @f @a avs) (fieldsToVar @f @b bvs)
  check (Tuple a b) = check @f @a a <> check @f @b b

instance (ConstrainedType f a c avar, Reflectable n Int) => ConstrainedType f (Vector n a) c (Vector n avar) where
  varToFields as = foldMap (varToFields @f @a) $ unVector as
  fieldsToVar as = unsafePartial fromJust $
    let
      chunks = chunk (Array.length as / reflectType (Proxy @n)) as
      vs = fieldsToVar @f @a <$> chunks
    in
      toVector (Proxy @n) vs
  check as = foldMap (check @f @a) $ unVector as

newtype FieldElem f = FieldElem f

derive instance Newtype (FieldElem f) _
derive instance Eq f => Eq (FieldElem f)
derive newtype instance Arbitrary f => Arbitrary (FieldElem f)

instance FieldEncoded f (FieldElem f) where
  valueToFields = Array.singleton <<< coerce
  fieldsToValue a = coerce $ unsafePartial fromJust $ Array.head a
  sizeInFields _ = 1

instance PrimeField f => ConstrainedType f (FieldElem f) c (CVar f Variable) where
  varToFields = Array.singleton
  fieldsToVar a = unsafePartial fromJust $ Array.head a
  check _ = mempty

newtype UnChecked var = UnChecked var

derive instance Newtype (UnChecked var) _

instance FieldEncoded f a => FieldEncoded f (UnChecked a) where
  valueToFields (UnChecked a) = valueToFields a
  fieldsToValue = UnChecked <<< fieldsToValue
  sizeInFields _ = sizeInFields @f (Proxy @a)

instance ConstrainedType f a c var => ConstrainedType f (UnChecked a) c (UnChecked var) where
  varToFields (UnChecked var) = varToFields @f @a var
  fieldsToVar a = UnChecked $ fieldsToVar @f @a a
  check _ = mempty