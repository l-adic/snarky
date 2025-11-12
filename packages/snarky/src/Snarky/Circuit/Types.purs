module Snarky.Circuit.Types
  ( Variable(..)
  , BooleanVariable(..)
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

newtype BooleanVariable = BooleanVariable Variable

derive newtype instance Eq BooleanVariable
derive newtype instance Show BooleanVariable
derive newtype instance Ord BooleanVariable
derive instance Newtype BooleanVariable _

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

class FieldEncoded f a <= ConstrainedType f var a c | a -> var c, c -> f var where
  varToFields :: var -> Array (CVar f Variable)
  fieldsToVar :: Array (CVar f Variable) -> var
  check :: var -> Array c

instance (PrimeField f, R1CSSystem (CVar f Variable) c) => ConstrainedType f (CVar f BooleanVariable) Boolean c where
  varToFields var = Array.singleton $ coerce var
  fieldsToVar a = coerce $ unsafePartial fromJust $ Array.head a
  check :: CVar f BooleanVariable -> Array c
  check var = Array.singleton $ boolean (coerce var :: CVar f Variable)

instance (ConstrainedType f avar a c) => ConstrainedType f avar (Tuple a Unit) c where
  varToFields av = varToFields @f @avar @a av
  fieldsToVar vs = fieldsToVar @f @avar @a vs
  check a = check @f @avar @a a

else instance (ConstrainedType f avar a c, ConstrainedType f bvar b c) => ConstrainedType f (Tuple avar bvar) (Tuple a b) c where
  varToFields (Tuple av bv) = varToFields @f @avar @a av <> varToFields @f @bvar @b bv
  fieldsToVar vs =
    let
      { before: avs, after: bvs } = Array.splitAt (sizeInFields @f (Proxy @a)) vs
    in
      Tuple (fieldsToVar @f @avar @a avs) (fieldsToVar @f @bvar @b bvs)
  check (Tuple a b) = check @f @avar @a a <> check @f @bvar @b b

instance (ConstrainedType f avar a c, Reflectable n Int) => ConstrainedType f (Vector n avar) (Vector n a) c where
  varToFields as = foldMap (varToFields @f @avar @a) $ unVector as
  fieldsToVar as = unsafePartial fromJust $
    let
      chunks = chunk (Array.length as / reflectType (Proxy @n)) as
      vs = fieldsToVar @f @avar @a <$> chunks
    in
      toVector (Proxy @n) vs
  check as = foldMap (check @f @avar @a) $ unVector as

newtype FieldElem f = FieldElem f

derive instance Newtype (FieldElem f) _
derive instance Eq f => Eq (FieldElem f)
derive newtype instance Arbitrary f => Arbitrary (FieldElem f)

instance FieldEncoded f (FieldElem f) where
  valueToFields = Array.singleton <<< coerce
  fieldsToValue a = coerce $ unsafePartial fromJust $ Array.head a
  sizeInFields _ = 1

instance PrimeField f => ConstrainedType f (CVar f Variable) (FieldElem f) c where
  varToFields = Array.singleton
  fieldsToVar a = unsafePartial fromJust $ Array.head a
  check _ = mempty

newtype UnChecked var = UnChecked var

derive instance Newtype (UnChecked var) _

instance FieldEncoded f a => FieldEncoded f (UnChecked a) where
  valueToFields (UnChecked a) = valueToFields a
  fieldsToValue = UnChecked <<< fieldsToValue
  sizeInFields _ = sizeInFields @f (Proxy @a)

instance ConstrainedType f var a c => ConstrainedType f (UnChecked var) (UnChecked a) c where
  varToFields (UnChecked var) = varToFields @f @var @a var
  fieldsToVar a = UnChecked $ fieldsToVar @f @var @a a
  check _ = mempty