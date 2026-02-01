module Snarky.Data.SizedF
  ( SizedF(..)
  , fromField
  , toField
  , fromBits
  , toBits
  , coerceViaBits
  ) where

import Prelude

import Data.Array as Array
import Data.Generic.Rep (class Generic)
import Data.Maybe (Maybe(..), fromJust)
import Data.Newtype (class Newtype)
import Data.Reflectable (class Reflectable, reflectType)
import Data.Traversable (all, for_)
import Data.Vector (Vector)
import Data.Vector as Vector
import Partial.Unsafe (unsafePartial)
import Prim.Int (class Add, class Compare)
import Prim.Ordering (LT)
import Snarky.Circuit.DSL (class CheckedType, class CircuitType, F, FVar, assert_, genericFieldsToValue, genericFieldsToVar, genericSizeInFields, genericValueToFields, genericVarToFields, not_, packPure, unpackPure, unpack_)
import Snarky.Constraint.Basic (class BasicSystem)
import Snarky.Curves.Class (class FieldSizeInBits, class PrimeField)
import Test.QuickCheck (class Arbitrary, arbitrary)
import Type.Proxy (Proxy(..))

-- | A field element known to have at most `n` significant bits.
-- | The type parameter `n` tracks the bit size at the type level.
-- | This allows safe coercion between fields when n fits in both.
newtype SizedF :: Int -> Type -> Type
newtype SizedF n f = SizedF f

derive instance Newtype (SizedF n f) _
derive instance Eq f => Eq (SizedF n f)
derive instance Ord f => Ord (SizedF n f)
derive newtype instance Show f => Show (SizedF n f)

derive instance Generic (SizedF n f) _

instance
  ( FieldSizeInBits f m
  ) =>
  CircuitType f (SizedF n (F f)) (SizedF n (FVar f)) where
  valueToFields = genericValueToFields
  fieldsToValue = genericFieldsToValue
  sizeInFields = genericSizeInFields
  varToFields = genericVarToFields @(SizedF n (F f))
  fieldsToVar = genericFieldsToVar @(SizedF n (F f))

instance
  ( FieldSizeInBits f k
  , Compare n k LT
  , BasicSystem f c
  , Reflectable n Int
  , Add n _l k
  ) =>
  CheckedType f c t m (SizedF n (FVar f)) where
  check (SizedF var) = do
    bits <- unpack_ var
    let
      { after } = Vector.splitAt @n bits
    for_ after \bit ->
      assert_ (not_ bit)

instance
  ( FieldSizeInBits f m
  , Reflectable n Int
  , Compare n m LT
  , PrimeField f
  ) =>
  Arbitrary (SizedF n f) where
  arbitrary = fromBits <$> Vector.generator (Proxy @n) arbitrary

-- | Convert a field element to a SizedF, checking that it fits in n bits.
-- | Returns Nothing if the value has significant bits beyond position n.
fromField
  :: forall n m f
   . FieldSizeInBits f m
  => Reflectable n Int
  => Compare n m LT
  => PrimeField f
  => f
  -> Maybe (SizedF n f)
fromField x =
  let
    bits = Vector.toUnfoldable $ unpackPure x
    { after } = Array.splitAt (reflectType (Proxy @n)) bits
  in
    if all not after then Just (SizedF x)
    else Nothing

-- | Convert a SizedF back to a field element
toField :: forall n f. SizedF n f -> f
toField (SizedF x) = x

-- | Construct a SizedF from a vector of n bits
fromBits
  :: forall n m f
   . FieldSizeInBits f m
  => Reflectable n Int
  => Compare n m LT
  => PrimeField f
  => Vector n Boolean
  -> SizedF n f
fromBits bits = SizedF $ packPure $ bits

-- | Extract the bits of a SizedF as a vector of exactly n booleans
toBits
  :: forall n m f
   . FieldSizeInBits f m
  => Reflectable n Int
  => Compare n m LT
  => PrimeField f
  => SizedF n f
  -> Vector n Boolean
toBits (SizedF x) =
  unsafePartial fromJust
    $ Vector.toVector
    $ Array.take (reflectType (Proxy @n))
    $ Vector.toUnfoldable
    $
      unpackPure x

coerceViaBits
  :: forall f f' n m
   . FieldSizeInBits f m
  => FieldSizeInBits f' m
  => Reflectable n Int
  => Compare n m LT
  => PrimeField f
  => SizedF n f
  -> SizedF n f'
coerceViaBits x = fromBits $ toBits x
