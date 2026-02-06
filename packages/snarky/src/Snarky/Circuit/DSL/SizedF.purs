-- | Field elements with type-level bit size tracking.
-- |
-- | `SizedF n f` represents a field element known to fit in `n` bits. This enables
-- | safe coercion between different fields when the value is small enough to fit
-- | in both. The `CheckedType` instance constrains the high bits to be zero.
module Snarky.Circuit.DSL.SizedF
  ( SizedF
  , fromField
  , toField
  , fromBits
  , toBits
  , coerceViaBits
  , lowestNBits
  , lowestNBitsPure
  ) where

import Prelude

import Data.Array as Array
import Data.FoldableWithIndex (foldlWithIndex)
import Data.Maybe (Maybe(..), fromJust)
import Data.Reflectable (class Reflectable, reflectType)
import Data.Traversable (all, for_)
import Data.Vector (Vector)
import Data.Vector as Vector
import JS.BigInt as BigInt
import Partial.Unsafe (unsafePartial)
import Prim.Int (class Add, class Compare)
import Prim.Ordering (LT)
import Snarky.Circuit.DSL.Assert (class AssertEqual, assertEq, assert_, isEqual)
import Snarky.Circuit.DSL.Bits (packPure, pack_, unpackPure, unpack_)
import Snarky.Circuit.DSL.Monad (class CheckedType, class CircuitM, Snarky, not_)
import Snarky.Circuit.Types (class CircuitType, F, FVar, fieldsToValue, fieldsToVar, sizeInFields, valueToFields, varToFields)
import Snarky.Constraint.Basic (class BasicSystem)
import Snarky.Curves.Class (class FieldSizeInBits, class PrimeField, fromInt, pow)
import Test.QuickCheck (class Arbitrary, arbitrary)
import Type.Proxy (Proxy(..))

newtype SizedF :: Int -> Type -> Type
newtype SizedF n f = SizedF f

derive instance Eq f => Eq (SizedF n f)
derive instance Ord f => Ord (SizedF n f)
derive newtype instance Show f => Show (SizedF n f)

instance
  ( FieldSizeInBits f m
  ) =>
  CircuitType f (SizedF n (F f)) (SizedF n (FVar f)) where
  valueToFields (SizedF x) = valueToFields x
  fieldsToValue = SizedF <<< fieldsToValue
  sizeInFields pf _ = sizeInFields pf (Proxy @(F f))
  varToFields (SizedF x) = varToFields @f @(F f) x
  fieldsToVar = SizedF <<< fieldsToVar @f @(F f)

instance
  ( FieldSizeInBits f k
  , Compare n k LT
  , BasicSystem f c
  , Reflectable n Int
  , Add n _l k
  ) =>
  CheckedType f c (SizedF n (FVar f)) where
  check (SizedF var) = do
    bits <- unpack_ var
    let
      { after } = Vector.splitAt @n bits
    for_ after \bit ->
      assert_ (not_ bit)

-- | AssertEqual instance for SizedF - delegates to inner field comparison
instance AssertEqual f c (SizedF n (FVar f)) where
  assertEq (SizedF x) (SizedF y) = assertEq @f x y
  isEqual (SizedF x) (SizedF y) = isEqual @f x y

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
  :: forall @n m f
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

toField :: forall n f. SizedF n f -> f
toField (SizedF x) = x

fromBits
  :: forall n m f
   . FieldSizeInBits f m
  => Reflectable n Int
  => Compare n m LT
  => PrimeField f
  => Vector n Boolean
  -> SizedF n f
fromBits bits = SizedF $ packPure $ bits

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

-- | Coerce between fields by unpacking to bits and repacking.
-- | Safe because both fields must have at least `m` bits and the value fits in `n < m`.
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

--------------------------------------------------------------------------------

lowestNBits
  :: forall f c t m @n k
   . PrimeField f
  => FieldSizeInBits f k
  => Reflectable n Int
  => Compare n k LT
  => CircuitM f c t m
  => FVar f
  -> Snarky c t m (SizedF n (FVar f))
lowestNBits x = do
  bits <- unpack_ x
  let
    n = reflectType $ Proxy @n
    lowN =
      unsafePartial fromJust
        $ Vector.toVector @n
        $ Array.take n
        $
          Vector.toUnfoldable bits
  pure $ SizedF $ pack_ lowN

lowestNBitsPure
  :: forall f @n k
   . PrimeField f
  => FieldSizeInBits f k
  => Reflectable n Int
  => Compare n k LT
  => f
  -> SizedF n f
lowestNBitsPure x =
  let
    n = reflectType $ Proxy @n
    -- Unpack to bits (LSB first), take first 128
    bits = Array.take n $ Vector.toUnfoldable $ unpackPure x
    two = fromInt 2
  in
    -- Pack back to field element
    SizedF $ foldlWithIndex
      (\i acc b -> if b then acc + pow two (BigInt.fromInt i) else acc)
      zero
      bits