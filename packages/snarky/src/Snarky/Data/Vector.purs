module Snarky.Data.Vector
  ( Vector
  , unVector
  , nilVector
  , vCons
  , (:<)
  , length
  , toVector
  , generator
  , concat
  , flatten
  , zip
  , zipWith
  , unzip
  , index
  , (!!)
  , generate
  , generateA
  , scanl
  , append
  , splitAt
  , chunks
  , head
  , last
  , reverse
  ) where

import Prelude

import Control.Monad.Gen (class MonadGen)
import Data.Array (foldMap, (:))
import Data.Array as A
import Data.Array as Array
import Data.Foldable (class Foldable)
import Data.FoldableWithIndex (class FoldableWithIndex, foldMapWithIndex, foldlWithIndex, foldrWithIndex)
import Data.FunctorWithIndex (class FunctorWithIndex, mapWithIndex)
import Data.Maybe (Maybe(..), fromJust)
import Data.Reflectable (class Reflectable, reflectType)
import Data.Traversable (class Traversable, traverse)
import Data.TraversableWithIndex (class TraversableWithIndex, traverseWithIndex)
import Data.Tuple (Tuple(..))
import Data.Unfoldable (class Unfoldable, class Unfoldable1, replicateA)
import Partial.Unsafe (unsafePartial)
import Prim.Int (class Add, class Compare, class Mul)
import Prim.Ordering (LT)
import Snarky.Circuit.Types (class CheckedType, class CircuitType, check, fieldsToValue, fieldsToVar, sizeInFields, valueToFields, varToFields)
import Snarky.Data.Fin (Finite, finites, getFinite, unsafeFinite)
import Type.Proxy (Proxy(..))

newtype Vector (n :: Int) a = Vector (Array a)

derive newtype instance Show a => Show (Vector n a)
derive newtype instance Eq a => Eq (Vector n a)
derive newtype instance Functor (Vector n)
derive newtype instance Unfoldable1 (Vector n)
derive newtype instance Unfoldable (Vector n)
derive newtype instance Foldable (Vector n)
derive newtype instance Traversable (Vector n)

instance (Reflectable n Int) => FoldableWithIndex (Finite n) (Vector n) where
  foldrWithIndex f init (Vector as) =
    foldrWithIndex (\i a b -> f (unsafeFinite i) a b) init as
  foldlWithIndex f init (Vector as) =
    foldlWithIndex (\i b a -> f (unsafeFinite i) b a) init as
  foldMapWithIndex f (Vector as) =
    foldMapWithIndex (\i a -> f (unsafeFinite i) a) as

instance (Reflectable n Int) => FunctorWithIndex (Finite n) (Vector n) where
  mapWithIndex f (Vector as) = Vector $ mapWithIndex (\i a -> f (unsafeFinite i) a) as

instance Reflectable n Int => TraversableWithIndex (Finite n) (Vector n) where
  traverseWithIndex f (Vector as) = Vector <$> traverseWithIndex (\i a -> f (unsafeFinite i) a) as

generator
  :: forall n m proxy a
   . Reflectable n Int
  => MonadGen m
  => proxy n
  -> m a
  -> m (Vector n a)
generator _ gen = Vector <$> replicateA (reflectType (Proxy @n)) gen

unVector :: forall a n. Vector n a -> Array a
unVector (Vector as) = as

nilVector :: forall a. Vector 0 a
nilVector = Vector mempty

vCons :: forall a n nInc. Add n 1 nInc => a -> Vector n a -> Vector nInc a
vCons a (Vector as) = Vector (a : as)

infixr 6 vCons as :<

length :: forall a n. Reflectable n Int => Vector n a -> Int
length _ = reflectType (Proxy @n)

toVector :: forall a (n :: Int) proxy. Reflectable n Int => proxy n -> Array a -> Maybe (Vector n a)
toVector _ as =
  if reflectType (Proxy @n) /= A.length as then
    Nothing
  else
    Just (Vector as)

concat
  :: forall n m k a
   . Add n m k
  => Vector n a
  -> Vector m a
  -> Vector k a
concat (Vector as) (Vector as') = Vector (as <> as')

flatten
  :: forall n m k a
   . Mul n m k
  => Vector n (Vector m a)
  -> Vector k a
flatten (Vector vectors) = Vector (Array.concatMap unVector vectors)

zip
  :: forall a b n
   . Vector n a
  -> Vector n b
  -> Vector n (Tuple a b)
zip = zipWith Tuple

zipWith
  :: forall a b n c
   . (a -> b -> c)
  -> Vector n a
  -> Vector n b
  -> Vector n c
zipWith f (Vector as) (Vector bs) =
  Vector (Array.zipWith f as bs)

unzip
  :: forall a b n
   . Vector n (Tuple a b)
  -> Tuple (Vector n a) (Vector n b)
unzip (Vector cs) =
  let
    Tuple as bs = Array.unzip cs
  in
    Tuple (Vector as) (Vector bs)

index :: forall a n. Reflectable n Int => Vector n a -> Finite n -> a
index (Vector as) k =
  unsafePartial $ fromJust $
    as Array.!! (getFinite k)

infixl 8 index as !!

generate :: forall n a. Reflectable n Int => (Finite n -> a) -> Vector n a
generate f = Vector $ map f (finites $ Proxy @n)

generateA :: forall n a f. Reflectable n Int => Applicative f => (Finite n -> f a) -> f (Vector n a)
generateA f = Vector <$> traverse f (finites $ Proxy @n)

instance (CircuitType f a var, Reflectable n Int) => CircuitType f (Vector n a) (Vector n var) where
  valueToFields as = foldMap valueToFields (unVector as)
  fieldsToValue as =
    let
      cs = chunk (sizeInFields (Proxy @f) (Proxy @a)) as
      vals = fieldsToValue <$> cs
    in
      unsafePartial $ fromJust $ toVector (Proxy @n) vals
  sizeInFields pf _ = reflectType (Proxy @n) * sizeInFields pf (Proxy @a)
  varToFields as = foldMap (varToFields @f @a) (unVector as)
  fieldsToVar as =
    let
      cs = chunk (sizeInFields (Proxy @f) (Proxy @a)) as
      vals = fieldsToVar @f @a <$> cs
    in
      unsafePartial $ fromJust $ toVector (Proxy @n) vals

instance CheckedType var c => CheckedType (Vector n var) c where
  check (Vector var) = foldMap check var

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

scanl :: forall a b n. (b -> a -> b) -> b -> Vector n a -> Vector n b
scanl f init (Vector as) = Vector $ Array.scanl f init as

append :: forall n m k a. Add m n k => Vector n a -> Vector m a -> Vector k a
append (Vector as) (Vector as') = Vector $ as <> as'

splitAt
  :: forall n k m a
   . Reflectable k Int
  => Compare k n LT
  => Add m k n
  => Proxy k
  -> Vector n a
  -> { before :: Vector k a, after :: Vector m a }
splitAt pk (Vector as) =
  let
    { after, before } = Array.splitAt (reflectType pk) as
  in
    { after: Vector after, before: Vector before }

chunks
  :: forall n m k a
   . Mul k m n
  => Reflectable k Int
  => Proxy k
  -> Vector n a
  -> Vector m (Vector k a)
chunks pk (Vector as) = Vector (Vector <$> chunk (reflectType pk) as)

head
  :: forall n a
   . Compare 0 n LT
  => Vector n a
  -> a
head (Vector as) = unsafePartial $ fromJust $ Array.head as

last
  :: forall n a
   . Compare 0 n LT
  => Vector n a
  -> a
last (Vector as) = unsafePartial $ fromJust $ Array.last as

reverse :: forall n a. Vector n a -> Vector n a
reverse (Vector as) = Vector (Array.reverse as)