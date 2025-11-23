module Snarky.Data.Vector
  ( Vector
  , unVector
  , nilVector
  , vCons
  , (:<)
  , vectorLength
  , toVector
  , generator
  , zip
  , zipWith
  , unzip
  , index
  , (!!)
  , generate
  , generateA
  ) where

import Prelude

import Control.Monad.Gen (class MonadGen)
import Data.Array ((:))
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
import Prim.Int (class Add)
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
  mapWithIndex f (Vector as) = Vector $ mapWithIndex
    (\i a -> f (unsafeFinite i) a)
    as

instance Reflectable n Int => TraversableWithIndex (Finite n) (Vector n) where
  traverseWithIndex f (Vector as) = Vector <$> traverseWithIndex
    (\i a -> f (unsafeFinite i) a)
    as

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

vectorLength :: forall a n. Reflectable n Int => Vector n a -> Int
vectorLength _ = reflectType (Proxy @n)

toVector
  :: forall a (n :: Int) proxy
   . Reflectable n Int
  => proxy n
  -> Array a
  -> Maybe (Vector n a)
toVector _ as =
  if reflectType (Proxy @n) /= A.length as then
    Nothing
  else
    Just (Vector as)

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

generateA
  :: forall n a f
   . Reflectable n Int
  => Applicative f
  => (Finite n -> f a)
  -> f (Vector n a)
generateA f = Vector <$> traverse f (finites $ Proxy @n)