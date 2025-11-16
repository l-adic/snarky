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
  , replicate
  ) where

import Prelude

import Control.Monad.Gen (class MonadGen)
import Data.Array ((:))
import Data.Array as A
import Data.Array as Array
import Data.Foldable (class Foldable)
import Data.Maybe (Maybe(..))
import Data.Reflectable (class Reflectable, reflectType)
import Data.Traversable (class Traversable)
import Data.Tuple (Tuple(..))
import Data.Unfoldable (class Unfoldable, class Unfoldable1, replicateA)
import Prim.Int (class Add)
import Type.Proxy (Proxy(..))

newtype Vector (n :: Int) a = Vector (Array a)

derive newtype instance Show a => Show (Vector n a)
derive newtype instance Eq a => Eq (Vector n a)
derive newtype instance Functor (Vector n)
derive newtype instance Unfoldable1 (Vector n)
derive newtype instance Unfoldable (Vector n)
derive newtype instance Foldable (Vector n)
derive newtype instance Traversable (Vector n)

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

vectorLength :: forall a n. Vector n a -> Int
vectorLength (Vector as) = A.length as

toVector :: forall a (n :: Int) proxy. Reflectable n Int => proxy n -> Array a -> Maybe (Vector n a)
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

replicate
  :: forall a n
   . Reflectable n Int
  => a
  -> Vector n a
replicate a = Vector $ Array.replicate (reflectType (Proxy @n)) a