-- | Length-indexed vectors.
-- |
-- | This module provides `Vector n a`, an array type where the length `n` is
-- | tracked at the type level. This enables compile-time guarantees about
-- | operations like indexing (using `Finite n`) and splitting.
-- |
-- | The API mirrors `Data.Array` where applicable, but operations that change
-- | length use type-level arithmetic constraints (`Add`, `Mul`) to track the
-- | resulting size.
-- |
-- | ```purescript
-- | -- Construction
-- | vec :: Vector 3 Int
-- | vec = 1 :< 2 :< 3 :< nil
-- |
-- | -- Safe indexing with Finite
-- | first :: Int
-- | first = vec !! unsafeFinite 0  -- No Maybe, bounds checked at compile time
-- |
-- | -- Type-safe splitting
-- | { before, after } = splitAt @2 vec
-- | -- before :: Vector 2 Int = [1, 2]
-- | -- after  :: Vector 1 Int = [3]
-- | ```
module Data.Vector
  ( Vector
  , nil
  , toUnfoldable
  , cons
  , snoc
  , (:<)
  , length
  , toVector
  , toVector'
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
  , take
  , drop
  , chunks
  , head
  , tail
  , uncons
  , last
  , unsnoc
  , reverse
  , updateAt
  , modifyAt
  , replicate
  --
  , chunk
  ) where

import Prelude

import Control.Monad.Gen (class MonadGen)
import Data.Array (foldMap, (:))
import Data.Array as A
import Data.Array as Array
import Data.Array.NonEmpty (foldMap1, foldl1)
import Data.Array.NonEmpty as NEA
import Data.Fin (Finite, finites, getFinite, unsafeFinite)
import Data.Foldable (class Foldable)
import Data.FoldableWithIndex (class FoldableWithIndex, foldMapWithIndex, foldlWithIndex, foldrWithIndex)
import Data.FunctorWithIndex (class FunctorWithIndex, mapWithIndex)
import Data.Maybe (Maybe(..), fromJust)
import Data.Reflectable (class Reflectable, reflectType)
import Data.Semigroup.Foldable (class Foldable1, foldr1)
import Data.Traversable (class Traversable, traverse)
import Data.TraversableWithIndex (class TraversableWithIndex, traverseWithIndex)
import Data.Tuple (Tuple(..))
import Data.Unfoldable (class Unfoldable, class Unfoldable1, replicateA)
import Partial.Unsafe (unsafePartial)
import Prim.Int (class Add, class Compare, class Mul)
import Prim.Ordering (LT)
import Test.QuickCheck (class Arbitrary, arbitrary)
import Type.Proxy (Proxy(..))

-- | A vector with a type-level length parameter.
-- |
-- | Internally represented as a plain `Array`, but the phantom type parameter
-- | `n` tracks the length at compile time.
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

instance Add 1 m n => Foldable1 (Vector n) where
  foldl1 f (Vector xs) = foldl1 f (unsafePartial fromJust $ NEA.fromFoldable xs)
  foldr1 f (Vector xs) =
    foldr1 f (unsafePartial fromJust $ NEA.fromFoldable xs)
  foldMap1 f (Vector xs) =
    foldMap1 f (unsafePartial fromJust $ NEA.fromFoldable xs)

instance (Reflectable n Int) => FunctorWithIndex (Finite n) (Vector n) where
  mapWithIndex f (Vector as) = Vector $ mapWithIndex (\i a -> f (unsafeFinite i) a) as

instance Reflectable n Int => TraversableWithIndex (Finite n) (Vector n) where
  traverseWithIndex f (Vector as) = Vector <$> traverseWithIndex (\i a -> f (unsafeFinite i) a) as

-- | Generate a random vector of the specified length using a `MonadGen`.
generator
  :: forall n m a
   . Reflectable n Int
  => MonadGen m
  => Proxy n
  -> m a
  -> m (Vector n a)
generator _ gen = Vector <$> replicateA (reflectType (Proxy @n)) gen

instance (Reflectable n Int, Arbitrary a) => Arbitrary (Vector n a) where
  arbitrary = generator (Proxy @n) arbitrary

-- | The empty vector.
nil :: forall a. Vector 0 a
nil = Vector mempty

-- | Convert a `Vector` to any `Unfoldable` structure.
toUnfoldable :: forall f n. Unfoldable f => Vector n ~> f
toUnfoldable (Vector xs) = Array.toUnfoldable xs

-- | Attach an element to the front of a vector.
-- |
-- | The resulting vector has length `n + 1`.
cons :: forall a n nInc. Add n 1 nInc => a -> Vector n a -> Vector nInc a
cons a (Vector as) = Vector (a : as)

-- | Append an element to the end of a vector.
-- |
-- | The resulting vector has length `n + 1`.
snoc :: forall a n nInc. Add n 1 nInc => Vector n a -> a -> Vector nInc a
snoc (Vector as) a = Vector (as `Array.snoc` a)

-- | Infix alias for `cons`.
-- |
-- | ```purescript
-- | 1 :< 2 :< 3 :< nil :: Vector 3 Int
-- | ```
infixr 6 cons as :<

-- | Get the length of a vector. This is a compile-time constant.
length :: forall a n. Reflectable n Int => Vector n a -> Int
length _ = reflectType (Proxy @n)

-- | Attempt to convert an array to a vector of the specified length.
-- | Returns `Nothing` if the array length doesn't match.
-- |
-- | ```purescript
-- | toVector @3 [1, 2, 3] = Just (Vector [1, 2, 3])
-- | toVector @3 [1, 2] = Nothing
-- | ```
toVector :: forall a @n. Reflectable n Int => Array a -> Maybe (Vector n a)
toVector as =
  if reflectType (Proxy @n) /= A.length as then
    Nothing
  else
    Just (Vector as)

-- | Variant of `toVector` that takes the length as a proxy argument.
toVector' :: forall n a. Reflectable n Int => Proxy n -> Array a -> (Maybe (Vector n a))
toVector' _ = toVector

-- | Flatten a vector of vectors into a single vector.
-- |
-- | The result has length `n * m` where `n` is the outer length and `m` is
-- | the inner length.
concat
  :: forall n m k a
   . Mul n m k
  => Vector n (Vector m a)
  -> Vector k a
concat (Vector as) = Vector (foldMap toUnfoldable as)

-- | Alias for `concat`.
flatten
  :: forall n m k a
   . Mul n m k
  => Vector n (Vector m a)
  -> Vector k a
flatten (Vector vectors) = Vector (Array.concatMap toUnfoldable vectors)

-- | Combine two vectors into a vector of pairs.
zip
  :: forall a b n
   . Vector n a
  -> Vector n b
  -> Vector n (Tuple a b)
zip = zipWith Tuple

-- | Combine two vectors element-wise using a function.
zipWith
  :: forall a b n c
   . (a -> b -> c)
  -> Vector n a
  -> Vector n b
  -> Vector n c
zipWith f (Vector as) (Vector bs) =
  Vector (Array.zipWith f as bs)

-- | Separate a vector of pairs into a pair of vectors.
unzip
  :: forall a b n
   . Vector n (Tuple a b)
  -> Tuple (Vector n a) (Vector n b)
unzip (Vector cs) =
  let
    Tuple as bs = Array.unzip cs
  in
    Tuple (Vector as) (Vector bs)

-- | Index into a vector using a `Finite n` index.
-- |
-- | This is total because `Finite n` can only hold values `0` to `n-1`.
index :: forall a n. Reflectable n Int => Vector n a -> Finite n -> a
index (Vector as) k =
  unsafePartial $ fromJust $
    as Array.!! (getFinite k)

-- | Infix alias for `index`.
infixl 8 index as !!

-- | Create a vector by applying a function to each index.
-- |
-- | ```purescript
-- | generate @3 getFinite = Vector [0, 1, 2]
-- | ```
generate :: forall n a. Reflectable n Int => (Finite n -> a) -> Vector n a
generate f = Vector $ map f (finites @n)

-- | Create a vector by applying an effectful function to each index.
generateA :: forall @n a f. Reflectable n Int => Applicative f => (Finite n -> f a) -> f (Vector n a)
generateA f = Vector <$> traverse f (finites @n)

-- | Create a vector of `n` copies of a value.
replicate :: forall n a. Reflectable n Int => a -> Vector n a
replicate a = generate (const a)

-- | Split an array into chunks of the specified size (internal helper).
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

-- | Fold from the left, keeping all intermediate results.
scanl :: forall a b n. (b -> a -> b) -> b -> Vector n a -> Vector n b
scanl f init (Vector as) = Vector $ Array.scanl f init as

-- | Concatenate two vectors.
-- |
-- | The result has length `n + m`.
append :: forall n m k a. Add n m k => Vector n a -> Vector m a -> Vector k a
append (Vector as) (Vector as') = Vector $ as <> as'

-- | Split a vector at a given index.
-- |
-- | ```purescript
-- | splitAt @2 (1 :< 2 :< 3 :< nil) = { before: 1 :< 2 :< nil, after: 3 :< nil }
-- | ```
splitAt
  :: forall n @k m a
   . Reflectable k Int
  => Add k m n
  => Vector n a
  -> { before :: Vector k a, after :: Vector m a }
splitAt (Vector as) =
  let
    { after, before } = Array.splitAt (reflectType $ Proxy @k) as
  in
    { after: Vector after, before: Vector before }

-- | Take the first `k` elements of a vector.
take
  :: forall n @k m a
   . Reflectable k Int
  => Add k m n
  => Vector n a
  -> Vector k a
take (Vector as) =
  Vector $ Array.take (reflectType $ Proxy @k) as

-- | Drop the first `k` elements of a vector.
drop
  :: forall n @k m a
   . Reflectable k Int
  => Add k m n
  => Vector n a
  -> Vector m a
drop (Vector as) =
  Vector $ Array.drop (reflectType $ Proxy @k) as

-- | Split a vector into chunks of size `k`.
-- |
-- | The type system ensures `n = k * m` where `m` is the number of chunks.
-- |
-- | ```purescript
-- | chunks @2 (1 :< 2 :< 3 :< 4 :< nil)
-- |   = (1 :< 2 :< nil) :< (3 :< 4 :< nil) :< nil
-- | ```
chunks
  :: forall n m @k a
   . Mul k m n
  => Reflectable k Int
  => Vector n a
  -> Vector m (Vector k a)
chunks (Vector as) = Vector (Vector <$> chunk (reflectType $ Proxy @k) as)

-- | Get the first element of a non-empty vector.
-- |
-- | The `Compare 0 n LT` constraint ensures `n > 0`.
head
  :: forall n a
   . Compare 0 n LT
  => Vector n a
  -> a
head (Vector as) = unsafePartial $ fromJust $ Array.head as

-- | Get all elements after the first.
-- |
-- | The result has length `n - 1`.
tail
  :: forall n m a
   . Add 1 m n
  => Vector n a
  -> Vector m a
tail (Vector as) = Vector $ unsafePartial $ fromJust $ Array.tail as

-- | Decompose a non-empty vector into its head and tail.
uncons
  :: forall n m a
   . Add 1 m n
  => Vector n a
  -> { head :: a, tail :: Vector m a }
uncons (Vector as) =
  let
    { head, tail } = unsafePartial $ fromJust $ Array.uncons as
  in
    { head, tail: Vector tail }

-- | Get the last element of a non-empty vector.
last
  :: forall n a
   . Compare 0 n LT
  => Vector n a
  -> a
last (Vector as) = unsafePartial $ fromJust $ Array.last as

-- | Decompose a non-empty vector into its last element and all preceding elements.
unsnoc
  :: forall n m a
   . Add 1 m n
  => Vector n a
  -> { last :: a, init :: Vector m a }
unsnoc (Vector as) =
  let
    { init, last } = unsafePartial $ fromJust $ Array.unsnoc as
  in
    { last, init: Vector init }

-- | Reverse a vector.
reverse :: forall n a. Vector n a -> Vector n a
reverse (Vector as) = Vector (Array.reverse as)

-- | Update the element at the specified index.
updateAt :: forall n a. Finite n -> a -> Vector n a -> Vector n a
updateAt n a (Vector as) =
  Vector
    $ unsafePartial fromJust
    $
      Array.updateAt (getFinite n) a as

-- | Apply a function to the element at the specified index.
modifyAt :: forall n a. Finite n -> (a -> a) -> Vector n a -> Vector n a
modifyAt n a (Vector as) =
  Vector
    $ unsafePartial fromJust
    $
      Array.modifyAt (getFinite n) a as