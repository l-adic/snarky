-- | Type-safe finite sets.
-- |
-- | This module provides `Finite n`, a type representing the integers
-- | from `0` to `n-1`. The bound `n` is tracked at the type level, enabling
-- | compile-time guarantees about array indexing with `Data.Vector`.
-- |
-- | ```purescript
-- | -- A value of type `Finite 3` can only be 0, 1, or 2
-- | example :: Finite 3
-- | example = unsafeFinite 2
-- |
-- | -- Use with Vector for bounds-safe indexing
-- | vec :: Vector 3 String
-- | vec = "a" :< "b" :< "c" :< nil
-- |
-- | safeIndex :: String
-- | safeIndex = vec !! example  -- Always safe, no Maybe needed
-- | ```
module Data.Fin
  ( Finite(..)
  , getFinite
  , finite
  , unsafeFinite
  , finites
  ) where

import Prelude

import Data.Array ((..))
import Data.Enum (class BoundedEnum, class Enum, Cardinality(..))
import Data.Generic.Rep (class Generic)
import Data.Maybe (Maybe(..))
import Data.Reflectable (class Reflectable, reflectType)
import Data.Show.Generic (genericShow)
import Effect.Exception (error)
import Effect.Exception.Unsafe (unsafeThrowException)
import Type.Proxy (Proxy(..))

-- | A finite type with exactly `n` inhabitants: the integers `0` through `n-1`.
-- |
-- | The internal representation is just an `Int`, but the type parameter
-- | ensures values stay within bounds.
newtype Finite (n :: Int) = Finite Int

-- | Extract the underlying integer from a `Finite` value.
-- |
-- | ```purescript
-- | getFinite (unsafeFinite @5 3) = 3
-- | ```
getFinite :: forall n. Finite n -> Int
getFinite (Finite k) = k

derive instance Generic (Finite n) _

instance Show (Finite n) where
  show x = genericShow x

derive newtype instance Eq (Finite n)
derive newtype instance Ord (Finite n)

instance Reflectable n Int => Bounded (Finite n) where
  top = Finite (reflectType (Proxy @n) - 1)
  bottom = Finite 0

instance Reflectable n Int => Enum (Finite n) where
  succ (Finite k) =
    let
      n = reflectType (Proxy @n)
      next = k + 1
    in
      if k + 1 < n then Just (Finite next)
      else Nothing
  pred (Finite k) =
    if k == 0 then Nothing
    else Just $ Finite (k - 1)

instance Reflectable n Int => BoundedEnum (Finite n) where
  cardinality = Cardinality (reflectType $ Proxy @n)
  toEnum i =
    if i < (reflectType $ Proxy @n) then Just (Finite i)
    else Nothing
  fromEnum (Finite i) = i

-- | Safely construct a `Finite n` from an integer, returning `Nothing` if
-- | the value is out of bounds (less than 0 or greater than or equal to n).
-- |
-- | ```purescript
-- | finite @3 2 = Just (Finite 2)
-- | finite @3 3 = Nothing
-- | finite @3 (-1) = Nothing
-- | ```
finite :: forall n. Reflectable n Int => Int -> Maybe (Finite n)
finite k =
  let
    n = reflectType (Proxy @n)
  in
    if k >= 0 && k < n then Just (Finite k)
    else Nothing

-- | Construct a `Finite n` from an integer, throwing an exception if the
-- | value is out of bounds.
-- |
-- | ```purescript
-- | unsafeFinite @3 2 = Finite 2
-- | unsafeFinite @3 5 -- throws exception
-- | ```
unsafeFinite :: forall @n. Reflectable n Int => Int -> Finite n
unsafeFinite k =
  case finite k of
    Just k' -> k'
    Nothing ->
      let
        n = reflectType (Proxy @n)
      in
        unsafeThrowException (error ("Attempted to coerce " <> show k <> " to Finite " <> show n))

-- | Enumerate all values of `Finite n` in ascending order.
-- |
-- | ```purescript
-- | finites @3 = [Finite 0, Finite 1, Finite 2]
-- | finites @0 = []
-- | ```
finites :: forall @n. Reflectable n Int => Array (Finite n)
finites =
  let
    n = reflectType (Proxy @n)
  in
    Finite <$> (0 .. (n - 1))