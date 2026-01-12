module Data.Fin where

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

newtype Finite (n :: Int) = Finite Int

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

finite :: forall n. Reflectable n Int => Int -> Maybe (Finite n)
finite k =
  let
    n = reflectType (Proxy @n)
  in
    if k >= 0 && k < n then Just (Finite k)
    else Nothing

unsafeFinite :: forall @n. Reflectable n Int => Int -> Finite n
unsafeFinite k =
  case finite k of
    Just k' -> k'
    Nothing ->
      let
        n = reflectType (Proxy @n)
      in
        unsafeThrowException (error ("Attempted to coerce " <> show k <> " to Finite " <> show n))

finites :: forall @n. Reflectable n Int => Array (Finite n)
finites =
  let
    n = reflectType (Proxy @n)
  in
    Finite <$> (0 .. (n - 1))