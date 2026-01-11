module Data.Fin where

import Prelude

import Data.Array ((..))
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