module Snarky.Data.Fin where

import Prelude

import Data.Array ((..))
import Data.Generic.Rep (class Generic)
import Data.Maybe (Maybe(..))
import Data.Reflectable (class Reflectable, reflectType)
import Data.Show.Generic (genericShow)
import Effect.Exception (error)
import Effect.Exception.Unsafe (unsafeThrowException)
import Prim.Int (class Add, class Mul)
import Safe.Coerce (coerce)
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

unsafeFinite :: forall n. Reflectable n Int => Int -> Finite n
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

-- [0.. n - 1] + [0.. m - 1] = [0..(n + m - 1) - 1]
add_
  :: forall n m _l k
   . Add n m _l
  => Add k 1 _l
  => Finite n
  -> Finite m
  -> Finite k
add_ (Finite n) (Finite m) = Finite (n + m)

-- n * [0.. m - 1] = [0..(n * m - n)]
--               = [0.. (n * m - n + 1) - 1 ]
scale
  :: forall @n m negN nTimesM k _l
   . Mul n m nTimesM
  => Add n negN 0
  => Add nTimesM negN _l
  => Add _l 1 k
  => Reflectable n Int
  => Finite m
  -> Finite k
scale (Finite m) = Finite (reflectType (Proxy @n) * m)

-- n + [0.. m - 1] = [0..( n + m - 1)]
translate
  :: forall @n m k
   . Add n m k
  => Reflectable n Int
  => Finite m
  -> Finite k
translate (Finite m) = Finite (reflectType (Proxy @n) + m)

relax :: forall m n k. Add n k m => Finite n -> Finite m
relax = coerce