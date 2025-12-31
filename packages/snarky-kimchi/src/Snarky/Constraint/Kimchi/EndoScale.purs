module Snarky.Constraint.Kimchi.EndoScale
  ( EndoScale
  , EndoScaleRound
  , reduce
  , eval
  ) where

import Prelude

import Data.Foldable (all, foldl)
import Data.Maybe (Maybe(..), maybe)
import Data.Traversable (traverse)
import Effect.Exception.Unsafe (unsafeThrow)
import Snarky.Circuit.CVar (Variable)
import Snarky.Circuit.Types (FVar)
import Snarky.Constraint.Kimchi.Reduction (class PlonkReductionM, reduceToVariable)
import Snarky.Constraint.Kimchi.Wire (GateKind(..), KimchiRow)
import Snarky.Curves.Class (class PrimeField, fromInt)
import Snarky.Data.Fin (unsafeFinite)
import Snarky.Data.Vector (Vector, (:<), (!!))
import Snarky.Data.Vector as Vector

type EndoScaleRound f =
  { n0 :: FVar f
  , n8 :: FVar f
  , a0 :: FVar f
  , a8 :: FVar f
  , b0 :: FVar f
  , b8 :: FVar f
  , xs :: Vector 8 (FVar f)
  }

type EndoScale f = Vector 8 (EndoScaleRound f)

reduce
  :: forall f m
   . PrimeField f
  => PlonkReductionM m f
  => EndoScale f
  -> m (Vector 8 (KimchiRow f))
reduce cs =
  traverse reduceRound cs
  where
  reduceRound c = do
    n0 <- reduceToVariable c.n0
    n8 <- reduceToVariable c.n8
    a0 <- reduceToVariable c.a0
    b0 <- reduceToVariable c.b0
    a8 <- reduceToVariable c.a8
    b8 <- reduceToVariable c.b8
    xs <- traverse reduceToVariable c.xs
    let
      variables =
        let
          vs = Just n0 :< Just n8 :< Just a0 :< Just a8 :< Just b0 :< Just b8 :< (Just <$> xs)
        in
          vs `Vector.append` (Nothing :< Vector.nil)
    pure { kind: EndoScale, coeffs: Vector.generate (const zero), variables }

eval
  :: forall f m
   . PrimeField f
  => Applicative m
  => (Variable -> m f)
  -> Vector 8 (KimchiRow f)
  -> m Boolean
eval lookup rounds = ado
  bs <- traverse (\r -> evalRound r.variables) rounds
  in all identity bs
  where
  double x = x + x
  aF x
    | x == zero = zero
    | x == one = zero
    | x == fromInt 2 = -one
    | x == fromInt 3 = one
    | otherwise = unsafeThrow ("unexpecte cF application: " <> show x)
  bF x
    | x == zero = -one
    | x == one = one
    | x == fromInt 2 = zero
    | x == fromInt 3 = zero
    | otherwise = unsafeThrow ("unexpecte dF application: " <> show x)
  lookup' = maybe (pure zero) lookup
  evalRound round = ado
    xs <- traverse lookup' (Vector.take @8 $ Vector.drop @6 round)
    n0 <- lookup' (round !! unsafeFinite 0)
    n8 <- lookup' (round !! unsafeFinite 1)
    a0 <- lookup' (round !! unsafeFinite 2)
    a8 <- lookup' (round !! unsafeFinite 3)
    b0 <- lookup' (round !! unsafeFinite 4)
    b8 <- lookup' (round !! unsafeFinite 5)
    in
      foldl (\acc x -> double (double acc) + x) n0 xs == n8
        && foldl (\acc x -> double acc + aF x) a0 xs == a8
        &&
          foldl (\acc x -> double acc + bF x) b0 xs == b8
