module Snarky.Constraint.Kimchi.EndoScalar
  ( EndoScalar
  , EndoScalarRound
  , Rows
  , reduce
  , eval
  ) where

import Prelude

import Data.Fin (unsafeFinite)
import Data.Foldable (all, foldl)
import Data.Maybe (Maybe(..), maybe)
import Data.Traversable (traverse)
import Data.Vector (Vector, (!!), (:<))
import Data.Vector as Vector
import Effect.Exception.Unsafe (unsafeThrow)
import Snarky.Circuit.DSL (FVar, Variable)
import Snarky.Constraint.Kimchi.Reduction (class PlonkReductionM, reduceToVariable)
import Snarky.Constraint.Kimchi.Types (class ToKimchiRows, GateKind(..), KimchiRow)
import Snarky.Curves.Class (class PrimeField, fromInt)

type EndoScalarRound f =
  { n0 :: FVar f
  , n8 :: FVar f
  , a0 :: FVar f
  , a8 :: FVar f
  , b0 :: FVar f
  , b8 :: FVar f
  , xs :: Vector 8 (FVar f)
  }

type EndoScalar f = Vector 8 (EndoScalarRound f)

newtype Rows f = Rows (Vector 8 (KimchiRow f))

instance ToKimchiRows f (Rows f) where
  toKimchiRows (Rows as) = Vector.toUnfoldable as

reduce
  :: forall f m
   . PlonkReductionM m f
  => EndoScalar f
  -> m (Rows f)
reduce cs = Rows <$>
  traverse reduceRound cs
  where
  -- OCaml's Endoscale_scalar_round.map evaluates record fields right-to-left,
  -- so reduce_to_v is called on xs, b8, a8, b0, a0, n8, n0 in that order.
  -- This matters for constant deduplication: b0 and a0 are both Const 2 in
  -- the first round, so whichever is reduced first creates the variable and
  -- the second reuses it via cached_constants.
  reduceRound c = do
    xs <- traverse reduceToVariable c.xs
    b8 <- reduceToVariable c.b8
    a8 <- reduceToVariable c.a8
    b0 <- reduceToVariable c.b0
    a0 <- reduceToVariable c.a0
    n8 <- reduceToVariable c.n8
    n0 <- reduceToVariable c.n0
    let
      variables =
        let
          vs = Just n0 :< Just n8 :< Just a0 :< Just b0 :< Just a8 :< Just b8 :< (Just <$> xs)
        in
          vs `Vector.append` (Nothing :< Vector.nil)
    pure { kind: EndoScalar, coeffs: mempty, variables }

eval
  :: forall f m
   . PrimeField f
  => Applicative m
  => (Variable -> m f)
  -> Rows f
  -> m Boolean
eval lookup (Rows rounds) = ado
  bs <- traverse (\r -> evalRound r.variables) rounds
  in all identity bs
  where
  double x = x + x
  aF x
    | x == zero = zero
    | x == one = zero
    | x == fromInt 2 = -one
    | x == fromInt 3 = one
    | otherwise = unsafeThrow ("unexpected aF application: " <> show x)
  bF x
    | x == zero = -one
    | x == one = one
    | x == fromInt 2 = zero
    | x == fromInt 3 = zero
    | otherwise = unsafeThrow ("unexpected bF application: " <> show x)
  evalRound round = ado
    xs <- traverse lookup' xs
    n0 <- lookup' (cs !! finite6 0)
    n8 <- lookup' (cs !! finite6 1)
    a0 <- lookup' (cs !! finite6 2)
    b0 <- lookup' (cs !! finite6 3)
    a8 <- lookup' (cs !! finite6 4)
    b8 <- lookup' (cs !! finite6 5)
    in
      foldl (\acc x -> double (double acc) + x) n0 xs == n8
        && foldl (\acc x -> double acc + aF x) a0 xs == a8
        &&
          foldl (\acc x -> double acc + bF x) b0 xs == b8
    where
    lookup' = maybe (pure zero) lookup
    { before: cs, after } = Vector.splitAt @6 round
    xs = Vector.take @8 after
    finite6 = unsafeFinite @6
