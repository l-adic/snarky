module Snarky.Constraint.Kimchi.EndoScale where

import Prelude

import Data.Foldable (all, foldl, traverse_)
import Data.Maybe (Maybe(..))
import Data.Traversable (traverse)
import Effect.Exception.Unsafe (unsafeThrow)
import Snarky.Circuit.CVar (Variable)
import Snarky.Circuit.CVar as CVar
import Snarky.Circuit.Types (FVar)
import Snarky.Constraint.Kimchi.Reduction (class PlonkReductionM, addRow, reduceToVariable)
import Snarky.Constraint.Kimchi.Wire (GateKind(..))
import Snarky.Curves.Class (class PrimeField, fromInt)
import Snarky.Data.Vector (Vector, (:<))
import Snarky.Data.Vector as Vector

type EndoScaleRound f =
  { n0 :: f
  , n8 :: f
  , a0 :: f
  , a8 :: f
  , b0 :: f
  , b8 :: f
  , xs :: Vector 8 f
  }

type EndoScale f = Vector 8 (EndoScaleRound f)

reduceEndoScalar
  :: forall f m
   . PrimeField f
  => PlonkReductionM m f
  => EndoScale (FVar f)
  -> m Unit
reduceEndoScalar cs =
  traverse_ reduceRound cs
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
      vars =
        let
          vs = Just n0 :< Just n8 :< Just a0 :< Just a8 :< Just b0 :< Just b8 :< (Just <$> xs)
        in
          vs `Vector.append` (Nothing :< Vector.nil)
    addRow vars { kind: EndoScale, coeffs: Vector.generate (const zero) }

eval
  :: forall f m
   . PrimeField f
  => Applicative m
  => (Variable -> m f)
  -> EndoScale (FVar f)
  -> m Boolean
eval lookup cs = ado
  bs <- traverse evalRound cs
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
  evalRound c = ado
    xs <- traverse (CVar.eval lookup) c.xs
    n0 <- CVar.eval lookup c.n0
    n8 <- CVar.eval lookup c.n8
    a0 <- CVar.eval lookup c.a0
    a8 <- CVar.eval lookup c.a8
    b0 <- CVar.eval lookup c.b0
    b8 <- CVar.eval lookup c.b8
    in
      foldl (\acc x -> double (double acc) + x) n0 xs == n8
        && foldl (\acc x -> double acc + aF x) a0 xs == a8
        &&
          foldl (\acc x -> double acc + bF x) b0 xs == b8
