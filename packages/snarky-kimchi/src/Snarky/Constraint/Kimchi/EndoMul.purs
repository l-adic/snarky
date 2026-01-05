module Snarky.Constraint.Kimchi.EndoMul
  ( Round
  , EndoMul
  , Rows
  , eval
  , reduce
  ) where

import Prelude

import Data.Maybe (Maybe(..), maybe)
import Data.Traversable (all, traverse)
import Data.Tuple (Tuple(..))
import Snarky.Circuit.CVar (Variable)
import Snarky.Circuit.Types (FVar)
import Snarky.Constraint.Kimchi.Reduction (class PlonkReductionM, reduceToVariable)
import Snarky.Constraint.Kimchi.Wire (class ToKimchiRows, GateKind(..), KimchiRow)
import Snarky.Curves.Class (class HasEndo, class PrimeField, endoBase)
import Snarky.Data.EllipticCurve (AffinePoint)
import Snarky.Data.Fin (unsafeFinite)
import Snarky.Data.Vector (Vector, (!!), (:<))
import Snarky.Data.Vector as Vector

type Round f =
  { t :: AffinePoint f
  , p :: AffinePoint f
  , r :: AffinePoint f
  , s :: AffinePoint f
  , s1 :: f
  , s3 :: f
  , nAcc :: f
  , nAccNext :: f
  , bits :: Vector 4 f
  }

type EndoMul f =
  { state :: Vector 32 (Round f)
  , s :: AffinePoint f
  , nAcc :: f
  }

newtype Rows f = Rows (Vector 33 (KimchiRow f))

instance ToKimchiRows f (Rows f) where
  toKimchiRows (Rows as) = Vector.toUnfoldable as

eval
  :: forall @f @f' m
   . PrimeField f
  => HasEndo f f'
  => Monad m
  => (Variable -> m f)
  -> Rows f
  -> m Boolean
eval lookup (Rows rs) = do
  let rs' = map _.variables rs
  let
    { before } = Vector.splitAt @32 rs'
    { after } = Vector.splitAt @1 rs'
    roundPairs = Vector.zip before after
  all identity <$> traverse lookupRound roundPairs
  where
  lookup' = maybe (pure zero) lookup

  lookupRound
    :: Tuple
         (Vector 15 (Maybe Variable))
         (Vector 15 (Maybe Variable))
    -> m Boolean
  lookupRound (Tuple round _next) = do
    { before, after: bits } <- Vector.splitAt @11 <$> traverse lookup' round
    next <- traverse lookup' _next
    let
      b1 = bits !! unsafeFinite 0
      b2 = bits !! unsafeFinite 1
      b3 = bits !! unsafeFinite 2
      b4 = bits !! unsafeFinite 3

      xt = before !! unsafeFinite 0
      yt = before !! unsafeFinite 1

      xs = next !! unsafeFinite 4
      ys = next !! unsafeFinite 5

      xp = before !! unsafeFinite 4
      yp = before !! unsafeFinite 5

      xr = before !! unsafeFinite 7
      yr = before !! unsafeFinite 8

      s1 = before !! unsafeFinite 9
      s3 = before !! unsafeFinite 10

      endoMinus1 = (endoBase @f @f') - one
      xq1 = (one + b1 * endoMinus1) * xt
      xq2 = (one + b3 * endoMinus1) * xt

      yq1 = (double b2 - one) * yt
      yq2 = (double b4 - one) * yt

      s1Squared = square s1
      s3Squared = square s3

      n = before !! unsafeFinite 6
      nNext = next !! unsafeFinite 6
      nConstraint = double (double (double (double n + b1) + b2) + b3) + b4 - nNext

      xpXr = xp - xr
      xrXs = xr - xs

      ysYr = ys + yr
      yrYp = yr + yp

    pure $ all (\x -> x == zero)
      [ boolean b1
      , boolean b2
      , boolean b3
      , boolean b4
      , (xq1 - xp) * s1 - (yq1 - yp)
      , (double xp - s1Squared + xq1) * (xpXr * s1 + yrYp) - double yp * xpXr
      , square yrYp - (square xpXr * (s1Squared - xq1 + xr))
      , (xq2 - xr) * s3 - (yq2 - yr)
      , (double xr - s3Squared + xq2) * (xrXs * s3 + ysYr) - double yr * xrXs
      , square ysYr - (square xrXs * (s3Squared - xq2 + xs))
      , nConstraint
      ]
    where
    double x = x + x
    square x = x * x
    boolean b = b * b - b

reduce
  :: forall f m
   . PrimeField f
  => PlonkReductionM m f
  => EndoMul (FVar f)
  -> m (Rows f)
reduce c = do
  xs <- reduceToVariable c.s.x
  ys <- reduceToVariable c.s.y
  nAcc <- reduceToVariable c.nAcc
  rows <- traverse (\r -> endoMulRound <$> reduceRound r) c.state
  pure $ Rows $ rows `Vector.snoc` finalZeroRow xs ys nAcc

  where
  reduceRound round = do
    let
      reducePoint { x, y } = do
        x' <- reduceToVariable x
        y' <- reduceToVariable y
        pure { x: x', y: y' }
    t <- reducePoint round.t
    p <- reducePoint round.p
    nAcc <- reduceToVariable round.nAcc
    r <- reducePoint round.r
    s1 <- reduceToVariable round.s1
    s3 <- reduceToVariable round.s3
    bits <- traverse reduceToVariable round.bits
    pure { t, p, nAcc, r, s1, s3, bits }

  endoMulRound { t, p, nAcc, r, s1, s3, bits } =
    let
      variables =
        Just t.x
          :< Just t.y
          :< Nothing
          :< Nothing
          :< Just p.x
          :< Just p.y
          :< Just nAcc
          :< Just r.x
          :< Just r.y
          :< Just s1
          :< Just s3
          :< map Just bits
    in
      { kind: EndoMul, coeffs: mempty, variables }

  finalZeroRow xs ys nAcc =
    let
      variables =
        Nothing
          :< Nothing
          :< Nothing
          :< Nothing
          :< Just xs
          :< Just ys
          :< Just nAcc
          :< Vector.generate (const Nothing)
    in
      { kind: Zero, coeffs: mempty, variables }