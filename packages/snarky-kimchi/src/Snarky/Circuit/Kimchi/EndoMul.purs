module Snarky.Circuit.Kimchi.EndoMul where

import Prelude

import Control.Monad.State (StateT(..), runStateT)
import Data.Traversable (class Traversable, foldl, traverse)
import Data.Tuple (Tuple(..))
import Prim.Int (class Add)
import Snarky.Circuit.DSL (class CircuitM, F(..), Snarky, addConstraint, const_, exists, read, readCVar, scale_)
import Snarky.Circuit.DSL.Bits (unpackPure)
import Snarky.Circuit.Kimchi.AddComplete (addComplete)
import Snarky.Circuit.Types (FVar)
import Snarky.Constraint.Kimchi (KimchiConstraint(..))
import Snarky.Curves.Class (class FieldSizeInBits, class PrimeField)
import Snarky.Data.EllipticCurve (AffinePoint)
import Snarky.Data.Fin (unsafeFinite)
import Snarky.Data.Vector (Vector, (!!))
import Snarky.Data.Vector as Vector

endo
  :: forall f t m n _l
   . PrimeField f
  => FieldSizeInBits f n
  => CircuitM f (KimchiConstraint f) t m
  => Add 128 _l n
  => F f
  -> AffinePoint (FVar f)
  -> FVar f
  -> Snarky (KimchiConstraint f) t m
       (AffinePoint (FVar f))
endo endoBase@(F f) g scalar = do
  lsbBits <- exists do
    F vVal <- readCVar scalar
    let _lsbBits = Vector.reverse $ Vector.take @128 $ unpackPure vVal
    pure $ map (\x -> if x then (one :: F f) else zero) _lsbBits
  -- acc = [2] (g + \phi g)
  let
    chunks :: Vector 32 (Vector 4 (FVar f))
    chunks = Vector.chunks @4 lsbBits
  accInit <- do
    { p } <- addComplete g (g { x = scale_ f g.x })
    _.p <$> addComplete p p
  Tuple roundsRev { nAcc, acc } <- mapAccumM
    ( \st bs -> do
        { p, r, s, s1, s3, nAcc } <- exists do
          { x: xt, y: yt } <- read @(AffinePoint _) g
          bits <- read bs
          let
            b0 = bits !! unsafeFinite 0
            b1 = bits !! unsafeFinite 1
            b2 = bits !! unsafeFinite 2
            b3 = bits !! unsafeFinite 3
          { x: xp, y: yp } <- read @(AffinePoint _) st.acc
          let
            xq1 = (one + (endoBase - one) * b0) * xt
            yq1 = (double b1 - one) * yt
            s1 = yq1 - yp / xq1 - xp
            s1Squared = square s1
            s2 = (double yp / (double xp + xq1 - s1Squared)) - s1
            xr = xq1 + square s2 - s1Squared
            yr = ((xp - xr) * s2) - yp
            xq2 = (one + (endoBase - one) * b2) * xt
            yq2 = (double b3 - one) * yt
            s3 = (yq2 - yr) / (xq2 - xr)
            s3Squared = square s3
            s4 = (double yr / (double xr + xq2 - s3Squared)) - s3
            xs = xq2 + square s4 - s3Squared
            ys = ((xr - xs) * s4) - yr
          nAccPrevVal <- readCVar st.nAcc
          pure
            { p: { x: xp, y: yp }
            , r: { x: xr, y: yr }
            , s1
            , s3
            , s: { x: xs, y: ys }
            , nAcc: foldl (\a b -> double a + b) nAccPrevVal bits
            }
        pure $ Tuple
          { bits: bs, p, r, s1, s3, t: g, nAcc }
          { nAcc, acc: s }
    )
    { nAcc: const_ zero, acc: accInit }
    chunks
  addConstraint $ KimchiEndoMul { nAcc, s: acc, state: Vector.reverse roundsRev }
  pure acc
  where
  double x = x + x
  square x = x * x

mapAccumM
  :: forall m s t a b
   . Monad m
  => Traversable t
  => (s -> a -> m (Tuple b s))
  -> s
  -> t a
  -> m (Tuple (t b) s)
mapAccumM f initial xs = runStateT (traverse step xs) initial
  where
  step x = StateT (\s -> f s x)