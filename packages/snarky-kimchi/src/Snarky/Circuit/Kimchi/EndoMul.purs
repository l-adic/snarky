module Snarky.Circuit.Kimchi.EndoMul (endo) where

import Prelude

import Data.Tuple (Tuple(..))
import Prim.Int (class Add)
import Snarky.Circuit.DSL (class CircuitM, F(..), Snarky, addConstraint, assertEqual_, const_, exists, read, readCVar, scale_)
import Snarky.Circuit.DSL.Bits (unpackPure)
import Snarky.Circuit.Kimchi.AddComplete (addComplete)
import Snarky.Circuit.Kimchi.Utils (mapAccumM)
import Snarky.Circuit.Types (FVar)
import Snarky.Constraint.Kimchi (KimchiConstraint(..))
import Snarky.Curves.Class (class FieldSizeInBits, class HasEndo, endoBase)
import Snarky.Data.EllipticCurve (AffinePoint)
import Snarky.Data.Fin (unsafeFinite)
import Snarky.Data.Vector (Vector, (!!))
import Snarky.Data.Vector as Vector

endo
  :: forall f f' t m n _l
   . FieldSizeInBits f n
  => HasEndo f f'
  => CircuitM f (KimchiConstraint f) t m
  => Add 128 _l n
  => AffinePoint (FVar f)
  -> FVar f
  -> Snarky (KimchiConstraint f) t m
       (AffinePoint (FVar f))
endo g scalar = do
  msbBits <- exists do
    F vVal <- readCVar scalar
    let lsbBits = Vector.take @128 $ unpackPure vVal
    pure $ map (\x -> if x then (one :: F f) else zero) (Vector.reverse lsbBits)
  -- acc = [2] (g + \phi g)
  let
    chunks :: Vector 32 (Vector 4 (FVar f))
    chunks = Vector.chunks @4 msbBits
  accInit <- do
    { p } <- addComplete g (g { x = scale_ (endoBase @f @f') g.x })
    _.p <$> addComplete p p
  Tuple rounds { nAcc, acc } <- mapAccumM
    ( \st bs -> do
        { p, r, s, s1, s3, nAccNext, nAccPrev } <- exists do
          { x: xt, y: yt } <- read @(AffinePoint _) g
          bits <- read bs
          let
            b1 = bits !! unsafeFinite 0
            b2 = bits !! unsafeFinite 1
            b3 = bits !! unsafeFinite 2
            b4 = bits !! unsafeFinite 3
          { x: xp, y: yp } <- read @(AffinePoint _) st.acc
          let
            xq1 = (one + (F (endoBase @f @f') - one) * b1) * xt
            yq1 = (double b2 - one) * yt
            s1 = (yq1 - yp) / (xq1 - xp)
            s1Squared = square s1
            s2 = (double yp / (double xp + xq1 - s1Squared)) - s1
            xr = xq1 + square s2 - s1Squared
            yr = ((xp - xr) * s2) - yp
            xq2 = (one + (F (endoBase @f @f') - one) * b3) * xt
            yq2 = (double b4 - one) * yt
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
            , nAccPrev: nAccPrevVal
            , nAccNext: double (double (double (double nAccPrevVal + b1) + b2) + b3) + b4
            }
        pure $ Tuple
          { bits: bs, p, r, s1, s3, t: g, nAcc: nAccPrev, nAccNext, s }
          { nAcc: nAccNext, acc: s }
    )
    { nAcc: const_ zero, acc: accInit }
    chunks
  assertEqual_ nAcc scalar
  addConstraint $ KimchiEndoMul { nAcc, s: acc, state: rounds }
  pure acc
  where
  double x = x + x
  square x = x * x