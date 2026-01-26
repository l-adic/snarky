module Snarky.Circuit.Kimchi.EndoMul (endo, endoInv, endoInvPure) where

import Prelude

import Data.Fin (unsafeFinite)
import Data.Maybe (fromJust)
import Data.Tuple (Tuple(..))
import Data.Vector (Vector, (!!))
import Data.Vector as Vector
import Partial.Unsafe (unsafePartial)
import Prim.Int (class Add)
import Snarky.Circuit.DSL (class CircuitM, F(..), Snarky, addConstraint, assertEqual_, const_, exists, read, readCVar, scale_)
import Snarky.Circuit.DSL.Bits (packPure, unpackPure)
import Snarky.Circuit.Kimchi.AddComplete (addComplete)
import Snarky.Circuit.Kimchi.EndoScalar (toFieldConstant)
import Snarky.Circuit.Kimchi.Utils (mapAccumM)
import Snarky.Circuit.Types (FVar)
import Snarky.Constraint.Kimchi (KimchiConstraint(..))
import Snarky.Curves.Class (class FieldSizeInBits, class FrModule, class HasEndo, class WeierstrassCurve, endoBase, endoScalar, fromAffine, scalarMul, toAffine)
import Snarky.Data.EllipticCurve (AffinePoint)

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

-- | Inverse endomorphism scalar multiplication.
-- | Computes `g / scalar` where scalar is the effective scalar derived from the challenge.
-- |
-- | Implementation: Witness the result, then verify via `endo(result, scalar) == g`.
-- | This is the pattern from mina's `endo_inv` in scalar_challenge.ml.
endoInv
  :: forall @f @f' @g t m n _l
   . FieldSizeInBits f n
  => FieldSizeInBits f' n
  => HasEndo f f'
  => FrModule f' g
  => WeierstrassCurve f g
  => CircuitM f (KimchiConstraint f) t m
  => Add 128 _l n
  => AffinePoint (FVar f)
  -> FVar f
  -> Snarky (KimchiConstraint f) t m (AffinePoint (FVar f))
endoInv g scalar = do
  -- Witness the result: g * (1 / effective_scalar)
  result <- exists $ do
    -- Read the input point
    { x: F gx, y: F gy } <- read @(AffinePoint _) g
    -- Read the scalar challenge
    F scalarVal <- readCVar scalar

    -- Coerce scalar from f to f' via bit representation
    -- (works because both fields have the same bit size n)
    let
      coerceViaBits :: f -> f'
      coerceViaBits = packPure <<< unpackPure

    -- Compute effective scalar in the scalar field f'
    let
      effectiveScalar :: f'
      effectiveScalar = toFieldConstant (coerceViaBits scalarVal) (endoScalar @f @f')

    -- Compute inverse scalar
    let
      invScalar :: f'
      invScalar = recip effectiveScalar

    -- Convert input point to curve group element and scale by inverse
    let
      gPoint :: g
      gPoint = fromAffine @f @g { x: gx, y: gy }

      resultPoint :: g
      resultPoint = scalarMul invScalar gPoint

    -- Convert result back to AffinePoint
    let { x: rx, y: ry } = unsafePartial $ fromJust $ toAffine @f @g resultPoint
    pure { x: F rx, y: F ry }

  -- Verify: endo(result, scalar) == g
  computed <- endo result scalar
  assertEqual_ computed.x g.x
  assertEqual_ computed.y g.y
  pure result

-- | Pure version of endoInv for reference implementations.
-- | Computes point / effective_scalar where effective_scalar = toFieldConstant(scalar, endoScalar).
endoInvPure
  :: forall f f' g n _l
   . FieldSizeInBits f n
  => FieldSizeInBits f' n
  => HasEndo f f'
  => FrModule f' g
  => WeierstrassCurve f g
  => Add 128 _l n
  => AffinePoint f
  -> f
  -> AffinePoint f
endoInvPure point scalar =
  let
    -- Coerce scalar from f to f' via bit representation
    coerceViaBits :: f -> f'
    coerceViaBits = packPure <<< unpackPure

    -- Compute effective scalar in the scalar field f'
    effectiveScalar :: f'
    effectiveScalar = toFieldConstant (coerceViaBits scalar) (endoScalar @f @f')

    -- Compute inverse scalar
    invScalar :: f'
    invScalar = recip effectiveScalar

    -- Convert to projective, scale, convert back
    projPoint :: g
    projPoint = fromAffine @f @g point

    resultPoint :: g
    resultPoint = scalarMul invScalar projPoint

    { x, y } = unsafePartial $ fromJust $ toAffine @f @g resultPoint
  in
    { x, y }