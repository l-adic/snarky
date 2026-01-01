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
import Snarky.Constraint.Kimchi.Wire (GateKind(..), KimchiRow)
import Snarky.Curves.Class (class HasEndo, class PrimeField, endoScalar)
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

eval
  :: forall @f @f' m
   . PrimeField f
  => HasEndo f' f
  => Monad m
  => (Variable -> m f)
  -> Rows f
  -> m Boolean
eval lookup (Rows rs) = do
  let rs' = map _.variables rs
  final <- traverse lookup' $ Vector.last rs'
  let
    s =
      { x: final !! unsafeFinite 4
      , y: final !! unsafeFinite 5
      }
    nAcc = final !! unsafeFinite 6
  rounds <- do
    let
      { before } = Vector.splitAt @32 rs'
      { after } = Vector.splitAt @1 rs'
      roundPairs = Vector.zip before after
    traverse (lookupRound s) roundPairs
  pure $ verifyEndoMul (endoScalar @f' @f) { s, nAcc, state: rounds }
  where
  lookup' = maybe (pure zero) lookup

  lookupRound
    :: AffinePoint f
    -> Tuple
         (Vector 15 (Maybe Variable))
         (Vector 15 (Maybe Variable))
    -> m (Round f)
  lookupRound s (Tuple round next) = do
    { before, after: bits } <- Vector.splitAt @11 <$> traverse lookup' round
    let
      xt = before !! unsafeFinite 0
      yt = before !! unsafeFinite 1
      xp = before !! unsafeFinite 4
      yp = before !! unsafeFinite 5
      nAcc = before !! unsafeFinite 6
      xr = before !! unsafeFinite 7
      yr = before !! unsafeFinite 8
      s1 = before !! unsafeFinite 9
      s3 = before !! unsafeFinite 10
    nAccNext <- lookup' $ next !! unsafeFinite 6
    pure
      { t: { x: xt, y: yt }
      , p: { x: xp, y: yp }
      , nAcc
      , r: { x: xr, y: yr }
      , s
      , s1
      , s3
      , bits
      , nAccNext
      }

verifyEndoMul :: forall f. PrimeField f => f -> EndoMul f -> Boolean
verifyEndoMul endo { state } = all verifyRound state
  where
  two :: f
  two = one + one

  boolean :: f -> Boolean
  boolean b = b * b == b
  verifyRound (round :: Round f) =
    let
      { bits, t, p, r, s1, s3, nAcc, s, nAccNext } = round
      b1 = bits !! unsafeFinite 0
      b2 = bits !! unsafeFinite 1
      b3 = bits !! unsafeFinite 2
      b4 = bits !! unsafeFinite 3
      endoMinus1 = endo - one
      xq1 = (one + b1 * endoMinus1) * t.x
      xq2 = (one + b3 * endoMinus1) * t.x
      yq1 = (b2 * two - one) * t.y
      yq2 = (b4 * two - one) * t.y
      s1Squared = s1 * s1
      s3Squared = s3 * s3
      nConstraint = (((nAcc * two + b1) * two + b2) * two + b3) * two + b4 - nAccNext
      xpXr = p.x - r.x
      xrXs = r.x - s.x
      ysYr = s.y + r.y
      yrYp = r.y + p.y

    in
      boolean b1
        && boolean b2
        && boolean b3
        && boolean b4
        && ((xq1 - p.x) * s1) == (yq1 - p.y)
        && (((p.x * two - s1Squared) + xq1) * ((xpXr * s1) + yrYp)) == (p.y * two * xpXr)
        && (yrYp * yrYp) == ((xpXr * xpXr) * ((s1Squared - xq1) + r.x))
        && ((xq2 - r.x) * s3) == (yq2 - r.y)
        && (((r.x * two - s3Squared) + xq2) * ((xrXs * s3) + ysYr)) == (r.y * two * xrXs)
        && (ysYr * ysYr) == ((xrXs * xrXs) * ((s3Squared - xq2) + s.x))
        &&
          nConstraint == (zero @f)

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
      { kind: EndoMul, coeffs: Vector.generate (const zero), variables }

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
      { kind: Zero, coeffs: Vector.generate (const zero), variables }