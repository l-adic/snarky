module Snarky.Constraint.Kimchi.EndoMul
  ( EndoscaleRound
  , EndoMul
  , EndoMul'
  , eval
  , reduceEndoMul
  , class EndoMulVerifiable
  , verifyEndoMul
  ) where

import Prelude

import Data.Maybe (Maybe(..))
import Data.Traversable (all, traverse, traverse_)
import Snarky.Circuit.CVar (Variable)
import Snarky.Circuit.CVar as CVar
import Snarky.Circuit.Types (FVar)
import Snarky.Constraint.Kimchi.Reduction (class PlonkReductionM, addRow, reduceToVariable)
import Snarky.Constraint.Kimchi.Wire (GateKind(..))
import Snarky.Curves.Class (class PrimeField)
import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Vesta as Vesta
import Snarky.Data.EllipticCurve (AffinePoint)
import Snarky.Data.Fin (unsafeFinite)
import Snarky.Data.Vector (Vector, nil, (:<), (!!))
import Snarky.Data.Vector as Vector

two :: forall f. Semiring f => f
two = one + one

class EndoMulVerifiable f where
  verifyEndoMul :: EndoMul' f -> Boolean

instance EndoMulVerifiable Pallas.ScalarField where
  verifyEndoMul = verifyEndoMul'Generic Pallas.endoCoefficient

instance EndoMulVerifiable Vesta.ScalarField where
  verifyEndoMul = verifyEndoMul'Generic Vesta.endoCoefficient

type EndoscaleRound f =
  { t :: AffinePoint f
  , p :: AffinePoint f
  , r :: AffinePoint f
  , s1 :: f
  , s3 :: f
  , nAcc :: f
  , bits :: Vector 4 f
  }

boolean :: forall f. PrimeField f => f -> Boolean
boolean b = b * b == b

verifyEndoMul'Generic :: forall f. PrimeField f => f -> EndoMul' f -> Boolean
verifyEndoMul'Generic endoCoeff c = all (verifyRound endoCoeff) c.state
  where
  verifyRound :: f -> EndoscaleRound f -> Boolean
  verifyRound endo round =
    let
      { bits, t, p, r, s1, s3, nAcc } = round
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
      nConstraint = (((nAcc * two + b1) * two + b2) * two + b3) * two + b4 - nAcc
      xpXr = p.x - r.x
      xrXs = r.x - c.s.x
      ysYr = c.s.y + r.y
      yrYp = r.y + p.y

    in
      boolean b1
        && boolean b2
        && boolean b3
        && boolean b4
        && ((xq1 - p.x) * s1) == (yq1 - p.y)
        && (((p.x * two - s1Squared) + xq1) * ((xpXr * s1) + yrYp)) == (p.y * two * xpXr)
        && (yrYp * yrYp) == ((xpXr * xpXr) * ((s1Squared - xq1) + r.x))
        && ((xq2 - r.y) * s3) == (yq2 - r.y)
        && (((r.x * two - s3Squared) + xq2) * ((xrXs * s3) + ysYr)) == (r.y * two * xrXs)
        && (ysYr * ysYr) == ((xrXs * xrXs) * ((s3Squared - xq2) + c.s.x))
        &&
          nConstraint == zero

eval
  :: forall f m
   . PrimeField f
  => EndoMulVerifiable f
  => Applicative m
  => (Variable -> m f)
  -> EndoMul' (FVar f)
  -> m Boolean
eval lookup constraint = ado
  xs <- CVar.eval lookup constraint.s.x
  ys <- CVar.eval lookup constraint.s.y
  _finalNAcc <- CVar.eval lookup constraint.nAcc
  rounds <- traverse lookupRound constraint.state
  let c = { s: { x: xs, y: ys }, nAcc: _finalNAcc, state: rounds }
  in verifyEndoMul c

  where
  lookupRound :: EndoscaleRound (FVar f) -> m (EndoscaleRound f)
  lookupRound round = ado
    xt <- CVar.eval lookup round.t.x
    yt <- CVar.eval lookup round.t.y
    xp <- CVar.eval lookup round.p.x
    yp <- CVar.eval lookup round.p.y
    nAcc <- CVar.eval lookup round.nAcc
    xr <- CVar.eval lookup round.r.x
    yr <- CVar.eval lookup round.r.y
    s1 <- CVar.eval lookup round.s1
    s3 <- CVar.eval lookup round.s3
    bits <- traverse (CVar.eval lookup) (round.bits)
    in
      { t: { x: xt, y: yt }
      , p: { x: xp, y: yp }
      , nAcc
      , r: { x: xr, y: yr }
      , s1
      , s3
      , bits
      }

type EndoMul' f =
  { state :: Vector 32 (EndoscaleRound f)
  , s :: AffinePoint f
  , nAcc :: f
  }

type EndoMul f = EndoMul' (FVar f)

reduceEndoMul
  :: forall f m
   . PrimeField f
  => PlonkReductionM m f
  => EndoMul f
  -> m Unit
reduceEndoMul c = do
  xs <- reduceToVariable c.s.x
  ys <- reduceToVariable c.s.y
  nAcc <- reduceToVariable c.nAcc
  traverse_ (\r -> reduceRound r >>= addEndoMul'Round) c.state
  addFinalZeroRow xs ys nAcc

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

  addEndoMul'Round { t, p, nAcc, r, s1, s3, bits } =
    let
      row =
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
          :< Just (bits !! unsafeFinite 0)
          :< Just (bits !! unsafeFinite 1)
          :< Just (bits !! unsafeFinite 2)
          :< Just (bits !! unsafeFinite 3)
          :< nil
    in
      addRow row { kind: EndoMul, coeffs: Vector.generate (const zero) }

  addFinalZeroRow xs ys nAcc =
    let
      row =
        Nothing
          :< Nothing
          :< Nothing
          :< Nothing
          :< Just xs
          :< Just ys
          :< Just nAcc
          :< Nothing
          :< Nothing
          :< Nothing
          :< Nothing
          :< Nothing
          :< Nothing
          :< Nothing
          :< Nothing
          :< nil
    in
      addRow row { kind: Zero, coeffs: Vector.generate (const zero) }