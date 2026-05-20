module Snarky.Constraint.Kimchi.EndoMul
  ( Round
  , EndoMul
  , Rows
  , reduce
  ) where

import Prelude

import Data.Array.NonEmpty (NonEmptyArray)
import Data.Array.NonEmpty as NEA
import Data.Fin (unsafeFinite)
import Data.Maybe (Maybe(..))
import Data.Traversable (traverse)
import Data.Vector (Vector, (:<))
import Data.Vector as Vector
import Snarky.Circuit.DSL (FVar, Variable)
import Snarky.Constraint.Kimchi.Reduction (class PlonkReductionM, reduceToVariable)
import Snarky.Constraint.Kimchi.Types (class ToKimchiRows, GateKind(..), KimchiRow)
import Snarky.Data.EllipticCurve (AffinePoint)

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
  { state :: NEA.NonEmptyArray (Round f)
  , s :: AffinePoint f
  , nAcc :: f
  }

newtype Rows f = Rows (NonEmptyArray (KimchiRow f))

instance ToKimchiRows f (Rows f) where
  toKimchiRows (Rows as) = NEA.toUnfoldable as

reduce
  :: forall f m
   . PlonkReductionM m f
  => EndoMul (FVar f)
  -> m (Rows f)
reduce c = do
  xs <- reduceToVariable c.s.x
  ys <- reduceToVariable c.s.y
  nAcc <- reduceToVariable c.nAcc
  rows <- traverse (\r -> endoMulRound <$> reduceRound r) c.state
  pure $ Rows $ rows `NEA.snoc` finalZeroRow xs ys nAcc

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