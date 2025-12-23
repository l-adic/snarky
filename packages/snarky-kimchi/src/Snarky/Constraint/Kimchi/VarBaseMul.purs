module Snarky.Constraint.Kimchi.VarBaseMul where

import Prelude

import Data.Maybe (Maybe(..))
import Data.Traversable (traverse, traverse_)
import Snarky.Circuit.Types (FVar)
import Snarky.Constraint.Kimchi.Reduction (class PlonkReductionM, addRow, reduceToVariable)
import Snarky.Constraint.Kimchi.Wire (GateKind(..))
import Snarky.Curves.Class (class PrimeField)
import Snarky.Data.EllipticCurve (AffinePoint)
import Snarky.Data.Fin (Finite, unsafeFinite)
import Snarky.Data.Vector (Vector, index, nilVector, (:<))
import Snarky.Data.Vector as Vector

type ScaleRound f =
  { accs :: Vector 6 (AffinePoint (FVar f))
  , bits :: Vector 5 (FVar f)
  , slopes :: Vector 5 (FVar f)
  , nPrev :: FVar f
  , nNext :: FVar f
  , base :: AffinePoint (FVar f)
  }

type VarBaseMul f = Array (ScaleRound f)

reduceVarBaseMul
  :: forall f m
   . PrimeField f
  => PlonkReductionM m f
  => VarBaseMul f
  -> m Unit
reduceVarBaseMul c =
  traverse_ (\r -> reduce r >>= addRound) c
  where
  reduce round = do
    let
      reducePointToVariable p = do
        x <- reduceToVariable p.x
        y <- reduceToVariable p.y
        pure { x, y }
    accs <- traverse reducePointToVariable round.accs
    bits <- traverse reduceToVariable round.bits
    slopes <- traverse reduceToVariable round.slopes
    nPrev <- reduceToVariable round.nPrev
    nNext <- reduceToVariable round.nNext
    base <- reducePointToVariable round.base
    pure { accs, bits, slopes, nPrev, nNext, base }

  addRound { accs, bits, slopes, nPrev, nNext, base } =
    let
      finite5 i = unsafeFinite i :: Finite 5
      finite6 i = unsafeFinite i :: Finite 6
      row =
        Just base.x
          :< Just base.y
          :< Just (accs `index` finite6 0).x
          :< Just (accs `index` finite6 0).y
          :< Just nPrev
          :< Just nNext
          :< Nothing
          :< Just (accs `index` finite6 1).x
          :< Just (accs `index` finite6 1).y
          :< Just (accs `index` finite6 2).x
          :< Just (accs `index` finite6 2).y
          :< Just (accs `index` finite6 3).x
          :< Just (accs `index` finite6 3).y
          :< Just (accs `index` finite6 4).x
          :< Just (accs `index` finite6 4).y
          :<
            nilVector
      nextRow =
        Just (accs `index` finite6 5).x
          :< Just (accs `index` finite6 5).y
          :< Just (bits `index` finite5 0)
          :< Just (bits `index` finite5 1)
          :< Just (bits `index` finite5 2)
          :< Just (bits `index` finite5 3)
          :< Just (bits `index` finite5 4)
          :< Just (slopes `index` finite5 0)
          :< Just (slopes `index` finite5 1)
          :< Just (slopes `index` finite5 2)
          :< Just (slopes `index` finite5 3)
          :< Just (slopes `index` finite5 4)
          :< Nothing
          :< Nothing
          :< Nothing
          :<
            nilVector
    in
      do
        addRow row { kind: VarBaseMul, coeffs: Vector.generate (const zero) }
        addRow nextRow { kind: Zero, coeffs: Vector.generate (const zero) }