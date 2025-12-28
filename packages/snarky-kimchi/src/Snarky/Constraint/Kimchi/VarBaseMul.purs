module Snarky.Constraint.Kimchi.VarBaseMul
  ( ScaleRound
  , VarBaseMul
  , eval
  , reduceVarBaseMul
  , class VarBaseMulVerifiable
  , verifyVarBaseMul
  ) where

import Prelude

import Data.Array (all)
import Data.Function.Uncurried (Fn1, runFn1)
import Data.Maybe (Maybe(..))
import Data.Traversable (traverse, traverse_)
import Snarky.Circuit.CVar (Variable)
import Snarky.Circuit.CVar as CVar
import Snarky.Circuit.Types (FVar)
import Snarky.Constraint.Kimchi.Reduction (class PlonkReductionM, addRow, reduceToVariable)
import Snarky.Constraint.Kimchi.Wire (GateKind(..))
import Snarky.Curves.Class (class PrimeField)
import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Vesta as Vesta
import Snarky.Data.EllipticCurve (AffinePoint)
import Snarky.Data.Fin (Finite, unsafeFinite)
import Snarky.Data.Vector (Vector, index, nilVector, (:<))
import Snarky.Data.Vector as Vector

class VarBaseMulVerifiable f where
  verifyVarBaseMul :: Vector 2 (Vector 15 f) -> Boolean

instance VarBaseMulVerifiable Pallas.ScalarField where
  verifyVarBaseMul = verifyPallasVarBaseMul

instance VarBaseMulVerifiable Vesta.ScalarField where
  verifyVarBaseMul = verifyVestaVarBaseMul

eval
  :: forall f m
   . PrimeField f
  => VarBaseMulVerifiable f
  => Applicative m
  => (Variable -> m f)
  -> VarBaseMul f
  -> m Boolean
eval lookup constraint =
  all verifyVarBaseMul <$> traverse evaluateScaleRound constraint

  where
  evaluateScaleRound :: ScaleRound f -> m (Vector 2 (Vector 15 f))
  evaluateScaleRound round = ado
    baseX <- CVar.eval lookup round.base.x
    baseY <- CVar.eval lookup round.base.y

    acc0X <- CVar.eval lookup (round.accs `index` unsafeFinite 0).x
    acc0Y <- CVar.eval lookup (round.accs `index` unsafeFinite 0).y
    acc1X <- CVar.eval lookup (round.accs `index` unsafeFinite 1).x
    acc1Y <- CVar.eval lookup (round.accs `index` unsafeFinite 1).y
    acc2X <- CVar.eval lookup (round.accs `index` unsafeFinite 2).x
    acc2Y <- CVar.eval lookup (round.accs `index` unsafeFinite 2).y
    acc3X <- CVar.eval lookup (round.accs `index` unsafeFinite 3).x
    acc3Y <- CVar.eval lookup (round.accs `index` unsafeFinite 3).y
    acc4X <- CVar.eval lookup (round.accs `index` unsafeFinite 4).x
    acc4Y <- CVar.eval lookup (round.accs `index` unsafeFinite 4).y
    acc5X <- CVar.eval lookup (round.accs `index` unsafeFinite 5).x
    acc5Y <- CVar.eval lookup (round.accs `index` unsafeFinite 5).y

    nPrev <- CVar.eval lookup round.nPrev
    nNext <- CVar.eval lookup round.nNext

    b0 <- CVar.eval lookup (round.bits `index` unsafeFinite 0)
    b1 <- CVar.eval lookup (round.bits `index` unsafeFinite 1)
    b2 <- CVar.eval lookup (round.bits `index` unsafeFinite 2)
    b3 <- CVar.eval lookup (round.bits `index` unsafeFinite 3)
    b4 <- CVar.eval lookup (round.bits `index` unsafeFinite 4)

    s0 <- CVar.eval lookup (round.slopes `index` unsafeFinite 0)
    s1 <- CVar.eval lookup (round.slopes `index` unsafeFinite 1)
    s2 <- CVar.eval lookup (round.slopes `index` unsafeFinite 2)
    s3 <- CVar.eval lookup (round.slopes `index` unsafeFinite 3)
    s4 <- CVar.eval lookup (round.slopes `index` unsafeFinite 4)

    in
      let
        row0 = baseX :< baseY :< acc0X :< acc0Y :< nPrev :< nNext :< zero :< acc1X :< acc1Y :< acc2X :< acc2Y :< acc3X :< acc3Y :< acc4X :< acc4Y :< nilVector
        row1 = acc5X :< acc5Y :< b0 :< b1 :< b2 :< b3 :< b4 :< s0 :< s1 :< s2 :< s3 :< s4 :< Vector.generate (const zero)
      in
        row0 :< row1 :< nilVector

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

foreign import verifyPallasVarBaseMulGadget
  :: Fn1 (Vector 2 (Vector 15 Pallas.ScalarField)) Boolean

foreign import verifyVestaVarBaseMulGadget
  :: Fn1 (Vector 2 (Vector 15 Vesta.ScalarField)) Boolean

verifyPallasVarBaseMul :: Vector 2 (Vector 15 Pallas.ScalarField) -> Boolean
verifyPallasVarBaseMul witness = runFn1 verifyPallasVarBaseMulGadget witness

verifyVestaVarBaseMul :: Vector 2 (Vector 15 Vesta.ScalarField) -> Boolean
verifyVestaVarBaseMul witness = runFn1 verifyVestaVarBaseMulGadget witness