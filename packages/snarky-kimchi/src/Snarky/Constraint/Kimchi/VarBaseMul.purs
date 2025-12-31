module Snarky.Constraint.Kimchi.VarBaseMul
  ( VarBaseMul
  , ScaleRound
  , eval
  , reduce
  , class VarBaseMulVerifiable
  , verifyVarBaseMul
  ) where

import Prelude

import Data.Array (all)
import Data.Function.Uncurried (Fn1, runFn1)
import Data.Maybe (Maybe(..), maybe)
import Data.Traversable (for, traverse)
import Snarky.Circuit.CVar (Variable)
import Snarky.Circuit.Types (FVar)
import Snarky.Constraint.Kimchi.Reduction (class PlonkReductionM, reduceToVariable)
import Snarky.Constraint.Kimchi.Wire (KimchiRow)
import Snarky.Constraint.Kimchi.Wire as Wire
import Snarky.Curves.Class (class PrimeField)
import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Vesta as Vesta
import Snarky.Data.EllipticCurve (AffinePoint)
import Snarky.Data.Fin (unsafeFinite)
import Snarky.Data.Vector (Vector, index, nil, (:<))
import Snarky.Data.Vector as Vector

type ScaleRound a =
  { accs :: Vector 6 (AffinePoint a)
  , bits :: Vector 5 a
  , slopes :: Vector 5 a
  , nPrev :: a
  , nNext :: a
  , base :: AffinePoint a
  }

type VarBaseMul f = Array (ScaleRound f)

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
  -> Array (Vector 2 (KimchiRow f))
  -> m Boolean
eval lookup rounds = do
  let
    f round = for round \r ->
      for r.variables \var ->
        maybe (pure zero) lookup var
  all verifyVarBaseMul <$> traverse f rounds

reduce
  :: forall f m
   . PrimeField f
  => PlonkReductionM m f
  => VarBaseMul (FVar f)
  -> m (Array (Vector 2 (KimchiRow f)))
reduce c =
  traverse (map makeRows <<< reduceRound) c
  where
  reduceRound round = do
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

  makeRows :: ScaleRound Variable -> Vector 2 (KimchiRow f)
  makeRows { accs, bits, slopes, nPrev, nNext, base } =
    let
      finite5 i = unsafeFinite @5 i
      finite6 i = unsafeFinite @6 i
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
            nil
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
            nil
    in
      { kind: Wire.VarBaseMul, coeffs: Vector.generate (const zero), variables: row }
        :< { kind: Wire.Zero, coeffs: Vector.generate (const zero), variables: nextRow }
        :<
          nil

foreign import verifyPallasVarBaseMulGadget
  :: Fn1 (Vector 2 (Vector 15 Pallas.ScalarField)) Boolean

foreign import verifyVestaVarBaseMulGadget
  :: Fn1 (Vector 2 (Vector 15 Vesta.ScalarField)) Boolean

verifyPallasVarBaseMul :: Vector 2 (Vector 15 Pallas.ScalarField) -> Boolean
verifyPallasVarBaseMul witness = runFn1 verifyPallasVarBaseMulGadget witness

verifyVestaVarBaseMul :: Vector 2 (Vector 15 Vesta.ScalarField) -> Boolean
verifyVestaVarBaseMul witness = runFn1 verifyVestaVarBaseMulGadget witness