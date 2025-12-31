module Snarky.Constraint.Kimchi.AddComplete
  ( AddComplete
  , eval
  , reduce
  , class AddCompleteVerifiable
  , verifyAddComplete
  ) where

import Prelude

import Data.Function.Uncurried (Fn1, runFn1)
import Data.Maybe (Maybe(..))
import Snarky.Circuit.CVar (Variable)
import Snarky.Circuit.CVar as CVar
import Snarky.Circuit.Types (FVar)
import Snarky.Constraint.Kimchi.Reduction (class PlonkReductionM, addRow, reduceToVariable)
import Snarky.Constraint.Kimchi.Wire (GateKind(..))
import Snarky.Curves.Class (class PrimeField)
import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Vesta as Vesta
import Snarky.Data.Vector (Vector, (:<))
import Snarky.Data.Vector as Vector

type AddComplete f =
  { p1 :: { x :: FVar f, y :: FVar f }
  , p2 :: { x :: FVar f, y :: FVar f }
  , p3 :: { x :: FVar f, y :: FVar f }
  , inf :: FVar f
  , sameX :: FVar f
  , s :: FVar f
  , infZ :: FVar f
  , x21Inv :: FVar f
  }

class AddCompleteVerifiable f where
  verifyAddComplete :: Vector 15 f -> Boolean

instance AddCompleteVerifiable Pallas.BaseField where
  verifyAddComplete = verifyPallasCompleteAdd

instance AddCompleteVerifiable Vesta.BaseField where
  verifyAddComplete = verifyVestaCompleteAdd

eval
  :: forall f m
   . PrimeField f
  => AddCompleteVerifiable f
  => Applicative m
  => (Variable -> m f)
  -> AddComplete f
  -> m Boolean
eval lookup c = ado
  x1 <- CVar.eval lookup c.p1.x
  y1 <- CVar.eval lookup c.p1.y
  x2 <- CVar.eval lookup c.p2.x
  y2 <- CVar.eval lookup c.p2.y
  x3 <- CVar.eval lookup c.p3.x
  y3 <- CVar.eval lookup c.p3.y
  inf <- CVar.eval lookup c.inf
  sameX <- CVar.eval lookup c.sameX
  s <- CVar.eval lookup c.s
  infZ <- CVar.eval lookup c.infZ
  x21Inv <- CVar.eval lookup c.x21Inv
  in
    let
      witness = x1 :< y1 :< x2 :< y2 :< x3 :< y3 :< inf :< sameX :< s :< infZ :< x21Inv :< Vector.generate (const zero)
    in
      verifyAddComplete witness

reduce
  :: forall f m
   . PrimeField f
  => PlonkReductionM m f
  => AddComplete f
  -> m Unit
reduce c = do
  p1 <- reduceAffinePoint c.p1
  p2 <- reduceAffinePoint c.p2
  p3 <- reduceAffinePoint c.p3
  inf <- reduceToVariable c.inf
  sameX <- reduceToVariable c.sameX
  s <- reduceToVariable c.s
  infZ <- reduceToVariable c.infZ
  x21Inv <- reduceToVariable c.x21Inv
  let
    vars :: Vector 15 (Maybe Variable)
    vars =
      Just p1.x :< Just p1.y :< Just p2.x :< Just p2.y :< Just p3.x
        :< Just p3.y
        :< Just inf
        :< Just sameX
        :< Just s
        :< Just infZ
        :< Just x21Inv
        :< Vector.generate (const Nothing)
  addRow vars { kind: AddCompleteGate, coeffs: Vector.generate zero }

  where
  reduceAffinePoint p = do
    x <- reduceToVariable p.x
    y <- reduceToVariable p.y
    pure { x, y }

foreign import verifyPallasCompleteAddGadget
  :: Fn1 (Vector 15 Pallas.BaseField) Boolean

foreign import verifyVestaCompleteAddGadget
  :: Fn1 (Vector 15 Vesta.BaseField) Boolean

verifyPallasCompleteAdd :: Vector 15 Pallas.BaseField -> Boolean
verifyPallasCompleteAdd witness = runFn1 verifyPallasCompleteAddGadget witness

verifyVestaCompleteAdd :: Vector 15 Vesta.BaseField -> Boolean
verifyVestaCompleteAdd witness = runFn1 verifyVestaCompleteAddGadget witness
