module Snarky.Constraint.Kimchi.AddComplete
  ( AddComplete
  , Rows
  , class AddCompleteVerifiable
  , verifyAddComplete
  , eval
  , reduce
  ) where

import Prelude

import Data.Array as Array
import Data.Function.Uncurried (Fn1, runFn1)
import Data.Maybe (Maybe(..), maybe)
import Data.Traversable (traverse)
import Data.Vector (Vector, (:<))
import Data.Vector as Vector
import Snarky.Circuit.CVar (Variable)
import Snarky.Circuit.Types (FVar)
import Snarky.Constraint.Kimchi.Reduction (class PlonkReductionM, reduceToVariable)
import Snarky.Constraint.Kimchi.Types (class ToKimchiRows, GateKind(..), KimchiRow)
import Snarky.Curves.Class (class PrimeField)
import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Vesta as Vesta

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

newtype Rows f = Rows (KimchiRow f)

instance ToKimchiRows f (Rows f) where
  toKimchiRows (Rows as) = Array.singleton as

eval
  :: forall f m
   . PrimeField f
  => AddCompleteVerifiable f
  => Applicative m
  => (Variable -> m f)
  -> Rows f
  -> m Boolean
eval lookup (Rows row) =
  verifyAddComplete <$> traverse lookup' row.variables
  where
  lookup' = maybe (pure zero) lookup

reduce
  :: forall f m
   . PlonkReductionM m f
  => AddComplete f
  -> m (Rows f)
reduce c = Rows <$> do
  p1 <- reduceAffinePoint c.p1
  p2 <- reduceAffinePoint c.p2
  p3 <- reduceAffinePoint c.p3
  inf <- reduceToVariable c.inf
  sameX <- reduceToVariable c.sameX
  s <- reduceToVariable c.s
  infZ <- reduceToVariable c.infZ
  x21Inv <- reduceToVariable c.x21Inv
  let
    variables :: Vector 15 (Maybe Variable)
    variables =
      Just p1.x :< Just p1.y :< Just p2.x :< Just p2.y :< Just p3.x
        :< Just p3.y
        :< Just inf
        :< Just sameX
        :< Just s
        :< Just infZ
        :< Just x21Inv
        :< Vector.generate (const Nothing)
  pure { kind: AddCompleteGate, coeffs: mempty, variables }

  where
  reduceAffinePoint p = do
    x <- reduceToVariable p.x
    y <- reduceToVariable p.y
    pure { x, y }

foreign import verifyPallasCompleteAddGadget
  :: Fn1 (Vector 15 Pallas.BaseField) Boolean

foreign import verifyVestaCompleteAddGadget
  :: Fn1 (Vector 15 Vesta.BaseField) Boolean

instance AddCompleteVerifiable Pallas.BaseField where
  verifyAddComplete = runFn1 verifyPallasCompleteAddGadget

instance AddCompleteVerifiable Vesta.BaseField where
  verifyAddComplete = runFn1 verifyVestaCompleteAddGadget