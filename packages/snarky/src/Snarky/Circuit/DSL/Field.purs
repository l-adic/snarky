module Snarky.Circuit.DSL.Field
  ( equals
  , equals_
  , neq_
  , sum_
  , pow_
  ) where

import Prelude

import Control.Apply (lift2)
import Data.Array (foldl)
import Safe.Coerce (coerce)
import Snarky.Circuit.CVar (CVar(Const))
import Snarky.Circuit.CVar as CVar
import Snarky.Circuit.Constraint.Class (r1cs)
import Snarky.Circuit.DSL.Monad (class CircuitM, Snarky, addConstraint, exists, readCVar)
import Snarky.Circuit.Types (Bool(..), BoolVar, F(..), FVar, Variable(..))
import Snarky.Curves.Class (class PrimeField)

equals
  :: forall f c t m
   . CircuitM f c t m
  => Snarky t m (FVar f)
  -> Snarky t m (FVar f)
  -> Snarky t m (BoolVar f)
equals a b = join $ lift2 equals_ a b

equals_
  :: forall f c t m
   . CircuitM f c t m
  => FVar f
  -> FVar f
  -> Snarky t m (BoolVar f)
equals_ a b = case a `CVar.sub_` b of
  Const f -> pure $ Const $ if f == zero then one else zero
  _ -> do
    let z = a `CVar.sub_` b
    { r, zInv } <- exists do
      zVal <- readCVar z
      pure $
        if zVal == zero then { r: F (one :: f), zInv: F zero }
        else { r: F zero, zInv: F $ recip zVal }
    addConstraint $ r1cs
      { left: zInv, right: z, output: Const one `CVar.sub_` r }
    addConstraint $ r1cs { left: r, right: z, output: Const zero }
    pure $ coerce r

neq_
  :: forall f c t m
   . CircuitM f c t m
  => FVar f
  -> FVar f
  -> Snarky t m (BoolVar f)
neq_ (a :: FVar f) (b :: FVar f) = not $ equals_ a b

sum_
  :: forall f
   . PrimeField f
  => Array (FVar f)
  -> FVar f
sum_ = foldl CVar.add_ (Const zero)

pow_
  :: forall f c t m
   . CircuitM f c t m
  => FVar f
  -> Int
  -> Snarky t m (FVar f)
pow_ x n
  | n == 0 = one
  | n == 1 = pure x
  | otherwise = pure x * pow_ x (n - 1)