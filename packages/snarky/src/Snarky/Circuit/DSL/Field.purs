-- | Field comparison and arithmetic operations.
-- |
-- | The `equals_` function is notable: it returns a `BoolVar` indicating equality
-- | rather than asserting it. This requires introducing witness variables and
-- | uses the standard "inverse-or-zero" trick to avoid branching.
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
import Snarky.Circuit.CVar (CVar(..), const_)
import Snarky.Circuit.CVar as CVar
import Snarky.Circuit.DSL.Monad (class CircuitM, Snarky, addConstraint, exists, readCVar)
import Snarky.Circuit.Types (Bool(..), BoolVar, F, FVar)
import Snarky.Constraint.Basic (r1cs)
import Snarky.Curves.Class (class PrimeField)

equals
  :: forall f c t m
   . CircuitM f c t m
  => Snarky c t m (FVar f)
  -> Snarky c t m (FVar f)
  -> Snarky c t m (BoolVar f)
equals a b = join $ lift2 equals_ a b

equals_
  :: forall f c t m
   . CircuitM f c t m
  => FVar f
  -> FVar f
  -> Snarky c t m (BoolVar f)
equals_ a b = case a `CVar.sub_` b of
  Const f -> pure $ Const $ if f == zero then one else zero
  _ -> do
    let z = a `CVar.sub_` b
    { r, zInv } <- exists do
      zVal <- readCVar z
      pure $
        if zVal == zero then { r: one @(F f), zInv: zero }
        else { r: zero, zInv: recip zVal }
    addConstraint $ r1cs { left: r, right: z, output: const_ zero }
    addConstraint $ r1cs { left: zInv, right: z, output: const_ one `CVar.sub_` r }
    pure $ coerce r

neq_
  :: forall f c t m
   . CircuitM f c t m
  => FVar f
  -> FVar f
  -> Snarky c t m (BoolVar f)
neq_ (a :: FVar f) (b :: FVar f) = not $ equals_ a b

sum_
  :: forall f
   . PrimeField f
  => Array (FVar f)
  -> FVar f
sum_ = foldl CVar.add_ (Const zero)

-- | Compute x^n using repeated squaring (matches OCaml's evaluation order).
pow_
  :: forall f c t m
   . CircuitM f c t m
  => FVar f
  -> Int
  -> Snarky c t m (FVar f)
pow_ x n
  | n == 0 = one
  | n == 1 = pure x
  | otherwise = do
      sq <- pure x * pure x
      y <- pow_ sq (n / 2)
      if n `mod` 2 == 0 then pure y
      else pure x * pure y