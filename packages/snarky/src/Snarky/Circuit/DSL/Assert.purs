module Snarky.Circuit.DSL.Assert
  ( assertNonZero
  , assertEqual
  , assertNotEqual
  , assertSquare
  , assert
  ) where

import Prelude

import Partial.Unsafe (unsafeCrashWith)
import Safe.Coerce (coerce)
import Snarky.Circuit.CVar (CVar(Const), const_, sub_)
import Snarky.Circuit.Constraint.Class (r1cs)
import Snarky.Circuit.DSL.Monad (class CircuitM, Snarky, addConstraint, inv_, mul_)
import Snarky.Circuit.Types (Bool(..), Variable)

assertNonZero
  :: forall f c t m
   . CircuitM f c t m
  => CVar f Variable
  -> Snarky t m Unit
assertNonZero v = void $ inv_ v

assertEqual
  :: forall f c t m
   . CircuitM f c t m
  => CVar f Variable
  -> CVar f Variable
  -> Snarky t m Unit
assertEqual x y = case x, y of
  Const f, Const g ->
    if f == g then pure unit
    else unsafeCrashWith $ "assertEqual: constants " <> show f <> " != " <> show g
  _, _ -> do
    addConstraint $ r1cs { left: x `sub_` y, right: Const one, output: Const zero }

assertNotEqual
  :: forall f c t m
   . CircuitM f c t m
  => CVar f Variable
  -> CVar f Variable
  -> Snarky t m Unit
assertNotEqual x y = assertNonZero (x `sub_` y)

assertSquare
  :: forall f c t m
   . CircuitM f c t m
  => CVar f Variable
  -> CVar f Variable
  -> Snarky t m Unit
assertSquare x y = do
  xSquared <- mul_ x x
  assertEqual xSquared y

assert
  :: forall f c t m
   . CircuitM f c t m
  => CVar f (Bool Variable)
  -> Snarky t m Unit
assert v = assertEqual (coerce v) (const_ $ one @f)