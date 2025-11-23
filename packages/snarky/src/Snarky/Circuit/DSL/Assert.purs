module Snarky.Circuit.DSL.Assert
  ( assertNonZero_
  , assertEqual_
  , assertNotEqual_
  , assertSquare_
  , assert_
  ) where

import Prelude

import Partial.Unsafe (unsafeCrashWith)
import Safe.Coerce (coerce)
import Snarky.Circuit.CVar (CVar(Const), const_, sub_)
import Snarky.Circuit.Constraint.Class (r1cs)
import Snarky.Circuit.DSL.Monad (class CircuitM, Snarky, addConstraint, inv_, mul_)
import Snarky.Circuit.Types (Bool(..), BoolVar, FVar)

assertNonZero_
  :: forall f c t m
   . CircuitM f c t m
  => FVar f
  -> Snarky t m Unit
assertNonZero_ v = void $ inv_ v

assertEqual_
  :: forall f c t m
   . CircuitM f c t m
  => FVar f
  -> FVar f
  -> Snarky t m Unit
assertEqual_ x y = case x, y of
  Const f, Const g ->
    if f == g then pure unit
    else unsafeCrashWith $ "assertEqual: constants " <> show f <> " != " <> show
      g
  _, _ -> do
    addConstraint $ r1cs
      { left: x `sub_` y, right: Const one, output: Const zero }

assertNotEqual_
  :: forall f c t m
   . CircuitM f c t m
  => FVar f
  -> FVar f
  -> Snarky t m Unit
assertNotEqual_ x y = assertNonZero_ (x `sub_` y)

assertSquare_
  :: forall f c t m
   . CircuitM f c t m
  => FVar f
  -> FVar f
  -> Snarky t m Unit
assertSquare_ x y = do
  xSquared <- mul_ x x
  assertEqual_ xSquared y

assert_
  :: forall f c t m
   . CircuitM f c t m
  => BoolVar f
  -> Snarky t m Unit
assert_ v = assertEqual_ (coerce v) (const_ $ one @f)