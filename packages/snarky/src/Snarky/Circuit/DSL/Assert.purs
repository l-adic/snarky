module Snarky.Circuit.DSL.Assert
  ( assertNonZero
  , assertEqual
  , assert
  ) where

import Prelude

import Partial.Unsafe (unsafeCrashWith)
import Safe.Coerce (coerce)
import Snarky.Circuit.CVar (CVar(Const), const_, sub_)
import Snarky.Circuit.Constraint.Class (r1cs)
import Snarky.Circuit.DSL (class CircuitM, addConstraint)
import Snarky.Circuit.DSL.Field (inv_)
import Snarky.Circuit.Types (Bool(..), Variable)

assertNonZero
  :: forall f c t m
   . CircuitM f c t m
  => CVar f Variable
  -> t m Unit
assertNonZero v = void $ inv_ v

assertEqual
  :: forall f c t m
   . CircuitM f c t m
  => CVar f Variable
  -> CVar f Variable
  -> t m Unit
assertEqual x y = case x, y of
  Const f, Const g ->
    if f == g then pure unit
    else unsafeCrashWith $ "assertEqual: constants " <> show f <> " != " <> show g
  _, _ -> do
    addConstraint $ r1cs { left: x `sub_` y, right: Const one, output: Const zero }

assert
  :: forall f c t m
   . CircuitM f c t m
  => CVar f (Bool Variable)
  -> t m Unit
assert v = assertEqual (coerce v) (const_ $ one @f)