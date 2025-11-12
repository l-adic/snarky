module Snarky.Circuit.DSL.Assert
  ( assertNonZero
  , assertEqual
  , assert
  ) where

import Prelude

import Partial.Unsafe (unsafeCrashWith)
import Safe.Coerce (coerce)
import Snarky.Circuit.CVar (CVar(Const), const_, sub_)
import Snarky.Circuit.Constraint (R1CS(..))
import Snarky.Circuit.DSL (class CircuitM, addConstraint)
import Snarky.Circuit.DSL.Field (inv_)
import Snarky.Circuit.Types (BooleanVariable(..), Variable)

assertNonZero
  :: forall f m n
   . CircuitM f m n
  => CVar f Variable
  -> m Unit
assertNonZero v = void $ inv_ v

assertEqual
  :: forall f m n
   . CircuitM f m n
  => CVar f Variable
  -> CVar f Variable
  -> m Unit
assertEqual x y = case x, y of
  Const f, Const g ->
    if f == g then pure unit
    else unsafeCrashWith $ "assertEqual: constants " <> show f <> " != " <> show g
  _, _ -> do
    addConstraint $ R1CS { left: x `sub_` y, right: Const one, output: Const zero }

assert
  :: forall f m n
   . CircuitM f m n
  => CVar f BooleanVariable
  -> m Unit
assert v = assertEqual (coerce v) (const_ $ one @f)