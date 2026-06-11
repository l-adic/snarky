-- | Circuit utility functions.
module Snarky.Circuit.DSL.Utils where

import Prelude

import Data.Array (toUnfoldable)
import Data.List (List(..))
import Data.Maybe (Maybe(..))
import Data.Tuple (Tuple(..))
import Snarky.Circuit.CVar (AffineExpression(..), CVar(..), const_, reduceToAffineExpression)
import Snarky.Circuit.DSL.Assert (assertEqual_)
import Snarky.Circuit.DSL.Monad (Snarky, exists, readCVar)
import Snarky.Circuit.Types (FVar)
import Snarky.Constraint.Basic (class BasicSystem)
import Snarky.Curves.Class (class PrimeField)

-- | Reduce an expression to a single variable if it's complex.
-- |
-- | If the expression is already simple (a lone variable or constant), returns it unchanged.
-- | Otherwise introduces a new variable constrained equal to the expression. Useful when
-- | you need a "sealed" value that won't expand during further operations.
seal
  :: forall f c r
   . PrimeField f
  => BasicSystem f c
  => FVar f
  -> Snarky f c r (FVar f)
seal x =
  let
    AffineExpression { constant, terms } = reduceToAffineExpression x
  in
    case constant, toUnfoldable terms of
      Nothing, Cons (Tuple v coeff) Nil | coeff == one -> pure $ Var v
      Just c, Nil -> pure $ const_ c
      _, _ -> do
        y <- exists (readCVar x)
        assertEqual_ x y
        pure y