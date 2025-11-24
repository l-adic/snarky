module Snarky.Circuit.DSL.Utils where

import Prelude

import Data.List (List(..))
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Tuple (Tuple(..))
import Snarky.Circuit.CVar (AffineExpression(..), CVar(..), reduce, const_)
import Snarky.Circuit.DSL.Assert (assertEqual_)
import Snarky.Circuit.DSL.Monad (class CircuitM, Snarky, exists, readCVar)
import Snarky.Circuit.Types (F(..), FVar)

seal
  :: forall f c t m
   . CircuitM f c t m
  => FVar f
  -> Snarky t m (FVar f)
seal x =
  let
    AffineExpression { constant, terms } = reduce x
  in
    case constant, Map.toUnfoldable terms of
      Nothing, Cons (Tuple v coeff) Nil | coeff == one -> pure $ Var v
      Just c, Nil -> pure $ const_ c
      _, _ -> do
        y <- exists (F <$> readCVar x)
        assertEqual_ x y
        pure y