module Test.Snarky.Constraint (spec) where

import Prelude

import Control.Monad.Error.Class (throwError)
import Control.Monad.Except (except, runExcept)
import Data.Either (Either(..))
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Effect.Class (liftEffect)
import Snarky.Circuit.CVar (EvaluationError(..), eval, evalAffineExpression, reduceToAffineExpression)
import Snarky.Circuit.CVar as CVar
import Snarky.Circuit.Constraint.Basic as Basic
import Snarky.Curves.BN254 as BN254
import Snarky.Curves.Class (class PrimeField)
import Test.QuickCheck (quickCheckGen)
import Test.Spec (Spec, describe, it)
import Type.Proxy (Proxy)

spec :: forall f. PrimeField f => Proxy f -> Spec Unit
spec pf = describe "Constraint Spec" do

  it "CVar.eval equals evalAffineExpression after reduction" do
    liftEffect $ quickCheckGen do
      { cvar, assignments } <- CVar.genWithAssignments pf
      let
        _lookup v = case Map.lookup v assignments of
          Nothing -> throwError $ MissingVariable v
          Just a -> pure a
      let
        lhs :: Either (EvaluationError f) f
        lhs = runExcept $ evalAffineExpression (reduceToAffineExpression cvar) _lookup
      let rhs = runExcept $ eval _lookup cvar
      pure $ lhs == rhs

  it "basic constraint gen is valid" do
    liftEffect $ quickCheckGen do
      { basic, assignments } <- Basic.genWithAssignments pf
      let
        lookup v = case Map.lookup v assignments of
          Nothing -> except $ Left $ MissingVariable v
          Just a -> pure a

        res :: Either (EvaluationError (BN254.ScalarField)) Boolean
        res = runExcept $ Basic.eval lookup basic
      pure $ res == Right true