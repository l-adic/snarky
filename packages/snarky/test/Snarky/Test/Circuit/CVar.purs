module Snarky.Test.Circuit.CVar (spec) where

import Prelude

import Control.Monad.Error.Class (throwError)
import Control.Monad.Except (runExcept)
import Data.Array as Array
import Data.Either (Either)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Set (Set)
import Data.Set as Set
import Data.Traversable (foldl, traverse)
import Effect.Class (liftEffect)
import Snarky.Circuit.CVar (CVar, EvaluationError(..), Variable, eval, evalAffineExpression, reduce)
import Snarky.Curves.BN254 (ScalarField)
import Snarky.Curves.BN254 as BN254
import Test.QuickCheck (arbitrary, quickCheckGen)
import Test.QuickCheck.Gen (Gen)
import Test.Spec (Spec, describe, it)

-- | Collect all variable identifiers used in an AffineCircuit
collectVariables :: forall f. CVar f Variable -> Set Variable
collectVariables = foldl (flip Set.insert) Set.empty

-- | Generate a random variable assignment for the given set of variables
genAssignments :: Set Variable -> Gen (Map Variable ScalarField)
genAssignments vars = do
  let varArray = Set.toUnfoldable vars :: Array Variable
  assignments <- traverse (\_ -> arbitrary) varArray
  pure $ Map.fromFoldable $ Array.zip varArray assignments

spec :: Spec Unit
spec = describe "AffineCircuit" do
  it "eval equals evalAffineExpression after reduction" do
    liftEffect $ quickCheckGen do
      cvar <- arbitrary @(CVar BN254.ScalarField Variable)
      assignments <- genAssignments $ collectVariables cvar
      let
        _lookup v = case Map.lookup v assignments of
          Nothing -> throwError $ MissingVariable v
          Just a -> pure a
      let
        lhs :: Either (EvaluationError BN254.ScalarField) BN254.ScalarField
        lhs = runExcept $ evalAffineExpression (reduce cvar) _lookup
      let rhs = runExcept $ eval _lookup cvar
      pure $ lhs == rhs