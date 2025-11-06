module Snarky.Test.Circuit.Affine (spec) where

import Prelude

import Data.Array as Array
import Data.Map (Map)
import Data.Map as Map
import Data.Set (Set)
import Data.Set as Set
import Data.Traversable (foldl, traverse)
import Effect.Class (liftEffect)
import Snarky.Circuit.Affine (AffineCircuit, eval, evalAffineExpression, reduce)
import Snarky.Curves.BN254 (ScalarField)
import Snarky.Curves.BN254 as BN254
import Test.QuickCheck (arbitrary, quickCheckGen)
import Test.QuickCheck.Gen (Gen)
import Test.Spec (Spec, describe, it)

-- | Collect all variable identifiers used in an AffineCircuit
collectVariables :: forall f i. Ord i => AffineCircuit f i -> Set i
collectVariables = foldl (flip Set.insert) Set.empty

-- | Generate a random variable assignment for the given set of variables
genAssignments :: Set Int -> Gen (Map Int ScalarField)
genAssignments vars = do
  let varArray = Set.toUnfoldable vars :: Array Int
  assignments <- traverse (\_ -> arbitrary) varArray
  pure $ Map.fromFoldable $ Array.zip varArray assignments

spec :: Spec Unit
spec = describe "AffineCircuit" do
  it "eval equals evalAffineExpression after reduction" do
    liftEffect $ quickCheckGen do
      affineCircuit <- arbitrary @(AffineCircuit BN254.ScalarField Int)
      assignments <- genAssignments $ collectVariables affineCircuit
      let lhs = evalAffineExpression (reduce affineCircuit) Map.lookup assignments
      let rhs = eval Map.lookup assignments affineCircuit
      pure $ lhs == rhs