module Test.Snarky.Constraint.Kimchi.GenericPlonk (spec) where

import Prelude

import Control.Monad.Except (except, runExcept)
import Data.Either (Either(..))
import Data.Foldable (foldM)
import Data.Map as Map
import Data.Maybe (Maybe(..), maybe)
import Data.Traversable (maximum)
import Effect.Class (liftEffect)
import Partial.Unsafe (unsafeCrashWith)
import Snarky.Circuit.CVar (EvaluationError(..), incrementVariable, v0)
import Snarky.Constraint.Basic as Basic
import Snarky.Constraint.Kimchi.GenericPlonk (reduceAsBuilder, reduceAsProver)
import Snarky.Constraint.Kimchi.GenericPlonk as Plonk
import Snarky.Constraint.Kimchi.Wire (emptyKimchiWireState)
import Snarky.Curves.Class (class PrimeField)
import Test.QuickCheck (quickCheckGen', (===))
import Test.Spec (Spec, describe, it)
import Type.Proxy (Proxy)

spec :: forall f. PrimeField f => Proxy f -> Spec Unit
spec pf = describe "Constraint Spec" do

  it "reduces basic constraints to plonk constraints" do
    liftEffect $ quickCheckGen' 10000 do
      { basic, assignments } <- Basic.genWithAssignments pf
      let
        nextVariable = maybe v0 incrementVariable $ maximum (Map.keys assignments)
        plonkConstraints = reduceAsBuilder { nextVariable, constraints: [ basic ], wireState: emptyKimchiWireState }
        finalAssignments = case reduceAsProver [ basic ] { nextVariable, assignments } of
          Left e -> unsafeCrashWith $ "Unexpected error in Plonk reduce as Prover: " <> show e
          Right { assignments: assignments' } -> assignments'
        lookup v = case Map.lookup v finalAssignments of
          Nothing -> except $ Left $ MissingVariable v
          Just a -> pure a

        basicEval :: Either (EvaluationError f) Boolean
        basicEval = runExcept $ Basic.eval lookup basic
        plonkEval = runExcept $
          foldM
            ( \acc c ->
                Plonk.eval lookup c <#> conj acc
            )
            true
            plonkConstraints.constraints
      pure $ plonkEval === basicEval