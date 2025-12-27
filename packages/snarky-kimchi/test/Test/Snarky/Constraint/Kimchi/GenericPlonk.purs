module Test.Snarky.Constraint.Kimchi.GenericPlonk (spec) where

import Prelude

import Control.Monad.Except (except, runExcept)
import Data.Either (Either(..))
import Data.Foldable (foldM)
import Data.Map as Map
import Data.Maybe (Maybe(..), maybe)
import Data.Traversable (maximum)
import Data.Tuple (Tuple(..))
import Effect.Class (liftEffect)
import Partial.Unsafe (unsafeCrashWith)
import Snarky.Circuit.CVar (EvaluationError(..), incrementVariable, v0)
import Snarky.Constraint.Basic as Basic
import Snarky.Constraint.Kimchi.GenericPlonk (reduceBasic)
import Snarky.Constraint.Kimchi.GenericPlonk as Plonk
import Snarky.Constraint.Kimchi.Reduction (reduceAsBuilder, reduceAsProver)
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
        Tuple _ plonkConstraints = reduceAsBuilder { nextVariable, wireState: emptyKimchiWireState } (reduceBasic basic)
        finalAssignments = case reduceAsProver { nextVariable, assignments } (reduceBasic basic) of
          Left e -> unsafeCrashWith $ "Unexpected error in Plonk reduce as Prover: " <> show e
          Right (Tuple _ { assignments: assignments' }) -> assignments'
        lookup v = case Map.lookup v finalAssignments of
          Nothing -> except $ Left $ MissingVariable v
          Just a -> pure a

        basicEval :: Either EvaluationError Boolean
        basicEval = runExcept $ Basic.eval lookup basic
        plonkEval = runExcept $
          foldM
            ( \acc c ->
                Plonk.eval lookup c <#> conj acc
            )
            true
            plonkConstraints.constraints
      pure $ plonkEval === basicEval