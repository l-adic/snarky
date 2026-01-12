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
import Snarky.Constraint.Kimchi.GenericPlonk (class GenericPlonkVerifiable)
import Snarky.Constraint.Kimchi.GenericPlonk as Plonk
import Snarky.Constraint.Kimchi.Reduction (reduceAsBuilder, reduceAsProver)
import Snarky.Constraint.Kimchi.Types (AuxState(..), emptyKimchiWireState)
import Snarky.Curves.Class (class PrimeField)
import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Vesta as Vesta
import Test.QuickCheck (quickCheckGen', (===))
import Test.Spec (Spec, describe, it)
import Type.Proxy (Proxy(..))

spec :: Spec Unit
spec = do
  spec' "Vesta" (Proxy @Vesta.ScalarField)
  spec' "Pallas" (Proxy @Pallas.ScalarField)

spec' :: forall f. PrimeField f => GenericPlonkVerifiable f => String -> Proxy f -> Spec Unit
spec' testName pf = describe ("Constraint Spec: " <> testName) do

  it "reduces basic constraints to plonk constraints" do
    liftEffect $ quickCheckGen' 10000 do
      { basic, assignments } <- Basic.genWithAssignments pf
      let
        nextVariable = maybe v0 incrementVariable $ maximum (Map.keys assignments)
        initStateBuilderState = { nextVariable, aux: AuxState { wireState: emptyKimchiWireState, queuedGenericGate: Nothing } }
        Tuple _ plonkConstraints = reduceAsBuilder initStateBuilderState (Plonk.reduce basic)
        finalAssignments = case reduceAsProver { nextVariable, assignments } (Plonk.reduce basic) of
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