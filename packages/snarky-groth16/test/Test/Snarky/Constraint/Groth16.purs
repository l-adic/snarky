module Test.Snarky.Constraint.Groth16 where

import Prelude

import Control.Monad.Except (runExcept, throwError)
import Data.Array as Array
import Data.Either (Either(..))
import Data.Map as Map
import Data.Maybe (maybe)
import Effect.Class (liftEffect)
import Partial.Unsafe (unsafeCrashWith)
import Snarky.Backend.Groth16.Gate (makeGates, makeGatesWitness, satisfies)
import Snarky.Circuit.DSL (EvaluationError(..))
import Snarky.Constraint.Basic as Basic
import Snarky.Curves.Class (class PrimeField)
import Test.QuickCheck (quickCheckGen', withHelp)
import Test.Spec (Spec, describe, it)
import Type.Proxy (Proxy)

spec :: forall f. PrimeField f => Proxy f -> Spec Unit
spec pf = describe "Constraint Spec" do
  it "reduces basic constraints to r1cs constraints" do
    liftEffect $ quickCheckGen' 1000 do
      { basic, assignments } <- Basic.genWithAssignments pf
      let
        lookup var = maybe (throwError $ MissingVariable var) pure $ Map.lookup var assignments
      case runExcept $ Basic.eval lookup basic of
        Left (e :: EvaluationError) -> unsafeCrashWith $ "basic eval failed " <> show e
        Right b -> if b then pure unit else unsafeCrashWith "Basic eval was false"
      let
        r1cs = Basic.fromBasic basic
        constraints = [ r1cs ]
        -- NB since this doesnt arise from a natural computation, the rules are all broken
        -- about the order/expressions in which you would first encounter variables
        publicInputs = Array.fromFoldable (Map.keys assignments)
        gates = makeGates { constraints, publicInputs }
      pure case runExcept $ makeGatesWitness { assignments, constraints, publicInputs } of
        Left e -> withHelp false $ "Gate witness creation failed: " <> show e
        Right w -> withHelp (satisfies w gates) "gate eval failed"