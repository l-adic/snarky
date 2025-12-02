module Test.Snarky.Constraint.R1CS where

import Prelude

import Control.Monad.Except (runExcept, throwError)
import Data.Either (Either(..))
import Data.Map as Map
import Data.Maybe (maybe)
import Effect.Class (liftEffect)
import Partial.Unsafe (unsafeCrashWith)
import Snarky.Circuit.CVar (EvaluationError(..), Variable)
import Snarky.Constraint.Basic as Basic
import Snarky.Backend.Bulletproof.Gate (satisfies, makeGates, makeMulGates, makeWitness)
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
        Left (e :: EvaluationError Variable) -> unsafeCrashWith $ "basic eval failed " <> show e
        Right b -> if b then pure unit else unsafeCrashWith "Basic eval was false"
      let
        r1cs = Basic.fromBasic basic
        constraints = [ r1cs ]
        gates = makeGates constraints
        mulGates = makeMulGates [ r1cs ]
      pure case runExcept $ makeWitness { assignments, mulGates } of
        Left e -> withHelp false $ "Shit " <> show e
        Right w -> withHelp (satisfies w gates) "gate eval failed"