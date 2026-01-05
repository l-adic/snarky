module Test.Snarky.Circuit.Kimchi.Poseidon (spec) where

import Prelude

import Data.Array as Array
import Data.Newtype (unwrap)
import Effect.Class (liftEffect)
import Poseidon.Class (fullRound)
import Snarky.Backend.Compile (compilePure, makeSolver)
import Snarky.Backend.Kimchi.Class (class CircuitGateConstructor)
import Snarky.Circuit.Kimchi.Poseidon as PoseidonCircuit
import Snarky.Circuit.Types (F(..))
import Snarky.Constraint.Kimchi (KimchiConstraint, eval)
import Snarky.Constraint.Kimchi as Kimchi
import Snarky.Data.Fin (unsafeFinite)
import Snarky.Data.Vector (Vector)
import Snarky.Data.Vector as Vector
import Test.QuickCheck (arbitrary)
import Test.Snarky.Circuit.Kimchi.Utils (verifyCircuit)
import Test.Snarky.Circuit.Utils (circuitSpecPure', satisfied)
import Test.Spec (Spec, describe, it)
import Type.Proxy (Proxy(..))

spec
  :: forall f f' g'
   . Kimchi.KimchiVerify f f'
  => CircuitGateConstructor f g'
  => Proxy f
  -> Spec Unit
spec _ = describe "Poseidon Circuit Tests" do

  it "Poseidon hash circuit matches reference implementation" do
    let
      referenceHash :: Vector 3 (F f) -> F f
      referenceHash inputs =
        let
          initialValues = map unwrap inputs
          rounds = Array.range 0 54
          finalState = Array.foldl (\state round -> fullRound state round) initialValues rounds
        in
          F (Vector.index finalState (unsafeFinite 2))

      solver = makeSolver (Proxy @(KimchiConstraint f)) PoseidonCircuit.poseidon
      s = compilePure
        (Proxy @(Vector 3 (F f)))
        (Proxy @(F f))
        (Proxy @(KimchiConstraint f))
        PoseidonCircuit.poseidon
        Kimchi.initialState
      genInputs = Vector.generator (Proxy @3) (F <$> arbitrary)

    circuitSpecPure'
      { builtState: s
      , checker: eval
      , solver: solver
      , testFunction: satisfied referenceHash
      , postCondition: Kimchi.postCondition
      }
      genInputs

    liftEffect $ verifyCircuit { s, gen: genInputs, solver }