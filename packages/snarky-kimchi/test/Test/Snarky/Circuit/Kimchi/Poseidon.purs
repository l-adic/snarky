module Test.Snarky.Circuit.Kimchi.Poseidon (spec) where

import Prelude

import Data.Array as Array
import Data.Vector (Vector)
import Data.Vector as Vector
import Effect.Class (liftEffect)
import Poseidon.Class (fullRound)
import Snarky.Backend.Compile (compilePure, makeSolver)
import Snarky.Backend.Kimchi.Class (class CircuitGateConstructor)
import Snarky.Circuit.Kimchi.Poseidon as PoseidonCircuit
import Snarky.Circuit.Kimchi.Utils (verifyCircuit)
import Snarky.Circuit.Types (F(..))
import Snarky.Constraint.Kimchi (KimchiConstraint, eval)
import Snarky.Constraint.Kimchi as Kimchi
import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Vesta as Vesta
import Test.QuickCheck (arbitrary)
import Test.Snarky.Circuit.Utils (circuitSpecPure', satisfied)
import Test.Spec (Spec, describe, it)
import Type.Proxy (Proxy(..))

spec :: Spec Unit
spec = do
  spec' "Vesta" (Proxy @Vesta.BaseField)
  spec' "Pallas" (Proxy @Pallas.BaseField)

spec'
  :: forall f f' g'
   . Kimchi.KimchiVerify f f'
  => CircuitGateConstructor f g'
  => String
  -> Proxy f
  -> Spec Unit
spec' testName _ = describe ("Poseidon Circuit Tests: " <> testName) do

  it "Poseidon hash circuit matches reference implementation" do
    let
      referenceHash :: Vector 3 (F f) -> Vector 3 (F f)
      referenceHash inputs =
        let
          rounds = Array.range 0 54
        in
          Array.foldl (\state round -> fullRound state round) inputs rounds

      solver = makeSolver (Proxy @(KimchiConstraint f)) PoseidonCircuit.poseidon
      s = compilePure
        (Proxy @(Vector 3 (F f)))
        (Proxy @(Vector 3 (F f)))
        (Proxy @(KimchiConstraint f))
        PoseidonCircuit.poseidon
        Kimchi.initialState
      genInputs = Vector.generator (Proxy @3) (F <$> arbitrary)

    circuitSpecPure' 100
      { builtState: s
      , checker: eval
      , solver: solver
      , testFunction: satisfied referenceHash
      , postCondition: Kimchi.postCondition
      }
      genInputs

    liftEffect $ verifyCircuit { s, gen: genInputs, solver }