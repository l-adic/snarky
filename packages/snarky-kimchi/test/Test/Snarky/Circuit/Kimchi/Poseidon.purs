module Test.Snarky.Circuit.Kimchi.Poseidon (spec) where

import Prelude

import Data.Array as Array
import Data.Array.NonEmpty as NEA
import Data.Identity (Identity)
import Data.Vector (Vector)
import Data.Vector as Vector
import Effect.Class (liftEffect)
import Poseidon (fullRound)
import Safe.Coerce (coerce)
import Snarky.Backend.Kimchi.Class (class CircuitGateConstructor)
import Snarky.Circuit.DSL (class CircuitM, F(..), FVar, Snarky)
import Snarky.Circuit.Kimchi.Poseidon as PoseidonCircuit
import Snarky.Circuit.Kimchi.Utils (verifyCircuit)
import Snarky.Constraint.Kimchi (class KimchiVerify, KimchiConstraint, KimchiGate, eval)
import Snarky.Constraint.Kimchi as Kimchi
import Snarky.Constraint.Kimchi.Types (AuxState)
import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Vesta as Vesta
import Test.QuickCheck (arbitrary)
import Test.Snarky.Circuit.Utils (TestConfig, circuitTest', satisfied)
import Test.Spec (Spec, describe, it)
import Type.Proxy (Proxy(..))

kimchiTestConfig :: forall f f'. KimchiVerify f f' => TestConfig f (KimchiGate f) (AuxState f)
kimchiTestConfig = { checker: eval, postCondition: Kimchi.postCondition, initState: Kimchi.initialState }

spec :: Spec Unit
spec = do
  spec' "Vesta" (Proxy @Vesta.BaseField)
  spec' "Pallas" (Proxy @Pallas.BaseField)

spec'
  :: forall f f' g'
   . KimchiVerify f f'
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
          inputs' :: Vector 3 f
          inputs' = coerce inputs
          rounds = Array.range 0 54
        in
          coerce $ Array.foldl (\state round -> fullRound state round) inputs' rounds

      poseidon'
        :: forall t
         . CircuitM f (KimchiConstraint f) t Identity
        => Vector 3 (FVar f)
        -> Snarky (KimchiConstraint f) t Identity (Vector 3 (FVar f))
      poseidon' = PoseidonCircuit.poseidon

      genInputs = Vector.generator (Proxy @3) (F <$> arbitrary)

    { builtState, solver } <- circuitTest' @f 100
      kimchiTestConfig
      ( NEA.singleton
          { testFunction: satisfied referenceHash
          , gen: genInputs
          }
      )
      poseidon'

    liftEffect $ verifyCircuit { s: builtState, gen: genInputs, solver }
