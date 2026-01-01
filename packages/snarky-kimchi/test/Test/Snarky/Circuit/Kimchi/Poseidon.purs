module Test.Snarky.Circuit.Kimchi.Poseidon (spec) where

import Prelude

import Data.Array as Array
import Data.Newtype (unwrap)
import Poseidon.Class (fullRound)
import Snarky.Backend.Compile (compilePure, makeSolver)
import Snarky.Circuit.Kimchi.Poseidon as PoseidonCircuit
import Snarky.Circuit.Types (F(..))
import Snarky.Constraint.Kimchi (KimchiConstraint, eval)
import Snarky.Constraint.Kimchi as Kimchi
import Snarky.Data.Fin (unsafeFinite)
import Snarky.Data.Vector (Vector)
import Snarky.Data.Vector as Vector
import Test.QuickCheck (arbitrary)
import Test.Snarky.Circuit.Utils (circuitSpecPure', satisfied)
import Test.Spec (Spec, describe, it)
import Type.Proxy (Proxy(..))

spec :: forall f f'. Kimchi.KimchiVerify f f' => Proxy f -> Spec Unit
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
      { constraints } = compilePure
        (Proxy @(Vector 3 (F f)))
        (Proxy @(F f))
        (Proxy @(KimchiConstraint f))
        PoseidonCircuit.poseidon
        Kimchi.initialState
      genInputs = Vector.generator (Proxy @3) (F <$> arbitrary)

    circuitSpecPure' constraints eval solver (satisfied referenceHash) genInputs