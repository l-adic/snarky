module Test.Snarky.Circuit.Kimchi.Poseidon (spec) where

import Prelude

import Data.Array as Array
import Data.Either (Either(..))
import Data.Newtype (unwrap)
import Data.Tuple (Tuple(..))
import Effect.Class (liftEffect)
import Poseidon.Class (fullRound)
import Snarky.Backend.Compile (compilePure, makeSolver, runSolver)
import Snarky.Circuit.Kimchi.Poseidon as PoseidonCircuit
import Snarky.Circuit.Types (F(..))
import Snarky.Constraint.Kimchi (class KimchiVerify, AuxState(..), KimchiConstraint, eval)
import Snarky.Constraint.Kimchi as Kimchi
import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Vesta as Vesta
import Snarky.Data.Fin (unsafeFinite)
import Snarky.Data.Vector (Vector)
import Snarky.Data.Vector as Vector
import Test.QuickCheck (arbitrary, quickCheck')
import Test.Snarky.Circuit.Utils (circuitSpecPure', satisfied)
import Test.Spec (Spec, describe, it)
import Test.Utils.Poseidon (class PoseidonVerifier)
import Test.Utils.Poseidon as PoseidonUtils
import Type.Proxy (Proxy(..))

spec :: forall f v. PoseidonVerifier f v => KimchiVerify Vesta.ScalarField => Proxy f -> Spec Unit
spec _ = describe "Poseidon Circuit Tests" do

  it "Poseidon hash circuit matches reference implementation" do
    let
      referenceHash :: Vector 3 (F Pallas.BaseField) -> F Pallas.BaseField
      referenceHash inputs =
        let
          initialValues = map unwrap inputs
          rounds = Array.range 0 54
          finalState = Array.foldl (\state round -> fullRound state round) initialValues rounds
        in
          F (Vector.index finalState (unsafeFinite 2))

      solver = makeSolver (Proxy @(KimchiConstraint Pallas.BaseField)) PoseidonCircuit.poseidon
      { constraints, aux: AuxState { wireState: { emittedRows, wireAssignments } } } = compilePure
        (Proxy @(Vector 3 (F Pallas.BaseField)))
        (Proxy @(F Pallas.BaseField))
        (Proxy @(KimchiConstraint Pallas.BaseField))
        PoseidonCircuit.poseidon
        Kimchi.initialState
      genInputs = Vector.generator (Proxy @3) (F <$> arbitrary)

    do
      circuitSpecPure' constraints eval solver (satisfied referenceHash) genInputs
      liftEffect $ quickCheck' 1 do
        input <- genInputs
        case runSolver solver input of
          Left _ -> pure false
          Right (Tuple _ varAssignments) ->
            pure $ PoseidonUtils._verify { wireAssignments, varAssignments, rows: emittedRows }