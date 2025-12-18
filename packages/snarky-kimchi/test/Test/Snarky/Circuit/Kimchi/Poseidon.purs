module Test.Snarky.Circuit.Kimchi.Poseidon (spec) where

import Prelude

import Data.Array as Array
import Data.Newtype (unwrap)
import Poseidon.Class (fullRound)
import Snarky.Curves.Pasta (PallasBaseField)
import Snarky.Backend.Compile (compilePure, makeSolver)
import Snarky.Circuit.Kimchi.Poseidon as PoseidonCircuit
import Snarky.Circuit.Types (F(..))
import Snarky.Constraint.Kimchi (KimchiConstraint, eval)
import Snarky.Data.Vector (Vector)
import Snarky.Data.Vector as Vector
import Snarky.Data.Fin (unsafeFinite)
import Test.QuickCheck (arbitrary)
import Test.Snarky.Circuit.Utils (circuitSpecPure', satisfied)
import Test.Spec (Spec, describe, it)
import Type.Proxy (Proxy(..))

spec :: Spec Unit
spec = describe "Poseidon Circuit Tests" do

  it "Poseidon hash circuit matches reference implementation" do
    let
      -- Reference function: compute 3-element Poseidon permutation and extract last element
      referenceHash :: Vector 3 (F PallasBaseField) -> F PallasBaseField
      referenceHash inputs =
        let
          initialValues = map unwrap inputs
          rounds = Array.range 0 54
          finalState = Array.foldl (\state round -> fullRound state round) initialValues rounds
        in
          F (Vector.index finalState (unsafeFinite 2)) -- Extract last element like the circuit does

      -- Circuit solver
      solver = makeSolver (Proxy @(KimchiConstraint PallasBaseField)) PoseidonCircuit.poseidonHash

      -- Compile the circuit
      { constraints } =
        compilePure
          (Proxy @(Vector 3 (F PallasBaseField)))
          (Proxy @(F PallasBaseField))
          PoseidonCircuit.poseidonHash

      -- Custom generator for Vector 3 (F PallasBaseField)
      genInputs = Vector.generator (Proxy @3) (F <$> arbitrary)

    circuitSpecPure' constraints eval solver (satisfied referenceHash) genInputs

  it "Poseidon constraint circuit matches reference implementation" do
    let
      -- Reference function: compute full 55-round Poseidon state evolution
      referenceConstraintOutput :: Vector 3 (F PallasBaseField) -> Vector 3 (F PallasBaseField)
      referenceConstraintOutput inputs =
        let
          initialValues = map unwrap inputs
          rounds = Array.range 0 54
          finalState = Array.foldl (\state round -> fullRound state round) initialValues rounds
        in
          map F finalState

      -- Circuit solver for the constraint circuit
      solver = makeSolver (Proxy @(KimchiConstraint PallasBaseField)) PoseidonCircuit.poseidonConstraintCircuit

      -- Compile the constraint circuit
      { constraints } =
        compilePure
          (Proxy @(Vector 3 (F PallasBaseField)))
          (Proxy @(Vector 3 (F PallasBaseField)))
          PoseidonCircuit.poseidonConstraintCircuit

      -- Custom generator for Vector 3 (F PallasBaseField)
      genInputs = Vector.generator (Proxy @3) (F <$> arbitrary)

    circuitSpecPure' constraints eval solver (satisfied referenceConstraintOutput) genInputs