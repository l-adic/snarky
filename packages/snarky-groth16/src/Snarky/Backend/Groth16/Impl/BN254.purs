module Snarky.Backend.Groth16.Impl.BN254
  ( module Snarky.Backend.Groth16.Types
  , setup
  , prove
  , verify
  , circuitIsSatisfiedBy
  ) where

import Data.Function.Uncurried (Fn1, Fn2, Fn3, Fn4, Fn5, runFn1, runFn2, runFn3, runFn4, runFn5)
import Data.Tuple (Tuple(..))
import Foreign (Foreign)
import Simple.JSON (write)
import Snarky.Backend.Groth16.Types (R1CSDimensions, CircuitGates, CircuitMatrix, CircuitWitness, Proof, ProvingKey, VerifyingKey)
import Snarky.Curves.BN254 (ScalarField, G)

setup
  :: { dimensions :: R1CSDimensions
     , matrixA :: CircuitMatrix ScalarField
     , matrixB :: CircuitMatrix ScalarField
     , matrixC :: CircuitMatrix ScalarField
     , publicInputIndices :: Array Int
     }
  -> Int
  -> { provingKey :: ProvingKey G, verifyingKey :: VerifyingKey G }
setup { dimensions, matrixA, matrixB, matrixC, publicInputIndices } seed =
  let
    circuit = runFn5 bn254CircuitCreate dimensions
      (write matrixA)
      (write matrixB)
      (write matrixC)
      publicInputIndices

    Tuple provingKey verifyingKey = runFn2 bn254Setup circuit seed
  in
    { provingKey, verifyingKey }

prove
  :: { provingKey :: ProvingKey G
     , gates ::
         { dimensions :: R1CSDimensions
         , matrixA :: CircuitMatrix ScalarField
         , matrixB :: CircuitMatrix ScalarField
         , matrixC :: CircuitMatrix ScalarField
         , publicInputIndices :: Array Int
         }
     , witness :: Array ScalarField
     , seed :: Int
     }
  -> Proof G
prove { provingKey, gates, witness, seed } =
  let
    circuit = runFn5 bn254CircuitCreate gates.dimensions
      (write gates.matrixA)
      (write gates.matrixB)
      (write gates.matrixC)
      gates.publicInputIndices

    witnessObj = runFn1 bn254WitnessCreate witness
  in
    runFn4 bn254Prove provingKey circuit witnessObj seed

verify
  :: { verifyingKey :: VerifyingKey G
     , proof :: Proof G
     , publicInputs :: Array ScalarField
     }
  -> Boolean
verify { verifyingKey, proof, publicInputs } =
  runFn3 bn254Verify verifyingKey proof publicInputs

circuitIsSatisfiedBy
  :: { gates ::
         { dimensions :: R1CSDimensions
         , matrixA :: CircuitMatrix ScalarField
         , matrixB :: CircuitMatrix ScalarField
         , matrixC :: CircuitMatrix ScalarField
         , publicInputIndices :: Array Int
         }
     , witness :: Array ScalarField
     }
  -> Boolean
circuitIsSatisfiedBy { gates, witness } =
  let
    circuit = runFn5 bn254CircuitCreate gates.dimensions
      (write gates.matrixA)
      (write gates.matrixB)
      (write gates.matrixC)
      gates.publicInputIndices

    witnessObj = runFn1 bn254WitnessCreate witness
  in
    runFn2 bn254CircuitIsSatisfiedBy circuit witnessObj

foreign import bn254CircuitCreate :: Fn5 R1CSDimensions Foreign Foreign Foreign (Array Int) Foreign
foreign import bn254WitnessCreate :: Fn1 (Array ScalarField) Foreign
foreign import bn254Setup :: Fn2 Foreign Int (Tuple (ProvingKey G) (VerifyingKey G))
foreign import bn254Prove :: Fn4 (ProvingKey G) Foreign Foreign Int (Proof G)
foreign import bn254Verify :: Fn3 (VerifyingKey G) (Proof G) (Array ScalarField) Boolean
foreign import bn254CircuitIsSatisfiedBy :: Fn2 Foreign Foreign Boolean