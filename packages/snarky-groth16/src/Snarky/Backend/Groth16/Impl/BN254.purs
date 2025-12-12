module Snarky.Backend.Groth16.Impl.BN254
  ( module Snarky.Backend.Groth16.Types
  , setup
  , prove
  , verify
  , circuitIsSatisfiedBy
  ) where

import Data.Function.Uncurried (Fn3, Fn5, Fn6, Fn8, runFn3, runFn5, runFn6, runFn8)
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
     }
  -> Int
  -> { provingKey :: ProvingKey G, verifyingKey :: VerifyingKey G }
setup { dimensions, matrixA, matrixB, matrixC } seed =
  let
    Tuple provingKey verifyingKey = runFn5 bn254Setup dimensions
      (write matrixA)
      (write matrixB)
      (write matrixC)
      seed
  in
    { provingKey, verifyingKey }

prove
  :: { provingKey :: ProvingKey G
     , gates ::
         { dimensions :: R1CSDimensions
         , matrixA :: CircuitMatrix ScalarField
         , matrixB :: CircuitMatrix ScalarField
         , matrixC :: CircuitMatrix ScalarField
         }
     , witness ::
         { witness :: Array ScalarField
         , publicInputs :: Array ScalarField
         }
     , seed :: Int
     }
  -> Proof G
prove { provingKey, gates, witness, seed } =
  runFn8 bn254Prove provingKey
    gates.dimensions
    (write gates.matrixA)
    (write gates.matrixB)
    (write gates.matrixC)
    witness.witness
    witness.publicInputs
    seed

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
         }
     , witness ::
         { witness :: Array ScalarField
         , publicInputs :: Array ScalarField
         }
     }
  -> Boolean
circuitIsSatisfiedBy { gates, witness } =
  runFn6 bn254CircuitCheckSatisfaction
    gates.dimensions
    (write gates.matrixA)
    (write gates.matrixB)
    (write gates.matrixC)
    witness.witness
    witness.publicInputs

foreign import bn254Setup :: Fn5 R1CSDimensions Foreign Foreign Foreign Int (Tuple (ProvingKey G) (VerifyingKey G))
foreign import bn254Prove :: Fn8 (ProvingKey G) R1CSDimensions Foreign Foreign Foreign (Array ScalarField) (Array ScalarField) Int (Proof G)
foreign import bn254Verify :: Fn3 (VerifyingKey G) (Proof G) (Array ScalarField) Boolean
foreign import bn254CircuitCheckSatisfaction :: Fn6 R1CSDimensions Foreign Foreign Foreign (Array ScalarField) (Array ScalarField) Boolean