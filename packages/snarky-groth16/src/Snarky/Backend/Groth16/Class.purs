module Snarky.Backend.Groth16.Class where

import Prelude

import Data.Newtype (unwrap)
import Snarky.Backend.Groth16.Impl.BN254 as BN254
import Snarky.Backend.Groth16.Types (GatesWitness, Gates, Proof, ProvingKey, VerifyingKey, R1CSDimensions, toCircuitGates, toCircuitWitness)
import Snarky.Curves.BN254 as BN254C

class Groth16 g f | g -> f where
  setup :: { gates :: Gates f, dimensions :: R1CSDimensions, seed :: Int } -> { provingKey :: ProvingKey g, verifyingKey :: VerifyingKey g }
  prove
    :: { provingKey :: ProvingKey g
       , gates :: Gates f
       , dimensions :: R1CSDimensions
       , witness :: GatesWitness f
       , seed :: Int
       }
    -> Proof g
  verify
    :: { verifyingKey :: VerifyingKey g
       , proof :: Proof g
       , publicInputs :: Array f
       }
    -> Boolean
  circuitIsSatisfiedBy :: { gates :: Gates f, dimensions :: R1CSDimensions, witness :: GatesWitness f } -> Boolean

instance Groth16 BN254C.G BN254C.ScalarField where
  setup { gates, dimensions, seed } =
    BN254.setup (unwrap $ toCircuitGates gates dimensions) seed
  prove { provingKey, gates, dimensions, witness, seed } =
    BN254.prove
      { provingKey
      , gates: unwrap $ toCircuitGates gates dimensions
      , witness: unwrap $ toCircuitWitness witness
      , seed
      }
  verify { verifyingKey, proof, publicInputs } =
    BN254.verify { verifyingKey, proof, publicInputs }
  circuitIsSatisfiedBy { gates, dimensions, witness } =
    BN254.circuitIsSatisfiedBy
      { gates: unwrap $ toCircuitGates gates dimensions
      , witness: unwrap $ toCircuitWitness witness
      }