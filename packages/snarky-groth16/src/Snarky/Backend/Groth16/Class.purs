module Snarky.Backend.Groth16.Class where

import Data.Array as Array
import Data.Foldable (foldl)
import Data.Map (Map)
import Data.Map as Map
import Data.Newtype (unwrap)
import Data.Set as Set
import Snarky.Backend.Groth16.Impl.BN254 as BN254
import Snarky.Backend.Groth16.Types (Gates, GatesWitness, Proof, ProvingKey, VerifyingKey, toCircuitGates)
import Snarky.Curves.BN254 as BN254C

calculateNumVariables :: forall f. Gates f -> Int
calculateNumVariables gates =
  let
    collectIndicesFromMatrix matrices =
      foldl (\acc matrix -> Set.union acc (Set.fromFoldable (Map.keys matrix))) Set.empty matrices

    allVariableIndices = Set.unions
      [ collectIndicesFromMatrix gates.a
      , collectIndicesFromMatrix gates.b
      , collectIndicesFromMatrix gates.c
      ]
  in
    Set.size allVariableIndices

class Groth16 g f | g -> f where
  setup :: { gates :: Gates f, seed :: Int } -> { provingKey :: ProvingKey g, verifyingKey :: VerifyingKey g }
  prove
    :: { provingKey :: ProvingKey g
       , gates :: Gates f
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
  circuitIsSatisfiedBy :: { gates :: Gates f, witness :: GatesWitness f } -> Boolean

instance Groth16 BN254C.G BN254C.ScalarField where
  setup { gates, seed } =
    let
      numConstraints = Array.length gates.a
      numInputs = Array.length gates.publicInputIndices
      numVariables = calculateNumVariables gates
      dimensions = { numConstraints, numVariables, numInputs }
      circuitGates = toCircuitGates gates dimensions
    in
      BN254.setup
        { dimensions
        , matrixA: (unwrap circuitGates).matrixA
        , matrixB: (unwrap circuitGates).matrixB
        , matrixC: (unwrap circuitGates).matrixC
        , publicInputIndices: gates.publicInputIndices
        }
        seed
  prove { provingKey, gates, witness, seed } =
    let
      numConstraints = Array.length gates.a
      numInputs = Array.length gates.publicInputIndices
      numVariables = Array.length witness
      dimensions = { numConstraints, numVariables, numInputs }
      circuitGates = toCircuitGates gates dimensions
    in
      BN254.prove
        { provingKey
        , gates:
            { dimensions
            , matrixA: (unwrap circuitGates).matrixA
            , matrixB: (unwrap circuitGates).matrixB
            , matrixC: (unwrap circuitGates).matrixC
            , publicInputIndices: gates.publicInputIndices
            }
        , witness
        , seed
        }
  verify { verifyingKey, proof, publicInputs } =
    BN254.verify { verifyingKey, proof, publicInputs }
  circuitIsSatisfiedBy { gates, witness } =
    let
      numConstraints = Array.length gates.a
      numInputs = Array.length gates.publicInputIndices
      numVariables = Array.length witness
      dimensions = { numConstraints, numVariables, numInputs }
      circuitGates = toCircuitGates gates dimensions
    in
      BN254.circuitIsSatisfiedBy
        { gates:
            { dimensions
            , matrixA: (unwrap circuitGates).matrixA
            , matrixB: (unwrap circuitGates).matrixB
            , matrixC: (unwrap circuitGates).matrixC
            , publicInputIndices: gates.publicInputIndices
            }
        , witness
        }