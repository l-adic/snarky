module Snarky.Backend.Kimchi.Impl.Vesta where

import Data.Vector (Vector)
import Effect (Effect)
import Snarky.Backend.Kimchi.Types (CRS, ConstraintSystem, Gate, GateWires, ProverIndex, VerifierIndex)
import Snarky.Curves.Vesta as Vesta

-- Create a new circuit gate with the given gate kind, wires, and coefficients
foreign import vestaCircuitGateNew :: String -> GateWires -> Array Vesta.ScalarField -> Gate Vesta.ScalarField

-- Get the gate wires from a circuit gate
foreign import vestaCircuitGateGetWires :: Gate Vesta.ScalarField -> GateWires

-- Get the number of coefficients in a circuit gate
foreign import vestaCircuitGateCoeffCount :: Gate Vesta.ScalarField -> Int

-- Get a coefficient at the specified index
foreign import vestaCircuitGateGetCoeff :: Gate Vesta.ScalarField -> Int -> Vesta.ScalarField

foreign import vestaConstraintSystemCreate :: Array (Gate Vesta.ScalarField) -> Int -> ConstraintSystem Vesta.ScalarField

foreign import vestaCrsLoadFromCache :: Effect (CRS Vesta.G)

foreign import vestaProverIndexCreate :: ConstraintSystem Vesta.ScalarField -> Vesta.ScalarField -> CRS Vesta.G -> ProverIndex Vesta.G Vesta.ScalarField

foreign import vestaProverIndexVerify :: ProverIndex Vesta.G Vesta.ScalarField -> Vector 15 (Array Vesta.ScalarField) -> Array Vesta.ScalarField -> Boolean

foreign import pallasVerifierIndex :: ProverIndex Vesta.G Vesta.ScalarField -> VerifierIndex Vesta.G Vesta.ScalarField

createCRS :: Effect (CRS Vesta.G)
createCRS = vestaCrsLoadFromCache

createProverIndex :: ConstraintSystem Vesta.ScalarField -> Vesta.ScalarField -> CRS Vesta.G -> ProverIndex Vesta.G Vesta.ScalarField
createProverIndex = vestaProverIndexCreate

createVerifierIndex :: ProverIndex Vesta.G Vesta.ScalarField -> VerifierIndex Vesta.G Vesta.ScalarField
createVerifierIndex = pallasVerifierIndex

verifyProverIndex :: ProverIndex Vesta.G Vesta.ScalarField -> Vector 15 (Array Vesta.ScalarField) -> Array Vesta.ScalarField -> Boolean
verifyProverIndex = vestaProverIndexVerify