module Snarky.Backend.Kimchi.Impl.Pallas where

import Effect (Effect)
import Snarky.Backend.Kimchi.Types (CRS, ConstraintSystem, Gate, GateWires, ProverIndex)
import Snarky.Curves.Pallas as Pallas
import Data.Vector (Vector)

-- Create a new circuit gate with the given gate kind, wires, and coefficients
foreign import pallasCircuitGateNew :: String -> GateWires -> Array Pallas.ScalarField -> Gate Pallas.ScalarField

-- Get the gate wires from a circuit gate
foreign import pallasCircuitGateGetWires :: Gate Pallas.ScalarField -> GateWires

-- Get the number of coefficients in a circuit gate
foreign import pallasCircuitGateCoeffCount :: Gate Pallas.ScalarField -> Int

-- Get a coefficient at the specified index
foreign import pallasCircuitGateGetCoeff :: Gate Pallas.ScalarField -> Int -> Pallas.ScalarField

foreign import pallasConstraintSystemCreate :: Array (Gate Pallas.ScalarField) -> Int -> ConstraintSystem Pallas.ScalarField

foreign import pallasCrsLoadFromCache :: Effect (CRS Pallas.G)

foreign import pallasProverIndexCreate :: ConstraintSystem Pallas.ScalarField -> Pallas.ScalarField -> CRS Pallas.G -> ProverIndex Pallas.G Pallas.ScalarField

foreign import pallasProverIndexVerify :: ProverIndex Pallas.G Pallas.ScalarField -> Vector 15 (Array Pallas.ScalarField) -> Array Pallas.ScalarField -> Boolean

createCRS :: Effect (CRS Pallas.G)
createCRS = pallasCrsLoadFromCache

createProverIndex :: ConstraintSystem Pallas.ScalarField -> Pallas.ScalarField -> CRS Pallas.G -> ProverIndex Pallas.G Pallas.ScalarField
createProverIndex = pallasProverIndexCreate

verifyProverIndex :: ProverIndex Pallas.G Pallas.ScalarField -> Vector 15 (Array Pallas.ScalarField) -> Array Pallas.ScalarField -> Boolean
verifyProverIndex = pallasProverIndexVerify