module Snarky.Backend.Kimchi.Impl.Pallas where

import Effect (Effect)
import Snarky.Backend.Kimchi.Types (CRS, ConstraintSystem, Gate, GateWires, Witness)
import Snarky.Curves.Pallas as Pallas
import Snarky.Data.Vector (Vector)

-- Create a new circuit gate with the given gate kind, wires, and coefficients
foreign import pallasCircuitGateNew :: String -> GateWires -> Array Pallas.ScalarField -> Gate Pallas.ScalarField

-- Get the gate wires from a circuit gate
foreign import pallasCircuitGateGetWires :: Gate Pallas.ScalarField -> GateWires

-- Get the number of coefficients in a circuit gate
foreign import pallasCircuitGateCoeffCount :: Gate Pallas.ScalarField -> Int

-- Get a coefficient at the specified index
foreign import pallasCircuitGateGetCoeff :: Gate Pallas.ScalarField -> Int -> Pallas.ScalarField

foreign import pallasConstraintSystemCreate :: Array (Gate Pallas.ScalarField) -> Int -> ConstraintSystem Pallas.ScalarField

foreign import pallasWitnessCreate :: Array (Vector 15 Pallas.ScalarField) -> Witness Pallas.ScalarField

foreign import pallasCrsLoadFromCache :: Effect (CRS Pallas.G)

createCRS :: Effect (CRS Pallas.G)
createCRS = pallasCrsLoadFromCache