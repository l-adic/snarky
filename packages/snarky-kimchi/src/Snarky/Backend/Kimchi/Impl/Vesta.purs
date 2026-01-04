module Snarky.Backend.Kimchi.Impl.Vesta where

import Snarky.Backend.Kimchi.Types (GateWires, ConstraintSystem, Gate, Witness)
import Snarky.Curves.Vesta (ScalarField)
import Snarky.Data.Vector (Vector)

-- Create a new circuit gate with the given gate kind, wires, and coefficients
foreign import vestaCircuitGateNew :: String -> GateWires -> Array ScalarField -> Gate ScalarField

-- Get the gate wires from a circuit gate
foreign import vestaCircuitGateGetWires :: Gate ScalarField -> GateWires

-- Get the number of coefficients in a circuit gate
foreign import vestaCircuitGateCoeffCount :: Gate ScalarField -> Int

-- Get a coefficient at the specified index
foreign import vestaCircuitGateGetCoeff :: Gate ScalarField -> Int -> ScalarField

foreign import vestaConstraintSystemCreate :: Array (Gate ScalarField) -> Int -> ConstraintSystem ScalarField

foreign import vestaWitnessCreate :: Array (Vector 15 ScalarField) -> Witness ScalarField