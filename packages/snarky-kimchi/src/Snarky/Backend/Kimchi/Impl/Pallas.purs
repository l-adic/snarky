module Snarky.Backend.Kimchi.Impl.Pallas where

import Snarky.Backend.Kimchi.Types (Gate, GateWires, ConstraintSystem, Witness)
import Snarky.Curves.Pallas (ScalarField)
import Snarky.Data.Vector (Vector)

-- Create a new circuit gate with the given gate kind, wires, and coefficients
foreign import pallasCircuitGateNew :: String -> GateWires -> Array ScalarField -> Gate ScalarField

-- Get the gate wires from a circuit gate
foreign import pallasCircuitGateGetWires :: Gate ScalarField -> GateWires

-- Get the number of coefficients in a circuit gate
foreign import pallasCircuitGateCoeffCount :: Gate ScalarField -> Int

-- Get a coefficient at the specified index
foreign import pallasCircuitGateGetCoeff :: Gate ScalarField -> Int -> ScalarField

foreign import pallasConstraintSystemCreate :: Array (Gate ScalarField) -> Int -> ConstraintSystem ScalarField

foreign import pallasWitnessCreate :: Array (Vector 15 ScalarField) -> Witness ScalarField