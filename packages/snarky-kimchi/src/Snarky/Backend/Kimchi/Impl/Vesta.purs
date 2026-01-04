module Snarky.Backend.Kimchi.Impl.Vesta where

import Effect (Effect)
import Snarky.Backend.Kimchi.Types (CRS, ConstraintSystem, Gate, GateWires, Witness)
import Snarky.Curves.Vesta as Vesta
import Snarky.Data.Vector (Vector)

-- Create a new circuit gate with the given gate kind, wires, and coefficients
foreign import vestaCircuitGateNew :: String -> GateWires -> Array Vesta.ScalarField -> Gate Vesta.ScalarField

-- Get the gate wires from a circuit gate
foreign import vestaCircuitGateGetWires :: Gate Vesta.ScalarField -> GateWires

-- Get the number of coefficients in a circuit gate
foreign import vestaCircuitGateCoeffCount :: Gate Vesta.ScalarField -> Int

-- Get a coefficient at the specified index
foreign import vestaCircuitGateGetCoeff :: Gate Vesta.ScalarField -> Int -> Vesta.ScalarField

foreign import vestaConstraintSystemCreate :: Array (Gate Vesta.ScalarField) -> Int -> ConstraintSystem Vesta.ScalarField

foreign import vestaWitnessCreate :: Array (Vector 15 Vesta.ScalarField) -> Witness Vesta.ScalarField

foreign import vestaCrsLoadFromCache :: Effect (CRS Vesta.G)

createCRS :: Effect (CRS Vesta.G)
createCRS = vestaCrsLoadFromCache