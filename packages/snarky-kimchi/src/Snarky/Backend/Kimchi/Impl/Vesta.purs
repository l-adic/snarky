module Snarky.Backend.Kimchi.Impl.Vesta where

import Snarky.Backend.Kimchi.Types (GateWires)
import Snarky.Curves.Vesta as Vesta
import Snarky.Data.Vector (Vector)

-- Opaque types for CircuitGate from proof-systems
foreign import data CircuitGate :: Type

-- Create a new circuit gate with the given gate kind, wires, and coefficients
foreign import vestaCircuitGateNew :: String -> GateWires -> Array Vesta.ScalarField -> CircuitGate

-- Get the gate wires from a circuit gate
foreign import vestaCircuitGateGetWires :: CircuitGate -> GateWires

-- Get the number of coefficients in a circuit gate
foreign import vestaCircuitGateCoeffCount :: CircuitGate -> Int

-- Get a coefficient at the specified index
foreign import vestaCircuitGateGetCoeff :: CircuitGate -> Int -> Vesta.ScalarField

-- Instance for vesta field
foreign import data ConstraintSystem :: Type

foreign import vestaConstraintSystemCreate :: Array CircuitGate -> Int -> ConstraintSystem

foreign import data Witness :: Type

foreign import vestaWitnessCreate :: Array (Vector 15 Vesta.ScalarField) -> Witness