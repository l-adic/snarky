module Snarky.Backend.Kimchi.Impl.Pallas where

import Snarky.Backend.Kimchi.Types (GateWires)
import Snarky.Curves.Pallas as Pallas
import Snarky.Data.Vector (Vector)

-- Opaque types for CircuitGate from proof-systems
foreign import data CircuitGate :: Type

-- Create a new circuit gate with the given gate kind, wires, and coefficients
foreign import pallasCircuitGateNew :: String -> GateWires -> Array Pallas.ScalarField -> CircuitGate

-- Get the gate wires from a circuit gate
foreign import pallasCircuitGateGetWires :: CircuitGate -> GateWires

-- Get the number of coefficients in a circuit gate
foreign import pallasCircuitGateCoeffCount :: CircuitGate -> Int

-- Get a coefficient at the specified index
foreign import pallasCircuitGateGetCoeff :: CircuitGate -> Int -> Pallas.ScalarField

-- Instance for Pallas field
foreign import data ConstraintSystem :: Type

foreign import pallasConstraintSystemCreate :: Array CircuitGate -> Int -> ConstraintSystem

foreign import data Witness :: Type

foreign import pallasWitnessCreate :: Array (Vector 15 Pallas.ScalarField) -> Witness