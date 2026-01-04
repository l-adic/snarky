module Snarky.Backend.Kimchi.Circuit where

import Snarky.Data.Vector (Vector)
import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Vesta as Vesta
import Snarky.Constraint.Kimchi.Wire (GateKind(..))

-- Opaque types for Wire and GateWires from proof-systems
foreign import data Wire :: Type
foreign import data GateWires :: Type

-- Create a new wire pointing to the given row and column
foreign import wireNew :: Int -> Int -> Wire

-- Get the row that this wire points to
foreign import wireGetRow :: Wire -> Int

-- Get the column that this wire points to  
foreign import wireGetCol :: Wire -> Int

-- Create gate wires from exactly 7 wires
foreign import gateWiresNewFromWires :: Vector 7 Wire -> GateWires

-- Get the wire at the specified column (0-6)
foreign import gateWiresGetWire :: GateWires -> Int -> Wire

-- Opaque types for CircuitGate from proof-systems
foreign import data PallasCircuitGate :: Type
foreign import data VestaCircuitGate :: Type

-- Create a new circuit gate with the given gate kind, wires, and coefficients
foreign import pallasCircuitGateNew :: String -> GateWires -> Array Pallas.ScalarField -> PallasCircuitGate

-- Get the gate wires from a circuit gate
foreign import pallasCircuitGateGetWires :: PallasCircuitGate -> GateWires

-- Get the number of coefficients in a circuit gate
foreign import pallasCircuitGateCoeffCount :: PallasCircuitGate -> Int

-- Get a coefficient at the specified index
foreign import pallasCircuitGateGetCoeff :: PallasCircuitGate -> Int -> Pallas.ScalarField

-- Create a new circuit gate with the given gate kind, wires, and coefficients  
foreign import vestaCircuitGateNew :: String -> GateWires -> Array Vesta.ScalarField -> VestaCircuitGate

-- Get the gate wires from a circuit gate
foreign import vestaCircuitGateGetWires :: VestaCircuitGate -> GateWires

-- Get the number of coefficients in a circuit gate
foreign import vestaCircuitGateCoeffCount :: VestaCircuitGate -> Int

-- Get a coefficient at the specified index
foreign import vestaCircuitGateGetCoeff :: VestaCircuitGate -> Int -> Vesta.ScalarField

-- Convert PureScript GateKind to string expected by Rust FFI
gateKindToString :: GateKind -> String
gateKindToString = case _ of
  GenericPlonkGate -> "GenericPlonkGate"
  AddCompleteGate -> "AddCompleteGate"
  PoseidonGate -> "PoseidonGate"
  VarBaseMul -> "VarBaseMul"
  EndoMul -> "EndoMul"
  EndoScalar -> "EndoScalar"
  Zero -> "Zero"

-- Typeclass for circuit gate construction over different field types
class CircuitGateConstructor f gate cs witness | f -> gate, f -> cs, f -> witness where
  circuitGateNew :: GateKind -> GateWires -> Array f -> gate
  circuitGateGetWires :: gate -> GateWires
  circuitGateCoeffCount :: gate -> Int
  circuitGateGetCoeff :: gate -> Int -> f
  constraintSystemCreate :: Array gate -> Int -> cs
  witnessCreate :: Array (Vector 15 f) -> witness

-- Instance for Pallas field
instance CircuitGateConstructor Pallas.ScalarField PallasCircuitGate PallasConstraintSystem PallasWitness where
  circuitGateNew kind wires coeffs = pallasCircuitGateNew (gateKindToString kind) wires coeffs
  circuitGateGetWires = pallasCircuitGateGetWires
  circuitGateCoeffCount = pallasCircuitGateCoeffCount
  circuitGateGetCoeff = pallasCircuitGateGetCoeff
  constraintSystemCreate = pallasConstraintSystemCreate
  witnessCreate = pallasWitnessCreate

-- Instance for Vesta field
instance CircuitGateConstructor Vesta.ScalarField VestaCircuitGate VestaConstraintSystem VestaWitness where
  circuitGateNew kind wires coeffs = vestaCircuitGateNew (gateKindToString kind) wires coeffs
  circuitGateGetWires = vestaCircuitGateGetWires
  circuitGateCoeffCount = vestaCircuitGateCoeffCount
  circuitGateGetCoeff = vestaCircuitGateGetCoeff
  constraintSystemCreate = vestaConstraintSystemCreate
  witnessCreate = vestaWitnessCreate

foreign import data PallasConstraintSystem :: Type
foreign import data VestaConstraintSystem :: Type

foreign import pallasConstraintSystemCreate :: Array PallasCircuitGate -> Int -> PallasConstraintSystem
foreign import vestaConstraintSystemCreate :: Array VestaCircuitGate -> Int -> VestaConstraintSystem

foreign import data PallasWitness :: Type
foreign import data VestaWitness :: Type

foreign import pallasWitnessCreate :: Array (Vector 15 Pallas.ScalarField) -> PallasWitness
foreign import vestaWitnessCreate :: Array (Vector 15 Vesta.ScalarField) -> VestaWitness
