module Snarky.Backend.Kimchi.Class where

import Snarky.Backend.Kimchi.Types (gateKindToString, GateWires)
import Snarky.Backend.Kimchi.Impl.Pallas (CircuitGate, ConstraintSystem, Witness, pallasCircuitGateCoeffCount, pallasCircuitGateGetCoeff, pallasCircuitGateGetWires, pallasCircuitGateNew, pallasConstraintSystemCreate, pallasWitnessCreate) as Pallas
import Snarky.Backend.Kimchi.Impl.Vesta (CircuitGate, ConstraintSystem, Witness, vestaCircuitGateCoeffCount, vestaCircuitGateGetCoeff, vestaCircuitGateGetWires, vestaCircuitGateNew, vestaConstraintSystemCreate, vestaWitnessCreate) as Vesta
import Snarky.Constraint.Kimchi.Wire (GateKind)
import Snarky.Curves.Pallas (ScalarField) as Pallas
import Snarky.Curves.Vesta (ScalarField) as Vesta
import Snarky.Data.Vector (Vector)

-- Typeclass for circuit gate construction over different field types
class CircuitGateConstructor f gate cs witness | f -> gate cs witness where
  circuitGateNew :: GateKind -> GateWires -> Array f -> gate
  circuitGateGetWires :: gate -> GateWires
  circuitGateCoeffCount :: gate -> Int
  circuitGateGetCoeff :: gate -> Int -> f
  constraintSystemCreate :: Array gate -> Int -> cs
  witnessCreate :: Array (Vector 15 f) -> witness

instance CircuitGateConstructor Pallas.ScalarField Pallas.CircuitGate Pallas.ConstraintSystem Pallas.Witness where
  circuitGateNew kind wires coeffs = Pallas.pallasCircuitGateNew (gateKindToString kind) wires coeffs
  circuitGateGetWires = Pallas.pallasCircuitGateGetWires
  circuitGateCoeffCount = Pallas.pallasCircuitGateCoeffCount
  circuitGateGetCoeff = Pallas.pallasCircuitGateGetCoeff
  constraintSystemCreate = Pallas.pallasConstraintSystemCreate
  witnessCreate = Pallas.pallasWitnessCreate

instance CircuitGateConstructor Vesta.ScalarField Vesta.CircuitGate Vesta.ConstraintSystem Vesta.Witness where
  circuitGateNew kind wires coeffs = Vesta.vestaCircuitGateNew (gateKindToString kind) wires coeffs
  circuitGateGetWires = Vesta.vestaCircuitGateGetWires
  circuitGateCoeffCount = Vesta.vestaCircuitGateCoeffCount
  circuitGateGetCoeff = Vesta.vestaCircuitGateGetCoeff
  constraintSystemCreate = Vesta.vestaConstraintSystemCreate
  witnessCreate = Vesta.vestaWitnessCreate

