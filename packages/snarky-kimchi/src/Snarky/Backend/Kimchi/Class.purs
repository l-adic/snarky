module Snarky.Backend.Kimchi.Class where

import Snarky.Backend.Kimchi.Impl.Pallas (pallasCircuitGateCoeffCount, pallasCircuitGateGetCoeff, pallasCircuitGateGetWires, pallasCircuitGateNew, pallasConstraintSystemCreate, pallasWitnessCreate) as Pallas
import Snarky.Backend.Kimchi.Impl.Vesta (vestaCircuitGateCoeffCount, vestaCircuitGateGetCoeff, vestaCircuitGateGetWires, vestaCircuitGateNew, vestaConstraintSystemCreate, vestaWitnessCreate) as Vesta
import Snarky.Backend.Kimchi.Types (ConstraintSystem, Gate, GateWires, Witness, gateKindToString)
import Snarky.Constraint.Kimchi.Wire (GateKind)
import Snarky.Curves.Pallas (ScalarField) as Pallas
import Snarky.Curves.Vesta (ScalarField) as Vesta
import Snarky.Data.Vector (Vector)

-- Typeclass for circuit gate construction over different field types
class CircuitGateConstructor f where
  circuitGateNew :: GateKind -> GateWires -> Array f -> Gate f
  circuitGateGetWires :: Gate f -> GateWires
  circuitGateCoeffCount :: Gate f -> Int
  circuitGateGetCoeff :: Gate f -> Int -> f
  constraintSystemCreate :: Array (Gate f) -> Int -> (ConstraintSystem f)
  witnessCreate :: Array (Vector 15 f) -> Witness f

instance CircuitGateConstructor Pallas.ScalarField where
  circuitGateNew kind wires coeffs = Pallas.pallasCircuitGateNew (gateKindToString kind) wires coeffs
  circuitGateGetWires = Pallas.pallasCircuitGateGetWires
  circuitGateCoeffCount = Pallas.pallasCircuitGateCoeffCount
  circuitGateGetCoeff = Pallas.pallasCircuitGateGetCoeff
  constraintSystemCreate = Pallas.pallasConstraintSystemCreate
  witnessCreate = Pallas.pallasWitnessCreate

instance CircuitGateConstructor Vesta.ScalarField where
  circuitGateNew kind wires coeffs = Vesta.vestaCircuitGateNew (gateKindToString kind) wires coeffs
  circuitGateGetWires = Vesta.vestaCircuitGateGetWires
  circuitGateCoeffCount = Vesta.vestaCircuitGateCoeffCount
  circuitGateGetCoeff = Vesta.vestaCircuitGateGetCoeff
  constraintSystemCreate = Vesta.vestaConstraintSystemCreate
  witnessCreate = Vesta.vestaWitnessCreate

