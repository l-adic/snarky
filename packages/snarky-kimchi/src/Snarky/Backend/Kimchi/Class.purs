module Snarky.Backend.Kimchi.Class where

import Effect (Effect)
import Snarky.Backend.Kimchi.Impl.Pallas (createCRS, createProverIndex, verifyProverIndex, pallasCircuitGateCoeffCount, pallasCircuitGateGetCoeff, pallasCircuitGateGetWires, pallasCircuitGateNew, pallasConstraintSystemCreate, pallasWitnessCreate) as Pallas
import Snarky.Backend.Kimchi.Impl.Vesta (createCRS, createProverIndex, verifyProverIndex, vestaCircuitGateCoeffCount, vestaCircuitGateGetCoeff, vestaCircuitGateGetWires, vestaCircuitGateNew, vestaConstraintSystemCreate, vestaWitnessCreate) as Vesta
import Snarky.Backend.Kimchi.Types (CRS, ConstraintSystem, Gate, GateWires, ProverIndex, Witness, gateKindToString)
import Snarky.Constraint.Kimchi.Wire (GateKind)
import Snarky.Curves.Pallas (ScalarField, G) as Pallas
import Snarky.Curves.Vesta (ScalarField, G) as Vesta
import Snarky.Data.Vector (Vector)

-- Typeclass for circuit gate construction over different field types
class CircuitGateConstructor f g | f -> g, g -> f where
  circuitGateNew :: GateKind -> GateWires -> Array f -> Gate f
  circuitGateGetWires :: Gate f -> GateWires
  circuitGateCoeffCount :: Gate f -> Int
  circuitGateGetCoeff :: Gate f -> Int -> f
  constraintSystemCreate :: Array (Gate f) -> Int -> (ConstraintSystem f)
  witnessCreate :: Array (Vector 15 f) -> Witness f
  createCRS :: Effect (CRS g)
  createProverIndex :: { crs :: CRS g, endo :: f, constraintSystem :: ConstraintSystem f } -> ProverIndex g f
  verifyProverIndex :: { proverIndex :: ProverIndex g f, witness :: Witness f, publicInputs :: Array f } -> Boolean

instance CircuitGateConstructor Pallas.ScalarField Pallas.G where
  circuitGateNew kind wires coeffs = Pallas.pallasCircuitGateNew (gateKindToString kind) wires coeffs
  circuitGateGetWires = Pallas.pallasCircuitGateGetWires
  circuitGateCoeffCount = Pallas.pallasCircuitGateCoeffCount
  circuitGateGetCoeff = Pallas.pallasCircuitGateGetCoeff
  constraintSystemCreate = Pallas.pallasConstraintSystemCreate
  witnessCreate = Pallas.pallasWitnessCreate
  createCRS = Pallas.createCRS
  createProverIndex { crs, endo, constraintSystem } = Pallas.createProverIndex constraintSystem endo crs
  verifyProverIndex { proverIndex, witness, publicInputs } = Pallas.verifyProverIndex proverIndex witness publicInputs

instance CircuitGateConstructor Vesta.ScalarField Vesta.G where
  circuitGateNew kind wires coeffs = Vesta.vestaCircuitGateNew (gateKindToString kind) wires coeffs
  circuitGateGetWires = Vesta.vestaCircuitGateGetWires
  circuitGateCoeffCount = Vesta.vestaCircuitGateCoeffCount
  circuitGateGetCoeff = Vesta.vestaCircuitGateGetCoeff
  constraintSystemCreate = Vesta.vestaConstraintSystemCreate
  witnessCreate = Vesta.vestaWitnessCreate
  createCRS = Vesta.createCRS
  createProverIndex { crs, endo, constraintSystem } = Vesta.createProverIndex constraintSystem endo crs
  verifyProverIndex { proverIndex, witness, publicInputs } = Vesta.verifyProverIndex proverIndex witness publicInputs