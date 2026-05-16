module Snarky.Backend.Kimchi.Class where

import Data.Vector (Vector)
import Effect (Effect)
import Snarky.Backend.Kimchi.Impl.Pallas (createCRS, createProverIndex, createVerifierIndex, pallasCircuitGateCoeffCount, pallasCircuitGateGetCoeff, pallasCircuitGateGetWires, pallasCircuitGateNew, pallasConstraintSystemCreate, pallasConstraintSystemCreateWithPrevChallenges, pallasConstraintSystemToJson, pallasCrsCreate, pallasCrsSize, pallasGatesToJson, verifyProverIndex) as Pallas
import Snarky.Backend.Kimchi.Impl.Vesta (createCRS, createProverIndex, createVerifierIndex, verifyProverIndex, vestaCircuitGateCoeffCount, vestaCircuitGateGetCoeff, vestaCircuitGateGetWires, vestaCircuitGateNew, vestaConstraintSystemCreate, vestaConstraintSystemCreateWithPrevChallenges, vestaConstraintSystemToJson, vestaCrsCreate, vestaCrsSize, vestaGatesToJson) as Vesta
import Snarky.Backend.Kimchi.Types (CRS, ConstraintSystem, Gate, GateWires, ProverIndex, VerifierIndex, gateKindToString)
import Snarky.Constraint.Kimchi.Types (GateKind)
import Snarky.Curves.Pallas (G, ScalarField) as Pallas
import Snarky.Curves.Vesta (G, ScalarField) as Vesta

-- Typeclass for circuit gate construction over different field types
class CircuitGateConstructor f g | f -> g, g -> f where
  circuitGateNew :: GateKind -> GateWires -> Array f -> Gate f
  circuitGateGetWires :: Gate f -> GateWires
  circuitGateCoeffCount :: Gate f -> Int
  circuitGateGetCoeff :: Gate f -> Int -> f
  -- | `Array (Gate f) -> publicInputCount -> maxPolySize -> CS`. The
  -- | last arg is the SRS's `max_poly_size`; kimchi uses it to compute
  -- | `num_chunks = ceil(domain_size / max_poly_size)` and pick the
  -- | matching `zk_rows = (16 * num_chunks + 5) / 7`. Without it, kimchi
  -- | defaults to `zk_rows = 3` (correct only at num_chunks = 1).
  constraintSystemCreate :: Array (Gate f) -> Int -> Int -> (ConstraintSystem f)
  constraintSystemCreateWithPrevChallenges :: Array (Gate f) -> Int -> Int -> Int -> (ConstraintSystem f)
  createCRS :: Effect (CRS g)
  crsCreate :: Int -> CRS g
  crsSize :: CRS g -> Int
  createProverIndex :: { crs :: CRS g, endo :: f, constraintSystem :: ConstraintSystem f } -> ProverIndex g f
  createVerifierIndex :: ProverIndex g f -> VerifierIndex g f
  verifyProverIndex :: { proverIndex :: ProverIndex g f, witness :: Vector 15 (Array f), publicInputs :: Array f } -> Boolean
  constraintSystemToJson :: ConstraintSystem f -> String
  gatesToJson :: Array (Gate f) -> Int -> String

instance CircuitGateConstructor Pallas.ScalarField Pallas.G where
  circuitGateNew kind wires coeffs = Pallas.pallasCircuitGateNew (gateKindToString kind) wires coeffs
  circuitGateGetWires = Pallas.pallasCircuitGateGetWires
  circuitGateCoeffCount = Pallas.pallasCircuitGateCoeffCount
  circuitGateGetCoeff = Pallas.pallasCircuitGateGetCoeff
  constraintSystemCreate = Pallas.pallasConstraintSystemCreate
  constraintSystemCreateWithPrevChallenges = Pallas.pallasConstraintSystemCreateWithPrevChallenges
  createCRS = Pallas.createCRS
  crsCreate = Pallas.pallasCrsCreate
  crsSize = Pallas.pallasCrsSize
  createProverIndex { crs, endo, constraintSystem } = Pallas.createProverIndex constraintSystem endo crs
  createVerifierIndex = Pallas.createVerifierIndex
  verifyProverIndex { proverIndex, witness, publicInputs } = Pallas.verifyProverIndex proverIndex witness publicInputs
  constraintSystemToJson = Pallas.pallasConstraintSystemToJson
  gatesToJson = Pallas.pallasGatesToJson

instance CircuitGateConstructor Vesta.ScalarField Vesta.G where
  circuitGateNew kind wires coeffs = Vesta.vestaCircuitGateNew (gateKindToString kind) wires coeffs
  circuitGateGetWires = Vesta.vestaCircuitGateGetWires
  circuitGateCoeffCount = Vesta.vestaCircuitGateCoeffCount
  circuitGateGetCoeff = Vesta.vestaCircuitGateGetCoeff
  constraintSystemCreate = Vesta.vestaConstraintSystemCreate
  constraintSystemCreateWithPrevChallenges = Vesta.vestaConstraintSystemCreateWithPrevChallenges
  createCRS = Vesta.createCRS
  crsCreate = Vesta.vestaCrsCreate
  crsSize = Vesta.vestaCrsSize
  createProverIndex { crs, endo, constraintSystem } = Vesta.createProverIndex constraintSystem endo crs
  createVerifierIndex = Vesta.createVerifierIndex
  verifyProverIndex { proverIndex, witness, publicInputs } = Vesta.verifyProverIndex proverIndex witness publicInputs
  constraintSystemToJson = Vesta.vestaConstraintSystemToJson
  gatesToJson = Vesta.vestaGatesToJson
