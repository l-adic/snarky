module Snarky.Backend.Kimchi.Class where

import Effect (Effect)
import Snarky.Backend.Kimchi.Impl.Pallas (createCRS, createProverIndex, createVerifierIndex, pallasCircuitGateCoeffCount, pallasCircuitGateGetCoeff, pallasCircuitGateGetWires, pallasCircuitGateNew, pallasCrsCreate, pallasCrsSize, pallasGatesToJson) as Pallas
import Snarky.Backend.Kimchi.Impl.Vesta (createCRS, createProverIndex, createVerifierIndex, vestaCircuitGateCoeffCount, vestaCircuitGateGetCoeff, vestaCircuitGateGetWires, vestaCircuitGateNew, vestaCrsCreate, vestaCrsSize, vestaGatesToJson) as Vesta
import Snarky.Backend.Kimchi.Types (CRS, Gate, GateWires, ProverIndex, VerifierIndex, gateKindToString)
import Snarky.Constraint.Kimchi.Types (GateKind)
import Snarky.Curves.Pallas (G, ScalarField) as Pallas
import Snarky.Curves.Vesta (G, ScalarField) as Vesta

-- | Typeclass for circuit gate construction over different field types.
-- |
-- | Note: the `ConstraintSystem` intermediate type has been collapsed
-- | away — `createProverIndex` now takes the raw circuit data (gates,
-- | publicInputSize, prevChallengesCount, maxPolySize) directly. The
-- | JS impl glues the underlying snarky-crypto two-step (CS-create
-- | then ProverIndex-create) internally; kimchi-napi's
-- | `caml_pasta_*_plonk_index_create` does this in one call, so the
-- | future swap to kimchi-napi is a JS-only change.
-- |
-- | The `endo` argument is also gone from `createProverIndex`; it's a
-- | curve constant fetched internally (and kimchi-napi derives it from
-- | the curve type automatically).
class CircuitGateConstructor f g | f -> g, g -> f where
  circuitGateNew :: GateKind -> GateWires -> Array f -> Gate f
  circuitGateGetWires :: Gate f -> GateWires
  circuitGateCoeffCount :: Gate f -> Int
  circuitGateGetCoeff :: Gate f -> Int -> f
  createCRS :: Effect (CRS g)
  crsCreate :: Int -> CRS g
  crsSize :: CRS g -> Int
  createProverIndex
    :: { crs :: CRS g
       , gates :: Array (Gate f)
       , publicInputSize :: Int
       , prevChallengesCount :: Int
       , maxPolySize :: Int
       }
    -> ProverIndex g f
  createVerifierIndex :: ProverIndex g f -> VerifierIndex g f
  gatesToJson :: Array (Gate f) -> Int -> String

instance CircuitGateConstructor Pallas.ScalarField Pallas.G where
  circuitGateNew kind wires coeffs = Pallas.pallasCircuitGateNew (gateKindToString kind) wires coeffs
  circuitGateGetWires = Pallas.pallasCircuitGateGetWires
  circuitGateCoeffCount = Pallas.pallasCircuitGateCoeffCount
  circuitGateGetCoeff = Pallas.pallasCircuitGateGetCoeff
  createCRS = Pallas.createCRS
  crsCreate = Pallas.pallasCrsCreate
  crsSize = Pallas.pallasCrsSize
  createProverIndex = Pallas.createProverIndex
  createVerifierIndex = Pallas.createVerifierIndex
  gatesToJson = Pallas.pallasGatesToJson

instance CircuitGateConstructor Vesta.ScalarField Vesta.G where
  circuitGateNew kind wires coeffs = Vesta.vestaCircuitGateNew (gateKindToString kind) wires coeffs
  circuitGateGetWires = Vesta.vestaCircuitGateGetWires
  circuitGateCoeffCount = Vesta.vestaCircuitGateCoeffCount
  circuitGateGetCoeff = Vesta.vestaCircuitGateGetCoeff
  createCRS = Vesta.createCRS
  crsCreate = Vesta.vestaCrsCreate
  crsSize = Vesta.vestaCrsSize
  createProverIndex = Vesta.createProverIndex
  createVerifierIndex = Vesta.createVerifierIndex
  gatesToJson = Vesta.vestaGatesToJson
