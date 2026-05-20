module Snarky.Backend.Kimchi.Impl.Pallas where

import Data.Array as Array
import Data.Maybe (Maybe(..))
import Effect (Effect)
import Partial.Unsafe (unsafeCrashWith)
import Snarky.Backend.Kimchi.Types (CRS, Gate, GateWires, ProverIndex, VerifierIndex)
import Snarky.Curves.Pallas as Pallas
import Snarky.Data.EllipticCurve (AffinePoint)

-- Create a new circuit gate with the given gate kind, wires, and coefficients
foreign import pallasCircuitGateNew :: String -> GateWires -> Array Pallas.ScalarField -> Gate Pallas.ScalarField

-- Get the gate wires from a circuit gate
foreign import pallasCircuitGateGetWires :: Gate Pallas.ScalarField -> GateWires

-- Get the number of coefficients in a circuit gate
foreign import pallasCircuitGateCoeffCount :: Gate Pallas.ScalarField -> Int

-- Get a coefficient at the specified index
foreign import pallasCircuitGateGetCoeff :: Gate Pallas.ScalarField -> Int -> Pallas.ScalarField

-- Debug helper: serialize the gate array to JSON (replaces the old
-- pallasConstraintSystemToJson which required the now-removed
-- ConstraintSystem type).
foreign import pallasGatesToJson :: Array (Gate Pallas.ScalarField) -> Int -> String

foreign import pallasCrsLoadFromCache :: Effect (CRS Pallas.G)
foreign import pallasCrsCreate :: Int -> CRS Pallas.G
foreign import pallasCrsSize :: CRS Pallas.G -> Int
-- | Compute challenge polynomial commitment from Pallas SRS.
-- | Pallas scalar field = Fq, result coords in Fp (= Vesta.ScalarField).
-- | OCaml: SRS.Fq.b_poly_commitment (Dummy.Ipa.Wrap.compute_sg)
-- |
-- | Returns a flat `[x, y]` array by FFI contract. Prefer
-- | `pallasSrsBPolyCommitmentPoint` for a typed `AffinePoint` result.
foreign import pallasSrsBPolyCommitment :: CRS Pallas.G -> Array Pallas.ScalarField -> Array Pallas.BaseField

-- | Typed wrapper over `pallasSrsBPolyCommitment` — returns an affine point
-- | directly instead of the `[x, y]` array the Rust FFI produces.
pallasSrsBPolyCommitmentPoint
  :: CRS Pallas.G -> Array Pallas.ScalarField -> AffinePoint Pallas.BaseField
pallasSrsBPolyCommitmentPoint srs chals =
  let
    xs = pallasSrsBPolyCommitment srs chals
  in
    case Array.index xs 0, Array.index xs 1 of
      Just x, Just y -> { x, y }
      _, _ -> unsafeCrashWith
        "pallasSrsBPolyCommitmentPoint: FFI returned unexpected length (must be [x, y])"

-- | Collapsed prover-index creation. Takes the raw circuit data
-- | (gates + publicInputSize + prevChallengesCount + maxPolySize) plus
-- | the SRS; the JS impl glues the snarky-crypto two-step CS-then-Index
-- | internally. The previous PS-level `ConstraintSystem` type is gone
-- | (no separate intermediate). `endo` is also dropped from the PS
-- | signature — it's a curve constant the JS layer fetches itself.
foreign import pallasProverIndexCreate
  :: { gates :: Array (Gate Pallas.ScalarField)
     , publicInputSize :: Int
     , prevChallengesCount :: Int
     , maxPolySize :: Int
     , crs :: CRS Pallas.G
     }
  -> ProverIndex Pallas.G Pallas.ScalarField

foreign import vestaVerifierIndex :: ProverIndex Pallas.G Pallas.ScalarField -> VerifierIndex Pallas.G Pallas.ScalarField

createCRS :: Effect (CRS Pallas.G)
createCRS = pallasCrsLoadFromCache

createProverIndex
  :: { gates :: Array (Gate Pallas.ScalarField)
     , publicInputSize :: Int
     , prevChallengesCount :: Int
     , maxPolySize :: Int
     , crs :: CRS Pallas.G
     }
  -> ProverIndex Pallas.G Pallas.ScalarField
createProverIndex = pallasProverIndexCreate

createVerifierIndex :: ProverIndex Pallas.G Pallas.ScalarField -> VerifierIndex Pallas.G Pallas.ScalarField
createVerifierIndex = vestaVerifierIndex
