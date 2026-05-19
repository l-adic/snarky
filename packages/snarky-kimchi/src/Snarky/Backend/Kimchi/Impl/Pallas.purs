module Snarky.Backend.Kimchi.Impl.Pallas where

import Data.Array as Array
import Data.Maybe (Maybe(..))
import Data.Vector (Vector)
import Effect (Effect)
import Partial.Unsafe (unsafeCrashWith)
import Snarky.Backend.Kimchi.Types (CRS, ConstraintSystem, Gate, GateWires, ProverIndex, VerifierIndex)
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

foreign import pallasConstraintSystemCreate :: Array (Gate Pallas.ScalarField) -> Int -> Int -> ConstraintSystem Pallas.ScalarField

foreign import pallasConstraintSystemCreateWithPrevChallenges
  :: Array (Gate Pallas.ScalarField) -> Int -> Int -> Int -> ConstraintSystem Pallas.ScalarField

foreign import pallasConstraintSystemToJson :: ConstraintSystem Pallas.ScalarField -> String
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

foreign import pallasProverIndexCreate :: ConstraintSystem Pallas.ScalarField -> Pallas.ScalarField -> CRS Pallas.G -> ProverIndex Pallas.G Pallas.ScalarField

foreign import pallasProverIndexVerify :: ProverIndex Pallas.G Pallas.ScalarField -> Vector 15 (Array Pallas.ScalarField) -> Array Pallas.ScalarField -> Boolean

foreign import vestaVerifierIndex :: ProverIndex Pallas.G Pallas.ScalarField -> VerifierIndex Pallas.G Pallas.ScalarField

createCRS :: Effect (CRS Pallas.G)
createCRS = pallasCrsLoadFromCache

createProverIndex :: ConstraintSystem Pallas.ScalarField -> Pallas.ScalarField -> CRS Pallas.G -> ProverIndex Pallas.G Pallas.ScalarField
createProverIndex = pallasProverIndexCreate

createVerifierIndex :: ProverIndex Pallas.G Pallas.ScalarField -> VerifierIndex Pallas.G Pallas.ScalarField
createVerifierIndex = vestaVerifierIndex

verifyProverIndex :: ProverIndex Pallas.G Pallas.ScalarField -> Vector 15 (Array Pallas.ScalarField) -> Array Pallas.ScalarField -> Boolean
verifyProverIndex = pallasProverIndexVerify