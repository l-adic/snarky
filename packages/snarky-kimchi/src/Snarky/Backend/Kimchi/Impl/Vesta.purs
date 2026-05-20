module Snarky.Backend.Kimchi.Impl.Vesta where

import Data.Array as Array
import Data.Maybe (Maybe(..))
import Effect (Effect)
import Partial.Unsafe (unsafeCrashWith)
import Snarky.Backend.Kimchi.Types (CRS, Gate, GateWires, ProverIndex, VerifierIndex)
import Snarky.Curves.Vesta as Vesta
import Snarky.Data.EllipticCurve (AffinePoint)

-- Create a new circuit gate with the given gate kind, wires, and coefficients
foreign import vestaCircuitGateNew :: String -> GateWires -> Array Vesta.ScalarField -> Gate Vesta.ScalarField

-- Get the gate wires from a circuit gate
foreign import vestaCircuitGateGetWires :: Gate Vesta.ScalarField -> GateWires

-- Get the number of coefficients in a circuit gate
foreign import vestaCircuitGateCoeffCount :: Gate Vesta.ScalarField -> Int

-- Get a coefficient at the specified index
foreign import vestaCircuitGateGetCoeff :: Gate Vesta.ScalarField -> Int -> Vesta.ScalarField

-- Debug helper: serialize the gate array to JSON (replaces the old
-- vestaConstraintSystemToJson which required the now-removed
-- ConstraintSystem type).
foreign import vestaGatesToJson :: Array (Gate Vesta.ScalarField) -> Int -> String

foreign import vestaCrsLoadFromCache :: Effect (CRS Vesta.G)
foreign import vestaCrsCreate :: Int -> CRS Vesta.G
foreign import vestaCrsSize :: CRS Vesta.G -> Int
-- | Compute challenge polynomial commitment from Vesta SRS.
-- | Vesta scalar field = Fp, result coords in Fq (= Pallas.ScalarField).
-- | OCaml: SRS.Fp.b_poly_commitment (Dummy.Ipa.Step.compute_sg)
-- |
-- | Returns a flat `[x, y]` array by FFI contract. Prefer
-- | `vestaSrsBPolyCommitmentPoint` for a typed `AffinePoint` result.
foreign import vestaSrsBPolyCommitment :: CRS Vesta.G -> Array Vesta.ScalarField -> Array Vesta.BaseField

-- | Typed wrapper over `vestaSrsBPolyCommitment` — returns an affine point
-- | directly instead of the `[x, y]` array the Rust FFI produces.
vestaSrsBPolyCommitmentPoint
  :: CRS Vesta.G -> Array Vesta.ScalarField -> AffinePoint Vesta.BaseField
vestaSrsBPolyCommitmentPoint srs chals =
  let
    xs = vestaSrsBPolyCommitment srs chals
  in
    case Array.index xs 0, Array.index xs 1 of
      Just x, Just y -> { x, y }
      _, _ -> unsafeCrashWith
        "vestaSrsBPolyCommitmentPoint: FFI returned unexpected length (must be [x, y])"

-- | Collapsed prover-index creation; see `Impl/Pallas.purs` for the
-- | rationale. JS impl glues snarky-crypto's two-step CS+Index until
-- | the kimchi-napi swap lands.
foreign import vestaProverIndexCreate
  :: { gates :: Array (Gate Vesta.ScalarField)
     , publicInputSize :: Int
     , prevChallengesCount :: Int
     , maxPolySize :: Int
     , crs :: CRS Vesta.G
     }
  -> ProverIndex Vesta.G Vesta.ScalarField

foreign import pallasVerifierIndex :: ProverIndex Vesta.G Vesta.ScalarField -> VerifierIndex Vesta.G Vesta.ScalarField

createCRS :: Effect (CRS Vesta.G)
createCRS = vestaCrsLoadFromCache

createProverIndex
  :: { gates :: Array (Gate Vesta.ScalarField)
     , publicInputSize :: Int
     , prevChallengesCount :: Int
     , maxPolySize :: Int
     , crs :: CRS Vesta.G
     }
  -> ProverIndex Vesta.G Vesta.ScalarField
createProverIndex = vestaProverIndexCreate

createVerifierIndex :: ProverIndex Vesta.G Vesta.ScalarField -> VerifierIndex Vesta.G Vesta.ScalarField
createVerifierIndex = pallasVerifierIndex
