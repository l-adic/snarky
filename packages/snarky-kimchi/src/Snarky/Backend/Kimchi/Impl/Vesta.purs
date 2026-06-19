module Snarky.Backend.Kimchi.Impl.Vesta where

import Data.Array as Array
import Data.ArrayBuffer.Types (Uint8Array)
import Data.Maybe (Maybe(..))
import Data.Unit (Unit)
import Effect (Effect)
import Partial.Unsafe (unsafeCrashWith)
import Snarky.Backend.Kimchi.Types (CRS, Gate, GateWires, ProverIndex, VerifierIndex)
import Snarky.Curves.Vesta as Vesta
import Snarky.Data.EllipticCurve (AffinePoint(..))

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

-- | Pre-warm the lagrange-basis cache of the (shared) SRS for the domain
-- | of size `2^log2`. Effectful: mutates the SRS in place, so later
-- | index/proof creation over that domain hits the cache.
foreign import vestaSrsAddLagrangeBasis :: CRS Vesta.G -> Int -> Effect Unit

-- | Serialize the lagrange basis for the domain of size `2^log2` to a byte
-- | blob (computing it if not yet cached). The out-of-band carrier the SRS
-- | cache manager persists — `vestaSrsToBytes` (generators) skips it.
foreign import vestaSrsLagrangeBasisToBytes :: CRS Vesta.G -> Int -> Effect Uint8Array

-- | Inject a serialized lagrange basis (from `vestaSrsLagrangeBasisToBytes`)
-- | into this SRS's cache for the domain of size `2^log2`, so later
-- | index/proof creation hits the cache instead of running the FFT.
foreign import vestaSrsSetLagrangeBasisFromBytes :: CRS Vesta.G -> Int -> Uint8Array -> Effect Unit

-- | Serialize the SRS generators (`g`, `h`) to a byte blob. The basis cache is
-- | `#[serde(skip)]`'d, so this carries generators only — pair with
-- | `vestaSrsLagrangeBasisToBytes` per domain.
foreign import vestaSrsToBytes :: CRS Vesta.G -> Effect Uint8Array

-- | Reconstruct an SRS (generators only) from `vestaSrsToBytes`, tagged with the
-- | given size. Deterministic alternative to `vestaCrsCreate size`.
foreign import vestaSrsFromBytes :: Int -> Uint8Array -> Effect (CRS Vesta.G)

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
      Just x, Just y -> AffinePoint { x, y }
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
