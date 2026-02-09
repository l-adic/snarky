-- | Test-only FFI bindings for proof creation and oracle computation.
module Test.Pickles.ProofFFI
  ( class ProofFFI
  , proverIndexShifts
  , createProof
  , proofWitnessEvals
  , proofZEvals
  , proofSigmaEvals
  , proofCoefficientEvals
  , proofOracles
  , proofBulletproofChallenges
  , verifyOpeningProof
  , computeB0
  , permutationVanishingPolynomial
  , domainGenerator
  , proofIpaRounds
  -- Functions not in typeclass (use different field than circuit field f)
  , pallasSpongeCheckpointBeforeChallenges
  , vestaSpongeCheckpointBeforeChallenges
  , pallasProofOpeningLr
  , vestaProofOpeningLr
  , pallasProofLrProd
  , vestaProofLrProd
  , pallasProofOpeningDelta
  , vestaProofOpeningDelta
  , pallasProofOpeningSg
  , vestaProofOpeningSg
  , pallasProofOpeningZ1
  , vestaProofOpeningZ1
  , pallasProofOpeningZ2
  , vestaProofOpeningZ2
  , pallasProverIndexBlindingGenerator
  , vestaProverIndexBlindingGenerator
  , pallasCombinedPolynomialCommitment
  , vestaCombinedPolynomialCommitment
  , pallasDebugVerify
  , vestaDebugVerify
  , pallasVerifierIndexMaxPolySize
  , vestaVerifierIndexMaxPolySize
  , pallasVerifierIndexDigest
  , pallasPublicComm
  , vestaPublicComm
  , pallasLagrangeCommitments
  , vestaLagrangeCommitments
  , pallasProofCommitments
  , pallasFtComm
  , pallasPermScalar
  , pallasSigmaCommLast
  , pallasVerifierIndexColumnComms
  , vestaVerifierIndexColumnComms
  , pallasChallengePolyCommitment
  , vestaChallengePolyCommitment
  , ProofCommitments
  , Proof
  , OraclesResult
  , PointEval
  , SpongeCheckpoint
  , LrPair
  ) where

import Data.Unit (Unit)
import Data.Vector (Vector)
import Snarky.Backend.Kimchi.Types (ProverIndex, VerifierIndex)
import Snarky.Circuit.DSL (SizedF)
import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Vesta as Vesta
import Snarky.Data.EllipticCurve (AffinePoint)

-- | Opaque proof type, parameterized by curve group and scalar field.
foreign import data Proof :: Type -> Type -> Type

-- | Polynomial evaluation at two points: zeta and zeta*omega
type PointEval f = { zeta :: f, omegaTimesZeta :: f }

-- | Result of running the Fiat-Shamir oracle computation on a proof.
type OraclesResult f =
  { alpha :: f
  , beta :: SizedF 128 f -- 128-bit challenge (no endo expansion, unlike alpha)
  , gamma :: SizedF 128 f -- 128-bit challenge (no endo expansion, unlike alpha)
  , zeta :: f
  , ftEval0 :: f
  , v :: f -- polyscale (xi)
  , u :: f -- evalscale
  , combinedInnerProduct :: f
  , ftEval1 :: f
  , publicEvalZeta :: f
  , publicEvalZetaOmega :: f
  , fqDigest :: f -- Fq-sponge digest before Fr-sponge (for xi derivation)
  , alphaChal :: SizedF 128 f -- raw 128-bit alpha challenge (pre-endo-expansion)
  , zetaChal :: SizedF 128 f -- raw 128-bit zeta challenge (pre-endo-expansion)
  , vChal :: SizedF 128 f -- raw 128-bit polyscale challenge (pre-endo-expansion)
  }

-- | Sponge checkpoint for debugging/testing challenge extraction.
-- | Contains the Poseidon sponge state (3 field elements) and mode info.
type SpongeCheckpoint f =
  { state :: Vector 3 f -- Poseidon state (3 field elements)
  , spongeMode :: String -- "Absorbed" or "Squeezed"
  , modeCount :: Int -- count from the sponge mode
  }

-- | A single L/R pair from the IPA opening proof.
type LrPair f = { l :: AffinePoint f, r :: AffinePoint f }

-- | Typeclass for proof-related FFI operations.
-- | `f` is the scalar field, `g` is the curve group.
-- | For Pallas (Fq circuits): f = Pallas.BaseField, g = Vesta.G
-- | For Vesta (Fp circuits): f = Vesta.BaseField, g = Pallas.G
class ProofFFI f g | f -> g where
  proverIndexShifts :: ProverIndex g f -> Vector 7 f
  createProof :: { proverIndex :: ProverIndex g f, witness :: Vector 15 (Array f) } -> Proof g f
  proofWitnessEvals :: Proof g f -> Vector 15 (PointEval f)
  proofZEvals :: Proof g f -> PointEval f
  proofSigmaEvals :: Proof g f -> Vector 6 (PointEval f)
  proofCoefficientEvals :: Proof g f -> Vector 15 (PointEval f)
  proofOracles :: VerifierIndex g f -> { proof :: Proof g f, publicInput :: Array f } -> OraclesResult f
  proofBulletproofChallenges :: VerifierIndex g f -> { proof :: Proof g f, publicInput :: Array f } -> Array f
  verifyOpeningProof :: VerifierIndex g f -> { proof :: Proof g f, publicInput :: Array f } -> Boolean
  permutationVanishingPolynomial :: { domainLog2 :: Int, zkRows :: Int, pt :: f } -> f
  domainGenerator :: Int -> f
  computeB0 :: { challenges :: Array f, zeta :: f, zetaOmega :: f, evalscale :: f } -> f
  proofIpaRounds :: Proof g f -> Int

--------------------------------------------------------------------------------
-- Private foreign imports
--------------------------------------------------------------------------------

foreign import pallasProverIndexShifts :: ProverIndex Vesta.G Pallas.BaseField -> Vector 7 Pallas.BaseField
foreign import vestaProverIndexShifts :: ProverIndex Pallas.G Vesta.BaseField -> Vector 7 Vesta.BaseField

foreign import pallasCreateProof :: { proverIndex :: ProverIndex Vesta.G Pallas.BaseField, witness :: Vector 15 (Array Pallas.BaseField) } -> Proof Vesta.G Pallas.BaseField
foreign import vestaCreateProof :: { proverIndex :: ProverIndex Pallas.G Vesta.BaseField, witness :: Vector 15 (Array Vesta.BaseField) } -> Proof Pallas.G Vesta.BaseField

foreign import pallasProofWitnessEvals :: Proof Vesta.G Pallas.BaseField -> Vector 15 (PointEval Pallas.BaseField)
foreign import vestaProofWitnessEvals :: Proof Pallas.G Vesta.BaseField -> Vector 15 (PointEval Vesta.BaseField)

foreign import pallasProofZEvals :: Proof Vesta.G Pallas.BaseField -> PointEval Pallas.BaseField
foreign import vestaProofZEvals :: Proof Pallas.G Vesta.BaseField -> PointEval Vesta.BaseField

foreign import pallasProofSigmaEvals :: Proof Vesta.G Pallas.BaseField -> Vector 6 (PointEval Pallas.BaseField)
foreign import vestaProofSigmaEvals :: Proof Pallas.G Vesta.BaseField -> Vector 6 (PointEval Vesta.BaseField)

foreign import pallasProofCoefficientEvals :: Proof Vesta.G Pallas.BaseField -> Vector 15 (PointEval Pallas.BaseField)
foreign import vestaProofCoefficientEvals :: Proof Pallas.G Vesta.BaseField -> Vector 15 (PointEval Vesta.BaseField)

foreign import pallasProofOracles :: VerifierIndex Vesta.G Pallas.BaseField -> { proof :: Proof Vesta.G Pallas.BaseField, publicInput :: Array Pallas.BaseField } -> OraclesResult Pallas.BaseField
foreign import vestaProofOracles :: VerifierIndex Pallas.G Vesta.BaseField -> { proof :: Proof Pallas.G Vesta.BaseField, publicInput :: Array Vesta.BaseField } -> OraclesResult Vesta.BaseField

foreign import pallasProofBulletproofChallenges :: VerifierIndex Vesta.G Pallas.BaseField -> { proof :: Proof Vesta.G Pallas.BaseField, publicInput :: Array Pallas.BaseField } -> Array Pallas.BaseField
foreign import vestaProofBulletproofChallenges :: VerifierIndex Pallas.G Vesta.BaseField -> { proof :: Proof Pallas.G Vesta.BaseField, publicInput :: Array Vesta.BaseField } -> Array Vesta.BaseField

foreign import pallasVerifyOpeningProof :: VerifierIndex Vesta.G Pallas.BaseField -> { proof :: Proof Vesta.G Pallas.BaseField, publicInput :: Array Pallas.BaseField } -> Boolean
foreign import vestaVerifyOpeningProof :: VerifierIndex Pallas.G Vesta.BaseField -> { proof :: Proof Pallas.G Vesta.BaseField, publicInput :: Array Vesta.BaseField } -> Boolean

foreign import pallasPermutationVanishingPolynomial :: { domainLog2 :: Int, zkRows :: Int, pt :: Pallas.BaseField } -> Pallas.BaseField
foreign import vestaPermutationVanishingPolynomial :: { domainLog2 :: Int, zkRows :: Int, pt :: Vesta.BaseField } -> Vesta.BaseField

foreign import pallasDomainGenerator :: Int -> Pallas.BaseField
foreign import vestaDomainGenerator :: Int -> Vesta.BaseField

foreign import pallasComputeB0 :: { challenges :: Array Pallas.BaseField, zeta :: Pallas.BaseField, zetaOmega :: Pallas.BaseField, evalscale :: Pallas.BaseField } -> Pallas.BaseField
foreign import vestaComputeB0 :: { challenges :: Array Vesta.BaseField, zeta :: Vesta.BaseField, zetaOmega :: Vesta.BaseField, evalscale :: Vesta.BaseField } -> Vesta.BaseField

foreign import pallasProofIpaRounds :: Proof Vesta.G Pallas.BaseField -> Int
foreign import vestaProofIpaRounds :: Proof Pallas.G Vesta.BaseField -> Int

-- Note: Sponge checkpoint state is in the commitment curve's base field (the "other" field in the 2-cycle)
-- Pallas circuits use Vesta for commitments, so sponge is over Vesta.BaseField = Pallas.ScalarField
-- Vesta circuits use Pallas for commitments, so sponge is over Pallas.BaseField = Vesta.ScalarField
foreign import pallasSpongeCheckpointBeforeChallenges :: VerifierIndex Vesta.G Pallas.BaseField -> { proof :: Proof Vesta.G Pallas.BaseField, publicInput :: Array Pallas.BaseField } -> SpongeCheckpoint Pallas.ScalarField
foreign import vestaSpongeCheckpointBeforeChallenges :: VerifierIndex Pallas.G Vesta.BaseField -> { proof :: Proof Pallas.G Vesta.BaseField, publicInput :: Array Vesta.BaseField } -> SpongeCheckpoint Vesta.ScalarField

-- Note: L/R coordinates are in the commitment curve's base field (the "other" field in the 2-cycle)
-- For Pallas circuits using Vesta commitments: Vesta.BaseField = Pallas.ScalarField
-- For Vesta circuits using Pallas commitments: Pallas.BaseField = Vesta.ScalarField
foreign import pallasProofOpeningLr :: Proof Vesta.G Pallas.BaseField -> Vector 16 (LrPair Pallas.ScalarField)
foreign import vestaProofOpeningLr :: Proof Pallas.G Vesta.BaseField -> Vector 16 (LrPair Vesta.ScalarField)

-- lr_prod: the curve point sum from bullet_reduce
-- lr_prod = Σ_i [chal_inv[i] * L_i + chal[i] * R_i]
-- Returns the coordinates of the result point in the commitment curve's base field
foreign import pallasProofLrProd :: VerifierIndex Vesta.G Pallas.BaseField -> { proof :: Proof Vesta.G Pallas.BaseField, publicInput :: Array Pallas.BaseField } -> AffinePoint Pallas.ScalarField
foreign import vestaProofLrProd :: VerifierIndex Pallas.G Vesta.BaseField -> { proof :: Proof Pallas.G Vesta.BaseField, publicInput :: Array Vesta.BaseField } -> AffinePoint Vesta.ScalarField

-- Opening proof delta (curve point)
-- Coordinates are in the commitment curve's base field
foreign import pallasProofOpeningDelta :: Proof Vesta.G Pallas.BaseField -> AffinePoint Pallas.ScalarField
foreign import vestaProofOpeningDelta :: Proof Pallas.G Vesta.BaseField -> AffinePoint Vesta.ScalarField

-- Opening proof sg (challenge polynomial commitment, curve point)
-- Coordinates are in the commitment curve's base field
foreign import pallasProofOpeningSg :: Proof Vesta.G Pallas.BaseField -> AffinePoint Pallas.ScalarField
foreign import vestaProofOpeningSg :: Proof Pallas.G Vesta.BaseField -> AffinePoint Vesta.ScalarField

-- Opening proof z1 scalar (in the commitment curve's scalar field = circuit field)
foreign import pallasProofOpeningZ1 :: Proof Vesta.G Pallas.BaseField -> Pallas.BaseField
foreign import vestaProofOpeningZ1 :: Proof Pallas.G Vesta.BaseField -> Vesta.BaseField

-- Opening proof z2 scalar (in the commitment curve's scalar field = circuit field)
foreign import pallasProofOpeningZ2 :: Proof Vesta.G Pallas.BaseField -> Pallas.BaseField
foreign import vestaProofOpeningZ2 :: Proof Pallas.G Vesta.BaseField -> Vesta.BaseField

-- Blinding generator H from SRS (coordinates in commitment curve's base field)
foreign import pallasProverIndexBlindingGenerator :: VerifierIndex Vesta.G Pallas.BaseField -> AffinePoint Pallas.ScalarField
foreign import vestaProverIndexBlindingGenerator :: VerifierIndex Pallas.G Vesta.BaseField -> AffinePoint Vesta.ScalarField

-- Combined polynomial commitment (coordinates in commitment curve's base field)
-- This is the batched commitment: sum_i polyscale^i * C_i
foreign import pallasCombinedPolynomialCommitment :: VerifierIndex Vesta.G Pallas.BaseField -> { proof :: Proof Vesta.G Pallas.BaseField, publicInput :: Array Pallas.BaseField } -> AffinePoint Pallas.ScalarField
foreign import vestaCombinedPolynomialCommitment :: VerifierIndex Pallas.G Vesta.BaseField -> { proof :: Proof Pallas.G Vesta.BaseField, publicInput :: Array Vesta.BaseField } -> AffinePoint Vesta.ScalarField

-- Debug verification: prints intermediate IPA values to stderr
foreign import pallasDebugVerify :: VerifierIndex Vesta.G Pallas.BaseField -> { proof :: Proof Vesta.G Pallas.BaseField, publicInput :: Array Pallas.BaseField } -> Unit
foreign import vestaDebugVerify :: VerifierIndex Pallas.G Vesta.BaseField -> { proof :: Proof Pallas.G Vesta.BaseField, publicInput :: Array Vesta.BaseField } -> Unit

-- Max polynomial size from verifier index
foreign import pallasVerifierIndexMaxPolySize :: VerifierIndex Vesta.G Pallas.BaseField -> Int
foreign import vestaVerifierIndexMaxPolySize :: VerifierIndex Pallas.G Vesta.BaseField -> Int

-- Fq-sponge transcript helpers
-- VK digest: returns Fq element (Pallas.ScalarField)
foreign import pallasVerifierIndexDigest :: VerifierIndex Vesta.G Pallas.BaseField -> Pallas.ScalarField

-- Public input polynomial commitment: returns array of {x, y} points in Fq (one per chunk)
foreign import pallasPublicComm :: VerifierIndex Vesta.G Pallas.BaseField -> Array Pallas.BaseField -> Array (AffinePoint Pallas.ScalarField)
foreign import vestaPublicComm :: VerifierIndex Pallas.G Vesta.BaseField -> Array Vesta.BaseField -> Array (AffinePoint Vesta.ScalarField)

-- Lagrange commitment points from SRS (constant bases for public input MSM)
foreign import pallasLagrangeCommitments :: VerifierIndex Vesta.G Pallas.BaseField -> Int -> Array (AffinePoint Pallas.ScalarField)
foreign import vestaLagrangeCommitments :: VerifierIndex Pallas.G Vesta.BaseField -> Int -> Array (AffinePoint Vesta.ScalarField)

-- ft_comm: the chunked commitment of the linearized constraint polynomial (in Fq)
foreign import pallasFtComm :: VerifierIndex Vesta.G Pallas.BaseField -> { proof :: Proof Vesta.G Pallas.BaseField, publicInput :: Array Pallas.BaseField } -> AffinePoint Pallas.ScalarField

-- perm_scalar: the scalar multiplier for sigma_comm_last in the linearization (in Fp)
foreign import pallasPermScalar :: VerifierIndex Vesta.G Pallas.BaseField -> { proof :: Proof Vesta.G Pallas.BaseField, publicInput :: Array Pallas.BaseField } -> Pallas.BaseField

-- sigma_comm[PERMUTS-1] from verifier index (in Fq)
foreign import pallasSigmaCommLast :: VerifierIndex Vesta.G Pallas.BaseField -> AffinePoint Pallas.ScalarField

-- VK column commitments: 27 points (6 index + 15 coefficient + 6 sigma) in to_batch order
foreign import pallasVerifierIndexColumnComms :: VerifierIndex Vesta.G Pallas.BaseField -> Array (AffinePoint Pallas.ScalarField)
foreign import vestaVerifierIndexColumnComms :: VerifierIndex Pallas.G Vesta.BaseField -> Array (AffinePoint Vesta.ScalarField)

-- Challenge polynomial commitment: MSM of b_poly_coefficients against SRS
-- Challenges are in the commitment curve's scalar field (= circuit field)
-- Returns point coordinates in the commitment curve's base field
foreign import pallasChallengePolyCommitment :: VerifierIndex Vesta.G Pallas.BaseField -> Array Pallas.BaseField -> AffinePoint Pallas.ScalarField
foreign import vestaChallengePolyCommitment :: VerifierIndex Pallas.G Vesta.BaseField -> Array Vesta.BaseField -> AffinePoint Vesta.ScalarField

-- | Proof commitments structured for Fq-sponge absorption.
type ProofCommitments f =
  { wComm :: Vector 15 (AffinePoint f)
  , zComm :: AffinePoint f
  , tComm :: Array (AffinePoint f)
  }

-- Proof commitments: w_comm (15 points), z_comm (1 point), t_comm (1+ points) in Fq
foreign import pallasProofCommitments :: Proof Vesta.G Pallas.BaseField -> ProofCommitments Pallas.ScalarField

--------------------------------------------------------------------------------
-- Instances
--------------------------------------------------------------------------------

instance ProofFFI Pallas.BaseField Vesta.G where
  proverIndexShifts = pallasProverIndexShifts
  createProof = pallasCreateProof
  proofWitnessEvals = pallasProofWitnessEvals
  proofZEvals = pallasProofZEvals
  proofSigmaEvals = pallasProofSigmaEvals
  proofCoefficientEvals = pallasProofCoefficientEvals
  proofOracles = pallasProofOracles
  proofBulletproofChallenges = pallasProofBulletproofChallenges
  verifyOpeningProof = pallasVerifyOpeningProof
  permutationVanishingPolynomial = pallasPermutationVanishingPolynomial
  domainGenerator = pallasDomainGenerator
  computeB0 = pallasComputeB0
  proofIpaRounds = pallasProofIpaRounds

instance ProofFFI Vesta.BaseField Pallas.G where
  proverIndexShifts = vestaProverIndexShifts
  createProof = vestaCreateProof
  proofWitnessEvals = vestaProofWitnessEvals
  proofZEvals = vestaProofZEvals
  proofSigmaEvals = vestaProofSigmaEvals
  proofCoefficientEvals = vestaProofCoefficientEvals
  proofOracles = vestaProofOracles
  proofBulletproofChallenges = vestaProofBulletproofChallenges
  verifyOpeningProof = vestaVerifyOpeningProof
  permutationVanishingPolynomial = vestaPermutationVanishingPolynomial
  domainGenerator = vestaDomainGenerator
  computeB0 = vestaComputeB0
  proofIpaRounds = vestaProofIpaRounds
