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
  , proofSpongeCheckpoint
  , verifyOpeningProof
  , computeB0
  , permutationVanishingPolynomial
  , domainGenerator
  , proofLr
  , proofDelta
  , proofZ1
  , proofZ2
  , proofSg
  , proverIndexH
  , proofIpaRounds
  , proofLrProd
  , Proof
  , OraclesResult
  , PointEval
  ) where

import Data.Vector (Vector)
import Snarky.Backend.Kimchi.Types (ProverIndex)
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
  , beta :: f
  , gamma :: f
  , zeta :: f
  , ftEval0 :: f
  , v :: f -- polyscale
  , u :: f -- evalscale
  , combinedInnerProduct :: f
  , ftEval1 :: f
  , publicEvalZeta :: f
  , publicEvalZetaOmega :: f
  }

-- | Typeclass for proof-related FFI operations.
-- | `f` is the scalar field, `g` is the curve group, `b` is the curve's base field.
-- | For Pallas (Fq circuits): f = Pallas.BaseField, g = Vesta.G, b = Vesta.BaseField
-- | For Vesta (Fp circuits): f = Vesta.BaseField, g = Pallas.G, b = Pallas.BaseField
-- | Note: Due to the Pasta cycle, b = the "other" base field (Vesta.BaseField ≅ Pallas.ScalarField).
class ProofFFI f g b | f -> g b where
  proverIndexShifts :: ProverIndex g f -> Vector 7 f
  createProof :: { proverIndex :: ProverIndex g f, witness :: Vector 15 (Array f) } -> Proof g f
  proofWitnessEvals :: Proof g f -> Vector 15 (PointEval f)
  proofZEvals :: Proof g f -> PointEval f
  proofSigmaEvals :: Proof g f -> Vector 6 (PointEval f)
  proofCoefficientEvals :: Proof g f -> Vector 15 (PointEval f)
  proofOracles :: ProverIndex g f -> { proof :: Proof g f, publicInput :: Array f } -> OraclesResult f
  proofBulletproofChallenges :: ProverIndex g f -> { proof :: Proof g f, publicInput :: Array f } -> Array f
  -- | Sponge checkpoint: squeeze value after oracle computation + absorbing cip.
  -- | Compare against PureScript sponge to verify states match before IPA.
  proofSpongeCheckpoint :: ProverIndex g f -> { proof :: Proof g f, publicInput :: Array f } -> f
  verifyOpeningProof :: ProverIndex g f -> { proof :: Proof g f, publicInput :: Array f } -> Boolean
  permutationVanishingPolynomial :: { domainLog2 :: Int, zkRows :: Int, pt :: f } -> f
  domainGenerator :: Int -> f
  computeB0 :: { challenges :: Array f, zeta :: f, zetaOmega :: f, evalscale :: f } -> f
  -- Opening proof components (point coordinates are in base field b)
  proofLr :: Proof g f -> Array { l :: AffinePoint b, r :: AffinePoint b }
  proofDelta :: Proof g f -> AffinePoint b
  proofZ1 :: Proof g f -> f
  proofZ2 :: Proof g f -> f
  proofSg :: Proof g f -> AffinePoint b
  proverIndexH :: ProverIndex g f -> AffinePoint b
  proofIpaRounds :: Proof g f -> Int
  -- Bullet reduction product: lr_prod = sum(chal_inv[i] * L[i] + chal[i] * R[i])
  proofLrProd :: ProverIndex g f -> { proof :: Proof g f, publicInput :: Array f } -> AffinePoint b

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

foreign import pallasProofOracles :: ProverIndex Vesta.G Pallas.BaseField -> { proof :: Proof Vesta.G Pallas.BaseField, publicInput :: Array Pallas.BaseField } -> OraclesResult Pallas.BaseField
foreign import vestaProofOracles :: ProverIndex Pallas.G Vesta.BaseField -> { proof :: Proof Pallas.G Vesta.BaseField, publicInput :: Array Vesta.BaseField } -> OraclesResult Vesta.BaseField

foreign import pallasProofBulletproofChallenges :: ProverIndex Vesta.G Pallas.BaseField -> { proof :: Proof Vesta.G Pallas.BaseField, publicInput :: Array Pallas.BaseField } -> Array Pallas.BaseField
foreign import vestaProofBulletproofChallenges :: ProverIndex Pallas.G Vesta.BaseField -> { proof :: Proof Pallas.G Vesta.BaseField, publicInput :: Array Vesta.BaseField } -> Array Vesta.BaseField

foreign import pallasProofSpongeCheckpoint :: ProverIndex Vesta.G Pallas.BaseField -> { proof :: Proof Vesta.G Pallas.BaseField, publicInput :: Array Pallas.BaseField } -> Pallas.BaseField
foreign import vestaProofSpongeCheckpoint :: ProverIndex Pallas.G Vesta.BaseField -> { proof :: Proof Pallas.G Vesta.BaseField, publicInput :: Array Vesta.BaseField } -> Vesta.BaseField

foreign import pallasVerifyOpeningProof :: ProverIndex Vesta.G Pallas.BaseField -> { proof :: Proof Vesta.G Pallas.BaseField, publicInput :: Array Pallas.BaseField } -> Boolean
foreign import vestaVerifyOpeningProof :: ProverIndex Pallas.G Vesta.BaseField -> { proof :: Proof Pallas.G Vesta.BaseField, publicInput :: Array Vesta.BaseField } -> Boolean

foreign import pallasPermutationVanishingPolynomial :: { domainLog2 :: Int, zkRows :: Int, pt :: Pallas.BaseField } -> Pallas.BaseField
foreign import vestaPermutationVanishingPolynomial :: { domainLog2 :: Int, zkRows :: Int, pt :: Vesta.BaseField } -> Vesta.BaseField

foreign import pallasDomainGenerator :: Int -> Pallas.BaseField
foreign import vestaDomainGenerator :: Int -> Vesta.BaseField

foreign import pallasComputeB0 :: { challenges :: Array Pallas.BaseField, zeta :: Pallas.BaseField, zetaOmega :: Pallas.BaseField, evalscale :: Pallas.BaseField } -> Pallas.BaseField
foreign import vestaComputeB0 :: { challenges :: Array Vesta.BaseField, zeta :: Vesta.BaseField, zetaOmega :: Vesta.BaseField, evalscale :: Vesta.BaseField } -> Vesta.BaseField

-- Opening proof L/R pairs (coordinates in curve's base field)
foreign import pallasProofLr :: Proof Vesta.G Pallas.BaseField -> Array { l :: AffinePoint Vesta.BaseField, r :: AffinePoint Vesta.BaseField }
foreign import vestaProofLr :: Proof Pallas.G Vesta.BaseField -> Array { l :: AffinePoint Pallas.BaseField, r :: AffinePoint Pallas.BaseField }

-- Opening proof delta commitment
foreign import pallasProofDelta :: Proof Vesta.G Pallas.BaseField -> AffinePoint Vesta.BaseField
foreign import vestaProofDelta :: Proof Pallas.G Vesta.BaseField -> AffinePoint Pallas.BaseField

-- Opening proof z1 scalar
foreign import pallasProofZ1 :: Proof Vesta.G Pallas.BaseField -> Pallas.BaseField
foreign import vestaProofZ1 :: Proof Pallas.G Vesta.BaseField -> Vesta.BaseField

-- Opening proof z2 scalar
foreign import pallasProofZ2 :: Proof Vesta.G Pallas.BaseField -> Pallas.BaseField
foreign import vestaProofZ2 :: Proof Pallas.G Vesta.BaseField -> Vesta.BaseField

-- Opening proof sg commitment
foreign import pallasProofSg :: Proof Vesta.G Pallas.BaseField -> AffinePoint Vesta.BaseField
foreign import vestaProofSg :: Proof Pallas.G Vesta.BaseField -> AffinePoint Pallas.BaseField

-- Prover index H generator
foreign import pallasProverIndexH :: ProverIndex Vesta.G Pallas.BaseField -> AffinePoint Vesta.BaseField
foreign import vestaProverIndexH :: ProverIndex Pallas.G Vesta.BaseField -> AffinePoint Pallas.BaseField

-- Proof IPA rounds (domain log2)
foreign import pallasProofIpaRounds :: Proof Vesta.G Pallas.BaseField -> Int
foreign import vestaProofIpaRounds :: Proof Pallas.G Vesta.BaseField -> Int

-- Bullet reduction product lr_prod (coordinates in curve's base field)
foreign import pallasProofLrProd :: ProverIndex Vesta.G Pallas.BaseField -> { proof :: Proof Vesta.G Pallas.BaseField, publicInput :: Array Pallas.BaseField } -> AffinePoint Vesta.BaseField
foreign import vestaProofLrProd :: ProverIndex Pallas.G Vesta.BaseField -> { proof :: Proof Pallas.G Vesta.BaseField, publicInput :: Array Vesta.BaseField } -> AffinePoint Pallas.BaseField

--------------------------------------------------------------------------------
-- Instances
--------------------------------------------------------------------------------

instance ProofFFI Pallas.BaseField Vesta.G Vesta.BaseField where
  proverIndexShifts = pallasProverIndexShifts
  createProof = pallasCreateProof
  proofWitnessEvals = pallasProofWitnessEvals
  proofZEvals = pallasProofZEvals
  proofSigmaEvals = pallasProofSigmaEvals
  proofCoefficientEvals = pallasProofCoefficientEvals
  proofOracles = pallasProofOracles
  proofBulletproofChallenges = pallasProofBulletproofChallenges
  proofSpongeCheckpoint = pallasProofSpongeCheckpoint
  verifyOpeningProof = pallasVerifyOpeningProof
  permutationVanishingPolynomial = pallasPermutationVanishingPolynomial
  domainGenerator = pallasDomainGenerator
  computeB0 = pallasComputeB0
  proofLr = pallasProofLr
  proofDelta = pallasProofDelta
  proofZ1 = pallasProofZ1
  proofZ2 = pallasProofZ2
  proofSg = pallasProofSg
  proverIndexH = pallasProverIndexH
  proofIpaRounds = pallasProofIpaRounds
  proofLrProd = pallasProofLrProd

instance ProofFFI Vesta.BaseField Pallas.G Pallas.BaseField where
  proverIndexShifts = vestaProverIndexShifts
  createProof = vestaCreateProof
  proofWitnessEvals = vestaProofWitnessEvals
  proofZEvals = vestaProofZEvals
  proofSigmaEvals = vestaProofSigmaEvals
  proofCoefficientEvals = vestaProofCoefficientEvals
  proofOracles = vestaProofOracles
  proofBulletproofChallenges = vestaProofBulletproofChallenges
  proofSpongeCheckpoint = vestaProofSpongeCheckpoint
  verifyOpeningProof = vestaVerifyOpeningProof
  permutationVanishingPolynomial = vestaPermutationVanishingPolynomial
  domainGenerator = vestaDomainGenerator
  computeB0 = vestaComputeB0
  proofLr = vestaProofLr
  proofDelta = vestaProofDelta
  proofZ1 = vestaProofZ1
  proofZ2 = vestaProofZ2
  proofSg = vestaProofSg
  proverIndexH = vestaProverIndexH
  proofIpaRounds = vestaProofIpaRounds
  proofLrProd = vestaProofLrProd
