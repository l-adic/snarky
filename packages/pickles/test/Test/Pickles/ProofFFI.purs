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
  , proofSg
  , bPolyCoefficients
  , polyLength
  , polyGetCoeffs
  , verifyDeferredCheck
  , pallasVerifyDeferredCheckInternal
  , Proof
  , Polynomial
  , OraclesResult
  , PointEval
  , SgPoint
  ) where

import Data.Vector (Vector)
import Snarky.Backend.Kimchi.Types (ProverIndex)
import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Vesta as Vesta

-- | Opaque proof type, parameterized by curve group and scalar field.
foreign import data Proof :: Type -> Type -> Type

-- | Opaque polynomial type for IPA deferred verification.
-- | The coefficients are in the circuit field f.
foreign import data Polynomial :: Type -> Type

-- | Polynomial evaluation at two points: zeta and zeta*omega
type PointEval f = { zeta :: f, omegaTimesZeta :: f }

-- | sg commitment point coordinates.
-- | The coordinates are in the commitment curve's base field (b),
-- | which is the "other" base field in the Pasta cycle.
type SgPoint b = { x :: b, y :: b }

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
-- | `f` is the circuit field (scalar field of the circuit), `g` is the commitment curve group.
-- | `b` is the commitment curve's base field (the "other" base field in Pasta cycle).
-- | For Pallas (Fq circuits): f = Pallas.BaseField, g = Vesta.G, b = Vesta.BaseField
-- | For Vesta (Fp circuits): f = Vesta.BaseField, g = Pallas.G, b = Pallas.BaseField
class ProofFFI f g b | f -> g, f -> b where
  proverIndexShifts :: ProverIndex g f -> Vector 7 f
  createProof :: { proverIndex :: ProverIndex g f, witness :: Vector 15 (Array f) } -> Proof g f
  proofWitnessEvals :: Proof g f -> Vector 15 (PointEval f)
  proofZEvals :: Proof g f -> PointEval f
  proofSigmaEvals :: Proof g f -> Vector 6 (PointEval f)
  proofCoefficientEvals :: Proof g f -> Vector 15 (PointEval f)
  proofOracles :: ProverIndex g f -> { proof :: Proof g f, publicInput :: Array f } -> OraclesResult f
  proofBulletproofChallenges :: ProverIndex g f -> { proof :: Proof g f, publicInput :: Array f } -> Array f
  verifyOpeningProof :: ProverIndex g f -> { proof :: Proof g f, publicInput :: Array f } -> Boolean
  permutationVanishingPolynomial :: { domainLog2 :: Int, zkRows :: Int, pt :: f } -> f
  domainGenerator :: Int -> f
  computeB0 :: { challenges :: Array f, zeta :: f, zetaOmega :: f, evalscale :: f } -> f
  proofIpaRounds :: Proof g f -> Int
  -- | Extract sg commitment coordinates from a proof.
  -- | The coordinates are in the commitment curve's base field (b).
  proofSg :: Proof g f -> SgPoint b
  -- | Create b_poly_coefficients polynomial from IPA challenges.
  bPolyCoefficients :: Array f -> Polynomial f
  -- | Get the number of coefficients in a polynomial.
  polyLength :: Polynomial f -> Int
  -- | Get the coefficients from a polynomial.
  polyGetCoeffs :: Polynomial f -> Array f
  -- | Verify the deferred sg commitment check.
  -- | Checks that sg = MSM(SRS.g, poly.coeffs).
  verifyDeferredCheck :: ProverIndex g f -> { sgX :: b, sgY :: b, poly :: Polynomial f } -> Boolean

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

foreign import pallasVerifyOpeningProof :: ProverIndex Vesta.G Pallas.BaseField -> { proof :: Proof Vesta.G Pallas.BaseField, publicInput :: Array Pallas.BaseField } -> Boolean
foreign import vestaVerifyOpeningProof :: ProverIndex Pallas.G Vesta.BaseField -> { proof :: Proof Pallas.G Vesta.BaseField, publicInput :: Array Vesta.BaseField } -> Boolean

foreign import pallasPermutationVanishingPolynomial :: { domainLog2 :: Int, zkRows :: Int, pt :: Pallas.BaseField } -> Pallas.BaseField
foreign import vestaPermutationVanishingPolynomial :: { domainLog2 :: Int, zkRows :: Int, pt :: Vesta.BaseField } -> Vesta.BaseField

foreign import pallasDomainGenerator :: Int -> Pallas.BaseField
foreign import vestaDomainGenerator :: Int -> Vesta.BaseField

foreign import pallasComputeB0 :: { challenges :: Array Pallas.BaseField, zeta :: Pallas.BaseField, zetaOmega :: Pallas.BaseField, evalscale :: Pallas.BaseField } -> Pallas.BaseField
foreign import vestaComputeB0 :: { challenges :: Array Vesta.BaseField, zeta :: Vesta.BaseField, zetaOmega :: Vesta.BaseField, evalscale :: Vesta.BaseField } -> Vesta.BaseField

foreign import pallasProofIpaRounds :: Proof Vesta.G Pallas.BaseField -> Int
foreign import vestaProofIpaRounds :: Proof Pallas.G Vesta.BaseField -> Int

-- sg commitment extraction (coordinates in the commitment curve's base field)
foreign import pallasProofSg :: Proof Vesta.G Pallas.BaseField -> SgPoint Vesta.BaseField
foreign import vestaProofSg :: Proof Pallas.G Vesta.BaseField -> SgPoint Pallas.BaseField

-- Polynomial / deferred check FFI
foreign import pallasBPolyCoefficients :: Array Pallas.BaseField -> Polynomial Pallas.BaseField
foreign import vestaBPolyCoefficients :: Array Vesta.BaseField -> Polynomial Vesta.BaseField

foreign import pallasPolyLength :: Polynomial Pallas.BaseField -> Int
foreign import vestaPolyLength :: Polynomial Vesta.BaseField -> Int

foreign import pallasPolyGetCoeffs :: Polynomial Pallas.BaseField -> Array Pallas.BaseField
foreign import vestaPolyGetCoeffs :: Polynomial Vesta.BaseField -> Array Vesta.BaseField

foreign import pallasVerifyDeferredCheck :: ProverIndex Vesta.G Pallas.BaseField -> { sgX :: Vesta.BaseField, sgY :: Vesta.BaseField, poly :: Polynomial Pallas.BaseField } -> Boolean
foreign import vestaVerifyDeferredCheck :: ProverIndex Pallas.G Vesta.BaseField -> { sgX :: Pallas.BaseField, sgY :: Pallas.BaseField, poly :: Polynomial Vesta.BaseField } -> Boolean

-- Internal check (entirely in Rust) for debugging
foreign import pallasVerifyDeferredCheckInternal :: ProverIndex Vesta.G Pallas.BaseField -> { proof :: Proof Vesta.G Pallas.BaseField, publicInput :: Array Pallas.BaseField } -> Boolean

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
  verifyOpeningProof = pallasVerifyOpeningProof
  permutationVanishingPolynomial = pallasPermutationVanishingPolynomial
  domainGenerator = pallasDomainGenerator
  computeB0 = pallasComputeB0
  proofIpaRounds = pallasProofIpaRounds
  proofSg = pallasProofSg
  bPolyCoefficients = pallasBPolyCoefficients
  polyLength = pallasPolyLength
  polyGetCoeffs = pallasPolyGetCoeffs
  verifyDeferredCheck = pallasVerifyDeferredCheck

instance ProofFFI Vesta.BaseField Pallas.G Pallas.BaseField where
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
  proofSg = vestaProofSg
  bPolyCoefficients = vestaBPolyCoefficients
  polyLength = vestaPolyLength
  polyGetCoeffs = vestaPolyGetCoeffs
  verifyDeferredCheck = vestaVerifyDeferredCheck
