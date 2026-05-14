-- | FFI bindings for proof creation, oracle computation, and other
-- | kimchi proof-systems operations.
-- |
-- | This module was originally `Test.Pickles.ProofFFI` — lifted into
-- | `packages/pickles/src/` so the prover library (`Pickles.Prove.*`)
-- | can consume `proofOracles`, `createProof`, etc. directly.
module Pickles.ProofFFI
  ( class ProofFFI
  , proverIndexShifts
  , createProof
  , pallasCreateProofWithPrev
  , vestaCreateProofWithPrev
  , proofWitnessEvals
  , proofZEvals
  , proofSigmaEvals
  , proofCoefficientEvals
  , proofIndexEvals
  , proofOracles
  , proofBulletproofChallenges
  , verifyOpeningProof
  , computeB0
  , permutationVanishingPolynomial
  , domainGenerator
  , proofIpaRounds
  -- Functions not in typeclass (use different field than circuit field f)
  , pallasProofOracles
  , vestaProofOracles
  , pallasProofOpeningLr
  , vestaProofOpeningLr
  , pallasProofOpeningDelta
  , vestaProofOpeningDelta
  , pallasProofOpeningSg
  , vestaProofOpeningSg
  , pallasProofOpeningZ1
  , vestaProofOpeningZ1
  , pallasProofOpeningZ2
  , vestaProofOpeningZ2
  , pallasProofOpeningPrechallenges
  , vestaProofOpeningPrechallenges
  , pallasProverIndexDomainLog2
  , pallasProofFtEval1
  , vestaProofFtEval1
  , vestaVerifierIndexDigest
  , pallasSrsLagrangeCommitmentAt
  , vestaSrsLagrangeCommitmentAt
  , pallasSrsLagrangeCommitmentChunksAt
  , vestaSrsLagrangeCommitmentChunksAt
  , pallasSrsBlindingGenerator
  , vestaSrsBlindingGenerator
  , pallasProofCommitments
  , vestaProofCommitments
  , pallasSigmaCommLast
  , vestaSigmaCommLast
  , pallasVerifierIndexColumnComms
  , vestaVerifierIndexColumnComms
  , vestaChallengePolyCommitment
  , vestaMakeWireProof
  , Dehydrated(..)
  , ProofCommitments
  , Proof
  , OraclesResult
  , PointEval
  , firstChunk
  , SpongeCheckpoint
  , LrPair
  -- Typed wrappers: length-checked at the FFI boundary
  , VerifierIndexCommitments
  , pallasVerifierIndexCommitments
  , vestaVerifierIndexCommitments
  , pallasProofOpeningPrechallengesVec
  , vestaProofOpeningPrechallengesVec
  , pallasProofOpeningLrVec
  , vestaProofOpeningLrVec
  , tCommVec
  , tCommChunked
  , wCommChunked
  , zCommChunked
  ) where

import Prelude

import Data.Array as Array
import Data.Array.NonEmpty (NonEmptyArray)
import Data.Array.NonEmpty as NonEmptyArray
import Data.Reflectable (class Reflectable, reflectType)
import Data.Vector (Vector)
import Data.Vector as Vector
import Pickles.Types (ChunkedCommitment(..), StepIPARounds, WrapIPARounds)
import Pickles.Util.Fatal (fromJust')
import Snarky.Backend.Kimchi.Types (CRS, ProverIndex, VerifierIndex)
import Snarky.Circuit.DSL (SizedF)
import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Vesta as Vesta
import Snarky.Data.EllipticCurve (AffinePoint)
import Type.Proxy (Proxy(..))

-- | Opaque proof type, parameterized by curve group and scalar field.
foreign import data Proof :: Type -> Type -> Type

-- | Polynomial evaluation at two points: zeta and zeta*omega.
type PointEval f = { zeta :: f, omegaTimesZeta :: f }

-- | Extract the first chunk from a chunked-eval array. Total because
-- | kimchi always emits at least one chunk per polynomial (witnessed
-- | by the `NonEmptyArray` type — the conversion from the JS-returned
-- | array happens in the FFI shim, validated to be non-empty there).
-- |
-- | At `num_chunks = 1` this is the only chunk; at `n > 1` it silently
-- | drops chunks > 0 (chunk-blind, must be replaced by
-- | `actualEvaluation` Horner-combine in Phase 2 / 3 of chunking.md).
-- |
-- | See `docs/chunking-ffi-audit.md`.
firstChunk :: forall f. NonEmptyArray (PointEval f) -> PointEval f
firstChunk = NonEmptyArray.head

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
  -- | Chunked public-input evaluations at zeta / zeta*omega.
  -- | `NonEmptyArray` of length `num_chunks` (≥1 by construction);
  -- | use `firstChunk` to get the n=1 single-PointEval view.
  , publicEvals :: NonEmptyArray (PointEval f)
  , fqDigest :: f -- Fq-sponge digest before Fr-sponge (for xi derivation)
  , alphaChal :: SizedF 128 f -- raw 128-bit alpha challenge (pre-endo-expansion)
  , zetaChal :: SizedF 128 f -- raw 128-bit zeta challenge (pre-endo-expansion)
  , vChal :: SizedF 128 f -- raw 128-bit polyscale challenge (pre-endo-expansion)
  , uChal :: SizedF 128 f -- raw 128-bit evalscale challenge (pre-endo-expansion)
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
  proofWitnessEvals :: Proof g f -> Vector 15 (NonEmptyArray (PointEval f))
  proofZEvals :: Proof g f -> NonEmptyArray (PointEval f)
  proofSigmaEvals :: Proof g f -> Vector 6 (NonEmptyArray (PointEval f))
  proofCoefficientEvals :: Proof g f -> Vector 15 (NonEmptyArray (PointEval f))
  proofIndexEvals :: Proof g f -> Vector 6 (NonEmptyArray (PointEval f))
  -- | Non-recursive variant of `{pallas,vesta}ProofOracles` — passes
  -- | `prevChallenges: []` behind the scenes. Use this from
  -- | curve-polymorphic code that only handles standalone proofs (e.g.
  -- | the test harness). For recursive proofs, call the direct
  -- | `pallasProofOracles` / `vestaProofOracles` foreign imports with
  -- | the real `prevChallenges` list — the class method can't express
  -- | them polymorphically because the sg-coord field type differs per
  -- | curve instance.
  proofOracles :: VerifierIndex g f -> { proof :: Proof g f, publicInput :: Array f } -> OraclesResult f
  -- | Raw 128-bit scalar challenges from the IPA round loop
  -- | (`O.opening_prechallenges` in OCaml). Each field element embeds
  -- | a 128-bit value pre-endo-expansion; consumers feed them through
  -- | `Scalar_challenge.to_field` to recover full-field bulletproof
  -- | challenges.
  -- NOTE: `proofOpeningPrechallenges` is not a class method —
  -- `prevChallenges`'s `sgX`/`sgY` type depends on the curve's
  -- BaseField (not the scalar field `f`), which can't be expressed
  -- through the existing fundep. Use `pallasProofOpeningPrechallenges`
  -- / `vestaProofOpeningPrechallenges` directly.
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

foreign import pallasCreateProofWithPrev
  :: { proverIndex :: ProverIndex Vesta.G Pallas.BaseField
     , witness :: Vector 15 (Array Pallas.BaseField)
     , prevChallenges ::
         Array
           { sgX :: Pallas.ScalarField
           , sgY :: Pallas.ScalarField
           , challenges :: Array Pallas.BaseField
           }
     }
  -> Proof Vesta.G Pallas.BaseField

foreign import vestaCreateProofWithPrev
  :: { proverIndex :: ProverIndex Pallas.G Vesta.BaseField
     , witness :: Vector 15 (Array Vesta.BaseField)
     , prevChallenges ::
         Array
           { sgX :: Vesta.ScalarField
           , sgY :: Vesta.ScalarField
           , challenges :: Array Vesta.BaseField
           }
     }
  -> Proof Pallas.G Vesta.BaseField

foreign import pallasProofWitnessEvals :: Proof Vesta.G Pallas.BaseField -> Vector 15 (NonEmptyArray (PointEval Pallas.BaseField))
foreign import vestaProofWitnessEvals :: Proof Pallas.G Vesta.BaseField -> Vector 15 (NonEmptyArray (PointEval Vesta.BaseField))

foreign import pallasProofZEvals :: Proof Vesta.G Pallas.BaseField -> NonEmptyArray (PointEval Pallas.BaseField)
foreign import vestaProofZEvals :: Proof Pallas.G Vesta.BaseField -> NonEmptyArray (PointEval Vesta.BaseField)

-- | Direct accessor for `proof.ft_eval1` — the prover-supplied
-- | evaluation of the linearization polynomial at `zeta·omega`.
-- |
-- | Kimchi's verifier does not recompute `ft_eval1`; it reads this
-- | value directly from the proof and uses it as one of the openings
-- | in the CIP check. Use this in place of `oraclesResult.ftEval1` to
-- | avoid the redundant kimchi-FS-replay round trip for what is, at
-- | the end of the day, a single field projection.
foreign import pallasProofFtEval1 :: Proof Vesta.G Pallas.BaseField -> Pallas.BaseField
foreign import vestaProofFtEval1 :: Proof Pallas.G Vesta.BaseField -> Vesta.BaseField

foreign import pallasProofSigmaEvals :: Proof Vesta.G Pallas.BaseField -> Vector 6 (NonEmptyArray (PointEval Pallas.BaseField))
foreign import vestaProofSigmaEvals :: Proof Pallas.G Vesta.BaseField -> Vector 6 (NonEmptyArray (PointEval Vesta.BaseField))

foreign import pallasProofCoefficientEvals :: Proof Vesta.G Pallas.BaseField -> Vector 15 (NonEmptyArray (PointEval Pallas.BaseField))
foreign import vestaProofCoefficientEvals :: Proof Pallas.G Vesta.BaseField -> Vector 15 (NonEmptyArray (PointEval Vesta.BaseField))

foreign import pallasProofIndexEvals :: Proof Vesta.G Pallas.BaseField -> Vector 6 (NonEmptyArray (PointEval Pallas.BaseField))
foreign import vestaProofIndexEvals :: Proof Pallas.G Vesta.BaseField -> Vector 6 (NonEmptyArray (PointEval Vesta.BaseField))

-- | `prevChallenges` carries the recursive `Challenge_polynomial.t`
-- | data that kimchi's Fiat-Shamir transcript absorbs before the
-- | current proof's commitments. Each entry has the prior proof's
-- | `sg` commitment (a single curve point) and its **expanded**
-- | bulletproof challenges in the current proof's scalar field.
-- | Non-recursive callers pass `[]`.
-- |
-- | For `pallasProofOracles` (Vesta-committed proofs = step proofs):
-- | the commitment is a Vesta point with coordinates in the Vesta
-- | base field (`Pallas.ScalarField`), and the challenges are in the
-- | Vesta scalar field (`Pallas.BaseField`).
foreign import pallasProofOracles
  :: VerifierIndex Vesta.G Pallas.BaseField
  -> { proof :: Proof Vesta.G Pallas.BaseField
     , publicInput :: Array Pallas.BaseField
     , prevChallenges ::
         Array
           { sgX :: Pallas.ScalarField
           , sgY :: Pallas.ScalarField
           , challenges :: Array Pallas.BaseField
           }
     }
  -> OraclesResult Pallas.BaseField

-- | For `vestaProofOracles` (Pallas-committed proofs = wrap proofs):
-- | the commitment is a Pallas point with coordinates in the Pallas
-- | base field (`Vesta.ScalarField`), and the challenges are in the
-- | Pallas scalar field (`Vesta.BaseField`).
foreign import vestaProofOracles
  :: VerifierIndex Pallas.G Vesta.BaseField
  -> { proof :: Proof Pallas.G Vesta.BaseField
     , publicInput :: Array Vesta.BaseField
     , prevChallenges ::
         Array
           { sgX :: Vesta.ScalarField
           , sgY :: Vesta.ScalarField
           , challenges :: Array Vesta.BaseField
           }
     }
  -> OraclesResult Vesta.BaseField

-- | Construct a Pallas-committed `Proof` (wrap proof) from flat component
-- | data. PureScript analog of OCaml `Wrap_wire_proof.to_kimchi_proof`
-- | (wrap_wire_proof.ml:202-210), used by `Pickles.Proof.Dummy` to build
-- | the PS equivalent of `Proof.dummy` (proof.ml:115-208).
-- |
-- | Field layout (all non-chunked, WrapIPARounds = 15):
-- | - `wComm`: 30 Fp coords = 15 × (x,y)   (Pallas base field = Vesta.ScalarField)
-- | - `zComm`: 2 Fp coords = 1 point
-- | - `tComm`: 14 Fp coords = 7 quotient-poly chunks
-- | - `lr`: 60 Fp coords = 15 × (l.x, l.y, r.x, r.y)
-- | - `delta`, `sg`: 2 Fp coords each
-- | - `z1`, `z2`, `ftEval1`: Fq scalars (Pallas scalar field = Vesta.BaseField)
-- | - `evals`: 88 Fq scalars = 44 × (zeta, zetaOmega) in the OCaml order:
-- |     `w[15] | coefficients[15] | z | s[6] | generic_selector
-- |      | poseidon_selector | complete_add_selector | mul_selector
-- |      | emul_selector | endomul_scalar_selector`
foreign import vestaMakeWireProof
  :: { wComm :: Array Vesta.ScalarField
     , zComm :: Array Vesta.ScalarField
     , tComm :: Array Vesta.ScalarField
     , lr :: Array Vesta.ScalarField
     , delta :: Array Vesta.ScalarField
     , sg :: Array Vesta.ScalarField
     , z1 :: Pallas.ScalarField
     , z2 :: Pallas.ScalarField
     , evals :: Array Pallas.ScalarField
     , ftEval1 :: Pallas.ScalarField
     }
  -> Proof Pallas.G Vesta.BaseField

-- | Tag marking a freshly-deserialized kimchi value (currently used only
-- | for `VerifierIndex` — see `Pickles.Sideload.FFI`) whose runtime
-- | needs further setup before use. Same runtime rep as the underlying
-- | value; the wrapper exists only as a type-level forcing function so
-- | callers must go through the matching `*HydrateX` step before passing
-- | the value to verify.
newtype Dehydrated a = Dehydrated a

foreign import pallasProofBulletproofChallenges :: VerifierIndex Vesta.G Pallas.BaseField -> { proof :: Proof Vesta.G Pallas.BaseField, publicInput :: Array Pallas.BaseField } -> Array Pallas.BaseField
foreign import vestaProofBulletproofChallenges :: VerifierIndex Pallas.G Vesta.BaseField -> { proof :: Proof Pallas.G Vesta.BaseField, publicInput :: Array Vesta.BaseField } -> Array Vesta.BaseField

foreign import pallasProofOpeningPrechallenges
  :: VerifierIndex Vesta.G Pallas.BaseField
  -> { proof :: Proof Vesta.G Pallas.BaseField
     , publicInput :: Array Pallas.BaseField
     , prevChallenges ::
         Array
           { sgX :: Pallas.ScalarField
           , sgY :: Pallas.ScalarField
           , challenges :: Array Pallas.BaseField
           }
     }
  -> Array Pallas.BaseField

foreign import vestaProofOpeningPrechallenges
  :: VerifierIndex Pallas.G Vesta.BaseField
  -> { proof :: Proof Pallas.G Vesta.BaseField
     , publicInput :: Array Vesta.BaseField
     , prevChallenges ::
         Array
           { sgX :: Vesta.ScalarField
           , sgY :: Vesta.ScalarField
           , challenges :: Array Vesta.BaseField
           }
     }
  -> Array Vesta.BaseField

foreign import pallasVerifyOpeningProof :: VerifierIndex Vesta.G Pallas.BaseField -> { proof :: Proof Vesta.G Pallas.BaseField, publicInput :: Array Pallas.BaseField } -> Boolean
foreign import vestaVerifyOpeningProof :: VerifierIndex Pallas.G Vesta.BaseField -> { proof :: Proof Pallas.G Vesta.BaseField, publicInput :: Array Vesta.BaseField } -> Boolean

-- NOTE: `u_t` is the sponge output AFTER absorbing shifted CIP and BEFORE
-- `group_map`. It is squeezed in the commitment curve's BASE field (=
-- the OTHER scalar field in the 2-cycle): for a Vesta proof it's Fq =
-- `Pallas.ScalarField`; for a Pallas proof it's Fp = `Vesta.ScalarField`.
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
-- Note: L/R coordinates are in the commitment curve's base field (the "other" field in the 2-cycle)
-- For Pallas circuits using Vesta commitments: Vesta.BaseField = Pallas.ScalarField
-- For Vesta circuits using Pallas commitments: Pallas.BaseField = Vesta.ScalarField
foreign import pallasProofOpeningLr :: Proof Vesta.G Pallas.BaseField -> Array (LrPair Pallas.ScalarField)
foreign import vestaProofOpeningLr :: Proof Pallas.G Vesta.BaseField -> Array (LrPair Vesta.ScalarField)

-- lr_prod: the curve point sum from bullet_reduce
-- lr_prod = Σ_i [chal_inv[i] * L_i + chal[i] * R_i]
-- Returns the coordinates of the result point in the commitment curve's base field
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
-- Combined polynomial commitment (coordinates in commitment curve's base field)
-- This is the batched commitment: sum_i polyscale^i * C_i
-- Debug verification: prints intermediate IPA values to stderr
-- Max polynomial size from verifier index
-- | Domain log2 size from a prover index. This is the `log_size_of_group` of
-- | the `d1` evaluation domain, i.e. the kimchi compile domain — what
-- | `Fix_domains.domains` returned for the circuit that was compiled.
-- |
-- | For step-circuit prover indices (Vesta commitments, Pallas.BaseField = Fp),
-- | use `pallasProverIndexDomainLog2`. For wrap-circuit prover indices
-- | (Pallas commitments, Vesta.BaseField = Fq), use `vestaProverIndexDomainLog2`.
foreign import pallasProverIndexDomainLog2 :: ProverIndex Vesta.G Pallas.BaseField -> Int
-- Fq-sponge transcript helpers
-- VK digest: returns Fq element (Pallas.ScalarField)
-- Public input polynomial commitment: returns array of {x, y} points in Fq (one per chunk)
-- Lagrange commitment points from SRS (constant bases for public input MSM)
-- Lagrange commitments directly from SRS (no verifier index needed)
-- | Fetch a single lagrange commitment by index from an SRS. PureScript
-- | analog of OCaml `Kimchi_bindings.Protocol.SRS.Fq.lagrange_commitment`
-- | (used in `step_verifier.ml:360-368`). Kimchi caches the full basis on
-- | first access, so per-index calls are O(1) after warmup. Lets callers
-- | avoid pre-sizing a `numPublic` buffer.
-- | Returns the FIRST chunk of the `i`-th lagrange commitment. For nc=1
-- | domains (everything except chunks2) this is the only chunk. For chunked
-- | domains use `pallasSrsLagrangeCommitmentChunksAt` instead.
foreign import pallasSrsLagrangeCommitmentAt
  :: CRS Vesta.G -> Int -> Int -> AffinePoint Pallas.ScalarField

foreign import vestaSrsLagrangeCommitmentAt
  :: CRS Pallas.G -> Int -> Int -> AffinePoint Vesta.ScalarField

-- | Returns ALL chunks of the `i`-th lagrange commitment as an `Array` of
-- | points. For domains ≤ SRS max_poly_size the array has length 1; for
-- | chunked domains (e.g. step domain > wrap SRS depth at chunks2) it has
-- | length `ceil(domain_size / max_poly_size)`. Callers reshape into a
-- | `Vector numChunks (AffinePoint)` at the use site. Mirrors OCaml's
-- | `lagrange_commitment srs d i .unshifted` array (`wrap_verifier.ml:336`).
foreign import pallasSrsLagrangeCommitmentChunksAt
  :: CRS Vesta.G -> Int -> Int -> Array (AffinePoint Pallas.ScalarField)

foreign import vestaSrsLagrangeCommitmentChunksAt
  :: CRS Pallas.G -> Int -> Int -> Array (AffinePoint Vesta.ScalarField)

-- Blinding generator H directly from SRS
foreign import pallasSrsBlindingGenerator :: CRS Vesta.G -> AffinePoint Pallas.ScalarField
foreign import vestaSrsBlindingGenerator :: CRS Pallas.G -> AffinePoint Vesta.ScalarField

-- sigma_comm[PERMUTS-1] (the last sigma commitment), ALL chunks.
-- The raw inner Array length = num_chunks (1 for nc=1 callers, 2+ when
-- chunked). FFI doesn't know `numChunks` at the type level; consumers
-- project to `Vector numChunks` via `verifierIndexCommitments`.
foreign import pallasSigmaCommLast :: VerifierIndex Vesta.G Pallas.BaseField -> Array (AffinePoint Pallas.ScalarField)

-- VK column commitments: 27 commitments (6 index + 15 coefficient + 6
-- sigma) in to_batch order, each entry an Array of chunk points
-- (length = num_chunks). The total flat byte count returned by the
-- Rust FFI is `27 * num_chunks * 2` field elements, reshaped here.
-- The outer 27 is checked via `Vector.toVector @6 / @15 / @6` at the
-- typed wrapper.
foreign import pallasVerifierIndexColumnComms :: VerifierIndex Vesta.G Pallas.BaseField -> Array (Array (AffinePoint Pallas.ScalarField))
foreign import vestaVerifierIndexColumnComms :: VerifierIndex Pallas.G Vesta.BaseField -> Array (Array (AffinePoint Vesta.ScalarField))

-- Challenge polynomial commitment: MSM of b_poly_coefficients against SRS
-- Challenges are in the commitment curve's scalar field (= circuit field)
-- Returns point coordinates in the commitment curve's base field
foreign import vestaChallengePolyCommitment :: VerifierIndex Pallas.G Vesta.BaseField -> Array Vesta.BaseField -> AffinePoint Vesta.ScalarField

-- | Proof commitments structured for Fq-sponge absorption.
-- |
-- | Each polynomial's commitment is a chunked group of points: at
-- | `num_chunks = 1` every inner `Array` has length 1. The PS-side FFI
-- | leaves these as plain `Array`s because num_chunks is decided by the
-- | prover/SRS at runtime and is not known at the type level here; use
-- | `wCommChunked`/`zCommChunked` to project into typed `Vector numChunks`
-- | at consumer sites that know the value statically.
type ProofCommitments f =
  { wComm :: Vector 15 (Array (AffinePoint f))
  , zComm :: Array (AffinePoint f)
  , tComm :: Array (AffinePoint f)
  }

-- Proof commitments: 15 w-poly chunked commitments + z-poly chunked
-- commitment + t-poly's `7 * num_chunks` flat pieces in Fq.
foreign import pallasProofCommitments :: Proof Vesta.G Pallas.BaseField -> ProofCommitments Pallas.ScalarField

-- Proof commitments from a Pallas proof (Vesta/Fq circuits)
foreign import vestaProofCommitments :: Proof Pallas.G Vesta.BaseField -> ProofCommitments Vesta.ScalarField

-- sigma_comm[PERMUTS-1] (the last sigma commitment) for Vesta/Fq
-- verifier indices, returned chunk-aware (inner Array length = num_chunks).
-- See note on `pallasSigmaCommLast`.
foreign import vestaSigmaCommLast :: VerifierIndex Pallas.G Vesta.BaseField -> Array (AffinePoint Vesta.ScalarField)

-- Verifier index digest for Vesta/Fq circuits (returns Fp element)
foreign import vestaVerifierIndexDigest :: VerifierIndex Pallas.G Vesta.BaseField -> Vesta.ScalarField

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
  proofIndexEvals = pallasProofIndexEvals
  proofOracles vk { proof, publicInput } =
    pallasProofOracles vk { proof, publicInput, prevChallenges: [] }
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
  proofIndexEvals = vestaProofIndexEvals
  proofOracles vk { proof, publicInput } =
    vestaProofOracles vk { proof, publicInput, prevChallenges: [] }
  proofBulletproofChallenges = vestaProofBulletproofChallenges
  verifyOpeningProof = vestaVerifyOpeningProof
  permutationVanishingPolynomial = vestaPermutationVanishingPolynomial
  domainGenerator = vestaDomainGenerator
  computeB0 = vestaComputeB0
  proofIpaRounds = vestaProofIpaRounds

--------------------------------------------------------------------------------
-- Typed wrappers
--
-- The raw `foreign import` functions return `Array a` because the FFI marshals
-- JS arrays. The wrappers below apply the length check once, at the FFI
-- boundary, so library code downstream can use `Vector n a` ops without
-- repeating the `fromJust' ... Vector.toVector @n` dance at every call site.
--
-- Each wrapper panics (via `fromJust'`) if the underlying FFI returns an
-- array of the wrong length. That's a programmer/FFI-contract error, not a
-- user-recoverable condition — the Rust side is expected to uphold the
-- shape invariant.
--------------------------------------------------------------------------------

-- | Verifier-index polynomial commitments, split into the three groups
-- | Pickles consumers actually work with. Layout (matches OCaml
-- | `Plonk_verification_key_evals`):
-- |   `index`  = 6 selector commitments (generic, psm, complete_add, mul,
-- |              emul, endomul_scalar)
-- |   `coeff`  = 15 coefficient commitments
-- |   `sigma`  = 7 sigma commitments (6 from `*VerifierIndexColumnComms`
-- |              + 1 from `*SigmaCommLast`, snoc'd into a Vector 7)
-- | Verifier-index commitments — 7 sigma + 15 coefficient + 6 index
-- | commitments, each carrying `numChunks` curve points. Both outer
-- | Vector sizes AND the inner chunk count are static.
-- |
-- | Wrap-side consumers (where OCaml currently hardcodes
-- | `num_chunks_by_default = 1` per `step_main.ml:347`) call with
-- | `@1`; step-side consumers (`wrap_main.ml:80`'s `~num_chunks`)
-- | pass the user-supplied compile param. The specialization is
-- | pushed all the way to the consumer so the wrapper stays a
-- | one-line projection.
type VerifierIndexCommitments :: Int -> Type -> Type
type VerifierIndexCommitments numChunks f =
  { index :: Vector 6 (ChunkedCommitment numChunks (AffinePoint f))
  , coeff :: Vector 15 (ChunkedCommitment numChunks (AffinePoint f))
  , sigma :: Vector 7 (ChunkedCommitment numChunks (AffinePoint f))
  }

-- | Vector-typed split of `pallasVerifierIndexColumnComms` +
-- | `pallasSigmaCommLast`. Used for step VK extraction (consumed by
-- | the wrap circuit). Pass `@numChunks` matching kimchi's
-- | `comm.chunks.len()`.
pallasVerifierIndexCommitments
  :: forall @numChunks
   . Reflectable numChunks Int
  => VerifierIndex Vesta.G Pallas.BaseField
  -> VerifierIndexCommitments numChunks Pallas.ScalarField
pallasVerifierIndexCommitments vk =
  splitVkCommitments @numChunks (pallasVerifierIndexColumnComms vk) (pallasSigmaCommLast vk)

-- | Vector-typed split of `vestaVerifierIndexColumnComms` +
-- | `vestaSigmaCommLast`. Used for wrap VK extraction (consumed by
-- | the step circuit). OCaml fixes this to `@1` at
-- | `step_main.ml:347` (TODO in OCaml flags future extensibility);
-- | callers here also pass `@1` until that invariant changes.
vestaVerifierIndexCommitments
  :: forall @numChunks
   . Reflectable numChunks Int
  => VerifierIndex Pallas.G Vesta.BaseField
  -> VerifierIndexCommitments numChunks Vesta.ScalarField
vestaVerifierIndexCommitments vk =
  splitVkCommitments @numChunks (vestaVerifierIndexColumnComms vk) (vestaSigmaCommLast vk)

-- | Shared splitter. Raw layout:
-- |   [ index(6) ; coeff(15) ; sigma-except-last(6) ]  = 27 commitments,
-- |   each entry an `Array (AffinePoint f)` of length numChunks.
-- | `sigmaLast` (also chunked) is snoc'd onto `sigma6` to produce
-- | the exported `Vector 7`. Inner Arrays reshape to
-- | `Vector numChunks` — a length mismatch panics via `fromJust'`.
splitVkCommitments
  :: forall @numChunks f
   . Reflectable numChunks Int
  => Array (Array (AffinePoint f))
  -> Array (AffinePoint f)
  -> VerifierIndexCommitments numChunks f
splitVkCommitments raw sigmaLast =
  let
    toChunks :: Array (AffinePoint f) -> ChunkedCommitment numChunks (AffinePoint f)
    toChunks = ChunkedCommitment <<< fromJust' "VerifierIndex commitment chunks length mismatch with @numChunks"
      <<< Vector.toVector @numChunks
    mkIndex = fromJust' "VerifierIndex index commits (6 entries)"
      <<< Vector.toVector @6
    mkCoeff = fromJust' "VerifierIndex coeff commits (15 entries)"
      <<< Vector.toVector @15
    mkSigma6 = fromJust' "VerifierIndex sigma commits (6 entries, pre-sigmaLast)"
      <<< Vector.toVector @6
    rawChunked = map toChunks raw
    sigmaLastChunked = toChunks sigmaLast
  in
    { index: mkIndex (Array.take 6 rawChunked)
    , coeff: mkCoeff (Array.take 15 (Array.drop 6 rawChunked))
    , sigma: Vector.snoc (mkSigma6 (Array.drop 21 rawChunked)) sigmaLastChunked
    }

-- | Vector-typed wrapper for `pallasProofOpeningPrechallenges`. The raw
-- | FFI produces an array of StepIPARounds (= 16) 128-bit scalar
-- | prechallenges for a Pallas (step-commitment) proof.
pallasProofOpeningPrechallengesVec
  :: VerifierIndex Vesta.G Pallas.BaseField
  -> { proof :: Proof Vesta.G Pallas.BaseField
     , publicInput :: Array Pallas.BaseField
     , prevChallenges ::
         Array
           { sgX :: Pallas.ScalarField
           , sgY :: Pallas.ScalarField
           , challenges :: Array Pallas.BaseField
           }
     }
  -> Vector StepIPARounds Pallas.BaseField
pallasProofOpeningPrechallengesVec vk input =
  fromJust' "pallasProofOpeningPrechallenges: expected Vector StepIPARounds (=16)"
    (Vector.toVector @StepIPARounds (pallasProofOpeningPrechallenges vk input))

-- | Vector-typed wrapper for `vestaProofOpeningPrechallenges`. The raw
-- | FFI produces an array of WrapIPARounds (= 15) 128-bit scalar
-- | prechallenges for a Vesta (wrap-commitment) proof.
vestaProofOpeningPrechallengesVec
  :: VerifierIndex Pallas.G Vesta.BaseField
  -> { proof :: Proof Pallas.G Vesta.BaseField
     , publicInput :: Array Vesta.BaseField
     , prevChallenges ::
         Array
           { sgX :: Vesta.ScalarField
           , sgY :: Vesta.ScalarField
           , challenges :: Array Vesta.BaseField
           }
     }
  -> Vector WrapIPARounds Vesta.BaseField
vestaProofOpeningPrechallengesVec vk input =
  fromJust' "vestaProofOpeningPrechallenges: expected Vector WrapIPARounds (=15)"
    (Vector.toVector @WrapIPARounds (vestaProofOpeningPrechallenges vk input))

-- | Vector-typed wrapper for `pallasProofOpeningLr` (step proof). Each
-- | IPA round contributes one L/R commitment pair; a Pallas step proof
-- | has `StepIPARounds` (= 16) rounds.
pallasProofOpeningLrVec
  :: Proof Vesta.G Pallas.BaseField
  -> Vector StepIPARounds (LrPair Pallas.ScalarField)
pallasProofOpeningLrVec p =
  fromJust' "pallasProofOpeningLr: expected Vector StepIPARounds (=16) L/R pairs"
    (Vector.toVector @StepIPARounds (pallasProofOpeningLr p))

-- | Vector-typed wrapper for `vestaProofOpeningLr` (wrap proof). Each
-- | IPA round contributes one L/R commitment pair; a Vesta wrap proof
-- | has `WrapIPARounds` (= 15) rounds.
vestaProofOpeningLrVec
  :: Proof Pallas.G Vesta.BaseField
  -> Vector WrapIPARounds (LrPair Vesta.ScalarField)
vestaProofOpeningLrVec p =
  fromJust' "vestaProofOpeningLr: expected Vector WrapIPARounds (=15) L/R pairs"
    (Vector.toVector @WrapIPARounds (vestaProofOpeningLr p))

-- | `ProofCommitments.tComm` is an `Array` because the FFI doesn't
-- | encode `num_chunks` at the type level. In vanilla Mina
-- | `num_chunks = 1` so the array is always 7 long (= quotient-poly
-- | chunk count). This helper exposes that statically.
tCommVec
  :: forall f
   . ProofCommitments f
  -> Vector 7 (AffinePoint f)
tCommVec c =
  fromJust' "ProofCommitments.tComm: expected Vector 7 (num_chunks=1)"
    (Vector.toVector @7 c.tComm)

-- | Project the per-polynomial chunked `wComm` array into a typed
-- | `Vector numChunks` per polynomial. Errors if any polynomial's
-- | chunk count differs from `numChunks`.
wCommChunked
  :: forall @numChunks f
   . Reflectable numChunks Int
  => ProofCommitments f
  -> Vector 15 (ChunkedCommitment numChunks (AffinePoint f))
wCommChunked c =
  map
    ( \chunks ->
        ChunkedCommitment $
          fromJust' "ProofCommitments.wComm: chunk count mismatch with @numChunks"
            (Vector.toVector @numChunks chunks)
    )
    c.wComm

-- | Project the chunked `zComm` array into a typed `ChunkedCommitment numChunks`.
zCommChunked
  :: forall @numChunks f
   . Reflectable numChunks Int
  => ProofCommitments f
  -> ChunkedCommitment numChunks (AffinePoint f)
zCommChunked c =
  ChunkedCommitment $
    fromJust' "ProofCommitments.zComm: chunk count mismatch with @numChunks"
      (Vector.toVector @numChunks c.zComm)

-- | Reshape the flat `tComm :: Array (AffinePoint f)` (length `7 *
-- | numChunks`) into the kimchi-faithful 2D shape
-- | `Vector 7 (Vector numChunks pt)` — outer = quotient sub-poly index,
-- | inner = chunk index. Errors if the array's length doesn't match
-- | `7 * numChunks`.
tCommChunked
  :: forall @numChunks f
   . Reflectable numChunks Int
  => ProofCommitments f
  -> Vector 7 (ChunkedCommitment numChunks (AffinePoint f))
tCommChunked c =
  let
    nc = reflectType (Proxy @numChunks)
    perPiece i = ChunkedCommitment $
      fromJust'
        "ProofCommitments.tComm: per-piece chunk count mismatch with @numChunks"
        (Vector.toVector @numChunks (Array.slice (i * nc) ((i + 1) * nc) c.tComm))
    pieces = map perPiece (Array.range 0 6)
  in
    fromJust'
      "ProofCommitments.tComm: expected 7 quotient pieces"
      (Vector.toVector @7 pieces)
