-- | FFI bindings for proof creation, oracle computation, and other
-- | kimchi proof-systems operations.
-- |
-- | This module was originally `Test.Pickles.ProofFFI` — lifted into
-- | `packages/pickles/src/` so the prover library (`Pickles.Prove.*`)
-- | can consume `proofOracles`, `createProof`, etc. directly.
module Pickles.ProofFFI
  ( class ProofFFI
  , class HasProofData
  , proofData
  , ProofData
  , ProofCommitments
  , OpeningProofData
  , ProofEvaluations
  , createProof
  , pallasCreateProofWithPrev
  , vestaCreateProofWithPrev
  , proofOracles
  , proofBulletproofChallenges
  , verifyOpeningProof
  , verifyOpeningProofsBatch
  , computeB0
  , permutationVanishingPolynomial
  , domainGenerator
  -- Curve-specific helpers — the prevChallenges sg-coord field type
  -- depends on the curve, so these can't go through the curve-polymorphic
  -- class.
  , pallasProofOracles
  , vestaProofOracles
  , pallasProofOpeningPrechallenges
  , vestaProofOpeningPrechallenges
  , pallasProverIndexDomainLog2
  , vestaVerifierIndexJsonKey
  , pallasVerifierIndexJsonKey
  , pallasSrsLagrangeCommitmentChunksAt
  , vestaSrsLagrangeCommitmentChunksAt
  , pallasSrsBlindingGenerator
  , vestaSrsBlindingGenerator
  , pallasSigmaCommLast
  , vestaSigmaCommLast
  , pallasVerifierIndexColumnComms
  , vestaVerifierIndexColumnComms
  , vestaChallengePolyCommitment
  , vestaMakeWireProof
  , Dehydrated(..)
  , Proof
  , OraclesResult
  , PointEval
  , publicEvalsChunked
  , SpongeCheckpoint
  , LrPair
  -- Typed wrappers: length-checked at the FFI boundary
  , VerifierIndexCommitments
  , pallasVerifierIndexCommitments
  , vestaVerifierIndexCommitments
  , pallasProofOpeningPrechallengesVec
  , vestaProofOpeningPrechallengesVec
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
import Pickles.Domain as Domain
import Pickles.Types (ChunkedCommitment(..), StepIPARounds, WrapIPARounds)
import Pickles.Util.Fatal (fromJust')
import Snarky.Backend.Kimchi.Types (CRS, ProverIndex, VerifierIndex)
import Snarky.Circuit.DSL (SizedF)
import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Vesta as Vesta
import Snarky.Data.EllipticCurve (AffinePoint)
import Type.Proxy (Proxy(..))

-- | Opaque proof type, parameterized by curve group and scalar field.
-- |
-- | The PS-side value is a kimchi-napi-shaped handle at runtime; consumers
-- | inspect proof components via the structured `ProofData` record returned
-- | by `proofData` (see `HasProofData` below) rather than the legacy
-- | per-component getter functions.
foreign import data Proof :: Type -> Type -> Type

--------------------------------------------------------------------------------
-- ProofData: structured record mirroring kimchi-napi's `WasmFpProverProof`
-- tree. One `proofData :: Proof g f -> ProofData c f` decoder per curve
-- handles the FFI-to-record translation; PS-side consumers then use direct
-- field access.
--
-- The `c` parameter is the COMMITMENT curve's coord field (= base field of
-- the commitment curve). For Pasta proofs the relationship is established
-- by `WeierstrassCurve c g`:
--   g = Vesta.G  → c = Vesta.BaseField  = Pallas.ScalarField  = Fq
--   g = Pallas.G → c = Pallas.BaseField = Vesta.ScalarField   = Fp
--------------------------------------------------------------------------------

-- | All commitments produced by a kimchi prover, in PS-record form.
-- | Each polynomial's commitment is chunked: one curve point per chunk.
type ProofCommitments c =
  { wComm :: Vector 15 (Array (AffinePoint c)) -- 15 witness polys × num_chunks chunks
  , zComm :: Array (AffinePoint c) -- permutation poly × num_chunks chunks
  , tComm :: Array (AffinePoint c) -- quotient poly × 7 * num_chunks chunks
  }

-- | Opening (IPA) proof: lr round pairs + delta + sg curve points, plus the
-- | z1/z2 scalars. Curve coords live in the commitment curve's base field
-- | `c`; scalars live in the witness/eval field `f`. The `rounds` phantom
-- | encodes the IPA round count at the type level so consumers don't pay a
-- | runtime length check — the FFI decoder validates once.
type OpeningProofData rounds c f =
  { lr :: Vector rounds (LrPair c)
  , delta :: AffinePoint c
  , sg :: AffinePoint c
  , z1 :: f
  , z2 :: f
  }

-- | Polynomial evaluations at zeta + zeta·ω. Each cell is a non-empty
-- | array of `PointEval` — one entry per polynomial chunk. For non-chunked
-- | proofs `NonEmptyArray (PointEval f)` has length 1.
-- |
-- | `public` mirrors the kimchi prover's `evals.public` field — the chunked
-- | evaluation of the public-input polynomial at zeta / zeta·ω. Always
-- | populated by `kimchi/src/prover.rs:996-1002` (unconditional `Some`),
-- | so on the PS side we expose it as a plain `NonEmptyArray`. Consumers
-- | that previously read `oraclesResult.publicEvals` now read
-- | `(proofData proof).evals.public`. Matches OCaml pickles `wrap.ml:111`
-- | (`proof.public_evals`).
type ProofEvaluations f =
  { w :: Vector 15 (NonEmptyArray (PointEval f)) -- 15 witness polys
  , z :: NonEmptyArray (PointEval f) -- permutation poly
  , s :: Vector 6 (NonEmptyArray (PointEval f)) -- sigma polys (PERMUTS-1 = 6)
  , coefficients :: Vector 15 (NonEmptyArray (PointEval f))
  -- | Selector evaluations in `to_batch` order:
  -- | `[generic, poseidon, completeAdd, mul, emul, endomulScalar]`.
  , indexEvals :: Vector 6 (NonEmptyArray (PointEval f))
  , public :: NonEmptyArray (PointEval f)
  , ftEval1 :: f
  }

-- | Top-level structured proof record. `rounds` is the IPA round count
-- | for this proof's commitment curve: `StepIPARounds` (= 16) for
-- | Vesta-committed (step) proofs, `WrapIPARounds` (= 15) for Pallas-committed
-- | (wrap) proofs.
type ProofData rounds c f =
  { commitments :: ProofCommitments c
  , opening :: OpeningProofData rounds c f
  , evals :: ProofEvaluations f
  }

-- | Curve-polymorphic decoder. The functional dependency `g -> f c rounds`
-- | lets the instance be picked from the `Proof g f` argument alone; the
-- | coord field `c` and IPA round count `rounds` flow out via the result
-- | type. See `WeierstrassCurve f g` for the underlying curve ↔ base-field
-- | mapping, and `Pickles.Types.{StepIPARounds, WrapIPARounds}` for the
-- | per-curve IPA round constants.
class HasProofData :: Type -> Type -> Type -> Int -> Constraint
class HasProofData g f c rounds | g -> f c rounds where
  proofData :: Proof g f -> ProofData rounds c f

-- | Polynomial evaluation at two points: zeta and zeta*omega.
type PointEval f = { zeta :: f, omegaTimesZeta :: f }

-- | Result of running the Fiat-Shamir oracle computation on a proof.
-- |
-- | Migration note: `publicEvals` moved to `ProofData.evals.public` (chunked,
-- | always populated by the kimchi prover). `ftEval0` and
-- | `combinedInnerProduct` were carried for snarky-crypto API parity but
-- | never read in production paths — both are PS-recomputed in
-- | `Pickles.PlonkChecks` against the chunked evals. Dropped during the
-- | kimchi-napi migration; `fp_oracles_create` does not return them.
type OraclesResult f =
  { alpha :: f
  , beta :: SizedF 128 f -- 128-bit challenge (no endo expansion, unlike alpha)
  , gamma :: SizedF 128 f -- 128-bit challenge (no endo expansion, unlike alpha)
  , zeta :: f
  , v :: f -- polyscale (xi)
  , u :: f -- evalscale
  , ftEval1 :: f
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
-- |
-- | The 13 legacy per-component getters (`proofWitnessEvals`,
-- | `proofZEvals`, `proofSigmaEvals`, `proofCoefficientEvals`,
-- | `proofIndexEvals`, `proofIpaRounds`, `proverIndexShifts`) were
-- | removed in the Phase D kimchi-napi migration — consumers access the
-- | same data via the structured `ProofData` record returned by
-- | `proofData`. Likewise the math helpers
-- | (`permutationVanishingPolynomial`, `domainGenerator`, `computeB0`)
-- | are kept as class methods but their bodies now bind directly to
-- | `Pickles.Domain` PS implementations.
class ProofFFI f g | f -> g where
  createProof :: { proverIndex :: ProverIndex g f, witness :: Vector 15 (Array f) } -> Proof g f
  -- | Non-recursive variant of `{pallas,vesta}ProofOracles` — passes
  -- | `prevChallenges: []` behind the scenes. Use this from
  -- | curve-polymorphic code that only handles standalone proofs. For
  -- | recursive proofs, call the curve-specific foreign imports with
  -- | the real `prevChallenges` list.
  proofOracles :: VerifierIndex g f -> { proof :: Proof g f, publicInput :: Array f } -> OraclesResult f
  proofBulletproofChallenges :: VerifierIndex g f -> { proof :: Proof g f, publicInput :: Array f } -> Array f
  verifyOpeningProof :: VerifierIndex g f -> { proof :: Proof g f, publicInput :: Array f } -> Boolean
  -- | Batched stage-3 kimchi verify: one amortized `batch_verify` over
  -- | many proofs that share this wrap verifier index. The homogeneous
  -- | specialization of OCaml `Verify.verify_heterogenous`'s final
  -- | `batch_verify` (all proofs of one tag). `[]` is vacuously `true`.
  verifyOpeningProofsBatch :: VerifierIndex g f -> Array { proof :: Proof g f, publicInput :: Array f } -> Boolean
  permutationVanishingPolynomial :: { domainLog2 :: Int, zkRows :: Int, pt :: f } -> f
  domainGenerator :: Int -> f
  computeB0 :: { challenges :: Array f, zeta :: f, zetaOmega :: f, evalscale :: f } -> f

--------------------------------------------------------------------------------
-- Private foreign imports
--------------------------------------------------------------------------------

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

-- | Eager-decode the whole proof to the structured `ProofData` record.
-- | Implementation reads the per-component FFI getters and assembles the
-- | record once; consumers should call this once per proof and pattern-match
-- | the result rather than calling the legacy per-component accessors. The
-- | per-component accessors are kept for backward compat during the
-- | migration and will be removed once all consumers switch.
-- | Raw FFI-returned record: identical to `ProofData` except `opening.lr`
-- | is an unsized `Array` (since the JS decoder doesn't know the type-level
-- | IPA round count). The PS-side `pallasProofData` / `vestaProofData`
-- | wrappers below project it into a `Vector rounds (LrPair c)` using the
-- | `Reflectable rounds Int` length pulled from the type parameter.
type RawProofData c f =
  { commitments :: ProofCommitments c
  , opening ::
      { lr :: Array (LrPair c)
      , delta :: AffinePoint c
      , sg :: AffinePoint c
      , z1 :: f
      , z2 :: f
      }
  , evals :: ProofEvaluations f
  }

foreign import pallasProofDataRaw
  :: Proof Vesta.G Pallas.BaseField
  -> RawProofData Pallas.ScalarField Pallas.BaseField

foreign import vestaProofDataRaw
  :: Proof Pallas.G Vesta.BaseField
  -> RawProofData Vesta.ScalarField Vesta.BaseField

-- | Promote a raw decoder result to the typed `ProofData rounds c f` by
-- | applying `Vector.toVector @rounds` once to the lr array. Failure here
-- | indicates a mismatch between the prover's SRS depth and the PS-side
-- | type-level expectation — surfaces as a clear `fromJust'` crash rather
-- | than silent corruption.
projectProofData
  :: forall @rounds c f
   . Reflectable rounds Int
  => RawProofData c f
  -> ProofData rounds c f
projectProofData raw =
  let
    expected = reflectType (Proxy :: Proxy rounds)
    actual = Array.length raw.opening.lr
    lrVec = fromJust'
      ( "ProofData.opening.lr: expected Vector of length " <> show expected
          <> " (= IPA rounds for this proof's commitment curve), got "
          <> show actual
      )
      (Vector.toVector @rounds raw.opening.lr)
  in
    { commitments: raw.commitments
    , opening:
        { lr: lrVec
        , delta: raw.opening.delta
        , sg: raw.opening.sg
        , z1: raw.opening.z1
        , z2: raw.opening.z2
        }
    , evals: raw.evals
    }

pallasProofData
  :: Proof Vesta.G Pallas.BaseField
  -> ProofData StepIPARounds Pallas.ScalarField Pallas.BaseField
pallasProofData = projectProofData <<< pallasProofDataRaw

vestaProofData
  :: Proof Pallas.G Vesta.BaseField
  -> ProofData WrapIPARounds Vesta.ScalarField Vesta.BaseField
vestaProofData = projectProofData <<< vestaProofDataRaw

-- The 13 per-component foreign imports (`pallasProofWitnessEvals`,
-- `vestaProofWitnessEvals`, `pallasProofZEvals`, …, `pallasProofIpaRounds`,
-- `vestaProofIpaRounds`) were removed in the Phase D kimchi-napi
-- migration. All component access goes through `proofData :: Proof g f ->
-- ProofData rounds c f`, whose JS impl walks `WasmFpProverProof`
-- directly. See `pallasProofDataRaw` / `vestaProofDataRaw` above.

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

foreign import pallasVerifyOpeningProofsBatch :: VerifierIndex Vesta.G Pallas.BaseField -> Array { proof :: Proof Vesta.G Pallas.BaseField, publicInput :: Array Pallas.BaseField } -> Boolean
foreign import vestaVerifyOpeningProofsBatch :: VerifierIndex Pallas.G Vesta.BaseField -> Array { proof :: Proof Pallas.G Vesta.BaseField, publicInput :: Array Vesta.BaseField } -> Boolean

-- NOTE: `u_t` is the sponge output AFTER absorbing shifted CIP and BEFORE
-- `group_map`. It is squeezed in the commitment curve's BASE field (=
-- the OTHER scalar field in the 2-cycle): for a Vesta proof it's Fq =
-- `Pallas.ScalarField`; for a Pallas proof it's Fp = `Vesta.ScalarField`.
-- `permutationVanishingPolynomial`, `domainGenerator`, and `computeB0` are
-- now pure PureScript via `Pickles.Domain` (running on `TwoAdicField` +
-- `PrimeField` arithmetic). The previous snarky-crypto foreign imports were
-- removed in the kimchi-napi migration — no behavior change, the math is
-- field-element arithmetic only.

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
-- Lagrange commitments directly from SRS (no verifier index needed).
-- | Returns ALL chunks of the `i`-th lagrange commitment as an `Array`
-- | of points. PureScript analog of OCaml
-- | `Kimchi_bindings.Protocol.SRS.Fq.lagrange_commitment`
-- | (`step_verifier.ml:360-368`); kimchi caches the full basis on
-- | first access so per-index calls are O(1) after warmup. For
-- | domains ≤ SRS max_poly_size the array has length 1; for chunked
-- | domains (e.g. step domain > wrap SRS depth at chunks2) it has
-- | length `ceil(domain_size / max_poly_size)`. Callers reshape into
-- | a `Vector stepChunks (AffinePoint)` at the use site. Mirrors
-- | OCaml's `lagrange_commitment srs d i .unshifted` array
-- | (`wrap_verifier.ml:336`).
foreign import pallasSrsLagrangeCommitmentChunksAt
  :: CRS Vesta.G -> Int -> Int -> Array (AffinePoint Pallas.ScalarField)

foreign import vestaSrsLagrangeCommitmentChunksAt
  :: CRS Pallas.G -> Int -> Int -> Array (AffinePoint Vesta.ScalarField)

-- Blinding generator H directly from SRS
foreign import pallasSrsBlindingGenerator :: CRS Vesta.G -> AffinePoint Pallas.ScalarField
foreign import vestaSrsBlindingGenerator :: CRS Pallas.G -> AffinePoint Vesta.ScalarField

-- sigma_comm[PERMUTS-1] (the last sigma commitment), ALL chunks.
-- The raw inner Array length = num_chunks (1 for nc=1 callers, 2+ when
-- chunked). FFI doesn't know `stepChunks` at the type level; consumers
-- project to `Vector stepChunks` via `verifierIndexCommitments`.
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

-- sigma_comm[PERMUTS-1] (the last sigma commitment) for Vesta/Fq
-- verifier indices, returned chunk-aware (inner Array length = num_chunks).
-- See note on `pallasSigmaCommLast`.
foreign import vestaSigmaCommLast :: VerifierIndex Pallas.G Vesta.BaseField -> Array (AffinePoint Vesta.ScalarField)

-- | Deterministic, full-VK string used as the disk-proof-cache key.
-- |
-- | Mirrors OCaml `Pickles.Proof_cache`'s keying scheme (`proof_cache.ml:185`):
-- | the OCaml cache is `verifier_key_yojson -> public_input_yojson -> proof`,
-- | so two VKs share a bucket iff they serialize identically. OCaml never
-- | materializes a host-side VK digest — the only "VK digest" in pickles is
-- | the in-circuit `Sponge.copy sponge_after_index` inside step/wrap
-- | verifier. We adopt the same full-VK-as-key approach so we don't have to
-- | port that sponge to JS.
-- |
-- | The string covers exactly the fields OCaml's `[%to_yojson:
-- | verifier_index]` does (`proof_cache.ml:152-163`): `domain`,
-- | `max_poly_size`, `public`, `prev_challenges`, `evals`, `shifts`,
-- | `zk_rows` (we skip `srs` because OCaml renders it as `null`, and the
-- | optional `lookup_index`, which is `None` for vanilla pickles VKs).
foreign import vestaVerifierIndexJsonKey :: VerifierIndex Pallas.G Vesta.BaseField -> String

foreign import pallasVerifierIndexJsonKey :: VerifierIndex Vesta.G Pallas.BaseField -> String

--------------------------------------------------------------------------------
-- Instances
--------------------------------------------------------------------------------

instance HasProofData Vesta.G Pallas.BaseField Pallas.ScalarField StepIPARounds where
  proofData = pallasProofData

instance HasProofData Pallas.G Vesta.BaseField Vesta.ScalarField WrapIPARounds where
  proofData = vestaProofData

instance ProofFFI Pallas.BaseField Vesta.G where
  createProof = pallasCreateProof
  proofOracles vk { proof, publicInput } =
    pallasProofOracles vk { proof, publicInput, prevChallenges: [] }
  proofBulletproofChallenges = pallasProofBulletproofChallenges
  verifyOpeningProof = pallasVerifyOpeningProof
  verifyOpeningProofsBatch = pallasVerifyOpeningProofsBatch
  permutationVanishingPolynomial = Domain.permutationVanishingPolynomial @Pallas.BaseField
  domainGenerator = Domain.domainGenerator @Pallas.BaseField
  computeB0 = Domain.computeB0

instance ProofFFI Vesta.BaseField Pallas.G where
  createProof = vestaCreateProof
  proofOracles vk { proof, publicInput } =
    vestaProofOracles vk { proof, publicInput, prevChallenges: [] }
  proofBulletproofChallenges = vestaProofBulletproofChallenges
  verifyOpeningProof = vestaVerifyOpeningProof
  verifyOpeningProofsBatch = vestaVerifyOpeningProofsBatch
  permutationVanishingPolynomial = Domain.permutationVanishingPolynomial @Vesta.BaseField
  domainGenerator = Domain.domainGenerator @Vesta.BaseField
  computeB0 = Domain.computeB0

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
-- | commitments, each carrying `stepChunks` curve points. Both outer
-- | Vector sizes AND the inner chunk count are static.
-- |
-- | Wrap-side consumers (where OCaml currently hardcodes
-- | `num_chunks_by_default = 1` per `step_main.ml:347`) call with
-- | `@1`; step-side consumers (`wrap_main.ml:80`'s `~num_chunks`)
-- | pass the user-supplied compile param. The specialization is
-- | pushed all the way to the consumer so the wrapper stays a
-- | one-line projection.
type VerifierIndexCommitments :: Int -> Type -> Type
type VerifierIndexCommitments stepChunks f =
  { index :: Vector 6 (ChunkedCommitment stepChunks (AffinePoint f))
  , coeff :: Vector 15 (ChunkedCommitment stepChunks (AffinePoint f))
  , sigma :: Vector 7 (ChunkedCommitment stepChunks (AffinePoint f))
  }

-- | Vector-typed split of `pallasVerifierIndexColumnComms` +
-- | `pallasSigmaCommLast`. Used for step VK extraction (consumed by
-- | the wrap circuit). Pass `@stepChunks` matching kimchi's
-- | `comm.chunks.len()`.
pallasVerifierIndexCommitments
  :: forall @stepChunks
   . Reflectable stepChunks Int
  => VerifierIndex Vesta.G Pallas.BaseField
  -> VerifierIndexCommitments stepChunks Pallas.ScalarField
pallasVerifierIndexCommitments vk =
  splitVkCommitments @stepChunks (pallasVerifierIndexColumnComms vk) (pallasSigmaCommLast vk)

-- | Vector-typed split of `vestaVerifierIndexColumnComms` +
-- | `vestaSigmaCommLast`. Used for wrap VK extraction (consumed by
-- | the step circuit). OCaml fixes this to `@1` at
-- | `step_main.ml:347` (TODO in OCaml flags future extensibility);
-- | callers here also pass `@1` until that invariant changes.
vestaVerifierIndexCommitments
  :: forall @stepChunks
   . Reflectable stepChunks Int
  => VerifierIndex Pallas.G Vesta.BaseField
  -> VerifierIndexCommitments stepChunks Vesta.ScalarField
vestaVerifierIndexCommitments vk =
  splitVkCommitments @stepChunks (vestaVerifierIndexColumnComms vk) (vestaSigmaCommLast vk)

-- | Shared splitter. Raw layout:
-- |   [ index(6) ; coeff(15) ; sigma-except-last(6) ]  = 27 commitments,
-- |   each entry an `Array (AffinePoint f)` of length stepChunks.
-- | `sigmaLast` (also chunked) is snoc'd onto `sigma6` to produce
-- | the exported `Vector 7`. Inner Arrays reshape to
-- | `Vector stepChunks` — a length mismatch panics via `fromJust'`.
splitVkCommitments
  :: forall @stepChunks f
   . Reflectable stepChunks Int
  => Array (Array (AffinePoint f))
  -> Array (AffinePoint f)
  -> VerifierIndexCommitments stepChunks f
splitVkCommitments raw sigmaLast =
  let
    toChunks :: Array (AffinePoint f) -> ChunkedCommitment stepChunks (AffinePoint f)
    toChunks = ChunkedCommitment <<< fromJust' "VerifierIndex commitment chunks length mismatch with @stepChunks"
      <<< Vector.toVector @stepChunks
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

-- The `pallasProofOpeningLrVec` / `vestaProofOpeningLrVec` helpers were
-- dropped in Phase D — the equivalent `Vector rounds (LrPair c)` is now
-- the `opening.lr` field on the `ProofData` record (see `projectProofData`
-- and the `OpeningProofData rounds c f` shape above), which does the
-- length check once at the FFI boundary via `Reflectable rounds Int`.

-- | Project the per-polynomial chunked `wComm` array into a typed
-- | `Vector stepChunks` per polynomial. Errors if any polynomial's
-- | chunk count differs from `stepChunks`.
wCommChunked
  :: forall @stepChunks f
   . Reflectable stepChunks Int
  => ProofCommitments f
  -> Vector 15 (ChunkedCommitment stepChunks (AffinePoint f))
wCommChunked c =
  map
    ( \chunks ->
        ChunkedCommitment $
          fromJust' "ProofCommitments.wComm: chunk count mismatch with @stepChunks"
            (Vector.toVector @stepChunks chunks)
    )
    c.wComm

-- | Project the chunked `zComm` array into a typed `ChunkedCommitment stepChunks`.
zCommChunked
  :: forall @stepChunks f
   . Reflectable stepChunks Int
  => ProofCommitments f
  -> ChunkedCommitment stepChunks (AffinePoint f)
zCommChunked c =
  ChunkedCommitment $
    fromJust' "ProofCommitments.zComm: chunk count mismatch with @stepChunks"
      (Vector.toVector @stepChunks c.zComm)

-- | Reshape the flat `tComm :: Array (AffinePoint f)` (length `7 *
-- | stepChunks`) into the kimchi-faithful 2D shape
-- | `Vector 7 (Vector stepChunks pt)` — outer = quotient sub-poly index,
-- | inner = chunk index. Errors if the array's length doesn't match
-- | `7 * stepChunks`.
tCommChunked
  :: forall @stepChunks f
   . Reflectable stepChunks Int
  => ProofCommitments f
  -> Vector 7 (ChunkedCommitment stepChunks (AffinePoint f))
tCommChunked c =
  let
    nc = reflectType (Proxy @stepChunks)
    perPiece i = ChunkedCommitment $
      fromJust'
        "ProofCommitments.tComm: per-piece chunk count mismatch with @stepChunks"
        (Vector.toVector @stepChunks (Array.slice (i * nc) ((i + 1) * nc) c.tComm))
    pieces = map perPiece (Array.range 0 6)
  in
    fromJust'
      "ProofCommitments.tComm: expected 7 quotient pieces"
      (Vector.toVector @7 pieces)

-- | Boundary projector for the chunked public-input evaluations.
-- |
-- | Takes the chunked `NonEmptyArray (PointEval f)` from
-- | `(proofData proof).evals.public` (kimchi/OCaml-pickles convention —
-- | `kimchi/src/prover.rs:996-1002` unconditionally populates
-- | `proof.evals.public` with one entry per PCS chunk) and reshapes it
-- | into a chunk-typed `Vector n`, length-checked at the boundary.
-- |
-- | For a WRAP proof the chunk count is protocol-pinned to 1 (wrap
-- | domain ≤ wrap SRS depth), so callers pass `@1` and extract the
-- | sole chunk via a total `Vector.head`. A step-proof consumer
-- | passes `@stepChunks` and is forced to handle real chunking
-- | rather than dropping chunks.
publicEvalsChunked
  :: forall @n f
   . Reflectable n Int
  => NonEmptyArray (PointEval f)
  -> Vector n (PointEval f)
publicEvalsChunked pe =
  fromJust'
    "publicEvalsChunked: chunk count mismatch with @n"
    (Vector.toVector @n (NonEmptyArray.toArray pe))
