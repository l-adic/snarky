-- | FFI bindings for proof creation, oracle computation, and other
-- | kimchi proof-systems operations — the core logic for computing
-- | relevant proof values.
-- |
-- | Higher-level disk-proof-cache codec helpers (the VK-keyed JSON store)
-- | live in `Pickles.Prove.Codecs`. This module owns the `Proof` type,
-- | the `proofData` decoder, and every prove/verify/oracle/SRS binding,
-- | plus the kimchi `ProverProof<G>` / `VerifierIndex<G>` serde codecs
-- | (formerly in `Pickles.Sideload.FFI`, now folded in below).
module Snarky.Backend.Kimchi.Proof
  ( class ProofFFI
  , class HasProofData
  , proofData
  , pallasProofCommitments
  , vestaProofCommitments
  , ProofData
  , ProofCommitments
  , OpeningProofData
  , ProofEvaluations
  , createProof
  , pallasCreateProofWithPrev
  , vestaCreateProofWithPrev
  , proofOracles
  , proofOraclesRec
  , proofBulletproofChallenges
  , proofOpeningPrechallenges
  , verifyOpeningProof
  , verifyOpeningProofsBatch
  , computeB0
  , permutationVanishingPolynomial
  , domainGenerator
  , proverIndexDomainLog2
  , srsLagrangeCommitmentChunksAt
  , srsBlindingGenerator
  , sigmaCommLast
  , verifierIndexColumnComms
  -- Genuinely wrap-only (no step-side analog), so they stay standalone
  -- rather than forcing a bogus second class instance.
  , vestaChallengePolyCommitment
  , vestaMakeWireProof
  , Proof
  , OraclesResult
  , PointEval
  , SpongeCheckpoint
  , LrPair
  -- Serde JSON codecs (formerly in `Pickles.Sideload.FFI`). The wire
  -- format is `serde_json::{to_string,from_str}` on kimchi's
  -- `ProverProof<G>` / `VerifierIndex<G>` derives — cross-stack-
  -- compatible with OCaml-emitted fixtures by construction. Public input
  -- is `#[serde(skip)]`; callers thread it separately.
  , vestaVerifierIndexToSerdeJson
  , vestaVerifierIndexFromSerdeJson
  , pallasVerifierIndexToSerdeJson
  , pallasVerifierIndexFromSerdeJson
  , vestaProofFromSerdeJson
  , vestaProofToSerdeJson
  , pallasProofFromSerdeJson
  , pallasProofToSerdeJson
  ) where

import Prelude

import Data.Array as Array
import Data.Array.NonEmpty (NonEmptyArray)
import Data.Array.NonEmpty as NonEmptyArray
import Data.Maybe (Maybe(..))
import Data.Nullable (Nullable, toMaybe)
import Data.Reflectable (class Reflectable, reflectType)
import Data.Vector (Vector)
import Data.Vector as Vector
import Snarky.Backend.Kimchi.Commitment (ChunkedCommitment(..), StepIPARounds, WrapIPARounds)
import Snarky.Backend.Kimchi.Domain as Domain
import Snarky.Backend.Kimchi.Types (CRS, ProverIndex, VerifierIndex)
import Snarky.Backend.Kimchi.Util.Fatal (fromJust')
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

-- | All commitments produced by a kimchi prover, in PS-record form, with
-- | the per-polynomial chunk count `nc` reflected in the type — each
-- | commitment carries exactly `nc` curve points (kimchi splits each
-- | polynomial commitment into `nc` slices of `max_poly_size`). Decoded +
-- | length-validated once by `proofCommitments @nc`; obtained separately
-- | from `proofData` because the chunk count is `nc`-dependent whereas the
-- | opening/evals are not (the many evals-only consumers stay chunk-agnostic).
type ProofCommitments :: Int -> Type -> Type
type ProofCommitments nc c =
  { wComm :: Vector 15 (ChunkedCommitment nc (AffinePoint c)) -- 15 witness polys, nc chunks each
  , zComm :: ChunkedCommitment nc (AffinePoint c) -- permutation poly, nc chunks
  , tComm :: Vector 7 (ChunkedCommitment nc (AffinePoint c)) -- quotient poly, 7 pieces × nc chunks
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

-- | Top-level structured proof record — the `nc`-agnostic half of a
-- | decoded proof (`opening` + `evals`). `rounds` is the IPA round count
-- | for this proof's commitment curve: `StepIPARounds` (= 16) for
-- | Vesta-committed (step) proofs, `WrapIPARounds` (= 15) for Pallas-committed
-- | (wrap) proofs. Commitments live in the separate, `nc`-typed
-- | `ProofCommitments` record returned by `proofCommitments @nc`.
type ProofData rounds c f =
  { opening :: OpeningProofData rounds c f
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
  -- | Public-input polynomial eval at zeta / zeta·ω as the FrSponge absorbed
  -- | it (kimchi `verifier.rs:332-393`): the proof's `evals.public` when
  -- | `Some`, else recomputed from the public input. This is OCaml's
  -- | `O.p_eval_1/p_eval_2` (`wrap.ml:110-116`) — the correct in-circuit
  -- | public eval for a dummy wrap proof, whose wire `evals.public` is `None`.
  , publicEvals :: PointEval f
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
-- | `c` is the commitment curve's coordinate field (where a proof's curve
-- | points live). The Pasta cycle makes `f`/`g`/`c` a three-way bijection,
-- | so all are mutually determined — `g -> f c` in particular lets methods
-- | whose signature mentions only `g` (e.g. `srsBlindingGenerator :: CRS g
-- | -> AffinePoint c`) resolve their instance and pin `c`.
class ProofFFI f g c | f -> g c, g -> f c where
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
  -- | Recursive oracles: like `proofOracles` but absorbs the prior proofs'
  -- | `prevChallenges` into the Fiat-Shamir transcript. `c` is the
  -- | commitment curve's coord field — where the prev proofs' `sg`
  -- | commitments live.
  proofOraclesRec
    :: VerifierIndex g f
    -> { proof :: Proof g f, publicInput :: Array f, prevChallenges :: Array { sgX :: c, sgY :: c, challenges :: Array f } }
    -> OraclesResult f
  -- | Raw 128-bit IPA opening prechallenges (pre-endo-expansion), recursive.
  proofOpeningPrechallenges
    :: VerifierIndex g f
    -> { proof :: Proof g f, publicInput :: Array f, prevChallenges :: Array { sgX :: c, sgY :: c, challenges :: Array f } }
    -> Array f
  -- | `log_size_of_group` of the prover index's d1 evaluation domain.
  proverIndexDomainLog2 :: ProverIndex g f -> Int
  -- | All chunks of the `i`-th SRS lagrange commitment at a given domain log2.
  srsLagrangeCommitmentChunksAt :: CRS g -> Int -> Int -> Array (AffinePoint c)
  -- | SRS blinding generator H (coords in the commitment curve's base field).
  srsBlindingGenerator :: CRS g -> AffinePoint c
  -- | `sigma_comm[PERMUTS-1]` (the last sigma commitment), all chunks.
  sigmaCommLast :: VerifierIndex g f -> Array (AffinePoint c)
  -- | 27 VK column commitments (6 index + 15 coeff + 6 sigma) in to_batch
  -- | order, each entry chunked.
  verifierIndexColumnComms :: VerifierIndex g f -> Array (Array (AffinePoint c))

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

-- | Typed foreign-record view of kimchi-napi's `WasmF{p,q}ProverProof`.
-- | The proof handle IS this object at runtime (snake/camel napi labels
-- | mirrored exactly), so `asNapiProof` is a zero-cost `unsafeCoerce`.
-- | Leaves are opaque `NapiBytes` (napi `Buffer`s), decoded per-curve by
-- | `fpFromBytesLE` / `fqFromBytesLE`. This is the single point where the
-- | napi shape is asserted; the structural walk below is fully typed PS.
foreign import data NapiBytes :: Type

-- | f = Pasta `Fp` (= `Vesta.ScalarField` = `Pallas.BaseField`).
foreign import fpFromBytesLE :: NapiBytes -> Vesta.ScalarField

-- | f = Pasta `Fq` (= `Pallas.ScalarField` = `Vesta.BaseField`).
foreign import fqFromBytesLE :: NapiBytes -> Pallas.ScalarField

type NapiG = { x :: NapiBytes, y :: NapiBytes }

-- | `NapiPolyComm { unshifted, shifted }`; pickles never sets `shifted`.
type NapiPolyComm = { unshifted :: Array NapiG }

-- | `NapiPointEvaluations { zeta, zetaOmega }`; parallel chunk arrays.
type NapiPointEvals = { zeta :: Array NapiBytes, zetaOmega :: Array NapiBytes }

type NapiProof =
  { commitments ::
      { w_comm :: Array NapiPolyComm
      , z_comm :: NapiPolyComm
      , t_comm :: NapiPolyComm
      }
  , proof ::
      { lr_0 :: Array NapiG -- L points
      , lr_1 :: Array NapiG -- R points (parallel to lr_0)
      , delta :: NapiG
      , sg :: NapiG
      , z1 :: NapiBytes
      , z2 :: NapiBytes
      }
  , evals ::
      { w :: Array NapiPointEvals
      , z :: NapiPointEvals
      , s :: Array NapiPointEvals
      , coefficients :: Array NapiPointEvals
      , genericSelector :: NapiPointEvals
      , poseidonSelector :: NapiPointEvals
      , completeAddSelector :: NapiPointEvals
      , mulSelector :: NapiPointEvals
      , emulSelector :: NapiPointEvals
      , endomulScalarSelector :: NapiPointEvals
      -- | `Nullable`: a kimchi prover always populates `public`, but the
      -- | hand-built dummy wrap proof (`vestaMakeWireProof`) leaves it `None`
      -- | to match OCaml `Wrap_wire_proof` — so consumers must source the
      -- | dummy's public eval from the oracle (`OraclesResult.publicEvals` =
      -- | the recomputed `x_hat`), never from this field.
      , public :: Nullable NapiPointEvals
      }
  , ft_eval1 :: NapiBytes
  }

-- | Reinterpret the opaque proof handle as its napi-record view. The JS
-- | impl is identity — the handle IS this object — so this is the one
-- | typed FFI boundary that asserts the napi shape; everything downstream
-- | is fully type-checked PS.
foreign import asNapiProof :: forall g f. Proof g f -> NapiProof

-- | Structural decode of the napi proof tree into the typed `ProofData`.
-- | `decF` decodes scalar/eval leaves (the circuit's witness field `f`);
-- | `decC` decodes curve-point coords (the commitment curve's base field
-- | `c`, the opposite cycle-half). `@rounds` fixes the IPA round count, so
-- | the opening's `lr` is length-checked here at the boundary — a mismatch
-- | means the prover's SRS depth disagrees with the type-level expectation
-- | (loud `fromJust'` rather than silent corruption). The `to_batch`
-- | selector order `[generic, poseidon, completeAdd, mul, emul,
-- | endomulScalar]` is preserved in `indexEvals`.
decodeProofData
  :: forall @rounds c f
   . Reflectable rounds Int
  => Semiring f
  => (NapiBytes -> f)
  -> (NapiBytes -> c)
  -> NapiProof
  -> ProofData rounds c f
decodeProofData decF decC p =
  { opening:
      { lr: toVec @rounds "opening.lr (IPA round count — check SRS depth)"
          (Array.zipWith (\l r -> { l: point l, r: point r }) p.proof.lr_0 p.proof.lr_1)
      , delta: point p.proof.delta
      , sg: point p.proof.sg
      , z1: decF p.proof.z1
      , z2: decF p.proof.z2
      }
  , evals:
      { w: toVec @15 "evals.w" (map pointEvals p.evals.w)
      , z: pointEvals p.evals.z
      , s: toVec @6 "evals.s" (map pointEvals p.evals.s)
      , coefficients: toVec @15 "evals.coefficients" (map pointEvals p.evals.coefficients)
      , indexEvals: toVec @6 "evals.indexEvals"
          [ pointEvals p.evals.genericSelector
          , pointEvals p.evals.poseidonSelector
          , pointEvals p.evals.completeAddSelector
          , pointEvals p.evals.mulSelector
          , pointEvals p.evals.emulSelector
          , pointEvals p.evals.endomulScalarSelector
          ]
      -- A `None` here is the dummy wrap proof (see the `public` field note
      -- above): its real public eval is the oracle's recomputed `x_hat`, so
      -- this placeholder is never read. Real proofs always carry `Some`.
      , public: case toMaybe p.evals.public of
          Just ev -> pointEvals ev
          Nothing -> NonEmptyArray.singleton { zeta: zero, omegaTimesZeta: zero }
      , ftEval1: decF p.ft_eval1
      }
  }
  where
  point :: NapiG -> AffinePoint c
  point g = { x: decC g.x, y: decC g.y }

  pointEvals :: NapiPointEvals -> NonEmptyArray (PointEval f)
  pointEvals ev =
    fromJust' "ProofData.evals: empty chunk array"
      $ NonEmptyArray.fromArray
      $ Array.zipWith (\z zo -> { zeta: decF z, omegaTimesZeta: decF zo }) ev.zeta ev.zetaOmega

  toVec :: forall @n a. Reflectable n Int => String -> Array a -> Vector n a
  toVec lbl arr =
    fromJust' ("ProofData." <> lbl <> ": unexpected chunk/array length") (Vector.toVector @n arr)

pallasProofData
  :: Proof Vesta.G Pallas.BaseField
  -> ProofData StepIPARounds Pallas.ScalarField Pallas.BaseField
pallasProofData = decodeProofData @StepIPARounds fpFromBytesLE fqFromBytesLE <<< asNapiProof

vestaProofData
  :: Proof Pallas.G Vesta.BaseField
  -> ProofData WrapIPARounds Vesta.ScalarField Vesta.BaseField
vestaProofData = decodeProofData @WrapIPARounds fqFromBytesLE fpFromBytesLE <<< asNapiProof

-- | Structural decode of just the proof's commitments, `nc`-typed. `decC`
-- | decodes curve-point coords (the commitment curve's base field `c`).
-- | Each polynomial commitment is reshaped to `ChunkedCommitment nc`, and
-- | the flat `t_comm` (length `7 * nc`) into `Vector 7 (ChunkedCommitment
-- | nc)` (outer = quotient sub-poly, inner = chunk). Chunk-count
-- | mismatches with `@nc` panic at the boundary via `fromJust'`.
decodeProofCommitments
  :: forall @nc c
   . Reflectable nc Int
  => (NapiBytes -> c)
  -> NapiProof
  -> ProofCommitments nc c
decodeProofCommitments decC p =
  { wComm: toVec @15 "wComm" (map (chunked <<< polyComm) p.commitments.w_comm)
  , zComm: chunked (polyComm p.commitments.z_comm)
  , tComm: tCommReshape (polyComm p.commitments.t_comm)
  }
  where
  point :: NapiG -> AffinePoint c
  point g = { x: decC g.x, y: decC g.y }

  polyComm :: NapiPolyComm -> Array (AffinePoint c)
  polyComm pc = map point pc.unshifted

  chunked :: Array (AffinePoint c) -> ChunkedCommitment nc (AffinePoint c)
  chunked =
    ChunkedCommitment <<< fromJust' "ProofCommitments: chunk count mismatch with @nc"
      <<< Vector.toVector @nc

  -- Flat `t_comm` (7 * nc points) → `Vector 7 (ChunkedCommitment nc)`.
  tCommReshape :: Array (AffinePoint c) -> Vector 7 (ChunkedCommitment nc (AffinePoint c))
  tCommReshape flat =
    let
      nc = reflectType (Proxy @nc)
      perPiece i = ChunkedCommitment $
        fromJust' "ProofCommitments.tComm: per-piece chunk count mismatch with @nc"
          (Vector.toVector @nc (Array.slice (i * nc) ((i + 1) * nc) flat))
      pieces = map perPiece (Array.range 0 6)
    in
      fromJust' "ProofCommitments.tComm: expected 7 quotient pieces" (Vector.toVector @7 pieces)

  toVec :: forall @n a. Reflectable n Int => String -> Array a -> Vector n a
  toVec lbl arr =
    fromJust' ("ProofCommitments." <> lbl <> ": unexpected length") (Vector.toVector @n arr)

pallasProofCommitments
  :: forall @nc
   . Reflectable nc Int
  => Proof Vesta.G Pallas.BaseField
  -> ProofCommitments nc Pallas.ScalarField
pallasProofCommitments = decodeProofCommitments @nc fqFromBytesLE <<< asNapiProof

vestaProofCommitments
  :: forall @nc
   . Reflectable nc Int
  => Proof Pallas.G Vesta.BaseField
  -> ProofCommitments nc Vesta.ScalarField
vestaProofCommitments = decodeProofCommitments @nc fpFromBytesLE <<< asNapiProof

-- The 13 per-component foreign imports (`pallasProofWitnessEvals`,
-- `vestaProofWitnessEvals`, `pallasProofZEvals`, …, `pallasProofIpaRounds`,
-- `vestaProofIpaRounds`) were removed in the Phase D kimchi-napi
-- migration. All component access goes through `proofData :: Proof g f ->
-- ProofData rounds c f`, decoded once by `decodeProofData` (see
-- `pallasProofData` / `vestaProofData` above).

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
foreign import vestaProverIndexDomainLog2 :: ProverIndex Pallas.G Vesta.BaseField -> Int
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

--------------------------------------------------------------------------------
-- Instances
--------------------------------------------------------------------------------

instance HasProofData Vesta.G Pallas.BaseField Pallas.ScalarField StepIPARounds where
  proofData = pallasProofData

instance HasProofData Pallas.G Vesta.BaseField Vesta.ScalarField WrapIPARounds where
  proofData = vestaProofData

instance ProofFFI Pallas.BaseField Vesta.G Pallas.ScalarField where
  createProof = pallasCreateProof
  proofOracles vk { proof, publicInput } =
    pallasProofOracles vk { proof, publicInput, prevChallenges: [] }
  proofBulletproofChallenges = pallasProofBulletproofChallenges
  verifyOpeningProof = pallasVerifyOpeningProof
  verifyOpeningProofsBatch = pallasVerifyOpeningProofsBatch
  permutationVanishingPolynomial = Domain.permutationVanishingPolynomial @Pallas.BaseField
  domainGenerator = Domain.domainGenerator @Pallas.BaseField
  computeB0 = Domain.computeB0
  proofOraclesRec = pallasProofOracles
  proofOpeningPrechallenges = pallasProofOpeningPrechallenges
  proverIndexDomainLog2 = pallasProverIndexDomainLog2
  srsLagrangeCommitmentChunksAt = pallasSrsLagrangeCommitmentChunksAt
  srsBlindingGenerator = pallasSrsBlindingGenerator
  sigmaCommLast = pallasSigmaCommLast
  verifierIndexColumnComms = pallasVerifierIndexColumnComms

instance ProofFFI Vesta.BaseField Pallas.G Vesta.ScalarField where
  createProof = vestaCreateProof
  proofOracles vk { proof, publicInput } =
    vestaProofOracles vk { proof, publicInput, prevChallenges: [] }
  proofBulletproofChallenges = vestaProofBulletproofChallenges
  verifyOpeningProof = vestaVerifyOpeningProof
  verifyOpeningProofsBatch = vestaVerifyOpeningProofsBatch
  permutationVanishingPolynomial = Domain.permutationVanishingPolynomial @Vesta.BaseField
  domainGenerator = Domain.domainGenerator @Vesta.BaseField
  computeB0 = Domain.computeB0
  proofOraclesRec = vestaProofOracles
  proofOpeningPrechallenges = vestaProofOpeningPrechallenges
  proverIndexDomainLog2 = vestaProverIndexDomainLog2
  srsLagrangeCommitmentChunksAt = vestaSrsLagrangeCommitmentChunksAt
  srsBlindingGenerator = vestaSrsBlindingGenerator
  sigmaCommLast = vestaSigmaCommLast
  verifierIndexColumnComms = vestaVerifierIndexColumnComms

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

-- The `pallasProofOpeningLrVec` / `vestaProofOpeningLrVec` helpers were
-- dropped in Phase D — the equivalent `Vector rounds (LrPair c)` is now
-- the `opening.lr` field on the `ProofData` record (see `decodeProofData`
-- and the `OpeningProofData rounds c f` shape above), which does the
-- length check once at the FFI boundary via `Reflectable rounds Int`.

--------------------------------------------------------------------------------
-- Serde JSON codecs (formerly Pickles.Sideload.FFI)
--
-- Cross-stack-compatible with OCaml-emitted fixtures: same kimchi-side
-- Rust struct, same serde derive on both ends. VK hydration
-- (linearization / powers_of_alpha / w / permutation_vanishing_polynomial_m)
-- is automatic in kimchi-napi's `From<NapiPlonkVerifierIndex>`
-- conversion, so no explicit hydrate step on the PS side.

-- | Vesta-protocol (Pallas.G commitments) VK serde JSON. SRS is
-- | `#[serde(skip)]`; deserialize re-attaches the supplied CRS.
foreign import vestaVerifierIndexToSerdeJson :: VerifierIndex Pallas.G Vesta.BaseField -> String

foreign import vestaVerifierIndexFromSerdeJson
  :: String
  -> CRS Pallas.G
  -> VerifierIndex Pallas.G Vesta.BaseField

-- | Step-protocol (Vesta.G commitments) VK serde JSON. Symmetric to
-- | the wrap variant.
foreign import pallasVerifierIndexToSerdeJson :: VerifierIndex Vesta.G Pallas.BaseField -> String

foreign import pallasVerifierIndexFromSerdeJson
  :: String
  -> CRS Vesta.G
  -> VerifierIndex Vesta.G Pallas.BaseField

-- | Wrap proof (Pallas.G commitments) serde JSON. Public input is
-- | `#[serde(skip)]`; callers thread it separately at verify time.
foreign import vestaProofFromSerdeJson :: String -> Proof Pallas.G Vesta.BaseField

foreign import vestaProofToSerdeJson :: Proof Pallas.G Vesta.BaseField -> String

-- | Step proof (Vesta.G commitments) serde JSON.
foreign import pallasProofToSerdeJson :: Proof Vesta.G Pallas.BaseField -> String

foreign import pallasProofFromSerdeJson :: String -> Proof Vesta.G Pallas.BaseField
