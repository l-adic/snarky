-- | The wrap prover's out-of-circuit assembly:
-- | `wrapComputeDeferredValues` derives the step-field deferred values
-- | from a freshly-minted step proof, and `assembleWrapMainInput`
-- | cross-field packs them into `wrap_main`'s public input.
-- |
-- | Everything up to that packing stays in the step field and Type1
-- | shifts. The scalar math itself is field-polymorphic and lives in
-- | `Pickles.Prove.Pure.Common`.
module Pickles.Prove.Pure.Wrap
  ( WrapDeferredValuesInput
  , WrapDeferredValuesOutput
  , wrapComputeDeferredValues
  , AssembleWrapMainInputInput
  , assembleWrapMainInput
  , branchDataMaskWidth
  , revOnesVector
  , packBranchDataWrap
  ) where

import Prelude

import Data.Array as Array
import Data.Fin (getFinite, unsafeFinite)
import Data.Vector (Vector, (!!), (:<))
import Data.Vector as Vector
import Partial.Unsafe (unsafePartial)
import Pickles.DeferredValues (BranchData, PlonkInCircuit, ScalarChallenge)
import Pickles.Field (StepField, WrapField)
import Pickles.Linearization.Types (LinearizationPoly)
import Pickles.PlonkChecks (collapseChunkedEvals)
import Pickles.Prove.Pure.Common (BulletproofBOutput, combinedInnerProductBatchChunked, computeBpChalsAndB, crossFieldDigest, derivePlonk, ftEval0)
import Pickles.Types (ChunkedEvals, StepIPARounds)
import Pickles.Wrap.Types as Wrap
import Snarky.Backend.Kimchi.Proof (OraclesResult, Proof, pallasProofData, proofOpeningPrechallenges, proofOraclesRec)
import Snarky.Backend.Kimchi.Types (VerifierIndex)
import Snarky.Backend.Kimchi.Util.Fatal (fromJust')
import Snarky.Circuit.DSL (F(..), UnChecked(..))
import Snarky.Circuit.DSL.SizedF (SizedF, coerceViaBits, unsafeFromField, unwrapF, wrapF)
import Snarky.Circuit.Kimchi (Type1, fromShifted, toShifted)
import Snarky.Curves.Class (fromInt)
import Snarky.Curves.Vesta as Vesta
import Snarky.Data.EllipticCurve (AffinePoint(..))

--------------------------------------------------------------------------------
-- Input / output
--------------------------------------------------------------------------------

-- | Input to `wrapComputeDeferredValues`. `n` is the number of
-- | previous proofs that fed into the step proof being wrapped; their
-- | `sg`s and already-expanded bp challenges go into the kimchi
-- | oracle call and into the combined inner product.
-- |
-- | The step proof's commitments are on Vesta, so `prevSgs`
-- | coordinates are in `WrapField` while the bp challenges carried
-- | alongside them are in `StepField`.
type WrapDeferredValuesInput n =
  { -- ===== The step proof being wrapped and its context. =====
    proof :: Proof Vesta.G StepField
  , verifierIndex :: VerifierIndex Vesta.G StepField
  , publicInput :: Array StepField

  -- ===== Polynomial evaluations from the step proof. =====
  --
  -- Chunked; `collapseChunkedEvals` below derives the collapsed form
  -- that `ftEval0` and `derivePlonk` need, once zeta and zetaw are in
  -- scope.
  , chunkedEvals :: ChunkedEvals StepField
  , pEval0Chunks :: Array StepField

  -- ===== Step domain info. =====
  , domainLog2 :: Int
  , zkRows :: Int
  , srsLengthLog2 :: Int
  , generator :: StepField
  , shifts :: Vector 7 StepField
  , vanishesOnZk :: StepField
  , omegaForLagrange :: { zkRows :: Boolean, offset :: Int } -> StepField

  -- ===== Endo + linearization. =====
  --
  -- `endo` expands raw 128-bit plonk and opening challenges to full
  -- step-field values, and feeds the scalar environment inside
  -- `ftEval0`.
  , endo :: StepField
  -- `Pickles.Linearization.pallas`.
  , linearizationPoly :: LinearizationPoly StepField

  -- ===== Previous-proof data. =====
  , prevSgs :: Vector n (AffinePoint WrapField)
  -- Already endo-expanded by the caller.
  , prevChallenges :: Vector n (Vector StepIPARounds StepField)

  -- ===== Output packaging. =====
  --
  -- Goes straight into the output `BranchData`. The caller passes the
  -- two-bit mask explicitly because PureScript cannot reflect the
  -- type-level `n` at runtime; `revOnesVector` builds it.
  , proofsVerifiedMask :: Vector 2 Boolean
  }

-- | Output of `wrapComputeDeferredValues`.
-- |
-- | * `plonk`, `combinedInnerProduct`, `xi`,
-- |   `bulletproofPrechallenges`, `b` and `branchData` are the
-- |   step-field Type1 deferred values. The prechallenges are stored
-- |   raw, at 128 bits.
-- | * `xHatEvals` — the public-input polynomial at
-- |   `(zeta, zeta·omega)`.
-- | * `oracles` — the raw kimchi result, exposed so callers can reuse
-- |   it without re-running the FFI.
-- | * `newBulletproofChallenges` — the same prechallenges
-- |   endo-expanded, plus `b`. Read this wherever the expanded field
-- |   values are wanted rather than the raw form.
type WrapDeferredValuesOutput =
  { plonk :: PlonkInCircuit (F StepField) (Type1 (F StepField))
  , combinedInnerProduct :: Type1 (F StepField)
  , xi :: ScalarChallenge (F StepField)
  , bulletproofPrechallenges :: Vector StepIPARounds (ScalarChallenge (F StepField))
  , b :: Type1 (F StepField)
  , branchData :: BranchData StepField Boolean
  , xHatEvals :: { zeta :: StepField, omegaTimesZeta :: StepField }
  , spongeDigestBeforeEvaluations :: StepField
  , oracles :: OraclesResult StepField
  , newBulletproofChallenges :: BulletproofBOutput StepIPARounds StepField
  }

--------------------------------------------------------------------------------
-- wrapComputeDeferredValues
--------------------------------------------------------------------------------

-- | The step-field Type1 deferred values the wrap circuit feeds into
-- | `wrap_main`, together with the `x_hat_evals` and sponge-digest
-- | hints, for one freshly-minted step proof and its predecessor
-- | `(sg, expanded bp challenges)` pairs.
wrapComputeDeferredValues
  :: forall n
   . WrapDeferredValuesInput n
  -> WrapDeferredValuesOutput
wrapComputeDeferredValues input =
  let
    -- ===== kimchi oracles (recursive variant) =====
    --
    -- Kimchi absorbs each previous challenge polynomial before
    -- replaying the transcript.
    prevChallengeList
      :: Array
           { sgX :: WrapField
           , sgY :: WrapField
           , challenges :: Array StepField
           }
    prevChallengeList =
      Array.fromFoldable
        ( Vector.zipWith
            ( \(AffinePoint sg) chals ->
                { sgX: sg.x
                , sgY: sg.y
                , challenges: Array.fromFoldable chals
                }
            )
            input.prevSgs
            input.prevChallenges
        )

    oraclesResult = proofOraclesRec input.verifierIndex
      { proof: input.proof
      , publicInput: input.publicInput
      , prevChallenges: prevChallengeList
      }

    -- The oracle's recomputed public eval, not
    -- `proofData.evals.public`. No chunk collapse: the public
    -- polynomial has degree below the domain size, so it is never
    -- split, and the oracle returns the one chunk.
    xHatEvals = oraclesResult.publicEvals

    -- Raw 128-bit challenges; `derivePlonk` endo-expands them
    -- internally.
    stepPlonkMinimal =
      { alpha: wrapF oraclesResult.alphaChal
      , beta: wrapF oraclesResult.beta
      , gamma: wrapF oraclesResult.gamma
      , zeta: wrapF oraclesResult.zetaChal
      }

    zetaField = oraclesResult.zeta

    zetaw = zetaField * input.generator

    -- Collapsed by Horner at `zeta^(2^srsLengthLog2)`, for `ftEval0`
    -- and `derivePlonk`; the combined inner product below takes the
    -- chunked form instead.
    collapsedEvals = collapseChunkedEvals
      { rounds: input.srsLengthLog2
      , zeta: zetaField
      , zetaOmega: zetaw
      }
      input.chunkedEvals

    derivePlonkInput =
      { plonkMinimal: stepPlonkMinimal
      , w: map _.zeta (Vector.take @7 collapsedEvals.witnessEvals)
      , sigma: map _.zeta collapsedEvals.sigmaEvals
      , zZeta: collapsedEvals.zEvals.zeta
      , zOmegaTimesZeta: collapsedEvals.zEvals.omegaTimesZeta
      , shifts: input.shifts
      , generator: input.generator
      , domainLog2: input.domainLog2
      , zkRows: input.zkRows
      , srsLengthLog2: input.srsLengthLog2
      , endo: input.endo
      }

    stepPlonkDerived = derivePlonk derivePlonkInput

    ftEval0Input =
      { plonkMinimal: stepPlonkMinimal
      , allEvals: collapsedEvals
      , pEval0Chunks: input.pEval0Chunks
      , shifts: input.shifts
      , generator: input.generator
      , domainLog2: input.domainLog2
      , zkRows: input.zkRows
      , srsLengthLog2: input.srsLengthLog2
      , endo: input.endo
      , vanishesOnZk: input.vanishesOnZk
      , omegaForLagrange: input.omegaForLagrange
      , linearizationPoly: input.linearizationPoly
      }

    stepFtEval0 = ftEval0 ftEval0Input

    cipInput =
      { allEvals: input.chunkedEvals
      , publicEvals: input.chunkedEvals.publicEvals
      , ftEval0: stepFtEval0
      , ftEval1: (pallasProofData @StepIPARounds input.proof).evals.ftEval1
      , oldBulletproofChallenges: input.prevChallenges
      , xi: oraclesResult.v
      , r: oraclesResult.u
      , zeta: zetaField
      , zetaw
      }

    cipActual = combinedInnerProductBatchChunked cipInput

    -- `unsafeFromField` is sound here because kimchi's
    -- `ScalarChallenge` contract bounds each prechallenge at 128 bits.
    rawPrechalsVec = map (unsafePartial unsafeFromField)
      ( fromJust' "proofOpeningPrechallenges: expected Vector StepIPARounds (=16)"
          ( Vector.toVector @StepIPARounds
              ( proofOpeningPrechallenges input.verifierIndex
                  { proof: input.proof
                  , publicInput: input.publicInput
                  , prevChallenges: prevChallengeList
                  }
              )
          )
      )

    newBpResult = computeBpChalsAndB
      { rawPrechallenges: rawPrechalsVec
      , endo: input.endo
      , zeta: zetaField
      , zetaw
      , r: oraclesResult.u
      }

    branchData =
      { domainLog2: fromInt input.domainLog2
      , proofsVerifiedMask: input.proofsVerifiedMask
      }
  in
    { plonk: stepPlonkDerived
    , combinedInnerProduct: toShifted (F cipActual)
    , xi: wrapF oraclesResult.vChal
    , bulletproofPrechallenges: map wrapF rawPrechalsVec
    , b: toShifted (F newBpResult.b)
    , branchData
    , xHatEvals
    , spongeDigestBeforeEvaluations: oraclesResult.fqDigest
    , oracles: oraclesResult
    , newBulletproofChallenges: newBpResult
    }

--------------------------------------------------------------------------------
-- Statement assembly
--------------------------------------------------------------------------------

-- | Input to `assembleWrapMainInput`. The two digests are already
-- | hashed by the caller, with
-- | `Pickles.Step.MessageHash.hashMessagesForNextStepProofPure` and
-- | `Pickles.Wrap.MessageHash.hashMessagesForNextWrapProofPureGeneral`.
type AssembleWrapMainInputInput =
  { deferredValues :: WrapDeferredValuesOutput
  , messagesForNextStepProofDigest :: StepField
  , messagesForNextWrapProofDigest :: WrapField
  }

-- | Re-shift a same-field step Type1 value into the cross-field wrap
-- | Type1 representation the wrap statement stores. The intermediate
-- | annotation is what picks the two `Shifted` instances apart.
crossFieldType1Step :: Type1 (F StepField) -> Type1 (F WrapField)
crossFieldType1Step t =
  toShifted (fromShifted t :: F StepField)

-- | Coerce a `SizedF 128 (F StepField)` to `SizedF 128 (F WrapField)`
-- | via bit decomposition. Safe because 128 < 255 = field size.
crossFieldSized128
  :: SizedF 128 (F StepField)
  -> SizedF 128 (F WrapField)
crossFieldSized128 s = wrapF (coerceViaBits (unwrapF s))

-- | Width of the packed proofs-verified mask: the global pickles cap
-- | on `max_proofs_verified`, to which the mask is padded whatever a
-- | particular circuit's own `mpv` is. Distinct from
-- | `Pickles.Types.MaxProofsVerified` and `Pickles.Types.PaddedLength`
-- | — all three are 2, with independent meanings.
branchDataMaskWidth :: Int
branchDataMaskWidth = 2

-- | The `proofsVerifiedMask` for a given `mostRecentWidth`: entry `i`
-- | is true iff `i >= branchDataMaskWidth - mostRecentWidth`, so
-- | `0 → [F, F]`, `1 → [F, T]`, `2 → [T, T]`.
-- |
-- | `Pickles.Wrap.Main` builds the same mask in-circuit under a
-- | different bit convention that packs to the same value.
revOnesVector :: Int -> Vector 2 Boolean
revOnesVector mostRecentWidth =
  Vector.generate @2 \i ->
    getFinite i >= branchDataMaskWidth - mostRecentWidth

-- | The mask and domain log2 packed into one wrap-field element, as
-- | `4 · domainLog2 + mask[0] + 2 · mask[1]`.
packBranchDataWrap
  :: BranchData StepField Boolean
  -> WrapField
packBranchDataWrap { domainLog2, proofsVerifiedMask } =
  let
    boolToField :: Boolean -> WrapField
    boolToField b = if b then one else zero

    m0 = boolToField (proofsVerifiedMask !! unsafeFinite @2 0)

    m1 = boolToField (proofsVerifiedMask !! unsafeFinite @2 1)

    two = fromInt 2

    four = fromInt 4

    log2W = crossFieldDigest domainLog2
  in
    four * log2W + m0 + two * m1

-- | The public input `wrap_main` consumes, built from the step-field
-- | deferred values and the two message hashes.
-- |
-- | The slot order below is fixed by the wrap statement's encoding,
-- | not by this code.
-- |
-- | Every cross-field conversion happens here, keeping
-- | `wrapComputeDeferredValues` wholly in the step field.
assembleWrapMainInput
  :: AssembleWrapMainInputInput
  -> Wrap.StatementPacked StepIPARounds (Type1 (F WrapField)) (F WrapField) Boolean
assembleWrapMainInput input =
  let
    dv = input.deferredValues

    fpFields =
      crossFieldType1Step dv.combinedInnerProduct
        :< crossFieldType1Step dv.b
        :< crossFieldType1Step dv.plonk.zetaToSrsLength
        :< crossFieldType1Step dv.plonk.zetaToDomainSize
        :< crossFieldType1Step dv.plonk.perm
        :< Vector.nil

    challenges =
      UnChecked (crossFieldSized128 dv.plonk.beta)
        :< UnChecked (crossFieldSized128 dv.plonk.gamma)
        :< Vector.nil

    scalarChallenges =
      UnChecked (crossFieldSized128 dv.plonk.alpha)
        :< UnChecked (crossFieldSized128 dv.plonk.zeta)
        :< UnChecked (crossFieldSized128 dv.xi)
        :< Vector.nil

    digests = map F
      ( crossFieldDigest dv.spongeDigestBeforeEvaluations
          :< input.messagesForNextWrapProofDigest
          :< crossFieldDigest input.messagesForNextStepProofDigest
          :< Vector.nil
      )

    bulletproofChallenges
      :: Vector StepIPARounds (UnChecked (SizedF 128 (F WrapField)))
    bulletproofChallenges =
      map (UnChecked <<< crossFieldSized128) dv.bulletproofPrechallenges

    branchData = F (packBranchDataWrap dv.branchData)

    -- The feature-flag and lookup slots are allocated but always
    -- zero: no feature flags are set and lookup is off.
    featureFlags = Vector.replicate zero
  in
    Wrap.StatementPacked
      { fpFields
      , challenges
      , scalarChallenges
      , digests
      , bulletproofChallenges
      , branchData
      , featureFlags
      , lookupOptFlag: zero
      , lookupOptScalarChallenge: zero
      }

