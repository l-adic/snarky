-- | The step prover's out-of-circuit assembly. `expandDeferred`
-- | derives the step-field Type1 deferred values for one predecessor
-- | wrap proof; `expandProof` consumes that and builds the whole
-- | per-predecessor witness the step circuit reads.
-- |
-- | The scalar math is field-polymorphic and lives in
-- | `Pickles.Prove.Pure.Common`. What this module adds is the
-- | step-field and wrap-field instantiations, the sponge pipeline and
-- | the kimchi FFI calls.
module Pickles.Prove.Pure.Step
  (
    ExpandDeferredInput
  , ExpandDeferredOutput
  , expandDeferred
  , ExpandProofInput
  , ExpandProofOutput
  , PrevStatementWithHashes
  , expandProof
  ) where

import Prelude

import Data.Foldable (for_)
import Data.Newtype (over, unwrap)
import Data.Reflectable (class Reflectable)
import Data.Vector (Vector)
import Data.Vector as Vector
import Partial.Unsafe (unsafePartial)
import Pickles.DeferredValues (BranchData, PlonkInCircuit, PlonkMinimal, ScalarChallenge, UnfinalizedProof)
import Pickles.Field (StepField, WrapField)
import Pickles.IPA (bPoly)
import Pickles.Linearization.Types (LinearizationPoly)
import Pickles.PlonkChecks (absorbEvals)
import Pickles.Prove.Pure.Common (BulletproofBOutput, combinedInnerProductBatch, computeBpChalsAndB, derivePlonk, ftEval0)
import Pickles.Sponge (absorb, evalPureSpongeM, initialSponge, squeeze, squeezeScalarChallengePure)
import Pickles.Step.MessageHash (hashMessagesForNextStepProofPure)
import Pickles.Step.Types as Step
import Pickles.Types (AllocEvals, ChunkedCommitment(..), Evals, StepIPARounds, WrapIPARounds, WrapProofMessages(..), WrapProofOpening(..))
import Pickles.VerificationKey (StepVK)
import Pickles.Wrap.MessageHash (hashMessagesForNextWrapProofPureGeneral)
import Snarky.Backend.Kimchi.Proof (OraclesResult, Proof, domainGenerator, proofOpeningPrechallenges, proofOraclesRec, vestaChallengePolyCommitment, vestaProofCommitments, vestaProofData)
import Snarky.Backend.Kimchi.Types (VerifierIndex)
import Snarky.Backend.Kimchi.Util.Fatal (fromJust')
import Snarky.Circuit.DSL (F(..), UnChecked(..))
import Snarky.Circuit.DSL.SizedF (SizedF, unsafeFromField, unwrapF, wrapF)
import Snarky.Circuit.DSL.SizedF as SizedF
import Snarky.Circuit.Kimchi (SplitField, Type1, Type2, toFieldPure, toShifted)
import Snarky.Curves.Pasta (PallasG)
import Snarky.Data.EllipticCurve (AffinePoint(..), WeierstrassAffinePoint(..))

--------------------------------------------------------------------------------
-- expandDeferred
--------------------------------------------------------------------------------

-- | Input to `expandDeferred`: `n` previous proofs contributing one
-- | `b_poly` each to the batched combined inner product, over `d`
-- | step IPA rounds.
type ExpandDeferredInput n d =
  { zkRows :: Int
  , srsLengthLog2 :: Int

  -- Collapsed evals; the caller recombines chunks upstream via
  -- `collapseChunkedEvals`.
  , allEvals :: Evals StepField
  -- Public-input evaluation at `zeta`, as a chunk array — a singleton
  -- at `num_chunks = 1`. Passed unfolded because `ftEval0` folds it
  -- at `zeta^(2^srsLengthLog2)`.
  , pEval0Chunks :: Array StepField

  , oldBulletproofChallenges :: Vector n (Vector d (SizedF 128 (F StepField)))

  -- Raw deferred-values data from the wrap proof's proof state.
  , plonkMinimal :: PlonkMinimal (F StepField)
  , rawBulletproofChallenges :: Vector d (SizedF 128 (F StepField))
  , branchData :: BranchData StepField Boolean
  , spongeDigestBeforeEvaluations :: StepField

  -- Step domain data, derived by the caller from `branchData`.
  , generator :: StepField
  , domainLog2 :: Int
  , shifts :: Vector 7 StepField
  , vanishesOnZk :: StepField
  , omegaForLagrange :: { zkRows :: Boolean, offset :: Int } -> StepField

  -- Endo scalar for step-field challenge expansion.
  , endo :: StepField

  -- Linearization for the wrap circuit being expanded:
  -- `Pickles.Linearization.pallas`.
  , linearizationPoly :: LinearizationPoly StepField
  }

-- | Output of `expandDeferred`.
-- |
-- | * `plonk` — raw 128-bit challenges on alpha/beta/gamma/zeta,
-- |   Type1 shifts on perm/zetaToDomainSize/zetaToSrsLength.
-- | * `xi` — squeezed afresh from the main sponge, not the `xi`
-- |   carried in the input proof state; the verifier cross-checks
-- |   those two elsewhere.
-- | * `bulletproofChallenges` — this proof's own, endo-expanded.
-- | * `b` — Type1 shift of `b_poly(zeta) + r · b_poly(zetaw)` over
-- |   those same challenges.
type ExpandDeferredOutput d =
  { plonk :: PlonkInCircuit (F StepField) (Type1 (F StepField))
  , combinedInnerProduct :: Type1 (F StepField)
  , xi :: ScalarChallenge (F StepField)
  , bulletproofChallenges :: Vector d StepField
  , b :: Type1 (F StepField)
  , branchData :: BranchData StepField Boolean
  }

-- | The Type1-shifted deferred values `step_main` reads for one
-- | predecessor wrap proof.
expandDeferred
  :: forall n d
   . Reflectable d Int
  => ExpandDeferredInput n d
  -> ExpandDeferredOutput d
expandDeferred input =
  let
    expandChal :: SizedF 128 (F StepField) -> StepField
    expandChal c = toFieldPure (unwrapF c) input.endo

    derivePlonkInput =
      { plonkMinimal: input.plonkMinimal
      , w: map _.zeta (Vector.take @7 input.allEvals.witnessEvals)
      , sigma: map _.zeta input.allEvals.sigmaEvals
      , zZeta: input.allEvals.zEvals.zeta
      , zOmegaTimesZeta: input.allEvals.zEvals.omegaTimesZeta
      , shifts: input.shifts
      , generator: input.generator
      , domainLog2: input.domainLog2
      , zkRows: input.zkRows
      , srsLengthLog2: input.srsLengthLog2
      , endo: input.endo
      }

    derivedPlonk = derivePlonk derivePlonkInput

    ftEval0Input =
      { plonkMinimal: input.plonkMinimal
      , allEvals: input.allEvals
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

    -- Fed both to the challenges-digest sponge below and to the
    -- combined inner product's `b_poly`s.
    prevExpanded = map (map expandChal) input.oldBulletproofChallenges

    challengesDigest = evalPureSpongeM initialSponge do
      for_ prevExpanded \chals -> for_ chals absorb
      squeeze

    mainSqueezes
      :: { xiRaw :: SizedF 128 StepField, rRaw :: SizedF 128 StepField }
    mainSqueezes = evalPureSpongeM initialSponge do
      absorb input.spongeDigestBeforeEvaluations
      absorb challengesDigest
      absorbEvals input.allEvals
      xiRaw <- squeezeScalarChallengePure
      rRaw <- squeezeScalarChallengePure
      pure { xiRaw, rRaw }

    xiExpanded = toFieldPure mainSqueezes.xiRaw input.endo
    rExpanded = toFieldPure mainSqueezes.rRaw input.endo

    zetaField = toFieldPure (unwrapF input.plonkMinimal.zeta) input.endo
    zetaw = zetaField * input.generator

    cipInputRec =
      { allEvals: input.allEvals
      , publicEvals: input.allEvals.publicEvals
      , ftEval0: stepFtEval0
      , ftEval1: input.allEvals.ftEval1
      , oldBulletproofChallenges: prevExpanded
      , xi: xiExpanded
      , r: rExpanded
      , zeta: zetaField
      , zetaw
      }

    cipActual = combinedInnerProductBatch cipInputRec

    ownExpanded = map expandChal input.rawBulletproofChallenges

    bActual =
      bPoly ownExpanded zetaField
        + rExpanded * bPoly ownExpanded zetaw

    xiOutput = wrapF mainSqueezes.xiRaw
  in
    { plonk: derivedPlonk
    , combinedInnerProduct: toShifted (F cipActual)
    , xi: xiOutput
    , bulletproofChallenges: ownExpanded
    , b: toShifted (F bActual)
    , branchData: input.branchData
    }

--------------------------------------------------------------------------------
-- expandProof
--------------------------------------------------------------------------------

-- | Input to `expandProof`: one raw wrap proof plus its
-- | per-predecessor metadata.
-- |
-- | * `n` — previous proofs whose bp challenges feed the step-side
-- |   combined-inner-product batching.
-- | * `nwp` — padded challenge vectors on the wrap side; the caller
-- |   has already padded.
-- | * `wrapVkChunks` — chunk count of the step's wrap VK
-- |   (`dlogIndex`), left polymorphic rather than pinned to 1.
-- |
-- | Inner bp-challenge vector lengths are fixed per field at
-- | `StepIPARounds` / `WrapIPARounds`, by which IPA the challenges
-- | came from.
type ExpandProofInput n nwp wrapVkChunks =
  { -- False for dummy predecessors whose verification the step
    -- circuit elides.
    mustVerify :: Boolean

  -- ===== Inputs to `expandDeferred` =====

  -- Plonk-checks constants for the wrap circuit being expanded.
  , zkRows :: Int
  , srsLengthLog2 :: Int

  -- Evaluations from the wrap proof, collapsed upstream via
  -- `collapseChunkedEvals`.
  , allEvals :: Evals StepField
  , pEval0Chunks :: Array StepField

  , oldBulletproofChallenges :: Vector n (Vector StepIPARounds (SizedF 128 (F StepField)))

  -- Raw deferred-values data from the wrap proof's statement.
  , plonkMinimal :: PlonkMinimal (F StepField)
  , rawBulletproofChallenges :: Vector StepIPARounds (SizedF 128 (F StepField))
  , branchData :: BranchData StepField Boolean
  , spongeDigestBeforeEvaluations :: StepField

  -- Step domain data, derived by the caller from `branchData`.
  , stepDomainLog2 :: Int
  , stepGenerator :: StepField
  , stepShifts :: Vector 7 StepField
  , stepVanishesOnZk :: StepField
  , stepOmegaForLagrange :: { zkRows :: Boolean, offset :: Int } -> StepField

  -- Endo scalar for step-field challenge expansion.
  , endo :: StepField

  -- Linearization for the wrap circuit being expanded.
  , linearizationPoly :: LinearizationPoly StepField

  -- ===== Inputs to the step-side messages digest =====
  -- Everything `hashMessagesForNextStepProofPure` reads.

  -- The wrap circuit's VK commitments.
  , dlogIndex :: StepVK wrapVkChunks StepField
  -- The predecessor's app-state projected to field elements.
  , appStateFields :: Array StepField
  -- The previous proofs' challenge-polynomial commitments, one per
  -- entry in `oldBulletproofChallenges`.
  , stepPrevSgs :: Vector n (AffinePoint StepField)

  -- ===== Inputs to the wrap-side messages digest =====

  -- The wrap proof's own challenge-polynomial commitment: a Vesta
  -- point, so its coordinates are in `WrapField`.
  , wrapChallengePolynomialCommitment :: AffinePoint WrapField
  -- Previous bp challenges for the wrap-side hash, already expanded
  -- and padded to `nwp` by the caller.
  , wrapPaddedPrevChallenges :: Vector nwp (Vector WrapIPARounds WrapField)

  -- ===== Wrap-proof oracles (FFI) =====
  , wrapVerifierIndex :: VerifierIndex PallasG WrapField
  , wrapProof :: Proof PallasG WrapField
  , tockPublicInput :: Array WrapField
  -- One `(sg, expanded wrap-IPA challenges)` pair per padded
  -- predecessor. The `sg`s are Pallas points, so their coordinates
  -- are in `StepField` while the challenges are in `WrapField`.
  , wrapOraclesPrevChallenges ::
      Array
        { sgX :: StepField
        , sgY :: StepField
        , challenges :: Array WrapField
        }

  -- ===== New bulletproof challenges + b =====
  , wrapDomainLog2 :: Int
  , wrapEndo :: WrapField

  -- ===== Wrap-field Type2 deferred values (`unfinalized` output) =====
  , wrapEvals :: Evals WrapField
  , wrapPEval0Chunks :: Array WrapField
  , wrapShifts :: Vector 7 WrapField
  , wrapZkRows :: Int
  , wrapSrsLengthLog2 :: Int
  , wrapVanishesOnZk :: WrapField
  , wrapOmegaForLagrange :: { zkRows :: Boolean, offset :: Int } -> WrapField
  , wrapLinearizationPoly :: LinearizationPoly WrapField

  -- ===== `perProofWitness` =====

  -- The wrap proof's embedded `prev_evals`: evaluations of the step
  -- proof it wraps.
  , stepProofPrevEvals :: AllocEvals (F StepField)

  -- Step-side previous bp challenges, already endo-expanded and
  -- padded with dummies to `n` by the caller.
  , stepPrevChallenges :: Vector n (Vector StepIPARounds (F StepField))

  -- Padded step-side previous `sg` commitments — distinct from
  -- `stepPrevSgs`, which is unpadded and feeds the hash.
  , stepPrevSgsPadded :: Vector n (AffinePoint StepField)
  }

-- | Output of `expandProof`: the witness data the step circuit reads
-- | for one predecessor slot.
type ExpandProofOutput stepChunks =
  { sg :: AffinePoint StepField
  -- | Wrap-field values with same-field Type2 shifts. The cross-field
  -- | limb-packing happens downstream, when this is allocated as a
  -- | step-circuit witness.
  , unfinalized ::
      UnfinalizedProof
        WrapIPARounds
        (F WrapField)
        (Type2 (F WrapField))
        Boolean
  -- | Exposed for the `expand_proof.deferred.*` diagnostic traces.
  , deferredStep :: ExpandDeferredOutput StepIPARounds
  , rawPrechallenges :: Array WrapField
  -- | The public-input polynomial at `(zeta, zeta·omega)`, as
  -- | recomputed by the wrap oracles.
  , xHat :: { zeta :: WrapField, omegaTimesZeta :: WrapField }
  , perProofWitness ::
      Step.PerProofWitness
        stepChunks
        StepIPARounds
        WrapIPARounds
        (F StepField)
        (Type2 (SplitField (F StepField) Boolean))
        Boolean
  , actualWrapDomain :: Int
  , prevStatementWithHashes :: PrevStatementWithHashes
  -- | Raw wrap-proof oracle output.
  , oracles :: OraclesResult WrapField
  -- | Endo-expanded, unlike the raw challenges in `unfinalized`.
  , newBulletproofChallenges :: BulletproofBOutput WrapIPARounds WrapField
  }

-- | The two Poseidon digests carried across the hash boundary between
-- | the step prover and the wrap oracles: a step-field digest of the
-- | VK, app state and previous `(sg, bp_challenges)` pairs, and a
-- | wrap-field digest of the padded previous bp challenges and this
-- | proof's own `sg`.
type PrevStatementWithHashes =
  { messagesForNextStepProof :: F StepField
  , messagesForNextWrapProof :: F WrapField
  }

-- | Assemble one predecessor slot's step-circuit witness from a raw
-- | wrap proof.
expandProof
  :: forall @stepChunks n nwp wrapVkChunks
   . Reflectable stepChunks Int
  => Reflectable wrapVkChunks Int
  => ExpandProofInput n nwp wrapVkChunks
  -> ExpandProofOutput stepChunks
expandProof input =
  let
    -- ===== Step-field Type1 deferred values =====
    --
    -- One call where OCaml has two: OCaml derives the plonk scalars
    -- locally and then calls `expand_deferred`, which derives them
    -- again.
    deferredStep = expandDeferred
      { zkRows: input.zkRows
      , srsLengthLog2: input.srsLengthLog2
      , allEvals: input.allEvals
      , pEval0Chunks: input.pEval0Chunks
      , oldBulletproofChallenges: input.oldBulletproofChallenges
      , plonkMinimal: input.plonkMinimal
      , rawBulletproofChallenges: input.rawBulletproofChallenges
      , branchData: input.branchData
      , spongeDigestBeforeEvaluations: input.spongeDigestBeforeEvaluations
      , generator: input.stepGenerator
      , domainLog2: input.stepDomainLog2
      , shifts: input.stepShifts
      , vanishesOnZk: input.stepVanishesOnZk
      , omegaForLagrange: input.stepOmegaForLagrange
      , endo: input.endo
      , linearizationPoly: input.linearizationPoly
      }

    -- ===== Step-side messages digest =====
    stepPrevProofs =
      Vector.zipWith
        ( \sg raw ->
            { sg
            , expandedBpChallenges:
                map (\c -> toFieldPure (unwrapF c) input.endo) raw
            }
        )
        input.stepPrevSgs
        input.oldBulletproofChallenges

    messagesForNextStepProofDigest = hashMessagesForNextStepProofPure
      { stepVk: input.dlogIndex
      , appState: input.appStateFields
      , proofs: stepPrevProofs
      }

    -- ===== Wrap-side messages digest =====
    messagesForNextWrapProofDigest = hashMessagesForNextWrapProofPureGeneral
      { sg: input.wrapChallengePolynomialCommitment
      , paddedChallenges: input.wrapPaddedPrevChallenges
      }

    -- ===== Wrap-proof oracles =====
    oraclesResult = proofOraclesRec input.wrapVerifierIndex
      { proof: input.wrapProof
      , publicInput: input.tockPublicInput
      , prevChallenges: input.wrapOraclesPrevChallenges
      }

    -- ===== New bulletproof challenges + b =====
    --
    -- `unsafeFromField` is sound here because kimchi's
    -- `ScalarChallenge` contract bounds each prechallenge at 128
    -- bits.
    rawPrechalsVec = map (unsafePartial unsafeFromField)
      ( fromJust' "proofOpeningPrechallenges: expected Vector WrapIPARounds (=15)"
          ( Vector.toVector @WrapIPARounds
              ( proofOpeningPrechallenges input.wrapVerifierIndex
                  { proof: input.wrapProof
                  , publicInput: input.tockPublicInput
                  , prevChallenges: input.wrapOraclesPrevChallenges
                  }
              )
          )
      )

    wrapGen = domainGenerator input.wrapDomainLog2

    wrapZetaw = oraclesResult.zeta * wrapGen

    newBpResult = computeBpChalsAndB
      { rawPrechallenges: rawPrechalsVec
      , endo: input.wrapEndo
      , zeta: oraclesResult.zeta
      , zetaw: wrapZetaw
      , r: oraclesResult.u
      }

    wrapProofData = vestaProofData @WrapIPARounds input.wrapProof

    challengePolynomialCommitment =
      if input.mustVerify then
        wrapProofData.opening.sg
      else
        vestaChallengePolyCommitment input.wrapVerifierIndex
          (Vector.toUnfoldable newBpResult.chals)

    -- ===== Wrap-field Type2 deferred values =====
    --
    -- The same `Common` helpers as the step-field side above; only
    -- the field and the linearization change.

    wrapPlonkMinimal =
      { alpha: wrapF oraclesResult.alphaChal
      , beta: wrapF oraclesResult.beta
      , gamma: wrapF oraclesResult.gamma
      , zeta: wrapF oraclesResult.zetaChal
      }

    wrapDerivePlonkInput =
      { plonkMinimal: wrapPlonkMinimal
      , w: map _.zeta (Vector.take @7 input.wrapEvals.witnessEvals)
      , sigma: map _.zeta input.wrapEvals.sigmaEvals
      , zZeta: input.wrapEvals.zEvals.zeta
      , zOmegaTimesZeta: input.wrapEvals.zEvals.omegaTimesZeta
      , shifts: input.wrapShifts
      , generator: wrapGen
      , domainLog2: input.wrapDomainLog2
      , zkRows: input.wrapZkRows
      , srsLengthLog2: input.wrapSrsLengthLog2
      , endo: input.wrapEndo
      }

    wrapPlonkDerived = derivePlonk wrapDerivePlonkInput

    wrapFtEval0Input =
      { plonkMinimal: wrapPlonkMinimal
      , allEvals: input.wrapEvals
      , pEval0Chunks: input.wrapPEval0Chunks
      , shifts: input.wrapShifts
      , generator: wrapGen
      , domainLog2: input.wrapDomainLog2
      , zkRows: input.wrapZkRows
      , srsLengthLog2: input.wrapSrsLengthLog2
      , endo: input.wrapEndo
      , vanishesOnZk: input.wrapVanishesOnZk
      , omegaForLagrange: input.wrapOmegaForLagrange
      , linearizationPoly: input.wrapLinearizationPoly
      }

    wrapFtEval0 = ftEval0 wrapFtEval0Input

    -- `oracles.v` is xi and `oracles.u` is r, both already
    -- endo-expanded by the FFI.
    wrapCipInput =
      { allEvals: input.wrapEvals
      -- The oracle's recomputed public eval, not
      -- `proofData.evals.public`: a dummy proof carries no wire
      -- evaluation, so that field holds a placeholder.
      , publicEvals: oraclesResult.publicEvals
      , ftEval0: wrapFtEval0
      , ftEval1: oraclesResult.ftEval1
      , oldBulletproofChallenges: input.wrapPaddedPrevChallenges
      , xi: oraclesResult.v
      , r: oraclesResult.u
      , zeta: oraclesResult.zeta
      , zetaw: wrapZetaw
      }

    wrapCip = combinedInnerProductBatch wrapCipInput

    -- alpha/beta/gamma/zeta must stay in their raw 128-bit form: the
    -- wrap verifier's `assertPlonkChallenges` matches them against
    -- its own in-circuit sponge squeezes.
    wrapPlonkWithRawChals = wrapPlonkDerived
      { alpha = wrapPlonkMinimal.alpha
      , beta = wrapPlonkMinimal.beta
      , gamma = wrapPlonkMinimal.gamma
      , zeta = wrapPlonkMinimal.zeta
      }

    wrapUnfinalized
      :: UnfinalizedProof WrapIPARounds (F WrapField) (Type2 (F WrapField)) Boolean
    wrapUnfinalized =
      { deferredValues:
          { plonk: wrapPlonkWithRawChals
          , combinedInnerProduct: toShifted (F wrapCip)
          , xi: wrapF oraclesResult.vChal
          , bulletproofChallenges: map wrapF rawPrechalsVec
          , b: toShifted (F newBpResult.b)
          }
      , shouldFinalize: input.mustVerify
      , spongeDigestBeforeEvaluations: F oraclesResult.fqDigest
      }

    -- ===== `perProofWitness` =====

    mkPallasPt
      :: AffinePoint StepField
      -> WeierstrassAffinePoint PallasG (F StepField)
    mkPallasPt (AffinePoint pt) = WeierstrassAffinePoint { x: F pt.x, y: F pt.y }

    wrapCommits = vestaProofCommitments @stepChunks input.wrapProof

    messages
      :: WrapProofMessages stepChunks (WeierstrassAffinePoint PallasG (F StepField))
    messages = WrapProofMessages
      { wComm: map (over ChunkedCommitment (map mkPallasPt)) wrapCommits.wComm
      , zComm: over ChunkedCommitment (map mkPallasPt) wrapCommits.zComm
      , tComm: map (over ChunkedCommitment (map mkPallasPt)) wrapCommits.tComm
      }

    -- The kimchi opening, with `sg` replaced by the
    -- `challengePolynomialCommitment` computed above.
    opening
      :: WrapProofOpening
           WrapIPARounds
           (WeierstrassAffinePoint PallasG (F StepField))
           (Type2 (SplitField (F StepField) Boolean))
    opening = WrapProofOpening
      { lr: map (\pair -> { l: mkPallasPt pair.l, r: mkPallasPt pair.r })
          wrapProofData.opening.lr
      , z1: toShifted (F wrapProofData.opening.z1)
      , z2: toShifted (F wrapProofData.opening.z2)
      , delta: mkPallasPt wrapProofData.opening.delta
      , sg: mkPallasPt challengePolynomialCommitment
      }

    wrapProofKimchi
      :: Step.WrapProof
           WrapIPARounds
           stepChunks
           (WeierstrassAffinePoint PallasG (F StepField))
           (Type2 (SplitField (F StepField) Boolean))
    wrapProofKimchi = Step.WrapProof
      { messages
      , opening
      }

    stepPlonkDerived = deferredStep.plonk

    branchData = Step.AllocBranchData
      { domainLog2: F deferredStep.branchData.domainLog2
      , proofsVerifiedMask: deferredStep.branchData.proofsVerifiedMask
      }

    proofState = Step.ProofState
      -- The five shifted slots store the inner value — `unwrap`, not
      -- `fromShifted`. Both give an `F StepField`, so swapping them
      -- compiles and silently changes the encoding.
      { fopState: Step.FopProofState
          { combinedInnerProduct: unwrap deferredStep.combinedInnerProduct
          , b: unwrap deferredStep.b
          , zetaToSrsLength: unwrap stepPlonkDerived.zetaToSrsLength
          , zetaToDomainSize: unwrap stepPlonkDerived.zetaToDomainSize
          , perm: unwrap stepPlonkDerived.perm
          , spongeDigest: F input.spongeDigestBeforeEvaluations
          , beta: UnChecked stepPlonkDerived.beta
          , gamma: UnChecked stepPlonkDerived.gamma
          , alpha: UnChecked stepPlonkDerived.alpha
          , zeta: UnChecked stepPlonkDerived.zeta
          , xi: UnChecked deferredStep.xi
          , bulletproofChallenges: map UnChecked input.rawBulletproofChallenges
          }
      , branchData
      }

    perProofWitness
      :: Step.PerProofWitness
           stepChunks
           StepIPARounds
           WrapIPARounds
           (F StepField)
           (Type2 (SplitField (F StepField) Boolean))
           Boolean
    perProofWitness = Step.PerProofWitness
      { wrapProof: wrapProofKimchi
      , proofState
      , prevEvals: input.stepProofPrevEvals
      , prevChallenges: Vector.toUnfoldable (map UnChecked input.stepPrevChallenges)
      , prevSgs: Vector.toUnfoldable (map mkPallasPt input.stepPrevSgsPadded)
      }
  in
    { sg: challengePolynomialCommitment
    , unfinalized: wrapUnfinalized
    , deferredStep: deferredStep
    , rawPrechallenges: Vector.toUnfoldable (map SizedF.toField rawPrechalsVec)
    -- The oracle's recomputed public eval, as in `wrapCipInput`.
    , xHat: oraclesResult.publicEvals
    , perProofWitness
    , actualWrapDomain: input.wrapDomainLog2
    , prevStatementWithHashes:
        { messagesForNextStepProof: F messagesForNextStepProofDigest
        , messagesForNextWrapProof: F messagesForNextWrapProofDigest
        }
    , oracles: oraclesResult
    , newBulletproofChallenges: newBpResult
    }
