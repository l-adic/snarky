-- | Prover-side glue for `Pickles.Step.Main.stepMain`: the builders
-- | that assemble the `StepAdvice` its witness generation reads, and
-- | the compile and solve driver around them. Sister module to
-- | `Pickles.Prove.Wrap`.
-- |
-- | Everything here is polymorphic in `prevsSpec`, the type-level
-- | per-slot `max_proofs_verified` list, so heterogeneous-prev rules
-- | get a distinct shape per slot. The commitment curve is pinned to
-- | `PallasG` and the field to `StepField` (= `Vesta.ScalarField` =
-- | `Pallas.BaseField`), because a step circuit verifies a wrap proof,
-- | whose commitments live on Pallas — structural for the Pasta cycle,
-- | not specific to a rule.
module Pickles.Prove.Step
  ( StepBranchData
  , BuildStepAdviceInput
  , BuildSlotAdviceInput
  , extractWrapVKCommsAdvice
  , dummyWrapTockPublicInput
  , StepRule
  , StepRuleAt
  , StepCompileResult
  , StepProveResult
  , module Pickles.Step.Advice
  , StepProveContext
  , SlotAdviceContrib
  , buildSlotAdvice
  , buildStepAdvice
  , stepCompile
  , preComputeStepDomainLog2
  , stepSolveAndProve
  , mkDummyMsgWrapHash
  ) where

import Prelude

import Data.Array (concatMap)
import Data.Array as Array
import Data.Either (Either(..))
import Data.Fin (getFinite)
import Data.Foldable (for_)
import Data.FoldableWithIndex (forWithIndex_)
import Data.Lazy as Lazy
import Data.Maybe (Maybe(..), fromJust, maybe)
import Data.Newtype (over, un, unwrap)
import Data.Reflectable (class Reflectable, reflectType)
import Data.String (Pattern(..), Replacement(..))
import Data.String as String
import Data.Traversable (traverse)
import Data.Tuple (Tuple(..))
import Data.Vector (Vector, (:<))
import Data.Vector as Vector
import Effect (Effect)
import Effect.Ref as Ref
import Effect.Unsafe (unsafePerformEffect)
import Node.Encoding (Encoding(..))
import Node.FS.Sync as FS
import Node.Process as Process
import Partial.Unsafe (unsafePartial)
import Pickles.Constants (zkRowsForNumChunks)
import Pickles.DeferredValues (BranchData) as VT
import Pickles.DeferredValues (UnfinalizedProof)
import Pickles.Dummy (dummyIpaChallenges)
import Pickles.Field (StepField, WrapField)
import Pickles.Linearization (pallas, vesta) as Linearization
import Pickles.Linearization.FFI (PointEval) as LFFI
import Pickles.Linearization.FFI (domainGenerator, domainShifts)
import Pickles.PlonkChecks (collapsePointEval)
import Pickles.Prove.Pure.Common (crossFieldDigest)
import Pickles.Prove.Pure.Step (expandProof) as PureStep
import Pickles.Prove.Pure.Wrap (packBranchDataWrap, revOnesVector)
import Pickles.Sideload.Advice (class MkUnitVkCarrier, class SideloadedVKsCarrier, mkUnitVkCarrier)
import Pickles.Sideload.Bundle (SlotProveVk) as SideloadBundle
import Pickles.Sideload.VerificationKey (VerificationKey) as SLVK
import Pickles.Step.Advice (StepAdvice(..))
import Pickles.Step.Dummy (BaseCaseDummies, computeDummySgValues) as Dummy
import Pickles.Step.Dummy (baseCaseDummies, stepDummyUnfinalizedProof, wrapDomainLog2ForProofsVerified, wrapDummyUnfinalizedProof)
import Pickles.Step.Main (class BuildSlotVkSources, RuleOutput, StepMainSrsData, stepMain)
import Pickles.Step.MessageHash (hashMessagesForNextStepProofPure, hashMessagesForNextStepProofPureTraced)
import Pickles.Step.Slots (class SlotStatementsCarrier, class StepSlotsCarrier, class StepSlotsTyp, replicateStepSlotsCarrier)
import Pickles.Step.Types as Step
import Pickles.Trace as Trace
import Pickles.Types (AllocEvals(..), ChunkedCommitment(..), Evals, PaddedLength, PerProofUnfinalized(..), StepIPARounds, WrapIPARounds, WrapProofMessages(..), WrapProofOpening(..), WrapVkChunks)
import Pickles.VerificationKey (VerificationKey(..), extractWrapVKForStepHash, vestaVerifierIndexCommitments)
import Pickles.Wrap.MessageHash (hashMessagesForNextWrapProofPureGeneral)
import Prim.Int (class Add, class Compare, class Mul)
import Prim.Ordering (LT)
import Safe.Coerce (coerce)
import Snarky.Backend.Advice (AdviceHandler)
import Snarky.Backend.Assignments as Assignments
import Snarky.Backend.Builder (CircuitBuilderState, Labeled, constraintsToArray)
import Snarky.Backend.Compile (SolverT, compile, makeSolver')
import Snarky.Backend.Kimchi (makeConstraintSystemWithPrevChallenges, makeWitness)
import Snarky.Backend.Kimchi.Class (class CircuitGateConstructor, createProverIndex, createVerifierIndex, crsSize, gatesToJson)
import Snarky.Backend.Kimchi.Proof (Proof, pallasCreateProofWithPrev, permutationVanishingPolynomial, proofOpeningPrechallenges, proofOraclesRec, vestaProofCommitments, vestaProofData)
import Snarky.Backend.Kimchi.ProofCache (ProofCache, getPallasProof, setPallasProof)
import Snarky.Backend.Kimchi.Types (CRS, Gate, ProverIndex, VerifierIndex)
import Snarky.Circuit.CVar (EvaluationError(..), Variable)
import Snarky.Circuit.CVar as CVar
import Snarky.Circuit.DSL (AsProver, BoolVar, F(..), FVar, SizedF, Snarky, UnChecked(..), coerceViaBits)
import Snarky.Circuit.DSL.Monad (class CheckedType)
import Snarky.Circuit.DSL.SizedF (toField, unwrapF, wrapF) as SizedF
import Snarky.Circuit.Kimchi (toFieldPure)
import Snarky.Circuit.Types (class CircuitType, valueToFields)
import Snarky.Constraint.Kimchi (KimchiConstraint, KimchiGate)
import Snarky.Constraint.Kimchi.Types (AuxState(..), KimchiRow, toKimchiRows)
import Snarky.Curves.Class (EndoScalar(..), endoScalar)
import Snarky.Curves.Class (fromInt, generator, toAffine) as Curves
import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Pasta (PallasG, VestaG)
import Snarky.Data.EllipticCurve (AffinePoint(..), WeierstrassAffinePoint(..))
import Snarky.Types.Shifted (SplitField(..), Type1(..), Type2(..), fromShifted, toShifted)
import Type.Proxy (Proxy(..))
import Unsafe.Coerce (unsafeCoerce)

--------------------------------------------------------------------------------
-- Advice
--------------------------------------------------------------------------------

-- | One prev proof's branch data: the step domain log2 it was proved
-- | at, and the two mask bits saying which prev-proof slot is active.
-- | The step statement carries them packed as
-- | `4 * domainLog2 + mask0 + 2 * mask1`.
type StepBranchData =
  { domainLog2 :: F StepField
  , mask0 :: Boolean
  , mask1 :: Boolean
  }

--------------------------------------------------------------------------------
-- Base-case advice builder
--------------------------------------------------------------------------------

-- | Inputs to `buildStepAdvice`; every other field of the advice is
-- | protocol-constant dummy data from `Pickles.Dummy`. The rule's
-- | `max_proofs_verified` is not among them: it is the type-level
-- | `len`, reified where an `Int` is needed.
type BuildStepAdviceInput inputVal valCarrier vkCarrier =
  { -- | Value bound to the step circuit's public input. Polymorphic in
    -- | `inputVal`, so a rule whose input typ is not `Field.typ` can
    -- | bind a multi-field record.
    publicInput :: inputVal

  -- | The prev rule's step domain log2, its wrap statement's
  -- | `branch_data.domain_log2`. Distinct from the step circuit's own
  -- | kimchi domain, which kimchi determines at proof-creation time
  -- | rather than reading from advice.
  , stepDomainLog2 :: Int

  -- | Heterogeneous per-slot prev statements, shaped by `prevsSpec`
  -- | through `SlotStatementsCarrier`. Each slot's value is the prev's
  -- | `StatementIO inputVal outputVal`; on the base case the caller
  -- | still supplies an inhabitant of the right type, whose value is
  -- | irrelevant when `proofMustVerify` is false for that slot.
  , prevAppStates :: valCarrier

  -- | Spec-indexed runtime side-loaded VK carrier: compiled slots
  -- | contribute `Unit`, side-loaded slots a runtime verification key.
  -- | Persisted into `StepAdvice.sideloadedVKs`, which is where the
  -- | step rule body reads it from.
  , sideloadedVKs :: vkCarrier
  }

-- | A base-case `StepAdvice`, keyed on the spec-indexed per-slot
-- | carrier. `prevsSpec` determines both the slot count `len` and the
-- | nested-tuple `carrier`, and the rank-2 `dummySlot` builds each
-- | slot's witness at that slot's own `n_i` — so homogeneous and
-- | heterogeneous specs go through one path, a slot at `n_i = 0`
-- | getting empty `prevChallenges` and `prevSgs`.
buildStepAdvice
  :: forall @prevsSpec inputVal len carrier valCarrier vkCarrier vkSourcesCarrier
   . Reflectable len Int
  => StepSlotsCarrier
       prevsSpec
       WrapVkChunks
       StepIPARounds
       WrapIPARounds
       (F StepField)
       (Type2 (SplitField (F StepField) Boolean))
       Boolean
       len
       carrier
       vkSourcesCarrier
  => SlotStatementsCarrier prevsSpec valCarrier
  => BuildStepAdviceInput inputVal valCarrier vkCarrier
  -> StepAdvice prevsSpec StepIPARounds WrapIPARounds WrapVkChunks inputVal len carrier valCarrier vkCarrier
buildStepAdvice input =
  let
    -- The Pallas generator, reused for every curve-point field of the
    -- base-case dummy advice. Never the point at infinity, so
    -- `toAffine` is always `Just`.
    g0 =
      let
        p = unsafePartial (fromJust (Curves.toAffine (Curves.generator :: Pallas.G)))
      in
        { x: F p.x, y: F p.y }

    g0w = WeierstrassAffinePoint g0

    -- `len` reified: the rule's `max_proofs_verified`, for the few
    -- places that need an `Int`.
    mrw = reflectType (Proxy @len)

    bcd = baseCaseDummies { maxProofsVerified: mrw }

    z1 = toShifted (F bcd.proofDummy.z1)

    z2 = toShifted (F bcd.proofDummy.z2)

    wrapPE :: LFFI.PointEval StepField -> LFFI.PointEval (F StepField)
    wrapPE pe = { zeta: F pe.zeta, omegaTimesZeta: F pe.omegaTimesZeta }

    wrapAE :: Evals StepField -> Evals (F StepField)
    wrapAE ae =
      { ftEval1: F ae.ftEval1
      , publicEvals: wrapPE ae.publicEvals
      , zEvals: wrapPE ae.zEvals
      , indexEvals: map wrapPE ae.indexEvals
      , witnessEvals: map wrapPE ae.witnessEvals
      , coeffEvals: map wrapPE ae.coeffEvals
      , sigmaEvals: map wrapPE ae.sigmaEvals
      }

    prevEvalsDummy =
      let
        aeF = wrapAE bcd.proofDummy.prevEvals
      in
        AllocEvals aeF

    dummyFop
      :: UnfinalizedProof StepIPARounds (F StepField) (Type1 (F StepField)) Boolean
    dummyFop = stepDummyUnfinalizedProof @len bcd
      { domainLog2: wrapDomainLog2ForProofsVerified mrw }
      (map SizedF.wrapF bcd.ipaStepChallenges)

    dummyBranch =
      -- The mask by width: 0 → [F, F], 1 → [F, T], 2 → [T, T].
      { domainLog2: F (Curves.fromInt input.stepDomainLog2)
      , proofsVerifiedMask: (mrw >= 2) :< (mrw >= 1) :< Vector.nil
      }

    dvFop = dummyFop.deferredValues
    pFop = dvFop.plonk

    -- `wrapDummyUnfinalizedProof` is in wrap-field
    -- `Type2 (F WrapField)`; the helpers below carry it across to the
    -- step-field `Type2 (SplitField (F StepField) Boolean)` that
    -- `publicInputCommit` walks over.
    du = wrapDummyUnfinalizedProof bcd

    t2toT2sf :: Type2 (F WrapField) -> Type2 (SplitField (F StepField) Boolean)
    t2toT2sf t = toShifted (fromShifted t :: F WrapField)

    chalToStep :: SizedF 128 (F WrapField) -> SizedF 128 (F StepField)
    chalToStep s = SizedF.wrapF (coerceViaBits (SizedF.unwrapF s))

    spongeDigest =
      let
        F digestWrap = du.spongeDigestBeforeEvaluations
      in
        F (crossFieldDigest digestWrap)

    dvDu = du.deferredValues
    pDu = dvDu.plonk

    dummyPublicUnfinalized
      :: PerProofUnfinalized
           WrapIPARounds
           (Type2 (SplitField (F StepField) Boolean))
           (F StepField)
           Boolean
    dummyPublicUnfinalized = PerProofUnfinalized
      { combinedInnerProduct: t2toT2sf dvDu.combinedInnerProduct
      , b: t2toT2sf dvDu.b
      , zetaToSrsLength: t2toT2sf pDu.zetaToSrsLength
      , zetaToDomainSize: t2toT2sf pDu.zetaToDomainSize
      , perm: t2toT2sf pDu.perm
      , spongeDigest
      , beta: UnChecked (chalToStep pDu.beta)
      , gamma: UnChecked (chalToStep pDu.gamma)
      , alpha: UnChecked (chalToStep pDu.alpha)
      , zeta: UnChecked (chalToStep pDu.zeta)
      , xi: UnChecked (chalToStep dvDu.xi)
      , bulletproofChallenges: map (UnChecked <<< chalToStep) dvDu.bulletproofChallenges
      , shouldFinalize: false
      }

    -- Rank-2 per-slot dummy: only `prevChallenges` and `prevSgs`
    -- depend on `n`, and they specialize per slot through
    -- `Array.replicate`; every other field is reused verbatim.
    dummySlot
      :: forall n
       . Reflectable n Int
      => Proxy n
      -> Step.PerProofWitness
           WrapVkChunks
           StepIPARounds
           WrapIPARounds
           (F StepField)
           (Type2 (SplitField (F StepField) Boolean))
           Boolean
    dummySlot slotWidth = Step.PerProofWitness
      { wrapProof: Step.WrapProof
          { opening: WrapProofOpening
              { lr: Vector.generate
                  ( \_ ->
                      { l: WeierstrassAffinePoint g0
                      , r: WeierstrassAffinePoint g0
                      }
                  )
              , z1
              , z2
              , delta: WeierstrassAffinePoint g0
              , sg: WeierstrassAffinePoint g0
              }
          , messages: WrapProofMessages
              { wComm: Vector.generate (\_ -> ChunkedCommitment (Vector.replicate (WeierstrassAffinePoint g0)))
              , zComm: ChunkedCommitment (Vector.replicate (WeierstrassAffinePoint g0))
              , tComm: Vector.generate (\_ -> ChunkedCommitment (Vector.replicate (WeierstrassAffinePoint g0)))
              }
          }
      , proofState: Step.ProofState
          { fopState: Step.FopProofState
              { combinedInnerProduct: unwrap dvFop.combinedInnerProduct
              , b: unwrap dvFop.b
              , zetaToSrsLength: unwrap pFop.zetaToSrsLength
              , zetaToDomainSize: unwrap pFop.zetaToDomainSize
              , perm: unwrap pFop.perm
              , spongeDigest: dummyFop.spongeDigestBeforeEvaluations
              , beta: UnChecked pFop.beta
              , gamma: UnChecked pFop.gamma
              , alpha: UnChecked pFop.alpha
              , zeta: UnChecked pFop.zeta
              , xi: UnChecked dvFop.xi
              , bulletproofChallenges: map UnChecked dvFop.bulletproofChallenges
              }
          , branchData: Step.AllocBranchData dummyBranch
          }
      , prevEvals: prevEvalsDummy
      , prevChallenges:
          Array.replicate (reflectType slotWidth)
            (UnChecked (map F dummyIpaChallenges.stepExpanded))
      , prevSgs: Array.replicate (reflectType slotWidth) (WeierstrassAffinePoint g0)
      }
  in
    StepAdvice
      { perProofSlotsCarrier: replicateStepSlotsCarrier @prevsSpec @WrapVkChunks dummySlot
      , publicInput: input.publicInput
      , publicUnfinalizedProofs: Vector.replicate dummyPublicUnfinalized
      , messagesForNextWrapProof: Vector.replicate (F zero)
      , messagesForNextWrapProofDummyHash: F zero
      , wrapVerifierIndex:
          VerificationKey
            { sigma: Vector.generate (\_ -> ChunkedCommitment (Vector.replicate g0w))
            , coeff: Vector.generate (\_ -> ChunkedCommitment (Vector.replicate g0w))
            , index: Vector.generate (\_ -> ChunkedCommitment (Vector.replicate g0w))
            }
      , kimchiPrevChallenges:
          Vector.replicate
            { sgX: zero
            , sgY: zero
            , challenges: Vector.replicate zero
            }
      , prevAppStates: input.prevAppStates
      , sideloadedVKs: input.sideloadedVKs
      }

-- | The sigma, coefficient and index commitments of a compiled wrap
-- | verifier index, in the shape the step advice wants. They are Pallas
-- | points with coordinates in `Pallas.BaseField = StepField`, so no
-- | cross-field coercion is needed.
-- |
-- | Pinned at `WrapVkChunks`, the wrap VK's own chunk count, which is
-- | not the wrap circuit's `stepChunks` — that is the one that varies.
extractWrapVKCommsAdvice
  :: VerifierIndex PallasG WrapField
  -> VerificationKey WrapVkChunks (WeierstrassAffinePoint PallasG (F StepField))
extractWrapVKCommsAdvice vk =
  let
    comms = vestaVerifierIndexCommitments @WrapVkChunks vk

    wrapPt :: AffinePoint StepField -> WeierstrassAffinePoint PallasG (F StepField)
    wrapPt (AffinePoint pt) = WeierstrassAffinePoint { x: F pt.x, y: F pt.y }
  in
    VerificationKey
      { sigma: map (over ChunkedCommitment (map wrapPt)) comms.sigma
      , coeff: map (over ChunkedCommitment (map wrapPt)) comms.coeff
      , index: map (over ChunkedCommitment (map wrapPt)) comms.index
      }

--------------------------------------------------------------------------------
-- mpvMax-padding dummies
--------------------------------------------------------------------------------

-- | The step-field `messages_for_next_wrap_proof` digest `stepMain`
-- | front-pads the step public input with, from `len` (the rule's own
-- | `max_proofs_verified`) up to the compile-wide `mpvMax`. Hashes the
-- | dummy step sg against `PaddedLength` copies of the dummy expanded
-- | wrap challenges, then casts the digest across fields.
mkDummyMsgWrapHash
  :: Dummy.BaseCaseDummies
  -> CRS PallasG
  -> CRS VestaG
  -> F StepField
mkDummyMsgWrapHash bcd pallasSrs vestaSrs =
  let
    sgValues = Dummy.computeDummySgValues bcd pallasSrs vestaSrs

    msgWrapHashWrap = hashMessagesForNextWrapProofPureGeneral
      { sg: sgValues.ipa.step.sg
      , paddedChallenges:
          Vector.replicate @PaddedLength dummyIpaChallenges.wrapExpanded
      }
  in
    F (crossFieldDigest msgWrapHashWrap)

-- | The `Array WrapField` the FFI oracles call receives for a dummy
-- | wrap proof.
-- |
-- | Its bits have to match what the step circuit's `packStatement` and
-- | `publicInputCommit` produce from the same advice, or the two
-- | disagree on `x_hat`. Cross-field re-shifting through
-- | `assembleWrapMainInput` would not match: it gives
-- | `(v - shift)/2` in the wrap field, where the step circuit emits
-- | `(v - shift)/2` in the step field and then reinterprets those bits
-- | as scalars. So the values here are the step-field-shifted ones,
-- | reinterpreted bit for bit into the wrap field.
-- |
-- | Field order is `packStatement`'s: 5 fp fields, 2 challenges, 3
-- | scalar challenges, 3 digests, `StepIPARounds` bulletproof
-- | challenges, packed branch data, 8 feature flags, 2 lookup slots.
dummyWrapTockPublicInput
  :: forall @n stmt stmtVar
   . Reflectable n Int
  => Compare n 3 LT
  => CircuitType StepField stmt stmtVar
  -- The first field is the prev rule's step domain log2, its wrap
  -- statement's `branch_data.domain_log2`, fed into
  -- `packBranchDataWrap` below.
  => { stepDomainLog2 :: Int
     , wrapVK :: VerifierIndex PallasG WrapField
     -- | The prev's full `StatementIO inputVal outputVal` value,
     -- | serialized by `valueToFields` for the
     -- | `messages_for_next_step_proof` app-state hash: input fields
     -- | then output fields, a `Unit` field contributing zero, so
     -- | Input-mode and Output-mode prevs serialize alike.
     , prevStatement :: stmt
     -- | The dummy wrap sg, standing in for the previous proofs'
     -- | `challenge_polynomial_commitments` in
     -- | `messagesForNextStepProof`.
     , wrapSg :: AffinePoint StepField
     -- | The dummy step sg. Not read here; the call site threads both
     -- | sg values together.
     , stepSg :: AffinePoint WrapField
     -- | The `hashMessagesForNextWrapProofPureGeneral` digest, computed
     -- | at `sg = stepSg`. Passed in rather than recomputed so that one
     -- | value serves both here, as `digests[1]`, and the advice's
     -- | `messagesForNextWrapProof` slot.
     , msgWrapDigest :: WrapField
     -- | The FOP proof state to serialize, which is what picks the
     -- | dummy plonk values the rule's shape calls for.
     , fopProofState ::
         UnfinalizedProof StepIPARounds (F StepField) (Type1 (F StepField)) Boolean
     }
  -> Array WrapField
dummyWrapTockPublicInput input =
  let
    fop = input.fopProofState

    dv = fop.deferredValues
    p = dv.plonk

    -- Reinterprets a step-field scalar's bits as a wrap-field scalar.
    -- Lossless: the step field's bits fit in the wrap field.
    stepToWrap :: F StepField -> WrapField
    stepToWrap (F x) = crossFieldDigest x

    -- The wrap public input takes the stored, shifted value of a
    -- `Type1`, not the unshifted original.
    type1StepBits :: Type1 (F StepField) -> WrapField
    type1StepBits (Type1 x) = stepToWrap x

    -- `coerceViaBits` is bounded by `Compare 128 m LT` on both fields'
    -- bit widths, so no value here can be out of range.
    sizedStepBits = SizedF.toField <<< (coerceViaBits) <<< SizedF.unwrapF

    -- In `packStatement`'s order: cip, b, zetaToSrsLength,
    -- zetaToDomainSize, perm.
    fpFields =
      [ type1StepBits dv.combinedInnerProduct
      , type1StepBits dv.b
      , type1StepBits p.zetaToSrsLength
      , type1StepBits p.zetaToDomainSize
      , type1StepBits p.perm
      ]

    challenges2 = [ sizedStepBits p.beta, sizedStepBits p.gamma ]

    scalarChallenges3 =
      [ sizedStepBits p.alpha, sizedStepBits p.zeta, sizedStepBits dv.xi ]

    msgWrapDigestWrapField = input.msgWrapDigest

    -- The `messages_for_next_step_proof` digest: a step-field hash over
    -- the wrap VK, the prev app state, and `n` copies of the dummy wrap
    -- sg with its expanded bulletproof challenges.
    wrapVkStep = extractWrapVKForStepHash @WrapVkChunks input.wrapVK

    stepExpanded = dummyIpaChallenges.stepExpanded

    singleEntry = { sg: input.wrapSg, expandedBpChallenges: stepExpanded }

    appStateFields = valueToFields @StepField @stmt input.prevStatement

    msgStepDigestStepField = hashMessagesForNextStepProofPure
      { stepVk: wrapVkStep
      , appState: appStateFields
      , proofs: Vector.replicate @n singleEntry
      }

    -- The digests in `packStatement`'s order: sponge, msgWrap, msgStep.
    sponge0 = fop.spongeDigestBeforeEvaluations

    digests3 =
      [ stepToWrap sponge0
      , msgWrapDigestWrapField -- already wrap field
      , stepToWrap (F msgStepDigestStepField)
      ]

    bpChals = map sizedStepBits (Vector.toUnfoldable dv.bulletproofChallenges)

    -- Branch data packed as `4 * domainLog2 + mask[0] + 2 * mask[1]`,
    -- through the same encoder the wrap side uses in circuit.
    packedBranchData = packBranchDataWrap
      { domainLog2: Curves.fromInt input.stepDomainLog2 :: StepField
      , proofsVerifiedMask: revOnesVector (reflectType (Proxy @n))
      }

    -- Feature flags and lookup slots: constant zero, no feature being
    -- enabled.
    featureFlags = Array.replicate 8 zero

    lookupSlots = [ zero, zero ]
  in
    fpFields
      <> challenges2
      <> scalarChallenges3
      <> digests3
      <> bpChals
      <> [ packedBranchData ]
      <> featureFlags
      <> lookupSlots

-- | Inputs for `buildSlotAdvice`, covering the base case (a dummy wrap
-- | proof) and the inductive case (a real one from the previous
-- | iteration) alike: the caller supplies the wrap proof, its public
-- | input and the padded accumulator, and the builder treats the two
-- | the same.
-- |
-- | `stmt` is the prev's statement type, which is not the rule's own
-- | `inputVal` when the rule verifies a differently-shaped prev.
type BuildSlotAdviceInput inputVal stmt =
  { publicInput :: inputVal
  -- | The prev's full `StatementIO inputVal outputVal` value. This
  -- | builder makes a single-slot `StepAdvice`, so the resulting
  -- | `prevAppStates` is the singleton carrier `Tuple stmt unit`.
  , prevStatement :: stmt
  , wrapDomainLog2 :: Int
  -- | Step-domain log2 of the proof being verified, its wrap
  -- | statement's `branch_data.domain_log2`, which drives
  -- | `zetaToDomainSize`, `perm` and omega. Distinct from
  -- | `wrapDomainLog2`, the wrap VK's own domain, whenever a rule uses
  -- | `override_wrap_domain` or verifies a prev whose step domain
  -- | differs from its wrap domain.
  , stepDomainLog2 :: Int
  -- | Kimchi `zk_rows` of the prev step proof, from its `num_chunks`.
  -- | Distinct from the wrap circuit's whenever the two chunk counts
  -- | differ.
  , stepZkRows :: Int
  -- | Kimchi `zk_rows` of the wrap proof being verified. Threaded
  -- | rather than assumed, though `WrapVkChunks = 1` pins it at 3.
  , wrapZkRows :: Int
  , wrapVK :: VerifierIndex PallasG WrapField
  -- | The prev step proof's opening sg, a Vesta point with wrap-field
  -- | coordinates: the wrap statement's
  -- | `messages_for_next_wrap_proof.challenge_polynomial_commitment`.
  -- | Feeds the `messages_for_next_wrap_proof` hash and `expandProof`.
  -- | The dummy step sg on the base case.
  , stepOpeningSg :: AffinePoint WrapField
  -- | Kimchi's own prev-IPA-fold reference, passed to
  -- | `pallasCreateProofWithPrev` as each entry's `sgX`/`sgY`. On the
  -- | base case it stays the compile-time dummy, so it differs from
  -- | `stepOpeningSg` once there is a real prev wrap proof.
  , kimchiPrevSg :: AffinePoint WrapField
  -- | The wrap proof to run oracles on: the dummy on the base case,
  -- | the previous iteration's proof otherwise.
  , wrapProof :: Proof PallasG WrapField
  -- | Public input of `wrapProof`, the serialized wrap statement. An
  -- | `Array` because its length follows the circuit configuration and
  -- | is only known at the FFI boundary.
  , wrapPublicInput :: Array WrapField
  -- | Padded accumulator for the oracles call, `PaddedLength` entries
  -- | of an sg with its expanded bulletproof challenges.
  -- |
  -- | The `sg` column serves twice over: it is what the oracles call
  -- | takes as `prev_challenges`, and what the advice slot carries as
  -- | `prev_challenge_polynomial_commitments`. The per-slot `Vector n`
  -- | comes off it by dropping the front padding, `Vector.drop @pad`
  -- | with `Add pad n PaddedLength`.
  -- |
  -- | At `n` below `PaddedLength` the front entries are dummies; at
  -- | `n = PaddedLength` there is no padding and the entries differ per
  -- | slot, following the prev wrap proof's own stored commitments.
  , prevChalPolys ::
      Vector PaddedLength
        { sg :: AffinePoint StepField
        , challenges :: Vector WrapIPARounds WrapField
        }
  -- | Raw 128-bit plonk challenges from the wrap statement's
  -- | `deferred_values.plonk`.
  , wrapPlonkRaw ::
      { alpha :: SizedF 128 StepField
      , beta :: SizedF 128 StepField
      , gamma :: SizedF 128 StepField
      , zeta :: SizedF 128 StepField
      }
  -- | Step-field polynomial evaluations of the wrap proof.
  , wrapPrevEvals :: Evals StepField
  -- | Branch data from the wrap proof's statement.
  , wrapBranchData :: VT.BranchData StepField Boolean
  -- | Sponge digest before evaluations, from the wrap proof's
  -- | statement. Zero on the base case.
  , wrapSpongeDigest :: StepField
  -- | Whether the step circuit must verify the previous proof, false
  -- | exactly on the base case. Controls whether `expandProof`
  -- | overrides `challenge_polynomial_commitment`.
  , mustVerify :: Boolean
  -- | The wrap proof's own bulletproof challenges — its statement's
  -- | `messages_for_next_step_proof.old_bulletproof_challenges`, padded
  -- | to `PaddedLength` and expanded.
  -- |
  -- | `expandProof` reads them twice over: the combined inner product
  -- | of the wrap proof is a function of these bulletproof polynomials,
  -- | and they go into the `messages_for_next_wrap_proof` hash.
  , wrapOwnPaddedBpChals :: Vector PaddedLength (Vector WrapIPARounds WrapField)
  -- | The wrap proof's stored deferred values. The step circuit's
  -- | `packStatement` reads them back to reconstruct the wrap proof's
  -- | public input for the incremental verifier's `x_hat` commitment,
  -- | so they have to be what `wrapProof`'s public inputs actually
  -- | serialize.
  , fopState ::
      UnfinalizedProof StepIPARounds (F StepField) (Type1 (F StepField)) Boolean
  -- | The evaluations the step finalizer reads to recompute the claimed
  -- | deferred values and check them against `fopState`. Distinct from
  -- | `wrapPrevEvals`, which feeds `expandProof` on a separate path.
  , stepAdvicePrevEvals :: Evals StepField
  -- | The expanded step-field bulletproof challenges of the proof being
  -- | verified, for this slot's entry of `advice.kimchiPrevChallenges`
  -- | — the prev proof's `deferred_values.bulletproof_challenges` run
  -- | through the step endo scalar.
  , kimchiPrevChallengesExpanded :: Vector StepIPARounds StepField
  -- | The per-slot expanded step-field bulletproof challenges feeding
  -- | the `messagesForNextStepProof` hash and `expandProof`'s
  -- | `stepPrevChallenges`, pre-padded to `PaddedLength` by the caller.
  -- | The builder takes its own `Vector n` off the front with
  -- | `Vector.drop @pad`, as it does for `prevChalPolys`.
  -- |
  -- | The entries differ per slot whenever the prev wrap proof's
  -- | `old_bulletproof_challenges` do.
  , prevChallengesForStepHash :: Vector PaddedLength (Vector StepIPARounds StepField)
  }

-- | One slot's contribution to a step advice: its entry of
-- | `challengePolynomialCommitments`, `publicUnfinalizedProofs`,
-- | `messagesForNextWrapProof` and `kimchiPrevChallenges`, plus its
-- | per-proof witness at that slot's own `n`.
-- |
-- | `Pickles.Prove.Compile`'s `mkStepAdvice` recurses over the slots to
-- | assemble these into one `StepAdvice`, and supplies the values that
-- | are shared across slots, which is why they are not here.
type SlotAdviceContrib :: Type
type SlotAdviceContrib =
  { challengePolynomialCommitment :: AffinePoint StepField
  , slotUnfinalized ::
      PerProofUnfinalized
        WrapIPARounds
        (Type2 (SplitField (F StepField) Boolean))
        (F StepField)
        Boolean
  , slotMsgWrapHashStep :: F StepField
  , slotKimchiPrevEntry ::
      { sgX :: WrapField
      , sgY :: WrapField
      , challenges :: Vector StepIPARounds StepField
      }
  , slotSppw ::
      Step.PerProofWitness
        WrapVkChunks
        StepIPARounds
        WrapIPARounds
        (F StepField)
        (Type2 (SplitField (F StepField) Boolean))
        Boolean
  }

--------------------------------------------------------------------------------
-- buildSlotAdvice — per-slot oracle-enriched advice builder
--------------------------------------------------------------------------------

-- | One slot's `SlotAdviceContrib`: runs the oracles on the supplied
-- | wrap proof and public input, feeds the result through
-- | `expandProof`, and packs what comes out.
buildSlotAdvice
  :: forall @n inputVal input prevHeadStmt prevHeadStmtVar pad
   . Reflectable n Int
  => Reflectable pad Int
  => Add pad n PaddedLength
  => CircuitType StepField inputVal input
  => CircuitType StepField prevHeadStmt prevHeadStmtVar
  => BuildSlotAdviceInput inputVal prevHeadStmt
  -> Effect SlotAdviceContrib
buildSlotAdvice input = do
  let
    wrapPadded = input.wrapOwnPaddedBpChals

    msgWrapHash = hashMessagesForNextWrapProofPureGeneral
      { sg: input.stepOpeningSg
      , paddedChallenges: wrapPadded
      }

    msgWrapHashStep = F (crossFieldDigest msgWrapHash)

  let
    wrapVkStep = extractWrapVKForStepHash @WrapVkChunks input.wrapVK

    -- This slot's own `Vector n` views, taken off the padded inputs by
    -- dropping the front padding.
    prevCpcs = map _.sg (Vector.drop @pad input.prevChalPolys)

    prevChalsPerSlot = Vector.drop @pad input.prevChallengesForStepHash

    prevProofsForHash =
      Vector.zipWith (\sg chals -> { sg, expandedBpChallenges: chals })
        prevCpcs
        prevChalsPerSlot

  msgStepDigestStepField <- hashMessagesForNextStepProofPureTraced
    { stepVk: wrapVkStep
    , appState: valueToFields @StepField @prevHeadStmt input.prevStatement
    , proofs: prevProofsForHash
    }

  Trace.field "expand_proof.msgForNextStep" msgStepDigestStepField
  Trace.field "expand_proof.msgForNextWrap" msgWrapHash

  for_ (Array.mapWithIndex Tuple input.wrapPublicInput) \(Tuple i v) ->
    Trace.field ("tock_pi." <> show i) v

  forWithIndex_ input.prevChalPolys \fi entry -> do
    let i = getFinite fi
    Trace.field ("expand_proof.chal_polys." <> show i <> ".comm.x") (unwrap entry.sg).x
    Trace.field ("expand_proof.chal_polys." <> show i <> ".comm.y") (unwrap entry.sg).y
    Trace.field ("expand_proof.chal_polys." <> show i <> ".chal.0") (Vector.head entry.challenges)

  let
    toFFIChalPoly r = { sgX: (unwrap r.sg).x, sgY: (unwrap r.sg).y, challenges: Vector.toUnfoldable r.challenges }

    oracles = proofOraclesRec input.wrapVK
      { proof: input.wrapProof
      , publicInput: input.wrapPublicInput
      , prevChallenges: map toFFIChalPoly (Vector.toUnfoldable input.prevChalPolys)
      }

  Trace.field "expand_proof.oracles.beta" (SizedF.toField oracles.beta)
  Trace.field "expand_proof.oracles.gamma" (SizedF.toField oracles.gamma)
  Trace.field "expand_proof.oracles.alpha_chal" (SizedF.toField oracles.alphaChal)
  Trace.field "expand_proof.oracles.zeta_chal" (SizedF.toField oracles.zetaChal)
  Trace.field "expand_proof.plonk0.alpha.raw" (SizedF.toField (SizedF.wrapF input.wrapPlonkRaw.alpha :: SizedF 128 (F StepField)))
  Trace.field "expand_proof.plonk0.beta" (SizedF.toField (SizedF.wrapF input.wrapPlonkRaw.beta :: SizedF 128 (F StepField)))
  Trace.field "expand_proof.plonk0.gamma" (SizedF.toField (SizedF.wrapF input.wrapPlonkRaw.gamma :: SizedF 128 (F StepField)))
  Trace.field "expand_proof.plonk0.zeta.raw" (SizedF.toField (SizedF.wrapF input.wrapPlonkRaw.zeta :: SizedF 128 (F StepField)))
  Trace.field "expand_proof.oracles.fq_digest" oracles.fqDigest
  -- No combined inner product is traced here: the napi oracles return
  -- random oracles, the public evaluations, the digest and the opening
  -- prechallenges, but no CIP. The PS-side value comes from
  -- `Pickles.Prove.Pure.Common`'s `combinedInnerProductBatchChunked`.

  let
    rawPrechalsForTrace = proofOpeningPrechallenges input.wrapVK
      { proof: input.wrapProof
      , publicInput: input.wrapPublicInput
      , prevChallenges: map toFFIChalPoly (Vector.toUnfoldable input.prevChalPolys)
      }
  for_ (Array.mapWithIndex Tuple rawPrechalsForTrace) \(Tuple i v) ->
    Trace.field ("expand_proof.bp_prechal." <> show i) v

  let
    chalToStep :: SizedF 128 WrapField -> SizedF 128 (F StepField)
    chalToStep s = SizedF.wrapF (coerceViaBits s)

    wrapEndoScalar =
      let EndoScalar e = (endoScalar) in e

    stepEndoScalarF =
      let EndoScalar e = (endoScalar) in e

    dummyStepBpChalsRaw = map SizedF.wrapF dummyIpaChallenges.stepRaw

    plonkMinimalStep =
      { alpha: SizedF.wrapF input.wrapPlonkRaw.alpha
      , beta: SizedF.wrapF input.wrapPlonkRaw.beta
      , gamma: SizedF.wrapF input.wrapPlonkRaw.gamma
      , zeta: SizedF.wrapF input.wrapPlonkRaw.zeta
      }

    branchData = input.wrapBranchData

    stepGenerator = domainGenerator input.stepDomainLog2

    stepShifts = domainShifts input.stepDomainLog2

    zetaExpandedStep =
      toFieldPure (SizedF.unwrapF plonkMinimalStep.zeta) stepEndoScalarF

    stepVanishesOnZk =
      (permutationVanishingPolynomial :: { domainLog2 :: Int, zkRows :: Int, pt :: StepField } -> StepField)
        { domainLog2: input.stepDomainLog2, zkRows: input.stepZkRows, pt: zetaExpandedStep }

    wrapGen = domainGenerator input.wrapDomainLog2
    wrapZetaw = oracles.zeta * wrapGen
    wrapSrsLog2 = reflectType (Proxy :: Proxy WrapIPARounds)
    wrapCollapse = collapsePointEval
      { rounds: wrapSrsLog2, zeta: oracles.zeta, zetaOmega: wrapZetaw }

    wrapProofData' = vestaProofData @WrapIPARounds input.wrapProof
    wrapEvals =
      { ftEval1: oracles.ftEval1
      -- `x_hat` comes from the oracles rather than from
      -- `proofData.evals.public`, because the oracles already fold in
      -- the recomputation: for a real wrap proof the two agree, and for
      -- the dummy, whose wire `evals.public` is absent, only the oracle
      -- has a value.
      , publicEvals: oracles.publicEvals
      , zEvals: wrapCollapse wrapProofData'.evals.z
      , witnessEvals: map wrapCollapse wrapProofData'.evals.w
      , coeffEvals: map wrapCollapse wrapProofData'.evals.coefficients
      , sigmaEvals: map wrapCollapse wrapProofData'.evals.s
      , indexEvals: map wrapCollapse wrapProofData'.evals.indexEvals
      }

    wrapShifts = domainShifts input.wrapDomainLog2

    wrapVanishesOnZk =
      (permutationVanishingPolynomial :: { domainLog2 :: Int, zkRows :: Int, pt :: WrapField } -> WrapField)
        { domainLog2: input.wrapDomainLog2, zkRows: input.wrapZkRows, pt: oracles.zeta }

    stepProofPrevEvals =
      let
        pe pe' = { zeta: F pe'.zeta, omegaTimesZeta: F pe'.omegaTimesZeta }
        ae = input.wrapPrevEvals
      in
        AllocEvals
          { ftEval1: F ae.ftEval1
          , publicEvals: pe ae.publicEvals
          , zEvals: pe ae.zEvals
          , witnessEvals: map pe ae.witnessEvals
          , coeffEvals: map pe ae.coeffEvals
          , sigmaEvals: map pe ae.sigmaEvals
          , indexEvals: map pe ae.indexEvals
          }

    expandProofInputRec =
      { mustVerify: input.mustVerify
      , zkRows: input.stepZkRows
      , srsLengthLog2: reflectType (Proxy :: Proxy StepIPARounds)
      , allEvals: input.wrapPrevEvals
      , pEval0Chunks: [ input.wrapPrevEvals.publicEvals.zeta ]
      , oldBulletproofChallenges: Vector.replicate @n dummyStepBpChalsRaw
      , plonkMinimal: plonkMinimalStep
      , rawBulletproofChallenges: input.fopState.deferredValues.bulletproofChallenges
      , branchData
      , spongeDigestBeforeEvaluations: input.wrapSpongeDigest
      , stepDomainLog2: input.stepDomainLog2
      , stepGenerator
      , stepShifts
      , stepVanishesOnZk
      , stepOmegaForLagrange: \_ -> one
      , endo: stepEndoScalarF
      , linearizationPoly: Linearization.pallas
      , dlogIndex: extractWrapVKForStepHash @WrapVkChunks input.wrapVK
      , appStateFields: valueToFields @StepField @prevHeadStmt input.prevStatement
      , stepPrevSgs: prevCpcs
      , wrapChallengePolynomialCommitment: input.stepOpeningSg
      , wrapPaddedPrevChallenges: wrapPadded
      , wrapVerifierIndex: input.wrapVK
      , wrapProof: input.wrapProof
      , tockPublicInput: input.wrapPublicInput
      , wrapOraclesPrevChallenges: map toFFIChalPoly (Vector.toUnfoldable input.prevChalPolys)
      , wrapDomainLog2: input.wrapDomainLog2
      , wrapEndo: wrapEndoScalar
      , wrapEvals
      -- One chunk: the public-input polynomial has degree below the
      -- domain size.
      , wrapPEval0Chunks: [ oracles.publicEvals.zeta ]
      , wrapShifts
      , wrapZkRows: input.wrapZkRows
      , wrapSrsLengthLog2: reflectType (Proxy :: Proxy WrapIPARounds)
      , wrapVanishesOnZk
      , wrapOmegaForLagrange: \_ -> one
      , wrapLinearizationPoly: Linearization.vesta
      , stepProofPrevEvals
      , stepPrevChallenges: map (map F) prevChalsPerSlot
      , stepPrevSgsPadded: prevCpcs
      }

    expandProofResult = PureStep.expandProof @WrapVkChunks expandProofInputRec

  let
    dStep = expandProofResult.deferredStep

    type1Inner :: forall a. Type1 a -> a
    type1Inner (Type1 x) = x
  Trace.fieldF "expand_proof.deferred.combined_inner_product" (type1Inner dStep.combinedInnerProduct)
  Trace.fieldF "expand_proof.deferred.b" (type1Inner dStep.b)
  Trace.fieldF "expand_proof.deferred.xi" (F (toFieldPure (SizedF.unwrapF dStep.xi) stepEndoScalarF) :: F StepField)
  Trace.fieldF "expand_proof.deferred.plonk.perm" (type1Inner dStep.plonk.perm)
  Trace.fieldF "expand_proof.deferred.plonk.zetaToSrsLength" (type1Inner dStep.plonk.zetaToSrsLength)
  Trace.fieldF "expand_proof.deferred.plonk.zetaToDomainSize" (type1Inner dStep.plonk.zetaToDomainSize)
  Trace.field "expand_proof.deferred.branch_data.domain_log2" dStep.branchData.domainLog2
  for_ (Array.mapWithIndex Tuple expandProofResult.rawPrechallenges) \(Tuple i v) ->
    Trace.field ("expand_proof.internal_bp_prechal." <> show i) v

  let
    wDv = expandProofResult.unfinalized.deferredValues

    type2InnerF :: Type2 (F WrapField) -> F WrapField
    type2InnerF (Type2 x) = x
  Trace.fieldF "expand_proof.wrap_deferred.combined_inner_product" (type2InnerF wDv.combinedInnerProduct)
  Trace.fieldF "expand_proof.wrap_deferred.b" (type2InnerF wDv.b)
  Trace.fieldF "expand_proof.wrap_deferred.plonk.perm" (type2InnerF wDv.plonk.perm)
  Trace.fieldF "expand_proof.wrap_deferred.plonk.beta" (SizedF.toField wDv.plonk.beta)
  Trace.fieldF "expand_proof.wrap_deferred.plonk.gamma" (SizedF.toField wDv.plonk.gamma)
  Trace.fieldF "expand_proof.wrap_deferred.sponge_digest" expandProofResult.unfinalized.spongeDigestBeforeEvaluations

  let
    -- Wrap-field unfinalized proof to step-field public unfinalized
    -- slot.
    wrapToStepType2
      :: Type2 (F WrapField)
      -> Type2 (SplitField (F StepField) Boolean)
    wrapToStepType2 t = toShifted (fromShifted t :: F WrapField)

    expandedUnfinalized
      :: PerProofUnfinalized WrapIPARounds
           (Type2 (SplitField (F StepField) Boolean))
           (F StepField)
           Boolean
    expandedUnfinalized =
      let
        u = expandProofResult.unfinalized
        dv = u.deferredValues
        p = dv.plonk
      in
        PerProofUnfinalized
          { combinedInnerProduct: wrapToStepType2 dv.combinedInnerProduct
          , b: wrapToStepType2 dv.b
          , zetaToSrsLength: wrapToStepType2 p.zetaToSrsLength
          , zetaToDomainSize: wrapToStepType2 p.zetaToDomainSize
          , perm: wrapToStepType2 p.perm
          , spongeDigest: F (crossFieldDigest (case u.spongeDigestBeforeEvaluations of F x -> x))
          , beta: UnChecked (chalToStep (SizedF.unwrapF p.beta))
          , gamma: UnChecked (chalToStep (SizedF.unwrapF p.gamma))
          , alpha: UnChecked (chalToStep (SizedF.unwrapF p.alpha))
          , zeta: UnChecked (chalToStep (SizedF.unwrapF p.zeta))
          , xi: UnChecked (chalToStep (SizedF.unwrapF dv.xi))
          , bulletproofChallenges:
              map (\sf -> UnChecked (chalToStep (SizedF.unwrapF sf))) dv.bulletproofChallenges
          , shouldFinalize: u.shouldFinalize
          }

    fopState
      :: UnfinalizedProof StepIPARounds (F StepField) (Type1 (F StepField)) Boolean
    fopState = input.fopState

  let
    t1Inner :: Type1 (F StepField) -> F StepField
    t1Inner (Type1 x) = x
  Trace.fieldF "diag.fopState.plonk.beta" (SizedF.toField fopState.deferredValues.plonk.beta)
  Trace.fieldF "diag.fopState.plonk.gamma" (SizedF.toField fopState.deferredValues.plonk.gamma)
  Trace.fieldF "diag.fopState.plonk.alpha" (SizedF.toField fopState.deferredValues.plonk.alpha)
  Trace.fieldF "diag.fopState.plonk.zeta" (SizedF.toField fopState.deferredValues.plonk.zeta)
  Trace.fieldF "diag.fopState.xi" (SizedF.toField fopState.deferredValues.xi)
  Trace.fieldF "diag.fopState.spongeDigest" fopState.spongeDigestBeforeEvaluations
  Trace.fieldF "diag.fopState.cip.shifted" (t1Inner fopState.deferredValues.combinedInnerProduct)
  Trace.fieldF "diag.fopState.b.shifted" (t1Inner fopState.deferredValues.b)
  Trace.fieldF "diag.fopState.perm.shifted" (t1Inner fopState.deferredValues.plonk.perm)

  let
    openingSg = coerce expandProofResult.sg

    mkPt :: AffinePoint StepField -> { x :: F StepField, y :: F StepField }
    mkPt (AffinePoint pt) = { x: F pt.x, y: F pt.y }

    wrapProofData = vestaProofData @WrapIPARounds input.wrapProof

    openingDelta = mkPt wrapProofData.opening.delta

    openingLr = map (\p -> { l: mkPt p.l, r: mkPt p.r })
      wrapProofData.opening.lr

    openingZ1Raw = wrapProofData.opening.z1

    openingZ2Raw = wrapProofData.opening.z2

    z1 = toShifted (F openingZ1Raw)

    z2 = toShifted (F openingZ2Raw)

    wrapCommits = vestaProofCommitments @WrapVkChunks input.wrapProof

    mkPallasAffine :: AffinePoint StepField -> { x :: F StepField, y :: F StepField }
    mkPallasAffine (AffinePoint pt) = { x: F pt.x, y: F pt.y }
    wrapMessages =
      { wComm: map (over ChunkedCommitment (map mkPallasAffine)) wrapCommits.wComm
      , zComm: over ChunkedCommitment (map mkPallasAffine) wrapCommits.zComm
      , tComm: map (over ChunkedCommitment (map mkPallasAffine)) wrapCommits.tComm
      }

    wrapPE' :: LFFI.PointEval StepField -> LFFI.PointEval (F StepField)
    wrapPE' pe = { zeta: F pe.zeta, omegaTimesZeta: F pe.omegaTimesZeta }

    evalsForAdvice =
      let
        ae = input.stepAdvicePrevEvals
      in
        { allEvals:
            { ftEval1: F ae.ftEval1
            , publicEvals: wrapPE' ae.publicEvals
            , zEvals: wrapPE' ae.zEvals
            , indexEvals: map wrapPE' ae.indexEvals
            , witnessEvals: map wrapPE' ae.witnessEvals
            , coeffEvals: map wrapPE' ae.coeffEvals
            , sigmaEvals: map wrapPE' ae.sigmaEvals
            }
        }

    slotBranchData = input.wrapBranchData { domainLog2 = F input.wrapBranchData.domainLog2 }

    dvFop = fopState.deferredValues
    pFop = dvFop.plonk

    -- This slot's per-proof witness. `prevSgs` and `prevChallenges`
    -- come straight off `Vector.drop @pad`, so entries that differ per
    -- slot stay distinct.
    slotSppw
      :: Step.PerProofWitness WrapVkChunks StepIPARounds WrapIPARounds
           (F StepField)
           (Type2 (SplitField (F StepField) Boolean))
           Boolean
    slotSppw = Step.PerProofWitness
      { wrapProof: Step.WrapProof
          { opening: WrapProofOpening
              { lr: map
                  ( \r ->
                      { l: WeierstrassAffinePoint r.l
                      , r: WeierstrassAffinePoint r.r
                      }
                  )
                  openingLr
              , z1
              , z2
              , delta: WeierstrassAffinePoint openingDelta
              , sg: WeierstrassAffinePoint openingSg
              }
          , messages: WrapProofMessages
              { wComm: map (over ChunkedCommitment (map WeierstrassAffinePoint)) wrapMessages.wComm
              , zComm: over ChunkedCommitment (map WeierstrassAffinePoint) wrapMessages.zComm
              , tComm: map (over ChunkedCommitment (map WeierstrassAffinePoint)) wrapMessages.tComm
              }
          }
      , proofState: Step.ProofState
          { fopState: Step.FopProofState
              { combinedInnerProduct: unwrap dvFop.combinedInnerProduct
              , b: unwrap dvFop.b
              , zetaToSrsLength: unwrap pFop.zetaToSrsLength
              , zetaToDomainSize: unwrap pFop.zetaToDomainSize
              , perm: unwrap pFop.perm
              , spongeDigest: fopState.spongeDigestBeforeEvaluations
              , beta: UnChecked pFop.beta
              , gamma: UnChecked pFop.gamma
              , alpha: UnChecked pFop.alpha
              , zeta: UnChecked pFop.zeta
              , xi: UnChecked dvFop.xi
              , bulletproofChallenges: map UnChecked dvFop.bulletproofChallenges
              }
          , branchData: Step.AllocBranchData slotBranchData
          }
      , prevEvals: AllocEvals evalsForAdvice.allEvals
      , prevChallenges: Vector.toUnfoldable $ map
          (\chals -> UnChecked (map F chals))
          (Vector.drop @pad input.prevChallengesForStepHash)
      , prevSgs: Vector.toUnfoldable $ map
          (\e -> WeierstrassAffinePoint (coerce e.sg :: { x :: F StepField, y :: F StepField }))
          (Vector.drop @pad input.prevChalPolys)
      }

  let
    tag = if input.mustVerify then "real" else "dummy"
    z1SplitField = case z1 of Type2 sf -> sf
    z2SplitField = case z2 of Type2 sf -> sf
    sDiv2OfSf sf = case sf of SplitField { sDiv2: F d } -> d
  Trace.field ("expand_proof.opening.z1.raw_" <> tag)
    (crossFieldDigest openingZ1Raw :: StepField)
  Trace.field ("expand_proof.opening.z1.sDiv2_" <> tag) (sDiv2OfSf z1SplitField)
  Trace.field ("expand_proof.opening.z2.raw_" <> tag)
    (crossFieldDigest openingZ2Raw :: StepField)
  Trace.field ("expand_proof.opening.z2.sDiv2_" <> tag) (sDiv2OfSf z2SplitField)

  pure
    { challengePolynomialCommitment: expandProofResult.sg
    , slotUnfinalized: expandedUnfinalized
    , slotMsgWrapHashStep: msgWrapHashStep
    , slotKimchiPrevEntry:
        { sgX: (unwrap input.kimchiPrevSg).x
        , sgY: (unwrap input.kimchiPrevSg).y
        , challenges: input.kimchiPrevChallengesExpanded
        }
    , slotSppw
    }

--------------------------------------------------------------------------------
-- The step prover: compile, solve, kimchi proof creation
--------------------------------------------------------------------------------

-- | An inductive rule's body, as `stepMain` runs it. Universal in the
-- | advice row `r'`, so one rule value serves both the compile-time
-- | shape walk and solve-time witness generation.
-- |
-- | `output` is the rule's public output: `Unit` for an Input-mode
-- | rule, and for an Output-mode rule the value flowing back in the
-- | returned `RuleOutput`. `valCarrier` is the per-rule prev-statement
-- | carrier `Pickles.Step.Slots.SlotStatementsCarrier` derives from the
-- | rule's `prevsSpec` — `Unit` with no prevs, a right-nested `Tuple`
-- | chain otherwise.
-- |
-- | The prev statements are the rule's one advice need, and they arrive
-- | as the deferred `AsProver StepField r' valCarrier` getter rather
-- | than through a class on the monad. The getter is consumed inside
-- | the rule's `exists` bodies, which compile discards, so it is never
-- | forced there. A rule needing more advice adds ordinary constraints
-- | on its own monad.
type StepRule (n :: Int) valCarrier inputVal input outputVal output prevInputVal prevInput =
  forall r'
   . CircuitType StepField inputVal input
  => CircuitType StepField outputVal output
  => CircuitType StepField prevInputVal prevInput
  => CheckedType StepField (KimchiConstraint StepField) input
  => AsProver StepField r' valCarrier
  -> input
  -> Snarky StepField (KimchiConstraint StepField) r' (RuleOutput n prevInput output)

-- | `StepRule` pinned to one advice row `r` — the shape the runners and
-- | `mkRuleEntry` accept, and one a universal `StepRule` subsumes into.
-- |
-- | Pinning is what lets an application rule carry its own advice
-- | constraints: they discharge at the concrete row the entry is built
-- | at, where the instances are in scope, with no rank-2 skolem in the
-- | way.
type StepRuleAt (r :: Row (Type -> Type)) (n :: Int) valCarrier inputVal input outputVal output prevInputVal prevInput =
  CircuitType StepField inputVal input
  => CircuitType StepField outputVal output
  => CircuitType StepField prevInputVal prevInput
  => CheckedType StepField (KimchiConstraint StepField) input
  => AsProver StepField r valCarrier
  -> input
  -> Snarky StepField (KimchiConstraint StepField) r (RuleOutput n prevInput output)

-- | Ambient data the step prover needs alongside the advice and the
-- | rule: the `StepMainSrsData` that `stepMain` consumes, the dummy sg
-- | that pads `sg_old` in `verifyOne`, and the step circuit's Vesta SRS.
type StepProveContext :: Int -> Int -> Type -> Type
type StepProveContext len nd blueprints =
  { srsData :: StepMainSrsData len nd blueprints
  , dummySg :: AffinePoint StepField
  , crs :: CRS VestaG
  -- | When `true`, enables the solver's prover-state debug checks and
  -- | writes the step circuit's row → label map to
  -- | `/tmp/ps_step_row_labels.txt`.
  , debug :: Boolean
  -- | Optional disk proof-cache, threaded from `CompileMultiConfig`.
  -- | `Nothing` = no caching.
  , proofCache :: Maybe ProofCache
  }

-- | Artifacts produced by `stepCompile`, to hand between compile, wrap
-- | compile and solve. The prover and verifier indices are created here
-- | rather than in `stepSolveAndProve` because the step VK is what
-- | `buildWrapMainConfigMulti` needs before the solver runs.
type StepCompileResult =
  { proverIndex :: ProverIndex VestaG StepField
  , verifierIndex :: VerifierIndex VestaG StepField
  , gates :: Array (Gate StepField)
  , publicInputSize :: Int
  , builtState :: CircuitBuilderState (KimchiGate StepField) (AuxState StepField)
  , constraints :: Array (KimchiRow StepField)
  }

-- | Artifacts produced by `stepSolveAndProve`.
type StepProveResult (outputSize :: Int) =
  { proverIndex :: ProverIndex VestaG StepField
  , verifierIndex :: VerifierIndex VestaG StepField
  , witness :: Vector 15 (Array StepField)
  , publicInputs :: Array StepField
  , publicOutputs :: Vector outputSize (F StepField)
  , proof :: Proof VestaG StepField
  , assignments :: Assignments.Frozen StepField
  -- | The rule's user `publicOutput`, recovered post-solve and
  -- | flattened to fields. Raw `Array StepField` rather than
  -- | `outputVal`, so a consumer that wants the value applies its own
  -- | `fieldsToValue` and one that does not can ignore it. Empty when
  -- | the rule's output type is `Unit`.
  , userPublicOutputFields :: Array StepField
  }

-- | Write the step circuit's row → label map to
-- | `/tmp/ps_step_row_labels.txt`, so a row kimchi reports as failing
-- | can be traced back to the `label`/`labelM` call site that produced
-- | the constraint. One line per constraint,
-- | `"<row_start>..<row_end>\t<label>/…/<label>"`, the range covering
-- | the several kimchi rows a labelled constraint can expand to.
-- |
-- | Numbering matches the kimchi witness dump: the first
-- | `publicInputSize` rows are reserved for public-input placement, so
-- | constraint rows start there. The wrong offset gives labels that
-- | look right and point at the wrong row.
dumpRowLabels
  :: Int -- ^ the rows kimchi reserves for the public input
  -> Array (Labeled (KimchiGate StepField))
  -> Effect Unit
dumpRowLabels = writeRowLabelsTo "/tmp/ps_step_row_labels.txt"

-- | Monotonic counter for `KIMCHI_STEP_LABELS_DUMP`'s filename
-- | template.
stepLabelsCounter :: Ref.Ref Int
stepLabelsCounter = unsafePerformEffect (Ref.new 0)

bumpStepLabelsCounter :: Effect Int
bumpStepLabelsCounter = do
  n <- Ref.read stepLabelsCounter
  Ref.write (n + 1) stepLabelsCounter
  pure n

-- | Counter for `KIMCHI_STEP_CS_DUMP`'s `%c` template, separate from
-- | `stepLabelsCounter` so that enabling both dumps in one run keeps
-- | each sequence aligned.
stepCsCounter :: Ref.Ref Int
stepCsCounter = unsafePerformEffect (Ref.new 0)

bumpStepCsCounter :: Effect Int
bumpStepCsCounter = do
  n <- Ref.read stepCsCounter
  Ref.write (n + 1) stepCsCounter
  pure n

-- | `dumpRowLabels` to a caller-chosen path, which is how the
-- | `KIMCHI_STEP_LABELS_DUMP` dump gives each branch its own file.
writeRowLabelsTo
  :: String
  -> Int
  -> Array (Labeled (KimchiGate StepField))
  -> Effect Unit
writeRowLabelsTo path publicInputSize cs = do
  let
    { out, row: finalRow } = Array.foldl
      ( \{ row, out } lc ->
          let
            nRows = Array.length (toKimchiRows lc.constraint :: Array (KimchiRow StepField))
            endRow = row + nRows - 1
            ctxPath = Array.intercalate "/" lc.context
            line = show row <> ".." <> show endRow <> "\t" <> ctxPath
          in
            { row: row + nRows, out: out <> [ line ] }
      )
      { row: publicInputSize, out: [] }
      cs
    header =
      "# publicInputSize=" <> show publicInputSize
        <> " constraintRowsEnd="
        <> show finalRow
        <> " (kimchi witness row = offset + publicInputSize)"
  FS.writeTextFile UTF8 path
    (header <> "\n" <> Array.intercalate "\n" out <> "\n")

-- | The step constraint system: `stepMain` run under `compile`, with
-- | the builder state's constraints flattened to kimchi rows.
-- |
-- | Both compile-time entry points go through here. `stepCompile` turns
-- | the result into a prover index; `preComputeStepDomainLog2` only
-- | counts its rows. They share one body because the pre-pass sizes the
-- | step domain that the real compile is then built against, which only
-- | works if the two see the same circuit.
buildStepCircuit
  :: forall @prevsSpec @outputSize @valCarrier @inputVal @input @outputVal @output @prevInputVal @prevInput
       @mpvMax @mpvPad @nd
       ndPred
       len carrier carrierVar sideloadedVkCarrier vkSourcesCarrier blueprints
       pad unfsTotal digestPlusUnfs r
   . CircuitGateConstructor StepField VestaG
  => BuildSlotVkSources (SLVK.VerificationKey WrapVkChunks (F StepField) Boolean) prevsSpec WrapVkChunks len blueprints sideloadedVkCarrier vkSourcesCarrier
  => MkUnitVkCarrier prevsSpec sideloadedVkCarrier
  => Reflectable len Int
  => Reflectable pad Int
  => Reflectable mpvMax Int
  => Reflectable mpvPad Int
  => Reflectable nd Int
  => Reflectable outputSize Int
  => Add 1 ndPred nd
  => Compare 0 nd LT
  => Add pad len PaddedLength
  => Add mpvPad len mpvMax
  => Mul mpvMax Step.UnfinalizedFieldCount unfsTotal
  => Add unfsTotal 1 digestPlusUnfs
  => Add digestPlusUnfs mpvMax outputSize
  => CircuitType StepField inputVal input
  => CircuitType StepField outputVal output
  => CircuitType StepField prevInputVal prevInput
  => StepSlotsTyp prevsSpec carrier carrierVar
  => StepSlotsCarrier
       prevsSpec
       WrapVkChunks
       StepIPARounds
       WrapIPARounds
       (F StepField)
       (Type2 (SplitField (F StepField) Boolean))
       Boolean
       len
       carrier
       vkSourcesCarrier
  => StepSlotsCarrier
       prevsSpec
       WrapVkChunks
       StepIPARounds
       WrapIPARounds
       (FVar StepField)
       (Type2 (SplitField (FVar StepField) (BoolVar StepField)))
       (BoolVar StepField)
       len
       carrierVar
       vkSourcesCarrier
  => CheckedType StepField (KimchiConstraint StepField) input
  => AdviceHandler r
  -> StepProveContext len nd blueprints
  -> StepRuleAt r len valCarrier inputVal input outputVal output prevInputVal prevInput
  -> Effect
       { builtState :: CircuitBuilderState (KimchiGate StepField) (AuxState StepField)
       , kimchiRows :: Array (KimchiRow StepField)
       }
buildStepCircuit handler ctx rule = do
  -- The circuit shape depends only on `prevsSpec`, `len` and
  -- `carrier`, so the runtime VKs are irrelevant here: every slot gets
  -- the all-`Unit` carrier.
  let
    sideloadedCarrier = mkUnitVkCarrier @prevsSpec
  -- Every advice read lives inside an `exists` body, which `compile`
  -- discards, so the advice record is never projected and the
  -- `unsafeCoerce unit` bottom below is never forced.
  let
    dummyAdvice
      :: StepAdvice prevsSpec StepIPARounds WrapIPARounds WrapVkChunks
           inputVal
           len
           carrier
           valCarrier
           sideloadedVkCarrier
    dummyAdvice = unsafeCoerce unit
  -- A throwaway capture Ref: `compile` discards the `exists` body that
  -- would write it, so it stays `Nothing`.
  throwawayCaptureRef <- Ref.new Nothing
  builtState <-
    compile handler
      (Proxy @Unit)
      (Proxy @(Vector outputSize (F StepField)))
      (Proxy @(KimchiConstraint StepField))
      ( \_ ->
          stepMain
            @prevsSpec
            @inputVal
            @outputVal
            @prevInputVal
            @valCarrier
            @mpvMax
            @nd
            @(SLVK.VerificationKey WrapVkChunks (F StepField) Boolean)
            rule
            ctx.srsData
            ctx.dummySg
            sideloadedCarrier
            dummyAdvice
            throwawayCaptureRef
      )

  pure
    { builtState
    , kimchiRows:
        concatMap (toKimchiRows <<< _.constraint) (constraintsToArray builtState.constraints)
    }

-- | The step circuit built, with the kimchi prover and verifier
-- | indices created from its gates.
stepCompile
  :: forall @prevsSpec @outputSize @valCarrier @inputVal @input @outputVal @output @prevInputVal @prevInput
       @mpvMax @mpvPad @nd
       ndPred
       len carrier carrierVar sideloadedVkCarrier vkSourcesCarrier blueprints
       pad unfsTotal digestPlusUnfs r
   . CircuitGateConstructor StepField VestaG
  => BuildSlotVkSources (SLVK.VerificationKey WrapVkChunks (F StepField) Boolean) prevsSpec WrapVkChunks len blueprints sideloadedVkCarrier vkSourcesCarrier
  => MkUnitVkCarrier prevsSpec sideloadedVkCarrier
  => Reflectable len Int
  => Reflectable pad Int
  => Reflectable mpvMax Int
  => Reflectable mpvPad Int
  => Reflectable nd Int
  => Reflectable outputSize Int
  => Add 1 ndPred nd
  => Compare 0 nd LT
  => Add pad len PaddedLength
  => Add mpvPad len mpvMax
  => Mul mpvMax Step.UnfinalizedFieldCount unfsTotal
  => Add unfsTotal 1 digestPlusUnfs
  => Add digestPlusUnfs mpvMax outputSize
  => CircuitType StepField inputVal input
  => CircuitType StepField outputVal output
  => CircuitType StepField prevInputVal prevInput
  => StepSlotsTyp prevsSpec carrier carrierVar
  => StepSlotsCarrier
       prevsSpec
       WrapVkChunks
       StepIPARounds
       WrapIPARounds
       (F StepField)
       (Type2 (SplitField (F StepField) Boolean))
       Boolean
       len
       carrier
       vkSourcesCarrier
  => StepSlotsCarrier
       prevsSpec
       WrapVkChunks
       StepIPARounds
       WrapIPARounds
       (FVar StepField)
       (Type2 (SplitField (FVar StepField) (BoolVar StepField)))
       (BoolVar StepField)
       len
       carrierVar
       vkSourcesCarrier
  => CheckedType StepField (KimchiConstraint StepField) input
  => AdviceHandler r
  -> StepProveContext len nd blueprints
  -> StepRuleAt r len valCarrier inputVal input outputVal output prevInputVal prevInput
  -> Effect StepCompileResult
stepCompile handler ctx rule = do
  { builtState, kimchiRows } <-
    buildStepCircuit
      @prevsSpec
      @outputSize
      @valCarrier
      @inputVal
      @input
      @outputVal
      @output
      @prevInputVal
      @prevInput
      @mpvMax
      @mpvPad
      @nd
      handler
      ctx
      rule
  csResult <- makeConstraintSystemWithPrevChallenges @StepField
    { constraints: kimchiRows
    , publicInputs: builtState.publicInputs
    , unionFind: (un AuxState builtState.aux).wireState.unionFind
    , prevChallengesCount: reflectType (Proxy @len)
    , maxPolySize: crsSize ctx.crs
    }
  let
    { gates, publicInputSize, constraints } = csResult

    -- No `cs.endo` in the argument record: `createProverIndex`'s JS
    -- implementation fetches the step curve's endo_base
    -- (= `Pallas.endo_base`) from the napi layer itself.
    proverIndex =
      createProverIndex @StepField @VestaG
        { gates
        , publicInputSize
        , prevChallengesCount: csResult.prevChallengesCount
        , maxPolySize: csResult.maxPolySize
        , crs: ctx.crs
        }

    verifierIndex = createVerifierIndex @StepField @VestaG proverIndex

  -- Optional compile-time dump of the row → label map, gated on
  -- `KIMCHI_STEP_LABELS_DUMP`, which localizes a per-branch constraint
  -- divergence without going through prove. `%c` in the filename
  -- template expands to a monotonic counter, one file per branch.
  Process.lookupEnv "KIMCHI_STEP_LABELS_DUMP" >>= case _ of
    Nothing -> pure unit
    Just pathTmpl -> do
      counter <- bumpStepLabelsCounter
      let
        path = String.replaceAll (Pattern "%c") (Replacement (show counter)) pathTmpl
        publicInputSize = Array.length builtState.publicInputs
      writeRowLabelsTo path publicInputSize (constraintsToArray builtState.constraints)

  -- Optional dump of the step constraint system as JSON, gated on
  -- `KIMCHI_STEP_CS_DUMP`. `%c` expands to a counter of its own,
  -- independent of `KIMCHI_STEP_LABELS_DUMP`'s.
  Process.lookupEnv "KIMCHI_STEP_CS_DUMP" >>= case _ of
    Nothing -> pure unit
    Just pathTmpl -> do
      counter <- bumpStepCsCounter
      let path = String.replaceAll (Pattern "%c") (Replacement (show counter)) pathTmpl
      FS.writeTextFile UTF8 path (gatesToJson gates publicInputSize)

  pure
    { proverIndex
    , verifierIndex
    , gates
    , publicInputSize
    , builtState
    , constraints
    }

-- | The rule's own step-circuit domain log2,
-- | `ceilLog2 (zkRows + publicInputSize + rowCount)`, from a pre-pass
-- | that builds the constraint system but creates no prover index.
-- |
-- | The gate count is the one `stepCompile` would get from the same
-- | `ctx`, both going through `buildStepCircuit`. The caller supplies a
-- | `ctx` whose `Self` slots carry a placeholder `selfStepDomainLog2`
-- | of 20; `External` slots use the real values from their compiled
-- | prover indices.
-- |
-- | Lookup-table sizing is omitted: no current rule uses
-- | `range_check`, `xor`, `lookup` or `runtime_tables` gates.
preComputeStepDomainLog2
  :: forall @prevsSpec @outputSize @valCarrier @inputVal @input @outputVal @output @prevInputVal @prevInput
       @mpvMax @mpvPad @nd
       ndPred
       len carrier carrierVar sideloadedVkCarrier vkSourcesCarrier blueprints
       pad unfsTotal digestPlusUnfs r
   . CircuitGateConstructor StepField VestaG
  => BuildSlotVkSources (SLVK.VerificationKey WrapVkChunks (F StepField) Boolean) prevsSpec WrapVkChunks len blueprints sideloadedVkCarrier vkSourcesCarrier
  => MkUnitVkCarrier prevsSpec sideloadedVkCarrier
  => Reflectable len Int
  => Reflectable pad Int
  => Reflectable mpvMax Int
  => Reflectable mpvPad Int
  => Reflectable nd Int
  => Reflectable outputSize Int
  => Add 1 ndPred nd
  => Compare 0 nd LT
  => Add pad len PaddedLength
  => Add mpvPad len mpvMax
  => Mul mpvMax Step.UnfinalizedFieldCount unfsTotal
  => Add unfsTotal 1 digestPlusUnfs
  => Add digestPlusUnfs mpvMax outputSize
  => CircuitType StepField inputVal input
  => CircuitType StepField outputVal output
  => CircuitType StepField prevInputVal prevInput
  => StepSlotsTyp prevsSpec carrier carrierVar
  => StepSlotsCarrier
       prevsSpec
       WrapVkChunks
       StepIPARounds
       WrapIPARounds
       (F StepField)
       (Type2 (SplitField (F StepField) Boolean))
       Boolean
       len
       carrier
       vkSourcesCarrier
  => StepSlotsCarrier
       prevsSpec
       WrapVkChunks
       StepIPARounds
       WrapIPARounds
       (FVar StepField)
       (Type2 (SplitField (FVar StepField) (BoolVar StepField)))
       (BoolVar StepField)
       len
       carrierVar
       vkSourcesCarrier
  => CheckedType StepField (KimchiConstraint StepField) input
  => AdviceHandler r
  -> StepProveContext len nd blueprints
  -> StepRuleAt r len valCarrier inputVal input outputVal output prevInputVal prevInput
  -> Effect Int
preComputeStepDomainLog2 handler ctx rule = do
  { builtState, kimchiRows } <-
    buildStepCircuit
      @prevsSpec
      @outputSize
      @valCarrier
      @inputVal
      @input
      @outputVal
      @output
      @prevInputVal
      @prevInput
      @mpvMax
      @mpvPad
      @nd
      handler
      ctx
      rule
  let
    gateCount = Array.length kimchiRows
    piSize = Array.length builtState.publicInputs
    -- Domain selection uses the one-chunk `zk_rows`, not the circuit's
    -- chunk-derived one: this constant belongs to the selection and
    -- does not follow `num_chunks`. A compile at `stepChunks = 2` sizes
    -- its domain here and still uses the real
    -- `zkRowsForNumChunks stepChunks` where the proof is checked, in
    -- `Pickles.Prove.Compile`'s `selfZkRows`. Deriving this one from
    -- `stepChunks` would shift the step domains.
    zkRows = zkRowsForNumChunks 1
    rows = zkRows + piSize + gateCount
  pure (ceilLog2 rows)
  where
  -- | The smallest `k` with `2^k >= n`; both `n = 0` and `n = 1` give 0.
  ceilLog2 :: Int -> Int
  ceilLog2 n = go 0 1
    where
    go acc p = if p >= n then acc else go (acc + 1) (p * 2)

-- | Solve phase of the step prover: runs the solver on a compiled
-- | circuit and the real advice, and creates the kimchi proof. Its
-- | `prevChallenges` come from the advice's `kimchiPrevChallenges`.
-- | Errors surface as `Either EvaluationError`, an unsatisfied
-- | constraint system among them as `FailedAssertion`.
stepSolveAndProve
  :: forall @prevsSpec @outputSize @valCarrier @inputVal @input @outputVal @output @prevInputVal @prevInput
       @mpvMax @mpvPad @nd
       ndPred
       len carrier carrierVar sideloadedVkCarrier vkSourcesCarrier blueprints
       pad unfsTotal digestPlusUnfs r
   . CircuitGateConstructor StepField VestaG
  => BuildSlotVkSources (SideloadBundle.SlotProveVk WrapVkChunks) prevsSpec WrapVkChunks len blueprints sideloadedVkCarrier vkSourcesCarrier
  => SideloadedVKsCarrier prevsSpec sideloadedVkCarrier
  => Reflectable len Int
  => Reflectable pad Int
  => Reflectable mpvMax Int
  => Reflectable mpvPad Int
  => Reflectable nd Int
  => Reflectable outputSize Int
  => Add 1 ndPred nd
  => Compare 0 nd LT
  => Add pad len PaddedLength
  => Add mpvPad len mpvMax
  => Mul mpvMax Step.UnfinalizedFieldCount unfsTotal
  => Add unfsTotal 1 digestPlusUnfs
  => Add digestPlusUnfs mpvMax outputSize
  => CircuitType StepField inputVal input
  => CircuitType StepField outputVal output
  => CircuitType StepField prevInputVal prevInput
  => StepSlotsTyp prevsSpec carrier carrierVar
  => StepSlotsCarrier
       prevsSpec
       WrapVkChunks
       StepIPARounds
       WrapIPARounds
       (F StepField)
       (Type2 (SplitField (F StepField) Boolean))
       Boolean
       len
       carrier
       vkSourcesCarrier
  => StepSlotsCarrier
       prevsSpec
       WrapVkChunks
       StepIPARounds
       WrapIPARounds
       (FVar StepField)
       (Type2 (SplitField (FVar StepField) (BoolVar StepField)))
       (BoolVar StepField)
       len
       carrierVar
       vkSourcesCarrier
  => CheckedType StepField (KimchiConstraint StepField) input
  => SlotStatementsCarrier prevsSpec valCarrier
  => AdviceHandler r
  -> StepProveContext len nd blueprints
  -> StepRuleAt r len valCarrier inputVal input outputVal output prevInputVal prevInput
  -> StepCompileResult
  -> StepAdvice prevsSpec StepIPARounds WrapIPARounds WrapVkChunks inputVal len carrier valCarrier sideloadedVkCarrier
  -> Effect (Either EvaluationError (StepProveResult outputSize))
stepSolveAndProve handler ctx rule compileResult advice = do
  -- Capture channel for the rule's user `publicOutput` FVars. The
  -- solver makes `stepMain`'s whole return value public, and these
  -- FVars must not be, so they ride a Ref instead: passed into
  -- `stepMain`, written inside an `exists` body at solve time, read
  -- back here. It is the only mutable channel — the read-only advice
  -- flows as a plain argument.
  captureRef <- Ref.new Nothing
  -- Taking the side-loaded VK carrier from the advice keeps the monad
  -- arbitrary, with no class constraint to discharge.
  let
    StepAdvice adv = advice
    sideloadedCarrier = adv.sideloadedVKs

    rawSolver
      :: SolverT StepField (KimchiConstraint StepField)
           r
           Unit
           (Vector outputSize (F StepField))
    rawSolver =
      makeSolver' { debug: ctx.debug }
        (Proxy @(KimchiConstraint StepField))
        ( \_ ->
            stepMain
              @prevsSpec
              @inputVal
              @outputVal
              @prevInputVal
              @valCarrier
              @mpvMax
              @nd
              @(SideloadBundle.SlotProveVk WrapVkChunks)
              rule
              ctx.srsData
              ctx.dummySg
              sideloadedCarrier
              advice
              captureRef
        )

  eRes <- rawSolver handler unit

  case eRes of
    Left e -> pure (Left (WithContext "stepProve solver" e))
    Right (Tuple publicOutputs assignments) -> do
      let
        { witness, publicInputs } = makeWitness
          { assignments
          , constraints: map _.variables compileResult.constraints
          , publicInputs: compileResult.builtState.publicInputs
          }
      when ctx.debug do
        let
          _ = unsafePerformEffect $
            dumpRowLabels
              (Array.length compileResult.builtState.publicInputs)
              (constraintsToArray compileResult.builtState.constraints)
        pure unit
      -- Evaluate the user `publicOutput` FVars `stepMain` wrote to
      -- `captureRef` against the post-solve assignments. An empty Ref
      -- means the rule body never ran, which surfaces as a
      -- `FailedAssertion` rather than a silent array of zeros.
      captured <- Ref.read captureRef
      let
        eUserPublicOutputFields = case captured of
          Nothing ->
            Left (FailedAssertion "stepProve: stepMain did not capture publicOutput FVars (captureRef was Nothing post-solve)")
          Just fieldVars ->
            let
              evalLookup :: Variable -> Either EvaluationError StepField
              evalLookup v =
                maybe (Left (MissingVariable v)) Right (Assignments.lookupFrozen v assignments)
            in
              traverse (CVar.eval evalLookup) fieldVars
      case eUserPublicOutputFields of
        Left e -> pure (Left e)
        Right userPublicOutputFields -> do
          let
            p = Lazy.defer \_ -> pallasCreateProofWithPrev
              { proverIndex: compileResult.proverIndex
              , witness
              , prevChallenges:
                  map
                    ( \r ->
                        { sgX: r.sgX
                        , sgY: r.sgY
                        , challenges: Vector.toUnfoldable r.challenges
                        }
                    )
                    ( Vector.toUnfoldable adv.kimchiPrevChallenges
                        :: Array
                             { sgX :: WrapField
                             , sgY :: WrapField
                             , challenges :: Vector StepIPARounds StepField
                             }
                    )
              }
          proof <-
            case ctx.proofCache of
              Nothing -> pure $ Lazy.force p
              Just cache -> do
                mp <- getPallasProof cache compileResult.verifierIndex publicInputs
                case mp of
                  Just proof -> pure proof
                  Nothing -> do
                    let proof = Lazy.force p
                    setPallasProof cache compileResult.verifierIndex publicInputs proof
                    pure proof
          pure $ Right
            { proverIndex: compileResult.proverIndex
            , verifierIndex: compileResult.verifierIndex
            , witness
            , publicInputs
            , publicOutputs
            , proof
            , assignments
            , userPublicOutputFields
            }

