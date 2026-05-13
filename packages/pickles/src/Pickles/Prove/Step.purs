-- | Prover-side infrastructure for `Pickles.Step.Main.stepMain`.
-- |
-- | Sister to `Pickles.Prove.Wrap`. This module provides the
-- | **effectful** glue that feeds `stepMain`'s `Req.*` advice during
-- | witness generation:
-- |
-- | * `StepAdvice` — a newtype holding all advice pieces (one per
-- |   OCaml `Req.*` request) keyed on the spec-indexed per-slot
-- |   `carrier`. Heterogeneous-prev rules (Tree_proof_return style)
-- |   use distinct per-slot shapes via `StepSlot n_i …`.
-- | * `StepProverT` — a `ReaderT` transformer serving `StepAdvice`
-- |   to the circuit body. Instances implement `StepWitnessM` /
-- |   `StepSlotsM` so the `stepMain` circuit body can `ask` for each
-- |   advice piece.
-- | * `runStepProverT` — runner that supplies the advice and unwraps
-- |   to the base monad (`Effect`).
-- | * `stepProve` — compile + solve + kimchi proof creation,
-- |   mirroring OCaml's `Backend.Tick.Proof.create_async` call site
-- |   in `mina/src/lib/crypto/pickles/step.ml:800-852`.
-- |
-- | The module is polymorphic in `prevsSpec` (the type-level
-- | per-slot `max_proofs_verified` list), `ds` (step IPA rounds), and
-- | `dw` (wrap IPA rounds). The commitment curve is pinned to
-- | `PallasG` (the wrap proof being verified by step has commitments
-- | on Pallas) and the field to `StepField` (= `Vesta.ScalarField` =
-- | `Pallas.BaseField`) — both structural for any step circuit in
-- | the Pasta cycle, not specific to any one application rule.
module Pickles.Prove.Step
  ( StepBranchData
  , BuildStepAdviceInput
  , BuildSlotAdviceInput
  , extractWrapVKCommsAdvice
  , extractWrapVKForStepHash
  , dummyWrapTockPublicInput
  , StepRule
  , StepCompileResult
  , StepProveResult
  , StepAdvice(..)
  , StepProverT(..)
  , StepProverCapture
  , runStepProverT
  , StepProveContext
  , SlotAdviceContrib
  , buildSlotAdvice
  , buildStepAdvice
  , stepCompile
  , preComputeStepDomainLog2
  , stepSolveAndProve
  -- mpvMax-padding helpers
  , mkDummyMsgWrapHash
  ) where

import Prelude

import Control.Monad.Except (ExceptT, throwError)
import Control.Monad.Reader (ReaderT, ask, runReaderT)
import Control.Monad.State (StateT, runStateT)
import Control.Monad.State as State
import Control.Monad.Trans.Class (lift)
import Data.Array (concatMap)
import Data.Array as Array
import Data.Array.NonEmpty as NonEmptyArray
import Data.Either (Either(..))
import Data.Fin (getFinite, unsafeFinite)
import Data.Foldable (for_)
import Data.FoldableWithIndex (forWithIndex_)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..), fromJust, maybe)
import Data.Newtype (class Newtype, un, unwrap)
import Data.Reflectable (class Reflectable, reflectType)
import Data.String (Pattern(..), Replacement(..))
import Data.String as String
import Data.Traversable (traverse)
import Data.Tuple (Tuple(..))
import Data.Vector (Vector)
import Data.Vector as Vector
import Effect (Effect)
import Effect.Ref as Ref
import Effect.Unsafe (unsafePerformEffect)
import Node.Encoding (Encoding(..))
import Node.FS.Sync as FS
import Node.Process as Process
import Partial.Unsafe (unsafePartial)
import Pickles.Constants (zkRows)
import Pickles.Dummy (dummyIpaChallenges)
import Pickles.Field (StepField, WrapField)
import Pickles.Linearization (pallas, vesta) as Linearization
import Pickles.Linearization.FFI (PointEval) as LFFI
import Pickles.Linearization.FFI (domainGenerator, domainShifts)
import Pickles.PlonkChecks.Chunks as Chunks
import Pickles.PlonkChecks (AllEvals)
import Pickles.ProofFFI (Proof, pallasCreateProofWithPrev, permutationVanishingPolynomial, proofCoefficientEvals, proofIndexEvals, proofSigmaEvals, proofWitnessEvals, proofZEvals, tCommChunked, vestaProofCommitments, vestaProofOpeningDelta, vestaProofOpeningLrVec, vestaProofOpeningPrechallenges, vestaProofOpeningZ1, vestaProofOpeningZ2, vestaProofOracles, vestaVerifierIndexCommitments, vestaVerifierIndexDigest, wCommChunked, zCommChunked)
import Pickles.Prove.Pure.Common (crossFieldDigest)
import Pickles.Prove.Pure.Step (expandProof) as PureStep
import Pickles.Prove.Pure.Wrap (packBranchDataWrap, revOnesVector)
import Pickles.Sideload.Advice (class MkUnitVkCarrier, class SideloadedVKsCarrier, class SideloadedVKsM, getSideloadedVKsCarrier)
import Pickles.Sideload.Bundle (Bundle) as SideloadBundle
import Pickles.Sideload.VerificationKey (VerificationKey) as SLVK
import Pickles.Step.Advice (class StepPrevValuesM, class StepSlotsM, class StepUserOutputM, class StepWitnessM)
import Pickles.Step.Dummy (BaseCaseDummies, computeDummySgValues) as Dummy
import Pickles.Step.Dummy (baseCaseDummies, stepDummyUnfinalizedProof, wrapDomainLog2ForProofsVerified, wrapDummyUnfinalizedProof)
import Pickles.Step.Main (class BuildSlotVkSources, RuleOutput, StepMainSrsData, stepMain)
import Pickles.Step.Main as MpvPadding
import Pickles.Step.MessageHash (hashMessagesForNextStepProofPure, hashMessagesForNextStepProofPureTraced)
import Pickles.Step.Slots (class SlotStatementsCarrier, class StepSlotsCarrier, replicateStepSlotsCarrier)
import Pickles.Step.Types as Step
import Pickles.Trace as Trace
import Pickles.Types (PaddedLength, PerProofUnfinalized(..), PointEval(..), StepAllEvals(..), StepIPARounds, WrapIPARounds, WrapProofMessages(..), WrapProofOpening(..))
import Pickles.VerificationKey (StepVK, VerificationKey(..))
import Pickles.Verify.Types (BranchData) as VT
import Pickles.Verify.Types (UnfinalizedProof)
import Pickles.Wrap.MessageHash (hashMessagesForNextWrapProofPureGeneral)
import Prim.Int (class Add, class Compare, class Mul)
import Prim.Ordering (LT)
import Safe.Coerce (coerce)
import Snarky.Backend.Builder (CircuitBuilderState, Labeled)
import Snarky.Backend.Compile (SolverT, compile, makeSolver', runSolverT)
import Snarky.Backend.Kimchi (makeConstraintSystemWithPrevChallenges, makeWitness)
import Snarky.Backend.Kimchi.Class (class CircuitGateConstructor, createProverIndex, createVerifierIndex, crsSize, verifyProverIndex)
import Snarky.Backend.Kimchi.Impl.Vesta (vestaConstraintSystemToJson)
import Snarky.Backend.Kimchi.Types (CRS, ConstraintSystem, ProverIndex, VerifierIndex)
import Snarky.Backend.Prover (emptyProverState)
import Snarky.Circuit.CVar (EvaluationError(..), Variable)
import Snarky.Circuit.CVar as CVar
import Snarky.Circuit.DSL (class CircuitM, BoolVar, F(..), FVar, SizedF, Snarky, UnChecked(..), coerceViaBits)
import Snarky.Circuit.DSL.Monad (class CheckedType)
import Snarky.Circuit.DSL.SizedF (toField, unwrapF, wrapF) as SizedF
import Snarky.Circuit.Kimchi (toFieldPure)
import Snarky.Circuit.Types (class CircuitType, valueToFields)
import Snarky.Constraint.Kimchi (KimchiConstraint, KimchiGate)
import Snarky.Constraint.Kimchi as Kimchi
import Snarky.Constraint.Kimchi.Types (AuxState(..), KimchiRow, toKimchiRows)
import Snarky.Curves.Class (EndoBase(..), EndoScalar(..), endoBase, endoScalar)
import Snarky.Curves.Class (fromInt, generator, toAffine) as Curves
import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Pasta (PallasG, VestaG)
import Snarky.Data.EllipticCurve (AffinePoint, WeierstrassAffinePoint(..))
import Snarky.Types.Shifted (SplitField(..), Type1(..), Type2(..), fromShifted, toShifted)
import Type.Proxy (Proxy(..))

--------------------------------------------------------------------------------
-- Advice
--------------------------------------------------------------------------------

-- | Per-proof branch data. OCaml:
-- |   `mina/src/lib/crypto/pickles/step_main.ml` packs each prev
-- |   proof's `branch_data` into the output via
-- |   `branch_data.pack = 4*domain_log2 + mask[0] + 2*mask[1]`.
-- |
-- | For single-rule compiles, all slots have the same `domainLog2`
-- | (read from `basic.step_domains.h` — for Simple_chain this is 16,
-- | per `dump_circuit_impl.ml:3723`) and `mask0`/`mask1` encode
-- | which prev-proof slot is active.
type StepBranchData =
  { domainLog2 :: F StepField
  , mask0 :: Boolean
  , mask1 :: Boolean
  }

--------------------------------------------------------------------------------
-- Base-case advice builder
--
-- `buildStepAdvice` assembles a fully-populated `StepAdvice` from
-- the few parameters a specific inductive rule's BASE case actually
-- picks (appState, stepDomainLog2, mostRecentWidth). Every other
-- field is filled from the Ro-derived dummies in `Pickles.Dummy`,
-- which are hardcoded at the Pasta protocol constants
-- `Tick.Rounds.n = 16` / `Tock.Rounds.n = 15` — matching OCaml
-- `dummy.ml:27-55` exactly.
--
-- Polymorphic in `prevsSpec` (the type-level per-slot
-- max_proofs_verified list). The per-slot dummy values feed a rank-2
-- `StepSlot n_i ds dw …` that `replicateStepSlotsCarrier` broadcasts to
-- each slot at its own `n_i`. The output type pins `ds` / `dw` at
-- `StepIPARounds` / `WrapIPARounds` because the underlying
-- `Pickles.Dummy` helpers are concretized there.
--
-- References:
--   OCaml `Proof.dummy h most_recent_width ~domain_log2` (proof.ml:115-208)
--   OCaml `step_main.ml:368-376` exists calls for Req.App_state,
--                                  Req.Unfinalized_proofs, Req.Wrap_index
--------------------------------------------------------------------------------

-- | Inputs `buildStepAdvice` needs from the caller. Everything else
-- | is protocol-constant dummy data derived from `Pickles.Dummy`.
-- | Inputs to `buildStepAdvice`. `most_recent_width` is NOT a field —
-- | it's carried at the type level as `len` (the number of prev slots,
-- | derived from `prevsSpec` via the `StepSlotsCarrier` instance), and
-- | reified to an Int internally via `reflectType (Proxy @len)` where
-- | needed.
type BuildStepAdviceInput inputVal valCarrier vkCarrier =
  { -- | Value bound to the step circuit's public input (OCaml
    -- | `Req.App_state`). Polymorphic in `inputVal` so rules with
    -- | Input-mode typ other than `Field.typ` can bind multi-field
    -- | records. For Simple_chain base case this is `F zero` (self = 0).
    publicInput :: inputVal

  -- | The prev rule's STEP domain log2 (= `branch_data.domain_log2`
  -- | of its wrap statement, per `proof.ml:140-141`). For
  -- | self-recursive rules with `override_wrap_domain` this also equals
  -- | `wrap_domains.h` (`common.ml:25-29`); for Simple_chain N1 this is
  -- | 14. Distinct from the step circuit's own kimchi domain (= 16
  -- | per `dump_circuit_impl.ml:3721-3723`); that value is determined
  -- | by kimchi at proof-creation time, not read from advice.
  , stepDomainLog2 :: Int

  -- | Heterogeneous per-slot prev statements (mirrors OCaml's
  -- | `previous_proof_statements` argument to `Inductive_rule.t.main`).
  -- | The carrier shape is determined by `prevsSpec` via
  -- | `SlotStatementsCarrier`. Each slot's value is the prev's
  -- | `StatementIO inputVal outputVal` — even on the base case,
  -- | callers supply an inhabitant of the right type (the values are
  -- | irrelevant when `proofMustVerify[i] = false`).
  , prevAppStates :: valCarrier

  -- | Spec-indexed runtime side-loaded VK carrier (mirrors OCaml's
  -- | per-prove `~handler` model). Compiled slots contribute `Unit`;
  -- | side-loaded slots contribute a runtime VerificationKey. Persisted
  -- | into `StepAdvice.sideloadedVKs` so `getSideloadedVKsCarrier` can
  -- | source it from inside the step rule body.
  , sideloadedVKs :: vkCarrier
  }

-- | Build a base-case `StepAdvice` keyed on a spec-indexed per-slot
-- | carrier.
-- |
-- | Requires a `StepSlotsCarrier prevsSpec … len carrier` instance so the
-- | caller's `prevsSpec` determines `len` (= number of prev slots) and
-- | `carrier` (= nested-tuple carrier type). The rank-2 `dummySlot`
-- | builds each slot's `Step.PerProofWitness` with the correct per-slot
-- | `n_i` via `Vector.replicate`.
-- |
-- | Handles homogeneous specs (Simple_chain N1/N2, Add_one_return) and
-- | heterogeneous specs (Tree_proof_return `[N0; N2]`) uniformly —
-- | `Vector.replicate` at `n=0` produces nil, so slots with `n_i=0`
-- | have empty `prevChallenges` / `prevSgs` automatically.
buildStepAdvice
  :: forall @prevsSpec inputVal len carrier valCarrier vkCarrier
   . Reflectable len Int
  => StepSlotsCarrier
       prevsSpec
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
  -> StepAdvice prevsSpec StepIPARounds WrapIPARounds wrapVkChunks inputVal len carrier valCarrier vkCarrier
buildStepAdvice input =
  let
    -- Pallas generator (= OCaml `Tock.Curve.one`). Never the
    -- point-at-infinity, so `toAffine` is always `Just`. Reused for
    -- every curve-point field in the base-case dummy advice.
    g0 = coerce (unsafePartial (fromJust (Curves.toAffine (Curves.generator :: Pallas.G))) :: AffinePoint StepField)

    g0w = WeierstrassAffinePoint g0

    -- Reify `len` (= most_recent_width = max_proofs_verified) to a
    -- runtime Int for the few places that need one.
    mrw = reflectType (Proxy @len)

    -- Ro-derived constants shared across all fields.
    bcd = baseCaseDummies { maxProofsVerified: mrw }

    -- z1 / z2 from OCaml `proof.ml:dummy` openings (Ro.tock values
    -- re-wrapped as cross-field Type2 SplitField in the step field).
    z1 = toShifted (F bcd.proofDummy.z1)

    z2 = toShifted (F bcd.proofDummy.z2)

    wrapPE :: LFFI.PointEval StepField -> LFFI.PointEval (F StepField)
    wrapPE pe = { zeta: F pe.zeta, omegaTimesZeta: F pe.omegaTimesZeta }

    wrapAE :: AllEvals StepField -> AllEvals (F StepField)
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
        StepAllEvals
          { publicEvals: PointEval aeF.publicEvals
          , witnessEvals: map PointEval aeF.witnessEvals
          , coeffEvals: map PointEval aeF.coeffEvals
          , zEvals: PointEval aeF.zEvals
          , sigmaEvals: map PointEval aeF.sigmaEvals
          , indexEvals: map PointEval aeF.indexEvals
          , ftEval1: aeF.ftEval1
          }

    dummyFop
      :: UnfinalizedProof StepIPARounds (F StepField) (Type1 (F StepField)) Boolean
    dummyFop = stepDummyUnfinalizedProof @len bcd
      { domainLog2: wrapDomainLog2ForProofsVerified mrw }
      (map SizedF.wrapF bcd.ipaStepChallenges)

    dummyBranch =
      -- OCaml wrap_main.ml:231-238 computes
      -- `actual_proofs_verified_mask = ones_vector ~first_zero:w
      --  |> Vector.rev`. Yields per-width masks:
      --   N0 → [F, F]
      --   N1 → [F, T]
      --   N2 → [T, T]
      { domainLog2: F (Curves.fromInt input.stepDomainLog2)
      , mask0: mrw >= 2
      , mask1: mrw >= 1
      }

    dvFop = dummyFop.deferredValues
    pFop = dvFop.plonk

    -- Cross-field conversion of `wrapDummyUnfinalizedProof` (which
    -- is in wrap-field `Type2 (F WrapField)`) to the step-field
    -- `Type2 (SplitField (F StepField) Boolean)` that step_main's
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

    -- Rank-2 per-slot dummy: the only n-dependent fields (`prevChallenges`,
    -- `prevSgs`) use `Vector.replicate` so they specialize per slot.
    -- All other fields are slot-agnostic and reused verbatim.
    --
    -- NB: the `UnChecked <$>` on `bulletproofChallenges` etc. matches
    -- OCaml's in-circuit wrapping at the FOP state construction site.
    dummySlot
      :: forall n nc
       . Reflectable n Int
      => Reflectable nc Int
      => Step.PerProofWitness
           n
           nc
           StepIPARounds
           WrapIPARounds
           (F StepField)
           (Type2 (SplitField (F StepField) Boolean))
           Boolean
    dummySlot = Step.PerProofWitness
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
              { wComm: Vector.generate (\_ -> Vector.replicate (WeierstrassAffinePoint g0))
              , zComm: Vector.replicate (WeierstrassAffinePoint g0)
              , tComm: Vector.generate (\_ -> Vector.replicate (WeierstrassAffinePoint g0))
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
          , branchData: Step.BranchData
              { domainLog2: dummyBranch.domainLog2
              , mask0: dummyBranch.mask0
              , mask1: dummyBranch.mask1
              }
          }
      , prevEvals: prevEvalsDummy
      , prevChallenges:
          Vector.replicate (UnChecked (map F dummyIpaChallenges.stepExpanded))
      , prevSgs: Vector.replicate (WeierstrassAffinePoint g0)
      }
  in
    StepAdvice
      { perProofSlotsCarrier: replicateStepSlotsCarrier @prevsSpec dummySlot
      , publicInput: input.publicInput
      , publicUnfinalizedProofs: Vector.replicate dummyPublicUnfinalized
      , messagesForNextWrapProof: Vector.replicate (F zero)
      , messagesForNextWrapProofDummyHash: F zero
      , wrapVerifierIndex:
          VerificationKey
            { sigma: Vector.generate (const g0w)
            , coeff: Vector.generate (const g0w)
            , index: Vector.generate (const g0w)
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

-- | Extract sigma/coeff/index point triples from a compiled wrap
-- | verifier index, in the lightweight `Pickles.VerificationKey.VerificationKey`
-- | shape the step advice uses (WeierstrassAffinePoint PallasG (F
-- | StepField)). The wrap VK's commitments are Pallas points with
-- | coordinates in Pallas.BaseField = StepField, so no cross-field
-- | coercion is needed.
-- | Polymorphic on `wrapVkChunks` — the wrap VK's own chunk count
-- | (Dim 2). Distinct from the wrap circuit's `numChunks` (Dim 1)
-- | and from a side-loaded slot's chunks (Dim 3 / `nc`).
extractWrapVKCommsAdvice
  :: forall @wrapVkChunks
   . Reflectable wrapVkChunks Int
  => VerifierIndex PallasG WrapField
  -> VerificationKey wrapVkChunks (WeierstrassAffinePoint PallasG (F StepField))
extractWrapVKCommsAdvice vk =
  let
    comms = vestaVerifierIndexCommitments @wrapVkChunks vk

    wrapPt :: AffinePoint StepField -> WeierstrassAffinePoint PallasG (F StepField)
    wrapPt pt = WeierstrassAffinePoint { x: F pt.x, y: F pt.y }
  in
    VerificationKey
      { sigma: map (map wrapPt) comms.sigma
      , coeff: map (map wrapPt) comms.coeff
      , index: map (map wrapPt) comms.index
      }

-- | `StepVK wrapVkChunks StepField` extracted from a compiled wrap
-- | verifier index. Used for `hashMessagesForNextStepProofPure` in
-- | the step field — the dummy wrap proof's
-- | `messages_for_next_step_proof` hash mirrors OCaml's
-- | `Common.hash_messages_for_next_step_proof` on the real wrap VK.
-- |
-- | `wrapVkChunks` is the wrap VK's own chunk count (Dim 2); distinct
-- | from the wrap circuit's `numChunks` (Dim 1). OCaml fixes
-- | `wrapVkChunks = num_chunks_by_default = 1` at `step_main.ml:347`;
-- | callers pass `@1` at the specialization boundary.
extractWrapVKForStepHash
  :: forall @wrapVkChunks
   . Reflectable wrapVkChunks Int
  => VerifierIndex PallasG WrapField
  -> StepVK wrapVkChunks StepField
extractWrapVKForStepHash vk =
  let
    comms = vestaVerifierIndexCommitments @wrapVkChunks vk
  in
    { sigmaComm: comms.sigma
    , coefficientsComm: comms.coeff
    , genericComm: Vector.index comms.index (unsafeFinite @6 0)
    , psmComm: Vector.index comms.index (unsafeFinite @6 1)
    , completeAddComm: Vector.index comms.index (unsafeFinite @6 2)
    , mulComm: Vector.index comms.index (unsafeFinite @6 3)
    , emulComm: Vector.index comms.index (unsafeFinite @6 4)
    , endomulScalarComm: Vector.index comms.index (unsafeFinite @6 5)
    }

--------------------------------------------------------------------------------
-- mpvMax-padding dummies
--
-- Mirror OCaml `Unfinalized.Constant.dummy` (unfinalized.ml:25-104)
-- and the prover-side `pad` function for `messages_for_next_wrap_proof`
-- (step.ml:868-875). Used by `stepMain` to front-pad the step PI from
-- `len` (rule's actual mpv) to `mpvMax` (compile-wide max). For
-- single-rule callers `mpvMax = len → mpvPad = 0`, so the dummies
-- are unused.
--------------------------------------------------------------------------------

-- | Cross-field-encoded step-side dummy `messages_for_next_wrap_proof`
-- | digest (value level). Hashes a constant
-- | `Messages_for_next_wrap_proof.t` (Dummy.Ipa.Step.sg + 2 copies of
-- | Dummy.Ipa.Wrap.challenges_computed) via Tock_field_sponge then
-- | cross-field-casts to step field, mirroring OCaml
-- | `step.ml:868-875`'s `pad` function.
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

-- | Build the `Array WrapField` the FFI oracles call receives.
-- |
-- | This MUST produce the same bits as the step circuit's in-circuit
-- | `packStatement` + `publicInputCommit` on the same dummy advice
-- | values. Going through `assembleWrapMainInput` (→ cross-field
-- | re-shifting) does NOT do that — it produces `Type1 (F WrapField)`
-- | values that are `(v - shift)/2` in the WRAP field, while the step
-- | circuit's `packStatement` emits `(v - shift)/2` in the STEP field.
-- | The FFI interprets its input array as wrap-field scalars and calls
-- | kimchi's lagrange MSM; the step circuit interprets its step-field
-- | values as step-field inputs to `publicInputCommit` which treats
-- | them as scalars via bit-level reinterpretation (kimchi's
-- | `scale_fast` cross-field call). For these two to produce the same
-- | `x_hat`, the bit patterns must match — so we emit the
-- | step-field-shifted values BIT-reinterpreted into the wrap field
-- | (via `fromBigInt <<< toBigInt`), NOT cross-field re-shifted.
-- |
-- | This helper mirrors the SAME field order as `packStatement` (= OCaml
-- | `Wrap.Statement.In_circuit.to_data`): 5 fp fields, 2 challenges,
-- | 3 scalar challenges, 3 digests, `StepIPARounds` bp challenges,
-- | packed branch data, 8 feature flags, 2 lookup slots.
dummyWrapTockPublicInput
  :: forall @n stmt stmtVar
   . Reflectable n Int
  => Compare n 3 LT
  => CircuitType StepField stmt stmtVar
  -- The first record field is the prev rule's STEP domain log2
  -- (= `branch_data.domain_log2` of its wrap statement, fed into
  -- `packBranchDataWrap` below). For self-recursive rules with
  -- `override_wrap_domain` this coincides with `wrap_domains.h`; in
  -- general it's the prev's actual step circuit's domain.
  => { stepDomainLog2 :: Int
     , wrapVK :: VerifierIndex PallasG WrapField
     -- | Prev rule's full `StatementIO inputVal outputVal` value
     -- | (matches OCaml's `Previous_proof_statement.public_input ::
     -- | 'prev_var`). Serialized via `valueToFields` for the
     -- | `messages_for_next_step_proof.app_state` hash field —
     -- | concatenation of input + output fields, with Unit fields
     -- | contributing zero so Input-mode/Output-mode prevs both
     -- | produce the field array OCaml would.
     , prevStatement :: stmt
     -- | `Dummy.Ipa.Wrap.sg` — Ro-derived Pallas point from
     -- | `computeDummySgValues.ipa.wrap.sg`. Used for the previous
     -- | proofs' `challenge_polynomial_commitments` in
     -- | `messagesForNextStepProof` (OCaml `proof.ml:168-171`).
     , wrapSg :: AffinePoint StepField
     -- | `Dummy.Ipa.Step.sg` — Ro-derived Vesta point from
     -- | `computeDummySgValues.ipa.step.sg`. Unused inside this
     -- | function now that `msgWrapDigest` is computed once and passed
     -- | in, but kept in the input record so the call site can thread
     -- | both sg values symmetrically.
     , stepSg :: AffinePoint WrapField
     -- | Precomputed `hashMessagesForNextWrapProofPureGeneral` result
     -- | (must be computed with `sg = stepSg`). Threaded in so the
     -- | same value is used both here (as `digests[1]`) and in the
     -- | advice's `messagesForNextWrapProof` slot — eliminates any
     -- | self-consistency risk between the two.
     , msgWrapDigest :: WrapField
     -- | Pre-computed FOP proof state to serialize. Picks which Ro
     -- | state's plonk values to use (SimpleChain vs Tree_proof_return
     -- | vs module-init). Caller passes e.g.
     -- | `Dummy.simpleChainStepDummyFopProofState { proofsVerified }` or
     -- | `Dummy.treeStepDummyFopProofState { proofsVerified }`.
     , fopProofState ::
         UnfinalizedProof StepIPARounds (F StepField) (Type1 (F StepField)) Boolean
     }
  -> Array WrapField
dummyWrapTockPublicInput input =
  let
    fop = input.fopProofState

    dv = fop.deferredValues
    p = dv.plonk

    -- Bit-level reinterpretation of a step-field scalar as a wrap-field
    -- scalar (Fp → Fq). Step field bits fit in wrap field, so this is
    -- lossless.
    stepToWrap :: F StepField -> WrapField
    stepToWrap (F x) = crossFieldDigest x

    -- Type1 (F StepField) → WrapField by reaching the STORED (shifted)
    -- inner value. OCaml's `Wrap.Statement.In_circuit.to_data` places
    -- the stored `t` from `Shifted_value.Type1.Shifted_value t` into
    -- the tock public input — NOT the unshifted original.
    type1StepBits :: Type1 (F StepField) -> WrapField
    type1StepBits (Type1 x) = stepToWrap x

    -- SizedF 128 (F StepField) → WrapField via type-safe bit
    -- reinterpretation (`coerceViaBits` is bounded by `Compare 128 m LT`
    -- on both fields' bit widths, so no value can be out of range).
    sizedStepBits = SizedF.toField <<< (coerceViaBits) <<< SizedF.unwrapF

    -- 5 Type1 fp fields, order: cip, b, zetaToSrsLength,
    -- zetaToDomainSize, perm (matches `packStatement`).
    fpFields =
      [ type1StepBits dv.combinedInnerProduct
      , type1StepBits dv.b
      , type1StepBits p.zetaToSrsLength
      , type1StepBits p.zetaToDomainSize
      , type1StepBits p.perm
      ]

    -- 2 raw challenges: beta, gamma.
    challenges2 = [ sizedStepBits p.beta, sizedStepBits p.gamma ]

    -- 3 scalar challenges: alpha, zeta, xi.
    scalarChallenges3 =
      [ sizedStepBits p.alpha, sizedStepBits p.zeta, sizedStepBits dv.xi ]

    -- Compute the two step-field digests the wrap statement carries.
    --
    -- messagesForNextWrapProof: OCaml hashes
    -- `(prev_wrap_bp_challenges_padded, Dummy.Ipa.Step.sg)` in the
    -- wrap field. Pre-computed upstream via
    -- `hashMessagesForNextWrapProofPureGeneral` on `stepSg` so the
    -- same exact value appears both here (as `digests[1]`) and in the
    -- advice's `messagesForNextWrapProof` slot.
    msgWrapDigestWrapField = input.msgWrapDigest

    -- messagesForNextStepProof: step-field hash over (real wrap VK +
    -- prev app_state + prev (Dummy.Ipa.Wrap.sg, expanded bp chals)).
    -- OCaml `proof.ml:168-171` sets
    --   messages_for_next_step_proof.challenge_polynomial_commitments
    --     = Vector.init most_recent_width ~f:(fun _ -> Lazy.force Dummy.Ipa.Wrap.sg)
    wrapVkStep = extractWrapVKForStepHash input.wrapVK

    stepExpanded = dummyIpaChallenges.stepExpanded

    singleEntry = { sg: input.wrapSg, expandedBpChallenges: stepExpanded }

    -- `proofs` has `n` entries (type param), matching OCaml
    -- `proof.ml:168-171`:
    --   messages_for_next_step_proof.challenge_polynomial_commitments
    --     = Vector.init most_recent_width (fun _ -> Dummy.Ipa.Wrap.sg)
    appStateFields = valueToFields @StepField @stmt input.prevStatement

    msgStepDigestStepField = hashMessagesForNextStepProofPure
      { stepVk: wrapVkStep
      , appState: appStateFields
      , proofs: Vector.replicate @n singleEntry
      }

    -- 3 digests in packStatement order:
    -- [spongeDigest, msgWrap, msgStep]. `fopProofState.spongeDigest`
    -- is already a step-field value; coerce to wrap bits.
    sponge0 = fop.spongeDigestBeforeEvaluations

    digests3 =
      [ stepToWrap sponge0
      , msgWrapDigestWrapField -- already wrap field
      , stepToWrap (F msgStepDigestStepField)
      ]

    -- StepIPARounds bulletproof challenges.
    bpChals = map sizedStepBits (Vector.toUnfoldable dv.bulletproofChallenges)

    -- Packed branch_data: `4 * domainLog2 + mask[0] + 2 * mask[1]`.
    -- The mask is OCaml's `ones_vector ~first_zero:most_recent_width |>
    -- Vector.rev` padded to `branchDataMaskWidth = 2`. Constructed via
    -- the shared `revOnesVector` helper and packed via the shared
    -- `packBranchDataWrap` (same encoder the wrap-side uses through its
    -- own in-circuit mask construction).
    packedBranchData = packBranchDataWrap
      { domainLog2: Curves.fromInt input.stepDomainLog2 :: StepField
      , proofsVerifiedMask: revOnesVector (reflectType (Proxy @n))
      }

    -- Feature flags + lookup slots — all constant zero for vanilla
    -- Mina (`Features.Full.none`).
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

-- | Inputs for `buildSlotAdvice`. Generalized to support both base
-- | case (dummy wrap proof) and inductive case (real wrap proof from
-- | a previous iteration). The caller provides the wrap proof, its
-- | public input, and the padded accumulator — the builder treats
-- | them uniformly.
-- |
-- | Parameterized on TWO types:
-- |
-- |   * `inputVal`     — the rule's own `public_input` value type.
-- |                      Serialized into `advice.publicInput` and
-- |                      ultimately the step proof's public input.
-- |                      For Input-mode rules this is the input
-- |                      field; for Output-mode rules it's `Unit`.
-- |
-- |   * `prevInputVal` — the PREV wrap proof's app_state type (what
-- |                      `hash_messages_for_next_step_proof` serializes
-- |                      as the app-state field). Distinct from
-- |                      `inputVal` for Output-mode rules that verify
-- |                      heterogeneous-shaped prevs (e.g.
-- |                      Tree_proof_return's Unit-input rule verifies
-- |                      a No_recursion_return prev whose app_state
-- |                      is `F StepField`).
type BuildSlotAdviceInput inputVal stmt =
  { publicInput :: inputVal
  -- | Prev rule's full `StatementIO inputVal outputVal` value (matches
  -- | OCaml's `Previous_proof_statement.public_input :: 'prev_var` —
  -- | the per-prev `app_state` per `step_main.ml:389`). This helper
  -- | builds a single-slot StepAdvice, so callers pass one full
  -- | statement; the resulting StepAdvice's `prevAppStates` field is
  -- | the singleton carrier `Tuple stmt unit`.
  , prevStatement :: stmt
  , wrapDomainLog2 :: Int
  -- | STEP-domain log2 of the proof being verified (= branch_data.domain_log2
  -- | of the wrap statement). OCaml `Wrap_deferred_values.expand_deferred`
  -- | uses `Branch_data.domain branch_data` for `step_domain`, which drives
  -- | `zetaToDomainSize`, `perm`, and omega. Distinct from `wrapDomainLog2`
  -- | (the wrap VK's own domain) whenever a rule uses `override_wrap_domain`
  -- | or verifies a prev whose step domain differs from its wrap domain.
  , stepDomainLog2 :: Int
  , wrapVK :: VerifierIndex PallasG WrapField
  -- | Previous step proof's opening sg (Vesta point, Fq coords =
  -- | WrapField). Used by the HELPER's msgForNextWrap hash + its
  -- | `wrapChallengePolynomialCommitment` feed into expandProof.
  -- | OCaml wrap.ml:541-556 stores this value as
  -- | `messages_for_next_wrap_proof.challenge_polynomial_commitment`
  -- | of the wrap statement.
  -- | Base case (no real prev step): `Dummy.Ipa.Step.sg`.
  -- | Inductive / verifying a REAL wrap: the step proof's actual
  -- | opening sg (`pallasProofOpeningSg prev_step_proof`).
  , stepOpeningSg :: AffinePoint WrapField
  -- | Kimchi-level prev-challenges sg: what the step prover passes
  -- | to `pallasCreateProofWithPrev` in each entry's `sgX/Y`. This
  -- | is kimchi's own prev-IPA-fold reference, which for the base
  -- | case remains the compile-time dummy (`Dummy.Ipa.Step.sg`),
  -- | DISTINCT from `stepOpeningSg` when the helper's caller has
  -- | a real prev wrap proof to verify.
  , kimchiPrevSg :: AffinePoint WrapField
  -- | The wrap proof to run oracles on. Base case: `Proof.dummy`.
  -- | Inductive: the real wrap proof from the previous iteration.
  , wrapProof :: Proof PallasG WrapField
  -- | Public input of `wrapProof` (serialized wrap statement).
  -- | Base case: `dummyWrapTockPublicInput`. Inductive: the real
  -- | wrap prover's `publicInputs` output. Array because its length
  -- | depends on the circuit configuration and is only known at the
  -- | FFI boundary.
  , wrapPublicInput :: Array WrapField
  -- | Padded accumulator for the oracles call. Wrap_hack.Padded_length = 2.
  -- | Each entry holds sg + expanded bp challenges.
  -- |
  -- | Per OCaml step.ml this field serves DOUBLE DUTY: its `sg` column
  -- | is the source for BOTH the FFI oracles call's `prev_challenges`
  -- | (step.ml:360-371) AND the advice slot's `prev_challenge_polynomial
  -- | _commitments` (step.ml:513-517, fed into IVP sg_old at
  -- | step_main.ml:104). The helper extracts the per-slot Vector n sg
  -- | values by dropping the Wrap_hack front-padding (via
  -- | `Vector.drop @pad` with `Add pad n PaddedLength`).
  -- |
  -- | Base case (prev wrap is dummy): both entries
  -- |   `(Dummy.Ipa.Wrap.sg, dummyIpaChallenges.wrapExpanded)`.
  -- | Inductive N=1: front-padded `[dummy, real]`.
  -- | Inductive N=PaddedLength (Tree, N=2): no padding —
  -- |   `[real_slot0, real_slot1]` with distinct values per the prev
  -- |   wrap proof's own stored `msg_for_next_step_proof.cpc`.
  , prevChalPolys ::
      Vector PaddedLength
        { sg :: AffinePoint StepField
        , challenges :: Vector WrapIPARounds WrapField
        }
  -- | Raw 128-bit plonk challenges from the wrap STATEMENT's
  -- | `deferred_values.plonk` (OCaml step.ml:150).
  -- | Base case: `simpleChainDummyPlonk`. Inductive: from `wrapDv.plonk`.
  , wrapPlonkRaw ::
      { alpha :: SizedF 128 StepField
      , beta :: SizedF 128 StepField
      , gamma :: SizedF 128 StepField
      , zeta :: SizedF 128 StepField
      }
  -- | Step-field polynomial evaluations from the wrap proof.
  -- | Base case: `simpleChainDummyPrevEvals`. Inductive: extracted
  -- | from the real wrap proof.
  , wrapPrevEvals :: AllEvals StepField
  -- | Branch data from the wrap proof's statement.
  -- | Base case: `{ domainLog2: wrapDomainLog2, proofsVerifiedMask: [false, true] }`.
  -- | Inductive: from the real wrap statement.
  , wrapBranchData :: VT.BranchData StepField Boolean
  -- | Sponge digest before evaluations from the wrap proof's statement.
  -- | Base case: zero. Inductive: from the real wrap statement.
  , wrapSpongeDigest :: StepField
  -- | Whether the step circuit must verify the previous proof (= not base case).
  -- | Controls `challenge_polynomial_commitment` override in expandProof.
  , mustVerify :: Boolean
  -- | Padded bp_challenges from the wrap proof's OWN IPA (the challenges
  -- | produced during wrap proving, to be verified by the step verifier).
  -- |
  -- | Semantically: wrap_proof.statement.messages_for_next_step_proof
  -- |   .old_bulletproof_challenges (padded via Wrap_hack.pad_challenges to
  -- |   PaddedLength = 2, expanded via Ipa.Wrap.compute_challenges).
  -- |
  -- | Base case: both slots are `dummyIpaChallenges.wrapExpanded` (since
  -- | the dummy wrap proof has dummy bp chals).
  -- | Inductive: slot 0 = dummy (padding), slot 1 = the REAL wrap proof's
  -- | new bp chals obtained via `vestaProofOpeningPrechallenges` expanded
  -- | via Pallas.endo_scalar.
  -- |
  -- | Used by `expandProof` for (a) computing the wrap CIP (CIP batch
  -- | equation depends on these bp_polys) and (b) hashing
  -- | messages_for_next_wrap_proof. Getting this wrong makes the in-circuit
  -- | IVP on the wrap proof diverge from the advice-computed deferred
  -- | values, triggering `ivp_assert_plonk_beta` at the wrap verifier.
  , wrapOwnPaddedBpChals :: Vector PaddedLength (Vector WrapIPARounds WrapField)
  -- | The wrap proof's stored deferred_values, packed into
  -- | `fopProofStates[0]` in the step advice. This gets read by the step
  -- | circuit's `packStatement` to reconstruct the wrap proof's public
  -- | input for the IVP xhat commitment. MUST match what
  -- | `wrap_proof.publicInputs` actually contains (=
  -- | wrap_proof.statement.proof_state.deferred_values serialized).
  -- |
  -- | Base case: `simpleChainStepDummyFopProofState { proofsVerified }`
  -- | (the dummy wrap proof's stored deferred values, matching OCaml's
  -- | wrap.ml computation on dummy step proof).
  -- | Inductive: constructed from the real `wrapDv` produced by
  -- | `wrapComputeDeferredValues` during wrap proving.
  , fopState ::
      UnfinalizedProof StepIPARounds (F StepField) (Type1 (F StepField)) Boolean
  -- | Step advice's `evals[i]` field value (= per_proof_witness.ml:81-86
  -- | `prev_proof_evals = Plonk_types.All_evals.In_circuit.t`). These are
  -- | the evaluations the step FOP reads to recompute claimed deferred
  -- | values and check against advice's `fopState`.
  -- |
  -- | Distinct from `wrapPrevEvals` input (which feeds `expandProof` for
  -- | the step-side deferred computation — a separate path). For b0 this
  -- | must equal `r.stepDummyPrevEvals` (what the compile-time placeholder
  -- | uses, matching OCaml's runtime dummy wrap proof's prev_evals). For
  -- | b1 this must be wrap_b0's actual `prev_evals` field (= step_b0's
  -- | openings + x_hat) so the FOP's recompute matches the fopState
  -- | claims.
  , stepAdvicePrevEvals :: AllEvals StepField
  -- | Expanded step-field bp challenges for the single entry of
  -- | `advice.kimchiPrevChallenges` (= kimchi-level prev_challenges fed to
  -- | `pallasCreateProofWithPrev` / stored in `ProverProof.prev_challenges`).
  -- |
  -- | Per OCaml step.ml:913-920, each entry's `challenges` is
  -- | `Ipa.Step.compute_challenges` applied to the prev proof's
  -- | `statement.proof_state.deferred_values.bulletproof_challenges`:
  -- |
  -- | * Base case (step verifies dummy wrap): prev = dummy wrap proof,
  -- |   its `deferred_values.bulletproof_challenges = Dummy.Ipa.Step.challenges`
  -- |   (proof.ml:143). Expanded = `dummyIpaChallenges.stepExpanded`.
  -- | * Inductive (step verifies wrap_b0): prev = wrap_b0,
  -- |   its `deferred_values.bulletproof_challenges` = `wrapDv.bulletproofPrechallenges`.
  -- |   Expanded = `toFieldPure <$> wrapDv.bulletproofPrechallenges` via
  -- |   step endo scalar.
  , kimchiPrevChallengesExpanded :: Vector StepIPARounds StepField
  -- | Per-slot expanded step-field bp challenges that feed
  -- | `messagesForNextStepProof` hash AND `stepPrevChallenges` in
  -- | `expandProofInputRec`. Pre-padded to PaddedLength=2 (the caller
  -- | front-pads with `Dummy.Ipa.Step.challenges_computed` when slot
  -- | width < PaddedLength, matching OCaml's
  -- | `Vector.extend_front_exn` behavior). The helper extracts its
  -- | own `Vector n` via `Vector.drop @pad`, symmetrically with how
  -- | `prevCpcs` is derived from `prevChalPolys` (Path A).
  -- |
  -- | MUST be heterogeneous when the prev wrap proof's
  -- | `msg_for_next_step_proof.old_bulletproof_challenges` has distinct
  -- | per-slot entries (e.g. Tree b1 slot-1 where wrap_b0 wrapped
  -- | step_b0 verifying [NRR, dummy-N2] → 2 distinct bp_chal vectors).
  -- |
  -- | Per OCaml step.ml:519-525:
  -- |   `Vector.map Ipa.Step.compute_challenges
  -- |      t.statement.messages_for_next_step_proof.old_bulletproof_challenges`
  -- | where `t` = prev wrap proof.
  -- |
  -- | Base-case / dummy prevs: all entries =
  -- |   `Dummy.dummyIpaChallenges.stepExpanded` (homogeneous).
  -- | Tree b1 slot 1: `[step_b0.unfinalized[0].bp_chals step-expanded,
  -- |   step_b0.unfinalized[1].bp_chals step-expanded]` — two distinct
  -- |   vectors from the REAL unfinalized state of step_b0.
  , prevChallengesForStepHash :: Vector PaddedLength (Vector StepIPARounds StepField)
  }

-- | Per-slot output of `buildSlotAdvice`. Mirrors OCaml `expand_proof`'s
-- | seven-tuple return (`step.ml:131-150`):
-- |
-- |   * `challengePolynomialCommitment` — `Sg sg`, the prev wrap
-- |     proof's verified opening sg. Feeds the outer step proof's
-- |     `messages_for_next_step_proof.challenge_polynomial_commitments[i]`.
-- |   * `slotUnfinalized` — `Unfinalized.Constant.t` cross-field
-- |     coerced to step field; feeds `publicUnfinalizedProofs[i]`.
-- |   * `slotMsgWrapHashStep` — `messages_for_next_wrap_proof_digest`
-- |     hash for THIS slot's wrap proof; feeds
-- |     `messagesForNextWrapProof[i]`.
-- |   * `slotKimchiPrevEntry` — `(sg, expanded bp_chals)` for kimchi's
-- |     `prev_challenges` array entry; feeds `kimchiPrevChallenges[i]`.
-- |   * `slotSppw` — single-slot witness (per-slot prev-proof
-- |     witness data) for THIS slot's `n`. Combined into the
-- |     `perProofSlotsCarrier` heterogeneous tuple by the assembler.
-- |
-- | Outputs whose values are shared across all slots (the outer rule's
-- | `publicInput`, `wrapVerifierIndex`, etc.) live OUTSIDE this record
-- | — the assembler in `mkStepAdvice` plugs them in.
-- |
-- | Reference: mina/src/lib/crypto/pickles/step.ml:131-150 (`expand_proof`
-- | signature) + step.ml:736-770 (the `go` recursion that conses each
-- | per-slot output onto the rest's vectors).
type SlotAdviceContrib :: Int -> Int -> Type
type SlotAdviceContrib n nc =
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
        n
        nc
        StepIPARounds
        WrapIPARounds
        (F StepField)
        (Type2 (SplitField (F StepField) Boolean))
        Boolean
  }

--------------------------------------------------------------------------------
-- buildSlotAdvice — per-slot oracle-enriched advice builder
--
-- PS analog of OCaml's `expand_proof` (`step.ml:122-150`). Returns ONE
-- slot's contribution as `SlotAdviceContrib n`; the caller
-- (`mkStepAdvice` in `Pickles.Prove.Compile`) cons-recurses over the
-- prev list to assemble the multi-slot `StepAdvice`, mirroring OCaml's
-- `go` recursion at `step.ml:736-770`.
--
-- Runs `vestaProofOracles` on the caller-supplied wrap proof + public
-- input, feeds the result through `expandProof`, and packs the
-- resulting per-slot data into the `StepSlot n` record + scalar
-- companion fields. No multi-slot wrapping is introduced — the
-- per-slot data flows out directly.
--
-- Reference: mina/src/lib/crypto/pickles/step.ml:298-343.
--------------------------------------------------------------------------------

buildSlotAdvice
  :: forall @n @nc inputVal input prevHeadStmt prevHeadStmtVar pad
   . Reflectable n Int
  => Reflectable nc Int
  => Reflectable pad Int
  => Add pad n PaddedLength
  => CircuitType StepField inputVal input
  => CircuitType StepField prevHeadStmt prevHeadStmtVar
  => BuildSlotAdviceInput inputVal prevHeadStmt
  -> Effect (SlotAdviceContrib n nc)
buildSlotAdvice input = do
  let
    -- Wrap_hack-padded bp_chals for the wrap proof's hash AND the
    -- expandProof input. Caller supplies; see input field docs.
    wrapPadded = input.wrapOwnPaddedBpChals

    msgWrapHash = hashMessagesForNextWrapProofPureGeneral
      { sg: input.stepOpeningSg
      , paddedChallenges: wrapPadded
      }

    msgWrapHashStep = F (crossFieldDigest msgWrapHash)

  let
    wrapVkStep = extractWrapVKForStepHash input.wrapVK

    -- Per-slot `prev_challenge_polynomial_commitments :: Vector n` —
    -- derived from the PaddedLength-sized input by dropping
    -- Wrap_hack front-padding. Mirrors OCaml step.ml:513.
    prevCpcs = map _.sg (Vector.drop @pad input.prevChalPolys)

    -- Per-slot step-expanded bp_chals — same pattern.
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
    Trace.field ("expand_proof.chal_polys." <> show i <> ".comm.x") entry.sg.x
    Trace.field ("expand_proof.chal_polys." <> show i <> ".comm.y") entry.sg.y
    Trace.field ("expand_proof.chal_polys." <> show i <> ".chal.0") (Vector.head entry.challenges)

  let
    toFFIChalPoly r = { sgX: r.sg.x, sgY: r.sg.y, challenges: Vector.toUnfoldable r.challenges }

    oracles = vestaProofOracles input.wrapVK
      { proof: input.wrapProof
      , publicInput: input.wrapPublicInput
      , prevChallenges: map toFFIChalPoly (Vector.toUnfoldable input.prevChalPolys)
      }

  Trace.field "expand_proof.wrap_vk_digest" (vestaVerifierIndexDigest input.wrapVK)
  Trace.field "expand_proof.oracles.beta" (SizedF.toField oracles.beta)
  Trace.field "expand_proof.oracles.gamma" (SizedF.toField oracles.gamma)
  Trace.field "expand_proof.oracles.alpha_chal" (SizedF.toField oracles.alphaChal)
  Trace.field "expand_proof.oracles.zeta_chal" (SizedF.toField oracles.zetaChal)
  Trace.field "expand_proof.plonk0.alpha.raw" (SizedF.toField (SizedF.wrapF input.wrapPlonkRaw.alpha :: SizedF 128 (F StepField)))
  Trace.field "expand_proof.plonk0.beta" (SizedF.toField (SizedF.wrapF input.wrapPlonkRaw.beta :: SizedF 128 (F StepField)))
  Trace.field "expand_proof.plonk0.gamma" (SizedF.toField (SizedF.wrapF input.wrapPlonkRaw.gamma :: SizedF 128 (F StepField)))
  Trace.field "expand_proof.plonk0.zeta.raw" (SizedF.toField (SizedF.wrapF input.wrapPlonkRaw.zeta :: SizedF 128 (F StepField)))
  Trace.field "expand_proof.oracles.fq_digest" oracles.fqDigest
  Trace.field "expand_proof.oracles.cip_kimchi" oracles.combinedInnerProduct

  let
    rawPrechalsForTrace = vestaProofOpeningPrechallenges input.wrapVK
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
        { domainLog2: input.stepDomainLog2, zkRows, pt: zetaExpandedStep }

    wrapGen = domainGenerator input.wrapDomainLog2
    wrapZetaw = oracles.zeta * wrapGen
    wrapSrsLog2 = reflectType (Proxy :: Proxy WrapIPARounds)
    wrapCollapse = Chunks.collapsePointEval
      { rounds: wrapSrsLog2, zeta: oracles.zeta, zetaOmega: wrapZetaw }

    wrapAllEvals =
      { ftEval1: oracles.ftEval1
      , publicEvals: wrapCollapse oracles.publicEvals
      , zEvals: wrapCollapse (proofZEvals input.wrapProof)
      , witnessEvals: map wrapCollapse (proofWitnessEvals input.wrapProof)
      , coeffEvals: map wrapCollapse (proofCoefficientEvals input.wrapProof)
      , sigmaEvals: map wrapCollapse (proofSigmaEvals input.wrapProof)
      , indexEvals: map wrapCollapse (proofIndexEvals input.wrapProof)
      }

    wrapShifts = domainShifts input.wrapDomainLog2

    wrapVanishesOnZk =
      (permutationVanishingPolynomial :: { domainLog2 :: Int, zkRows :: Int, pt :: WrapField } -> WrapField)
        { domainLog2: input.wrapDomainLog2, zkRows, pt: oracles.zeta }

    stepProofPrevEvals =
      let
        pe pe' = PointEval { zeta: F pe'.zeta, omegaTimesZeta: F pe'.omegaTimesZeta }
        ae = input.wrapPrevEvals
      in
        StepAllEvals
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
      , zkRows
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
      , dlogIndex: extractWrapVKForStepHash input.wrapVK
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
      , wrapAllEvals
      , wrapPEval0Chunks: map _.zeta (NonEmptyArray.toArray oracles.publicEvals)
      , wrapShifts
      , wrapZkRows: zkRows
      , wrapSrsLengthLog2: reflectType (Proxy :: Proxy WrapIPARounds)
      , wrapVanishesOnZk
      , wrapOmegaForLagrange: \_ -> one
      , wrapLinearizationPoly: Linearization.vesta
      , stepProofPrevEvals
      , stepPrevChallenges: map (map F) prevChalsPerSlot
      , stepPrevSgsPadded: prevCpcs
      }

    expandProofResult = PureStep.expandProof @nc expandProofInputRec

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
    -- Convert wrap-field unfinalized → step-field publicUnfinalized slot.
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

    mkPt :: AffinePoint StepField -> AffinePoint (F StepField)
    mkPt pt = { x: F pt.x, y: F pt.y }

    openingDelta = mkPt (vestaProofOpeningDelta input.wrapProof)

    openingLr = map (\p -> { l: mkPt p.l, r: mkPt p.r })
      (vestaProofOpeningLrVec input.wrapProof)

    openingZ1Raw = vestaProofOpeningZ1 input.wrapProof

    openingZ2Raw = vestaProofOpeningZ2 input.wrapProof

    z1 = toShifted (F openingZ1Raw)

    z2 = toShifted (F openingZ2Raw)

    wrapCommits = vestaProofCommitments input.wrapProof

    mkPallasAffine :: AffinePoint StepField -> AffinePoint (F StepField)
    mkPallasAffine pt = { x: F pt.x, y: F pt.y }
    wrapMessages =
      { wComm: map (map mkPallasAffine) (wCommChunked @nc wrapCommits)
      , zComm: map mkPallasAffine (zCommChunked @nc wrapCommits)
      , tComm: map (map mkPallasAffine) (tCommChunked @nc wrapCommits)
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

    slotBranchData =
      { domainLog2: F input.wrapBranchData.domainLog2
      , mask0: input.wrapBranchData.proofsVerifiedMask `Vector.index` (unsafeFinite @2 0)
      , mask1: input.wrapBranchData.proofsVerifiedMask `Vector.index` (unsafeFinite @2 1)
      }

    dvFop = fopState.deferredValues
    pFop = dvFop.plonk

    -- This slot's per-proof witness — the per-slot `prevSgs` and
    -- `prevChallenges` come straight from `Vector.drop @pad`,
    -- preserving heterogeneous per-entry values for rules like
    -- Tree_proof_return.
    slotSppw
      :: Step.PerProofWitness n nc StepIPARounds WrapIPARounds
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
              { wComm: map (map WeierstrassAffinePoint) wrapMessages.wComm
              , zComm: map WeierstrassAffinePoint wrapMessages.zComm
              , tComm: map (map WeierstrassAffinePoint) wrapMessages.tComm
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
          , branchData: Step.BranchData
              { domainLog2: slotBranchData.domainLog2
              , mask0: slotBranchData.mask0
              , mask1: slotBranchData.mask1
              }
          }
      , prevEvals: StepAllEvals
          { publicEvals: PointEval evalsForAdvice.allEvals.publicEvals
          , witnessEvals: map PointEval evalsForAdvice.allEvals.witnessEvals
          , coeffEvals: map PointEval evalsForAdvice.allEvals.coeffEvals
          , zEvals: PointEval evalsForAdvice.allEvals.zEvals
          , sigmaEvals: map PointEval evalsForAdvice.allEvals.sigmaEvals
          , indexEvals: map PointEval evalsForAdvice.allEvals.indexEvals
          , ftEval1: evalsForAdvice.allEvals.ftEval1
          }
      , prevChallenges: map
          (\chals -> UnChecked (map F chals))
          (Vector.drop @pad input.prevChallengesForStepHash)
      , prevSgs: map
          (\e -> WeierstrassAffinePoint (coerce e.sg :: AffinePoint (F StepField)))
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
        { sgX: input.kimchiPrevSg.x
        , sgY: input.kimchiPrevSg.y
        , challenges: input.kimchiPrevChallengesExpanded
        }
    , slotSppw
    }

--------------------------------------------------------------------------------
-- stepProve — compile + solve + kimchi proof creation
--------------------------------------------------------------------------------

-- | Rule type the step prover accepts. This is the inductive-rule
-- | body `stepMain` passes to `verifyOne` for each previous proof.
-- |
-- | The type is polymorphic in both `t` and the base monad `m'` so
-- | that `stepProve` can reuse the same rule for compile-time
-- | (circuit shape walk, `m' = Effect`) and solve-time (witness
-- | generation, `m' = StepProverT …`).
-- |
-- | Mirrors OCaml's `Inductive_rule.main` signature at
-- | `mina/src/lib/crypto/pickles/inductive_rule.ml` + the usage site
-- | in `step_main.ml:278-283`.
-- |
-- | The `output` type parameter is the rule's `public_output` (mirroring
-- | OCaml's `Inductive_rule.t.public_output`). For Input-mode rules
-- | (`~public_input:(Input _)`) callers use `output = Unit`. For
-- | Output-mode rules the computed value flows back via the rule's
-- | returned `RuleOutput`.
-- | The `valCarrier` slot is the per-rule heterogeneous prev-statement
-- | carrier shape that `Pickles.Step.Slots.SlotStatementsCarrier` derives
-- | from the rule's `prevsSpec`. It mirrors the `'prev_values` axis of
-- | OCaml's `Inductive_rule.Make.t` — what `previous_proof_statements
-- | :: H4.T(...)` resolves to per rule. The body reads each slot's
-- | statement via `StepPrevValuesM.getPrevAppStates`, which `stepMain`
-- | / `runStepProverT` populate from the user-supplied advice carrier
-- | at prove time.
-- |
-- | Per-rule instantiations:
-- |   * NRR (no prevs):           `valCarrier = Unit`
-- |   * Simple_chain (1 prev):    `valCarrier = Tuple (StatementIO …) Unit`
-- |   * Tree_proof_return (2):    `valCarrier = Tuple stmt0 (Tuple stmt1 Unit)`
type StepRule (n :: Int) valCarrier inputVal input outputVal output prevInputVal prevInput =
  forall t m' wrapVkChunks
   . CircuitM StepField (KimchiConstraint StepField) t m'
  => StepWitnessM n StepIPARounds WrapIPARounds wrapVkChunks PallasG StepField m' inputVal
  => StepPrevValuesM m' valCarrier
  => CircuitType StepField inputVal input
  => CircuitType StepField outputVal output
  => CircuitType StepField prevInputVal prevInput
  => CheckedType StepField (KimchiConstraint StepField) input
  => input
  -> Snarky (KimchiConstraint StepField) t m' (RuleOutput n prevInput output)

-- | Ambient data the step prover needs alongside the advice and rule.
-- |
-- | * `srsData` — `StepMainSrsData len` with per-slot FOP domain log2
-- |   (lagrange-base lookup, blinding H, per-slot FOP domains, per-slot
-- |   known wrap keys) that `stepMain` consumes.
-- | * `dummySg` — dummy sg point for sg_old padding in verify_one.
-- | * `crs` — the step circuit's Vesta SRS.
type StepProveContext len nd blueprints =
  { srsData :: StepMainSrsData len nd blueprints
  , dummySg :: AffinePoint StepField
  , crs :: CRS VestaG
  -- | When `true`, enables prover-state debug checks and runs a
  -- | `verifyProverIndex` sanity check against the solved witness.
  -- | On failure, the row → label map for the step circuit gets
  -- | written to `/tmp/ps_step_row_labels.txt`. Off by default.
  , debug :: Boolean
  }

-- | Artifacts produced by `stepCompile`. These are the pieces the
-- | SimpleChain test (and anything else that wraps the split flow)
-- | needs to hand off between compile → wrap compile → solve.
-- |
-- | The `proverIndex` / `verifierIndex` are created here (not in
-- | `stepSolveAndProve`) because the step VK is what downstream
-- | `buildWrapMainConfig` needs *before* the solver runs.
type StepCompileResult =
  { proverIndex :: ProverIndex VestaG StepField
  , verifierIndex :: VerifierIndex VestaG StepField
  , constraintSystem :: ConstraintSystem StepField
  , builtState :: CircuitBuilderState (KimchiGate StepField) (AuxState StepField)
  , constraints :: Array (KimchiRow StepField)
  }

-- | Artifacts produced by `stepProve` / `stepSolveAndProve`. Shape mirrors
-- | `WrapProveResult` so downstream code can retarget with minimal
-- | glue.
type StepProveResult (outputSize :: Int) =
  { proverIndex :: ProverIndex VestaG StepField
  , verifierIndex :: VerifierIndex VestaG StepField
  , constraintSystem :: ConstraintSystem StepField
  , witness :: Vector 15 (Array StepField)
  , publicInputs :: Array StepField
  , publicOutputs :: Vector outputSize (F StepField)
  , proof :: Proof VestaG StepField
  , assignments :: Map Variable StepField
  -- | Field-flattened representation of the rule's user
  -- | `publicOutput` value, recovered post-solve. Carried as a raw
  -- | `Array StepField` (not `outputVal`) so that consumers like
  -- | `runProverBody` apply their own `fieldsToValue @StepField
  -- | @outputVal` and producers that don't care can ignore it.
  -- | Empty when the rule's output type is `Unit`.
  , userPublicOutputFields :: Array StepField
  }

-- | Build a row→label_stack text dump from a compiled constraint list and
-- | write it to /tmp/ps_step_row_labels.txt. Called when the kimchi
-- | prover-index verification fails so the user can look up the failing
-- | row reported on stderr (as "Custom { row: N, err: ... }") and find
-- | the `label`/`labelM` call site that produced the constraint.
-- |
-- | The output format is one line per starting row:
-- |    "<row_start>..<row_end>\t<label>/<label>/.../<label>"
-- | Each labeled constraint may expand to multiple Kimchi rows (e.g. an
-- | EndoMul gate = 32 rows); the row range covers all of them.
-- |
-- | Row numbering aligns with the final kimchi witness file
-- | (`KIMCHI_WITNESS_DUMP`): the first `publicInputSize` rows are
-- | reserved by `makeGateData` for public-input placement, so
-- | constraint rows begin at `publicInputSize`. The wrong offset
-- | gives labels that look correct but point at the wrong row.
dumpRowLabels
  :: Int -- ^ publicInputSize — number of rows kimchi reserves for PI
  -> Array (Labeled (KimchiGate StepField))
  -> Effect Unit
dumpRowLabels = writeRowLabelsTo "/tmp/ps_step_row_labels.txt"

-- | Monotonic counter for `KIMCHI_STEP_LABELS_DUMP` filename
-- | templating. Mirrors the AtomicUsize counter on the Rust side for
-- | `KIMCHI_WITNESS_DUMP` / `KIMCHI_CS_DUMP`.
stepLabelsCounter :: Ref.Ref Int
stepLabelsCounter = unsafePerformEffect (Ref.new 0)

bumpStepLabelsCounter :: Effect Int
bumpStepLabelsCounter = do
  n <- Ref.read stepLabelsCounter
  Ref.write (n + 1) stepLabelsCounter
  pure n

-- | Independent counter for `KIMCHI_STEP_CS_DUMP`'s `%c` template so
-- | enabling both `KIMCHI_STEP_LABELS_DUMP` and `KIMCHI_STEP_CS_DUMP`
-- | in one run keeps each numbering sequence aligned.
stepCsCounter :: Ref.Ref Int
stepCsCounter = unsafePerformEffect (Ref.new 0)

bumpStepCsCounter :: Effect Int
bumpStepCsCounter = do
  n <- Ref.read stepCsCounter
  Ref.write (n + 1) stepCsCounter
  pure n

-- | Variant of `dumpRowLabels` that takes a destination path. Used
-- | by the `KIMCHI_STEP_LABELS_DUMP` env-var-gated dump in
-- | `stepCompile` so each branch's CS labels go to a distinct file.
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

--------------------------------------------------------------------------------
-- Spec-indexed advice stack
--
-- `StepAdvice` keys advice pieces on a `prevsSpec` type-level list so
-- heterogeneous-prev rules (Tree_proof_return style) can express
-- per-slot `max_proofs_verified` distinctly. `StepProverT` serves
-- that advice to the circuit body via `StepWitnessM` and
-- `StepSlotsM`.
--------------------------------------------------------------------------------

-- | Advice record keyed on a spec-indexed per-slot carrier.
-- |
-- | * `perProofSlotsCarrier` — nested-tuple of per-slot `StepSlot`s
-- |   (sized by `prevsSpec`). Heterogeneous per-slot data lives here.
-- | * Uniform-per-slot fields (`publicUnfinalizedProofs`,
-- |   `messagesForNextWrapProof`) are plain `Vector len` — their
-- |   element types don't depend on per-slot `n_i`.
-- | * Singletons (`wrapVerifierIndex`, `publicInput`) stand alone.
-- | `wrapVkChunks` (Dim 2) is the chunks count of THIS compile's
-- | wrap VK as carried by `wrapVerifierIndex`. OCaml hardcodes this
-- | to 1 at `step_main.ml:347` (`num_chunks_by_default`); the type
-- | stays polymorphic so the parameter tracks the OCaml TODO.
newtype StepAdvice
  :: Type -> Int -> Int -> Int -> Type -> Int -> Type -> Type -> Type -> Type
newtype StepAdvice prevsSpec ds dw wrapVkChunks inputVal len carrier valCarrier vkCarrier =
  StepAdvice
    { perProofSlotsCarrier :: carrier
    , publicInput :: inputVal
    , publicUnfinalizedProofs ::
        Vector len
          ( PerProofUnfinalized
              dw
              (Type2 (SplitField (F StepField) Boolean))
              (F StepField)
              Boolean
          )
    , messagesForNextWrapProof :: Vector len (F StepField)
    -- | Dummy hash value used to pad `messagesForNextWrapProof` from
    -- | `len` to `mpvMax` at solve time. Mirrors OCaml's
    -- | `Reduced_messages_for_next_proof_over_same_field.Wrap.dummy.hash`
    -- | which the prover supplies for padding positions in
    -- | `Req.Messages_for_next_wrap_proof` (step_main.ml:368-370).
    , messagesForNextWrapProofDummyHash :: F StepField
    , wrapVerifierIndex ::
        VerificationKey wrapVkChunks (WeierstrassAffinePoint PallasG (F StepField))
    -- | Kimchi-level prev_challenges threaded to
    -- | `pallasCreateProofWithPrev`. One entry per prev slot of the
    -- | step circuit. Uniform Vector len — each entry's `challenges`
    -- | is sized by `ds` (step IPA rounds, fixed), NOT by per-slot
    -- | `n_i`, so this stays a plain Vector (not a spec-indexed
    -- | carrier).
    , kimchiPrevChallenges ::
        Vector len
          { sgX :: WrapField
          , sgY :: WrapField
          , challenges :: Vector ds StepField
          }
    -- | Heterogeneous per-slot prev statements, in the same nested-tuple
    -- | shape `SlotStatementsCarrier prevsSpec valCarrier` derives:
    -- |   Unit                            → Unit
    -- |   Slot Compiled n stmt /\ rest               → Tuple stmt restValCarrier
    -- | Each `stmt` is the prev rule's `StatementIO inputVal outputVal`
    -- | (the same type bundled in `Slot Compiled`'s second parameter).
    -- | Mirrors OCaml's `previous_proof_statements` argument flowing into
    -- | the rule's `main` — the rule body reads slot-specific values out
    -- | (input for Input-mode prevs, output for Output-mode) inside its
    -- | `exists` calls so the witness for the prev's app-state circuit
    -- | variable is sourced from advice rather than baked into a closure.
    , prevAppStates :: valCarrier
    -- | Runtime side-loaded VK carrier, shape derived from `prevsSpec`
    -- | by `Pickles.Sideload.Advice.SideloadedVKsCarrier` (compiled
    -- | slots contribute `Unit`, side-loaded slots contribute a
    -- | `Pickles.Sideload.VerificationKey`). PS analog of OCaml's
    -- | per-prove `~handler`.
    , sideloadedVKs :: vkCarrier
    }

derive instance
  Newtype
    (StepAdvice prevsSpec ds dw wrapVkChunks inputVal len carrier valCarrier vkCarrier)
    _

-- | Mutable side-state captured during the rule body's structural pass.
-- | Currently just the user's `publicOutput` FVars; callers post-run
-- | evaluate them against the assignments map (see `stepSolveAndProve`).
-- | Kept as a record so future captured values slot in without churn.
type StepProverCapture =
  { userPublicOutputFields :: Maybe (Array (FVar StepField))
  }

initialStepProverCapture :: StepProverCapture
initialStepProverCapture =
  { userPublicOutputFields: Nothing
  }

-- | ReaderT-over-StateT transformer for the v2 prover stack. The Reader
-- | layer carries the read-only `StepAdvice` (advice methods like
-- | `getStepPublicInput`); the State layer captures values written
-- | from inside the rule body (so far: `setUserPublicOutputFields`,
-- | the OCaml `Req.Return_value` analog).
newtype StepProverT
  :: Type -> Int -> Int -> Int -> Type -> Int -> Type -> Type -> Type -> (Type -> Type) -> Type -> Type
newtype StepProverT prevsSpec ds dw wrapVkChunks inputVal len carrier valCarrier vkCarrier m a =
  StepProverT
    ( ReaderT (StepAdvice prevsSpec ds dw wrapVkChunks inputVal len carrier valCarrier vkCarrier)
        (StateT StepProverCapture m)
        a
    )

derive instance
  Newtype
    (StepProverT prevsSpec ds dw wrapVkChunks inputVal len carrier valCarrier vkCarrier m a)
    _

derive newtype instance
  Functor m =>
  Functor (StepProverT prevsSpec ds dw wrapVkChunks inputVal len carrier valCarrier vkCarrier m)

derive newtype instance
  Monad m =>
  Apply (StepProverT prevsSpec ds dw wrapVkChunks inputVal len carrier valCarrier vkCarrier m)

derive newtype instance
  Monad m =>
  Applicative (StepProverT prevsSpec ds dw wrapVkChunks inputVal len carrier valCarrier vkCarrier m)

derive newtype instance
  Monad m =>
  Bind (StepProverT prevsSpec ds dw wrapVkChunks inputVal len carrier valCarrier vkCarrier m)

derive newtype instance
  Monad m =>
  Monad (StepProverT prevsSpec ds dw wrapVkChunks inputVal len carrier valCarrier vkCarrier m)

-- | Run a `StepProverT` action with the supplied advice. Returns both
-- | the action's result AND the post-run `StepProverCapture` so the
-- | caller can read whatever the rule body wrote (e.g. the user's
-- | `publicOutput` FVars).
runStepProverT
  :: forall prevsSpec ds dw inputVal len carrier valCarrier vkCarrier m a
   . Monad m
  => StepAdvice prevsSpec ds dw inputVal len carrier valCarrier vkCarrier
  -> StepProverT prevsSpec ds dw wrapVkChunks inputVal len carrier valCarrier vkCarrier m a
  -> m (Tuple a StepProverCapture)
runStepProverT advice (StepProverT m) =
  runStateT (runReaderT m advice) initialStepProverCapture

instance
  ( Monad m
  , StepSlotsCarrier
      prevsSpec
      ds
      dw
      (F StepField)
      (Type2 (SplitField (F StepField) Boolean))
      Boolean
      len
      carrier
      vkSourcesCarrier
  ) =>
  StepSlotsM
    prevsSpec
    ds
    dw
    PallasG
    StepField
    (StepProverT prevsSpec ds dw wrapVkChunks inputVal len carrier valCarrier vkCarrier m)
    len
    carrier
    vkSourcesCarrier where
  getStepSlotsCarrier _ =
    StepProverT $ map (\(StepAdvice r) -> r.perProofSlotsCarrier) ask

-- | `StepWitnessM` instance on `StepProverT`. Implements the uniform
-- | methods `stepMain` actually calls (getStepPublicInput,
-- | getStepUnfinalizedProofs, getMessagesForNextWrapProof,
-- | getWrapVerifierIndex) via direct field access. The remaining
-- | legacy methods (getProofWitnesses, getPrevChallenges,
-- | getStepPerProofWitnesses, etc.) throw — v2 code uses
-- | `getStepSlotsCarrier` instead, and the legacy per-slot methods
-- | are dead code from the deleted `Step.Circuit` path.
instance
  ( Monad m
  , Reflectable len Int
  ) =>
  StepWitnessM
    len -- ← n in StepWitnessM's class header. For the v2 stack the
    --   advice's outer `Vector len` fields are sized by len, and
    --   len matches what StepWitnessM's methods expect.
    ds
    dw
    wrapVkChunks
    PallasG
    StepField
    (StepProverT prevsSpec ds dw wrapVkChunks inputVal len carrier valCarrier vkCarrier m)
    inputVal where

  getMessagesForNextWrapProof _ =
    StepProverT $ map (\(StepAdvice r) -> r.messagesForNextWrapProof) ask
  getMessagesForNextWrapProofDummyHash _ =
    StepProverT $ map (\(StepAdvice r) -> r.messagesForNextWrapProofDummyHash) ask
  getWrapVerifierIndex _ =
    StepProverT $ map (\(StepAdvice r) -> r.wrapVerifierIndex) ask
  getStepPublicInput _ =
    StepProverT $ map (\(StepAdvice r) -> r.publicInput) ask
  getStepUnfinalizedProofs _ =
    StepProverT $ map (\(StepAdvice r) -> r.publicUnfinalizedProofs) ask

instance
  Monad m =>
  StepPrevValuesM
    (StepProverT prevsSpec ds dw wrapVkChunks inputVal len carrier valCarrier vkCarrier m)
    valCarrier where
  getPrevAppStates _ =
    StepProverT $ map (\(StepAdvice r) -> r.prevAppStates) ask

-- | Write to the State layer of the StepProverT stack. The OCaml
-- | analog is the `Req.Return_value` handler at step.ml:896-898 which
-- | does `return_value := Some res`.
instance
  Monad m =>
  StepUserOutputM
    (StepProverT prevsSpec ds dw wrapVkChunks inputVal len carrier valCarrier vkCarrier m) where
  setUserPublicOutputFields fields =
    StepProverT $ lift $ State.modify_ \s ->
      s { userPublicOutputFields = Just fields }

-- | `SideloadedVKsM` instance for `StepProverT`. Reads the runtime
-- | side-loaded VK carrier out of the `StepAdvice` Reader payload.
instance
  ( Monad m
  , SideloadedVKsCarrier prevsSpec vkCarrier
  ) =>
  SideloadedVKsM
    prevsSpec
    (StepProverT prevsSpec ds dw wrapVkChunks inputVal len carrier valCarrier vkCarrier m)
    vkCarrier
  where
  getSideloadedVKsCarrier _ =
    StepProverT $ map (\(StepAdvice r) -> r.sideloadedVKs) ask

-- | V2 compile phase — parallel to `stepCompile` but runs `stepMain`
-- | in `Effect`, which dispatches to the `StepWitnessM`/`StepSlotsM`
-- | `Effect` instances — every advice method there throws. The
-- | circuit shape only depends on `prevsSpec` / `len` / `carrier`;
-- | anything that escapes the throw instance is a bug.
-- |
-- | `stepSolveAndProve` / `stepProve` are not yet added — they need
-- | per-slot kimchi-prev-challenges data in StepAdvice that we
-- | haven't introduced yet.
stepCompile
  :: forall @prevsSpec @outputSize @valCarrier @inputVal @input @outputVal @output @prevInputVal @prevInput
       @mpvMax @mpvPad @nd ndPred len carrier carrierVar sideloadedVkCarrier blueprints
       pad unfsTotal digestPlusUnfs
   . CircuitGateConstructor StepField VestaG
  => BuildSlotVkSources (SLVK.VerificationKey nc (F StepField) Boolean) prevsSpec len blueprints sideloadedVkCarrier vkSourcesCarrier
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
  => MpvPadding.MpvPadding mpvPad len mpvMax
  => Mul mpvMax Step.UnfinalizedFieldCount unfsTotal
  => Add unfsTotal 1 digestPlusUnfs
  => Add digestPlusUnfs mpvMax outputSize
  => CircuitType StepField inputVal input
  => CircuitType StepField outputVal output
  => CircuitType StepField prevInputVal prevInput
  => CircuitType StepField carrier carrierVar
  => CheckedType StepField (KimchiConstraint StepField) carrierVar
  => StepSlotsCarrier
       prevsSpec
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
       StepIPARounds
       WrapIPARounds
       (FVar StepField)
       (Type2 (SplitField (FVar StepField) (BoolVar StepField)))
       (BoolVar StepField)
       len
       carrierVar
       vkSourcesCarrierVar
  => CheckedType StepField (KimchiConstraint StepField) input
  => StepProveContext len nd blueprints
  -> StepRule len valCarrier inputVal input outputVal output prevInputVal prevInput
  -> Effect StepCompileResult
stepCompile ctx rule = do
  -- For compiled-only specs the Effect `SideloadedVKsM` instance
  -- synthesises an all-Unit chain via `mkUnitVkCarrier`; specs with
  -- side-loaded slots won't resolve unless a prover monad with a
  -- real runtime-VK source is in scope.
  sideloadedCarrier <- getSideloadedVKsCarrier @prevsSpec unit
  builtState <-
    compile
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
            @(SLVK.VerificationKey nc (F StepField) Boolean)
            rule
            ctx.srsData
            ctx.dummySg
            sideloadedCarrier
      )
      (Kimchi.initialState :: CircuitBuilderState (KimchiGate StepField) (AuxState StepField))

  let
    kimchiRows :: Array (KimchiRow StepField)
    kimchiRows = concatMap (toKimchiRows <<< _.constraint) builtState.constraints
    { constraintSystem, constraints } = makeConstraintSystemWithPrevChallenges @StepField
      { constraints: kimchiRows
      , publicInputs: builtState.publicInputs
      , unionFind: (un AuxState builtState.aux).wireState.unionFind
      , prevChallengesCount: reflectType (Proxy @len)
      , maxPolySize: crsSize ctx.crs
      }

    endo =
      let EndoBase e = (endoBase) in e

    proverIndex =
      createProverIndex @StepField @VestaG
        { endo, constraintSystem, crs: ctx.crs }

    verifierIndex = createVerifierIndex @StepField @VestaG proverIndex

  -- Optional compile-time dump of the row→label map, gated on the
  -- `KIMCHI_STEP_LABELS_DUMP` env var. Filename template uses `%c`
  -- (replaced with a monotonic counter) so multi-rule compileMulti
  -- writes one file per branch — same convention as
  -- `KIMCHI_WITNESS_DUMP` / `KIMCHI_CS_DUMP`. Useful for localizing
  -- multi-rule per-branch CS divergences without going through prove.
  Process.lookupEnv "KIMCHI_STEP_LABELS_DUMP" >>= case _ of
    Nothing -> pure unit
    Just pathTmpl -> do
      counter <- bumpStepLabelsCounter
      let
        path = String.replaceAll (Pattern "%c") (Replacement (show counter)) pathTmpl
        publicInputSize = Array.length builtState.publicInputs
      writeRowLabelsTo path publicInputSize builtState.constraints

  -- Optional dump of the step constraint system as JSON, gated on
  -- `KIMCHI_STEP_CS_DUMP`. Mirrors the wrap-side `KIMCHI_WRAP_CS_DUMP`
  -- in `Pickles.Prove.Wrap`. Filename template uses `%c` (replaced
  -- with a monotonic counter independent of `KIMCHI_STEP_LABELS_DUMP`'s).
  Process.lookupEnv "KIMCHI_STEP_CS_DUMP" >>= case _ of
    Nothing -> pure unit
    Just pathTmpl -> do
      counter <- bumpStepCsCounter
      let path = String.replaceAll (Pattern "%c") (Replacement (show counter)) pathTmpl
      FS.writeTextFile UTF8 path (vestaConstraintSystemToJson constraintSystem)

  pure
    { proverIndex
    , verifierIndex
    , constraintSystem
    , builtState
    , constraints
    }

-- | Pre-pass that builds the step constraint system (no Rust prover-
-- | index creation) just to count gates and derive the rule's own
-- | step-circuit domain log2. PS analog of OCaml's `Fix_domains.domains`
-- | (`mina/src/lib/crypto/pickles/fix_domains.ml:22-91`).
-- |
-- | Mirrors `stepCompile`'s setup so the gate count it produces is the
-- | same one `stepCompile` would produce given the same `ctx`. Caller
-- | is expected to construct `ctx` with placeholder `selfStepDomainLog2 = 20`
-- | (= OCaml `rough_domains.h`, `fix_domains.ml:6-8`) for `Self` slots,
-- | matching OCaml's pre-pass; `External` slots use real values from
-- | their compiled prover indices.
-- |
-- | Returns `ceil_log2(zk_rows + public_input_size + rows_len)` with
-- | `zk_rows = 3` (`fix_domains.ml:4`). Lookup-table sizing
-- | (`fix_domains.ml:28-71`) is omitted — current rules don't use
-- | `range_check` / `xor` / `lookup` / `runtime_tables` gates.
preComputeStepDomainLog2
  :: forall @prevsSpec @outputSize @valCarrier @inputVal @input @outputVal @output @prevInputVal @prevInput
       @mpvMax @mpvPad @nd ndPred len carrier carrierVar sideloadedVkCarrier vkSourcesCarrier vkSourcesCarrierVar blueprints
       pad unfsTotal digestPlusUnfs
       nc
   . CircuitGateConstructor StepField VestaG
  -- Side-loaded VK carrier — see stepMain. preComputeStepDomainLog2
  -- runs at compile time; the caller synthesizes a placeholder
  -- carrier (e.g. `mkUnitVkCarrier` for compiled-only specs).
  => BuildSlotVkSources (SLVK.VerificationKey nc (F StepField) Boolean) prevsSpec len blueprints sideloadedVkCarrier vkSourcesCarrier
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
  => MpvPadding.MpvPadding mpvPad len mpvMax
  => Mul mpvMax Step.UnfinalizedFieldCount unfsTotal
  => Add unfsTotal 1 digestPlusUnfs
  => Add digestPlusUnfs mpvMax outputSize
  => CircuitType StepField inputVal input
  => CircuitType StepField outputVal output
  => CircuitType StepField prevInputVal prevInput
  => CircuitType StepField carrier carrierVar
  => CheckedType StepField (KimchiConstraint StepField) carrierVar
  => StepSlotsCarrier
       prevsSpec
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
       StepIPARounds
       WrapIPARounds
       (FVar StepField)
       (Type2 (SplitField (FVar StepField) (BoolVar StepField)))
       (BoolVar StepField)
       len
       carrierVar
       vkSourcesCarrierVar
  => CheckedType StepField (KimchiConstraint StepField) input
  => StepProveContext len nd blueprints
  -> StepRule len valCarrier inputVal input outputVal output prevInputVal prevInput
  -> Effect Int
preComputeStepDomainLog2 ctx rule = do
  sideloadedCarrier <- getSideloadedVKsCarrier @prevsSpec unit
  builtState <-
    compile
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
            @(SLVK.VerificationKey nc (F StepField) Boolean)
            rule
            ctx.srsData
            ctx.dummySg
            sideloadedCarrier
      )
      (Kimchi.initialState :: CircuitBuilderState (KimchiGate StepField) (AuxState StepField))

  let
    kimchiRows :: Array (KimchiRow StepField)
    kimchiRows = concatMap (toKimchiRows <<< _.constraint) builtState.constraints
    gateCount = Array.length kimchiRows
    piSize = Array.length builtState.publicInputs
    zkRows = 3
    rows = zkRows + piSize + gateCount
  pure (ceilLog2 rows)
  where
  -- | `ceilLog2 n` = smallest k such that `2^k >= n`. `n = 0` and `n = 1`
  -- | both return 0 (matching OCaml `Int.ceil_log2`).
  ceilLog2 :: Int -> Int
  ceilLog2 n = go 0 1
    where
    go acc p = if p >= n then acc else go (acc + 1) (p * 2)

-- | V2 solve phase — parallel to `stepSolveAndProve` but uses
-- | `StepProverT` / `StepAdvice` / `stepMain`. `prevChallenges` for
-- | `pallasCreateProofWithPrev` come from the uniform
-- | `kimchiPrevChallenges` field on `StepAdvice` (sized `len`).
-- | Errors surface through `ExceptT EvaluationError m` — the same
-- | error type the underlying `SolverT` uses. Constraint-system-
-- | unsatisfied failures are reported as `FailedAssertion`.
stepSolveAndProve
  :: forall @prevsSpec @outputSize @valCarrier @inputVal @input @outputVal @output @prevInputVal @prevInput
       @mpvMax @mpvPad @nd ndPred len carrier carrierVar sideloadedVkCarrier blueprints
       pad unfsTotal digestPlusUnfs m
   . CircuitGateConstructor StepField VestaG
  => BuildSlotVkSources SideloadBundle.Bundle prevsSpec len blueprints sideloadedVkCarrier
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
  => MpvPadding.MpvPadding mpvPad len mpvMax
  => Mul mpvMax Step.UnfinalizedFieldCount unfsTotal
  => Add unfsTotal 1 digestPlusUnfs
  => Add digestPlusUnfs mpvMax outputSize
  => CircuitType StepField inputVal input
  => CircuitType StepField outputVal output
  => CircuitType StepField prevInputVal prevInput
  => CircuitType StepField carrier carrierVar
  => CheckedType StepField (KimchiConstraint StepField) carrierVar
  => StepSlotsCarrier
       prevsSpec
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
       StepIPARounds
       WrapIPARounds
       (FVar StepField)
       (Type2 (SplitField (FVar StepField) (BoolVar StepField)))
       (BoolVar StepField)
       len
       carrierVar
       vkSourcesCarrierVar
  => CheckedType StepField (KimchiConstraint StepField) input
  => Monad m
  => SlotStatementsCarrier prevsSpec valCarrier
  => StepProveContext len nd blueprints
  -> StepRule len valCarrier inputVal input outputVal output prevInputVal prevInput
  -> StepCompileResult
  -> StepAdvice prevsSpec StepIPARounds WrapIPARounds wrapVkChunks inputVal len carrier valCarrier sideloadedVkCarrier
  -> ExceptT EvaluationError m (StepProveResult outputSize)
stepSolveAndProve ctx rule compileResult advice = do
  -- Source the side-loaded VK carrier directly from the StepAdvice.
  -- The advice was constructed by `mkStepAdvice` from the same
  -- spec-indexed runtime carrier the prover monad would have served;
  -- pulling it from the field here keeps `m` arbitrary (no
  -- `SideloadedVKsM` constraint required) and lets `StepProverT`'s
  -- instance for `SideloadedVKsM` route any in-rule call to
  -- `getSideloadedVKsCarrier` to the same field.
  let
    StepAdvice adv = advice
    sideloadedCarrier = adv.sideloadedVKs

    rawSolver
      :: SolverT StepField (KimchiConstraint StepField)
           ( StepProverT prevsSpec StepIPARounds WrapIPARounds inputVal
               len
               carrier
               valCarrier
               sideloadedVkCarrier
               m
           )
           Unit
           (Vector outputSize (F StepField))
    rawSolver =
      makeSolver' (emptyProverState { debug = ctx.debug })
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
              @SideloadBundle.Bundle
              rule
              ctx.srsData
              ctx.dummySg
              sideloadedCarrier
        )

  -- `runStepProverT` returns the solver result paired with the
  -- `StepProverCapture` State accumulated by the rule body — in
  -- particular the FVars `setUserPublicOutputFields` wrote.
  Tuple eRes capturedState <- lift $
    runStepProverT advice (runSolverT rawSolver unit)

  case eRes of
    Left e -> throwError (WithContext "stepProve solver" e)
    Right (Tuple publicOutputs assignments) -> do
      let
        { witness, publicInputs } = makeWitness
          { assignments
          , constraints: map _.variables compileResult.constraints
          , publicInputs: compileResult.builtState.publicInputs
          }
      when ctx.debug do
        let
          csSatisfied = verifyProverIndex @StepField @VestaG
            { proverIndex: compileResult.proverIndex, witness, publicInputs }
        when (not csSatisfied) do
          let
            _ = unsafePerformEffect $
              dumpRowLabels
                (Array.length compileResult.builtState.publicInputs)
                compileResult.builtState.constraints
          throwError (FailedAssertion "stepProve: constraint system not satisfied (wrote row→label map to /tmp/ps_step_row_labels.txt)")
      -- Evaluate the rule's user `publicOutput` FVars (captured by
      -- `setUserPublicOutputFields` in the StepProverT State) against
      -- the post-solve assignments map. If the State slot is empty,
      -- `stepMain`'s rule_main block didn't run — that's a bug; we
      -- surface it as a FailedAssertion rather than silently
      -- producing zeros. Raw field values are returned;
      -- `runProverBody` applies `fieldsToValue` against the rule's
      -- specific `outputVal`.
      userPublicOutputFields <- case capturedState.userPublicOutputFields of
        Nothing ->
          throwError (FailedAssertion "stepProve: stepMain did not capture publicOutput FVars (StepProverT.State.userPublicOutputFields was Nothing post-solve)")
        Just fieldVars -> do
          let
            evalLookup :: Variable -> Either EvaluationError StepField
            evalLookup v =
              maybe (Left (MissingVariable v)) Right (Map.lookup v assignments)
          case traverse (CVar.eval evalLookup) fieldVars of
            Left e -> throwError e
            Right fieldVals -> pure fieldVals
      let
        proof = pallasCreateProofWithPrev
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
      pure
        { proverIndex: compileResult.proverIndex
        , verifierIndex: compileResult.verifierIndex
        , constraintSystem: compileResult.constraintSystem
        , witness
        , publicInputs
        , publicOutputs
        , proof
        , assignments
        , userPublicOutputFields
        }

