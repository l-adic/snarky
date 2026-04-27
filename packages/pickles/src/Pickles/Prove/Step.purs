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
  , BuildStepAdviceWithOraclesInput
  , extractWrapVKCommsAdvice
  , extractWrapVKForStepHash
  , dummyWrapTockPublicInput
  , StepRule
  , StepCompileResult
  , StepProveResult
  , StepAdvice(..)
  , StepProverT(..)
  , runStepProverT
  , StepProveContext
  , SlotAdviceContrib
  , buildSlotAdvice
  , buildStepAdvice
  , buildStepAdviceWithOracles
  , stepCompile
  , stepSolveAndProve
  ) where

import Prelude

import Control.Monad.Except (ExceptT, throwError)
import Control.Monad.Reader (ReaderT, ask, runReaderT)
import Control.Monad.Trans.Class (lift)
import Data.Array (concatMap)
import Data.Array as Array
import Data.Either (Either(..))
import Data.Fin (getFinite, unsafeFinite)
import Data.Foldable (for_)
import Data.FoldableWithIndex (forWithIndex_)
import Data.Traversable (traverse)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..), fromJust, maybe)
import Data.Newtype (class Newtype, un, unwrap)
import Data.Reflectable (class Reflectable, reflectType)
import Data.Tuple (Tuple(..))
import Data.Vector (Vector)
import Data.Vector as Vector
import Effect (Effect)
import Effect.Class (class MonadEffect, liftEffect)
import Effect.Ref as Ref
import Effect.Unsafe (unsafePerformEffect)
import Node.Encoding (Encoding(..))
import Node.FS.Sync as FS
import Partial.Unsafe (unsafePartial)
import Pickles.Dummy (baseCaseDummies, dummyIpaChallenges, stepDummyUnfinalizedProof, wrapDomainLog2ForProofsVerified, wrapDummyUnfinalizedProof)
import Pickles.Linearization (pallas, vesta) as Linearization
import Pickles.Linearization.FFI (PointEval) as LFFI
import Pickles.Linearization.FFI (domainGenerator, domainShifts)
import Pickles.PlonkChecks (AllEvals)
import Pickles.ProofFFI (OraclesResult) as ProofFFI
import Pickles.ProofFFI (Proof, pallasCreateProofWithPrev, permutationVanishingPolynomial, proofCoefficientEvals, proofIndexEvals, proofSigmaEvals, proofWitnessEvals, proofZEvals, tCommVec, vestaProofCommitments, vestaProofOpeningDelta, vestaProofOpeningLrVec, vestaProofOpeningPrechallenges, vestaProofOpeningZ1, vestaProofOpeningZ2, vestaProofOracles, vestaVerifierIndexCommitments, vestaVerifierIndexDigest)
import Pickles.ProofWitness (ProofWitness)
import Pickles.Prove.Pure.Common (crossFieldDigest)
import Pickles.Prove.Pure.Step (ExpandProofInput, ExpandProofOutput, expandProof) as PureStep
import Pickles.Prove.Pure.Wrap (packBranchDataWrap, revOnesVector)
import Pickles.Step.Advice (class StepPrevValuesM, class StepSlotsM, class StepWitnessM)
import Pickles.Step.Main (RuleOutput, StepMainSrsData, stepMain)
import Pickles.Step.MessageHash (hashMessagesForNextStepProofPure, hashMessagesForNextStepProofPureTraced)
import Pickles.Step.Prevs (class PrevValuesCarrier, class PrevsCarrier, PrevsSpecCons, PrevsSpecNil, StepSlot(..), replicatePrevsCarrier)
import Pickles.Trace as Trace
import Pickles.Types (BranchData(..), FopProofState(..), PaddedLength, PerProofUnfinalized(..), PointEval(..), StepAllEvals(..), StepField, StepIPARounds, StepPerProofWitness(..), StepProofState(..), VerificationKey(..), WrapField, WrapIPARounds, WrapProof(..), WrapProofMessages(..), WrapProofOpening(..))
import Pickles.VerificationKey (StepVK)
import Pickles.Verify.Types (BranchData) as VT
import Pickles.Verify.Types (PlonkMinimal, UnfinalizedProof)
import Pickles.Wrap.MessageHash (hashMessagesForNextWrapProofPureGeneral)
import Prim.Int (class Add, class Compare, class Mul)
import Prim.Ordering (LT)
import Safe.Coerce (coerce)
import Snarky.Backend.Builder (CircuitBuilderState, Labeled)
import Snarky.Backend.Compile (SolverT, compile, makeSolver', runSolverT)
import Snarky.Backend.Kimchi (makeConstraintSystemWithPrevChallenges, makeWitness)
import Snarky.Backend.Kimchi.Class (class CircuitGateConstructor, createProverIndex, createVerifierIndex, verifyProverIndex)
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
-- `StepSlot n_i ds dw …` that `replicatePrevsCarrier` broadcasts to
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
-- | derived from `prevsSpec` via the `PrevsCarrier` instance), and
-- | reified to an Int internally via `reflectType (Proxy @len)` where
-- | needed.
type BuildStepAdviceInput inputVal valCarrier =
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
  -- | `PrevValuesCarrier`. Each slot's value is the prev's
  -- | `StatementIO inputVal outputVal` — even on the base case,
  -- | callers supply an inhabitant of the right type (the values are
  -- | irrelevant when `proofMustVerify[i] = false`).
  , prevAppStates :: valCarrier
  }

-- | Build a base-case `StepAdvice` keyed on a spec-indexed per-slot
-- | carrier.
-- |
-- | Requires a `PrevsCarrier prevsSpec … len carrier` instance so the
-- | caller's `prevsSpec` determines `len` (= number of prev slots) and
-- | `carrier` (= nested-tuple carrier type). The rank-2 `dummySlot`
-- | builds each slot's `StepPerProofWitness` with the correct per-slot
-- | `n_i` via `Vector.replicate`.
-- |
-- | Handles homogeneous specs (Simple_chain N1/N2, Add_one_return) and
-- | heterogeneous specs (Tree_proof_return `[N0; N2]`) uniformly —
-- | `Vector.replicate` at `n=0` produces nil, so slots with `n_i=0`
-- | have empty `prevChallenges` / `prevSgs` automatically.
buildStepAdvice
  :: forall @prevsSpec inputVal len carrier valCarrier
   . Reflectable len Int
  => PrevsCarrier
       prevsSpec
       StepIPARounds
       WrapIPARounds
       (F StepField)
       (Type2 (SplitField (F StepField) Boolean))
       Boolean
       len
       carrier
  => PrevValuesCarrier prevsSpec valCarrier
  => BuildStepAdviceInput inputVal valCarrier
  -> StepAdvice prevsSpec StepIPARounds WrapIPARounds inputVal len carrier valCarrier
buildStepAdvice input =
  let
    -- Pallas generator (= OCaml `Tock.Curve.one`). Never the
    -- point-at-infinity, so `toAffine` is always `Just`. Reused for
    -- every curve-point field in the base-case dummy advice.
    g0 :: AffinePoint (F StepField)
    g0 = coerce (unsafePartial (fromJust (Curves.toAffine (Curves.generator :: Pallas.G))) :: AffinePoint StepField)

    g0w :: WeierstrassAffinePoint PallasG (F StepField)
    g0w = WeierstrassAffinePoint g0

    -- Reify `len` (= most_recent_width = max_proofs_verified) to a
    -- runtime Int for the few places that need one.
    mrw = reflectType (Proxy @len)

    -- Ro-derived constants shared across all fields.
    bcd = baseCaseDummies { maxProofsVerified: mrw }

    -- z1 / z2 from OCaml `proof.ml:dummy` openings (Ro.tock values
    -- re-wrapped as cross-field Type2 SplitField in the step field).
    z1 :: Type2 (SplitField (F StepField) Boolean)
    z1 = toShifted (F bcd.proofDummy.z1)

    z2 :: Type2 (SplitField (F StepField) Boolean)
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

    prevEvalsDummy :: StepAllEvals (F StepField)
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

    dummyBranch :: StepBranchData
    dummyBranch =
      -- OCaml wrap_main.ml:231-238 computes
      -- `actual_proofs_verified_mask = ones_vector ~first_zero:w
      --  |> Vector.rev`. Yields per-width masks:
      --   N0 → [F, F]
      --   N1 → [F, T]
      --   N2 → [T, T]
      { domainLog2: F (Curves.fromInt input.stepDomainLog2 :: StepField)
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

    digestStep :: F StepField
    digestStep =
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
      , spongeDigest: digestStep
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
      :: forall n
       . Reflectable n Int
      => StepSlot
           n
           StepIPARounds
           WrapIPARounds
           (F StepField)
           (Type2 (SplitField (F StepField) Boolean))
           Boolean
    dummySlot = StepSlot
      { sppw: StepPerProofWitness
          { wrapProof: WrapProof
              { opening: WrapProofOpening
                  { lr: Vector.generate
                      ( \_ ->
                          { l: WeierstrassAffinePoint g0
                          , r: WeierstrassAffinePoint g0
                          }
                      )
                  , z1: z1
                  , z2: z2
                  , delta: WeierstrassAffinePoint g0
                  , sg: WeierstrassAffinePoint g0
                  }
              , messages: WrapProofMessages
                  { wComm: Vector.generate (\_ -> WeierstrassAffinePoint g0)
                  , zComm: WeierstrassAffinePoint g0
                  , tComm: Vector.generate (\_ -> WeierstrassAffinePoint g0)
                  }
              }
          , proofState: StepProofState
              { fopState: FopProofState
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
              , branchData: BranchData
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
      }
  in
    StepAdvice
      { perProofSlotsCarrier: replicatePrevsCarrier @prevsSpec dummySlot
      , publicInput: input.publicInput
      , publicUnfinalizedProofs: Vector.replicate dummyPublicUnfinalized
      , messagesForNextWrapProof: Vector.replicate (F zero)
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
      }

-- | Extract sigma/coeff/index point triples from a compiled wrap
-- | verifier index, in the lightweight `Pickles.Types.VerificationKey`
-- | shape the step advice uses (WeierstrassAffinePoint PallasG (F
-- | StepField)). The wrap VK's commitments are Pallas points with
-- | coordinates in Pallas.BaseField = StepField, so no cross-field
-- | coercion is needed.
extractWrapVKCommsAdvice
  :: VerifierIndex PallasG WrapField
  -> VerificationKey (WeierstrassAffinePoint PallasG (F StepField))
extractWrapVKCommsAdvice vk =
  let
    comms = vestaVerifierIndexCommitments vk

    wrapPt :: AffinePoint StepField -> WeierstrassAffinePoint PallasG (F StepField)
    wrapPt pt = WeierstrassAffinePoint { x: F pt.x, y: F pt.y }
  in
    VerificationKey
      { sigma: map wrapPt comms.sigma
      , coeff: map wrapPt comms.coeff
      , index: map wrapPt comms.index
      }

-- | `StepVK StepField` (the eight named-field VK shape) extracted from
-- | a compiled wrap verifier index. Used for
-- | `hashMessagesForNextStepProofPure` in the step field — the dummy
-- | wrap proof's `messages_for_next_step_proof` hash mirrors OCaml's
-- | `Common.hash_messages_for_next_step_proof` on the real wrap VK.
extractWrapVKForStepHash
  :: VerifierIndex PallasG WrapField
  -> StepVK StepField
extractWrapVKForStepHash vk =
  let
    comms = vestaVerifierIndexCommitments vk
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
    fop :: UnfinalizedProof StepIPARounds (F StepField) (Type1 (F StepField)) Boolean
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
    sizedStepBits :: SizedF 128 (F StepField) -> WrapField
    sizedStepBits = SizedF.toField <<< (coerceViaBits :: SizedF 128 StepField -> SizedF 128 WrapField) <<< SizedF.unwrapF

    -- 5 Type1 fp fields, order: cip, b, zetaToSrsLength,
    -- zetaToDomainSize, perm (matches `packStatement`).
    fpFields :: Array WrapField
    fpFields =
      [ type1StepBits dv.combinedInnerProduct
      , type1StepBits dv.b
      , type1StepBits p.zetaToSrsLength
      , type1StepBits p.zetaToDomainSize
      , type1StepBits p.perm
      ]

    -- 2 raw challenges: beta, gamma.
    challenges2 :: Array WrapField
    challenges2 = [ sizedStepBits p.beta, sizedStepBits p.gamma ]

    -- 3 scalar challenges: alpha, zeta, xi.
    scalarChallenges3 :: Array WrapField
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
    msgWrapDigestWrapField :: WrapField
    msgWrapDigestWrapField = input.msgWrapDigest

    -- messagesForNextStepProof: step-field hash over (real wrap VK +
    -- prev app_state + prev (Dummy.Ipa.Wrap.sg, expanded bp chals)).
    -- OCaml `proof.ml:168-171` sets
    --   messages_for_next_step_proof.challenge_polynomial_commitments
    --     = Vector.init most_recent_width ~f:(fun _ -> Lazy.force Dummy.Ipa.Wrap.sg)
    wrapVkStep :: StepVK StepField
    wrapVkStep = extractWrapVKForStepHash input.wrapVK

    stepExpanded :: Vector StepIPARounds StepField
    stepExpanded = dummyIpaChallenges.stepExpanded

    singleEntry :: { sg :: AffinePoint StepField, expandedBpChallenges :: Vector StepIPARounds StepField }
    singleEntry = { sg: input.wrapSg, expandedBpChallenges: stepExpanded }

    -- `proofs` has `n` entries (type param), matching OCaml
    -- `proof.ml:168-171`:
    --   messages_for_next_step_proof.challenge_polynomial_commitments
    --     = Vector.init most_recent_width (fun _ -> Dummy.Ipa.Wrap.sg)
    appStateFields = valueToFields @StepField @stmt input.prevStatement

    msgStepDigestStepField :: StepField
    msgStepDigestStepField = hashMessagesForNextStepProofPure
      { stepVk: wrapVkStep
      , appState: appStateFields
      , proofs: Vector.replicate @n singleEntry
      }

    -- 3 digests in packStatement order:
    -- [spongeDigest, msgWrap, msgStep]. `fopProofState.spongeDigest`
    -- is already a step-field value; coerce to wrap bits.
    sponge0 :: F StepField
    sponge0 = fop.spongeDigestBeforeEvaluations

    digests3 :: Array WrapField
    digests3 =
      [ stepToWrap sponge0
      , msgWrapDigestWrapField -- already wrap field
      , stepToWrap (F msgStepDigestStepField)
      ]

    -- StepIPARounds bulletproof challenges.
    bpChals :: Array WrapField
    bpChals = map sizedStepBits (Vector.toUnfoldable dv.bulletproofChallenges)

    -- Packed branch_data: `4 * domainLog2 + mask[0] + 2 * mask[1]`.
    -- The mask is OCaml's `ones_vector ~first_zero:most_recent_width |>
    -- Vector.rev` padded to `branchDataMaskWidth = 2`. Constructed via
    -- the shared `revOnesVector` helper and packed via the shared
    -- `packBranchDataWrap` (same encoder the wrap-side uses through its
    -- own in-circuit mask construction).
    packedBranchData :: WrapField
    packedBranchData = packBranchDataWrap
      { domainLog2: Curves.fromInt input.stepDomainLog2 :: StepField
      , proofsVerifiedMask: revOnesVector (reflectType (Proxy @n))
      }

    -- Feature flags + lookup slots — all constant zero for vanilla
    -- Mina (`Features.Full.none`).
    featureFlags :: Array WrapField
    featureFlags = Array.replicate 8 zero

    lookupSlots :: Array WrapField
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

-- | Inputs for `buildStepAdviceWithOracles`.
-- |
-- | Generalized to support both base case (dummy wrap proof) and
-- | inductive case (real wrap proof from a previous iteration).
-- | The caller provides the wrap proof, its public input, and the
-- | padded accumulator — the builder treats them uniformly.
-- | Input record for `buildStepAdviceWithOracles`. Parameterized on
-- | TWO types:
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
type BuildStepAdviceWithOraclesInput inputVal stmt =
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
-- | — the assembler in `mkStepAdvice` (or `buildStepAdviceWithOracles`'s
-- | wrapper) plugs them in.
-- |
-- | Reference: mina/src/lib/crypto/pickles/step.ml:131-150 (`expand_proof`
-- | signature) + step.ml:736-770 (the `go` recursion that conses each
-- | per-slot output onto the rest's vectors).
type SlotAdviceContrib :: Int -> Type
type SlotAdviceContrib n =
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
      StepSlot
        n
        StepIPARounds
        WrapIPARounds
        (F StepField)
        (Type2 (SplitField (F StepField) Boolean))
        Boolean
  }

--------------------------------------------------------------------------------
-- Oracle-enriched advice builder (spec-indexed per-slot carrier)
--
-- `buildStepAdviceWithOracles` runs `vestaProofOracles` on
-- `input.wrapProof` + `input.wrapPublicInput`, then feeds the result
-- through `expandProof` to compute the per-slot template data that
-- the rank-2 `StepSlot` dummy passes to `replicatePrevsCarrier`.
--
-- For rules with no prev proofs (Add_one_return / `PrevsSpecNil`), use
-- `buildStepAdvice` directly — this builder assumes at least one prev
-- slot's worth of oracle data is meaningful.
--
-- Reference: mina/src/lib/crypto/pickles/step.ml:298-343
--------------------------------------------------------------------------------

-- | Oracle-enriched builder producing a `StepAdvice` spec-indexed
-- | carrier. Runs `vestaProofOracles` on the provided wrap proof +
-- | public input, feeds through `expandProof`, and assembles the
-- | per-slot rank-2 `StepSlot` dummy used by `replicatePrevsCarrier`.
buildStepAdviceWithOracles
  :: forall @n @prevsSpec inputVal input prevHeadStmt prevHeadStmtVar
       len carrier pad
   . Reflectable n Int
  => Reflectable len Int
  => Reflectable pad Int
  => Add pad n PaddedLength
  => CircuitType StepField inputVal input
  => CircuitType StepField prevHeadStmt prevHeadStmtVar
  => PrevsCarrier
       prevsSpec
       StepIPARounds
       WrapIPARounds
       (F StepField)
       (Type2 (SplitField (F StepField) Boolean))
       Boolean
       len
       carrier
  => PrevValuesCarrier prevsSpec (Tuple prevHeadStmt Unit)
  => BuildStepAdviceWithOraclesInput inputVal prevHeadStmt
  -> Effect
       { advice ::
           StepAdvice prevsSpec StepIPARounds WrapIPARounds inputVal len carrier
             (Tuple prevHeadStmt Unit)
       , challengePolynomialCommitment :: AffinePoint StepField
       }
buildStepAdviceWithOracles input = do
  let
    -- Previously hardcoded to [dummy, dummy] — correct for base case but
    -- wrong for inductive (where slot 1 should be the real wrap proof's
    -- own new bp chals). Now threaded through from the caller so they
    -- pass the right values per case. See input field docs.
    wrapPadded :: Vector 2 (Vector WrapIPARounds WrapField)
    wrapPadded = input.wrapOwnPaddedBpChals

    msgWrapHash :: WrapField
    msgWrapHash = hashMessagesForNextWrapProofPureGeneral
      { sg: input.stepOpeningSg
      , paddedChallenges: wrapPadded
      }

    msgWrapHashStep :: F StepField
    msgWrapHashStep = F (crossFieldDigest msgWrapHash)

  -- === TRACE Stage 3: the two digest hashes ===
  let
    wrapVkStep :: StepVK StepField
    wrapVkStep = extractWrapVKForStepHash input.wrapVK

    -- | Per-slot `prev_challenge_polynomial_commitments :: Vector n`,
    -- | derived from `input.prevChalPolys :: Vector PaddedLength` by
    -- | dropping the Wrap_hack front-padding. Each entry preserves its
    -- | distinct sg value — no replication. Mirrors OCaml step.ml:513
    -- | where the same vector feeds both IVP sg_old (step_main.ml:104)
    -- | and msg_for_next_step_proof hash (step_main.ml:70-71).
    prevCpcs :: Vector n (AffinePoint StepField)
    prevCpcs = map _.sg (Vector.drop @pad input.prevChalPolys)

    -- | Per-slot step-expanded bp_chals, derived from the pre-padded
    -- | `input.prevChallengesForStepHash :: Vector PaddedLength` via
    -- | `Vector.drop @pad`. Heterogeneous per slot.
    prevChalsPerSlot :: Vector n (Vector StepIPARounds StepField)
    prevChalsPerSlot = Vector.drop @pad input.prevChallengesForStepHash

    -- | Per-slot `prev_proofs_for_hash`: zips each slot's sg with its
    -- | corresponding step-field-expanded bp_chals vector. Mirrors OCaml
    -- | `Common.hash_messages_for_next_step_proof_traced`'s per-slot
    -- | vectorized input (step.ml:303-306).
    prevProofsForHash :: Vector n { sg :: AffinePoint StepField, expandedBpChallenges :: Vector StepIPARounds StepField }
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

  -- === TRACE Stage 4: full tock_public_input (= wrapPublicInput), index-by-index ===
  for_ (Array.mapWithIndex Tuple input.wrapPublicInput) \(Tuple i v) ->
    Trace.field ("tock_pi." <> show i) v

  -- === TRACE: chal_polys passed to vestaProofOracles ===
  forWithIndex_ input.prevChalPolys \fi entry -> do
    let i = getFinite fi
    Trace.field ("expand_proof.chal_polys." <> show i <> ".comm.x") entry.sg.x
    Trace.field ("expand_proof.chal_polys." <> show i <> ".comm.y") entry.sg.y
    Trace.field ("expand_proof.chal_polys." <> show i <> ".chal.0") (Vector.head entry.challenges)

  let
    toFFIChalPoly r = { sgX: r.sg.x, sgY: r.sg.y, challenges: Vector.toUnfoldable r.challenges }

    oracles :: ProofFFI.OraclesResult WrapField
    oracles = vestaProofOracles input.wrapVK
      { proof: input.wrapProof
      , publicInput: input.wrapPublicInput
      , prevChallenges: map toFFIChalPoly (Vector.toUnfoldable input.prevChalPolys :: Array _)
      }

  Trace.field "expand_proof.wrap_vk_digest" (vestaVerifierIndexDigest input.wrapVK)
  -- === TRACE Stage 5: oracle outputs ===
  Trace.field "expand_proof.oracles.beta" (SizedF.toField oracles.beta)
  Trace.field "expand_proof.oracles.gamma" (SizedF.toField oracles.gamma)
  Trace.field "expand_proof.oracles.alpha_chal" (SizedF.toField oracles.alphaChal)
  Trace.field "expand_proof.oracles.zeta_chal" (SizedF.toField oracles.zetaChal)
  -- === TRACE: plonk0 raw challenges (from wrap statement) ===
  Trace.field "expand_proof.plonk0.alpha.raw" (SizedF.toField (SizedF.wrapF input.wrapPlonkRaw.alpha :: SizedF 128 (F StepField)))
  Trace.field "expand_proof.plonk0.beta" (SizedF.toField (SizedF.wrapF input.wrapPlonkRaw.beta :: SizedF 128 (F StepField)))
  Trace.field "expand_proof.plonk0.gamma" (SizedF.toField (SizedF.wrapF input.wrapPlonkRaw.gamma :: SizedF 128 (F StepField)))
  Trace.field "expand_proof.plonk0.zeta.raw" (SizedF.toField (SizedF.wrapF input.wrapPlonkRaw.zeta :: SizedF 128 (F StepField)))
  Trace.field "expand_proof.oracles.fq_digest" oracles.fqDigest
  Trace.field "expand_proof.oracles.cip_kimchi" oracles.combinedInnerProduct

  -- Trace raw opening prechallenges from the wrap proof.
  let
    rawPrechalsForTrace :: Array WrapField
    rawPrechalsForTrace = vestaProofOpeningPrechallenges input.wrapVK
      { proof: input.wrapProof
      , publicInput: input.wrapPublicInput
      , prevChallenges: map toFFIChalPoly (Vector.toUnfoldable input.prevChalPolys :: Array _)
      }
  for_ (Array.mapWithIndex Tuple rawPrechalsForTrace) \(Tuple i v) ->
    Trace.field ("expand_proof.bp_prechal." <> show i) v

  let
    chalToStep :: SizedF 128 WrapField -> SizedF 128 (F StepField)
    chalToStep s = SizedF.wrapF (coerceViaBits s)

    wrapEndoScalar :: WrapField
    wrapEndoScalar =
      let EndoScalar e = (endoScalar :: EndoScalar WrapField) in e

    stepEndoScalarF :: StepField
    stepEndoScalarF =
      let EndoScalar e = (endoScalar :: EndoScalar StepField) in e

    dummyStepBpChalsRaw :: Vector StepIPARounds (SizedF 128 (F StepField))
    dummyStepBpChalsRaw = map SizedF.wrapF dummyIpaChallenges.stepRaw

    -- plonk0 from the wrap STATEMENT's deferred_values.plonk (matching
    -- OCaml step.ml:150 `let plonk0 = t.statement.proof_state.deferred_values.plonk`).
    plonkMinimalStep :: PlonkMinimal (F StepField)
    plonkMinimalStep =
      { alpha: SizedF.wrapF input.wrapPlonkRaw.alpha
      , beta: SizedF.wrapF input.wrapPlonkRaw.beta
      , gamma: SizedF.wrapF input.wrapPlonkRaw.gamma
      , zeta: SizedF.wrapF input.wrapPlonkRaw.zeta
      }

    branchDataStep :: VT.BranchData StepField Boolean
    branchDataStep = input.wrapBranchData

    stepFopGenerator :: StepField
    stepFopGenerator = domainGenerator input.stepDomainLog2

    stepFopShifts :: Vector 7 StepField
    stepFopShifts = domainShifts input.stepDomainLog2

    zetaExpandedStep :: StepField
    zetaExpandedStep =
      toFieldPure (SizedF.unwrapF plonkMinimalStep.zeta) stepEndoScalarF

    stepFopVanishesOnZk :: StepField
    stepFopVanishesOnZk =
      (permutationVanishingPolynomial :: { domainLog2 :: Int, zkRows :: Int, pt :: StepField } -> StepField)
        { domainLog2: input.stepDomainLog2, zkRows: 3, pt: zetaExpandedStep }

    wrapAllEvalsW :: AllEvals WrapField
    wrapAllEvalsW =
      { ftEval1: oracles.ftEval1
      , publicEvals:
          { zeta: oracles.publicEvalZeta
          , omegaTimesZeta: oracles.publicEvalZetaOmega
          }
      , zEvals: proofZEvals input.wrapProof
      , witnessEvals: proofWitnessEvals input.wrapProof
      , coeffEvals: proofCoefficientEvals input.wrapProof
      , sigmaEvals: proofSigmaEvals input.wrapProof
      , indexEvals: proofIndexEvals input.wrapProof
      }

    wrapShiftsW :: Vector 7 WrapField
    wrapShiftsW = domainShifts input.wrapDomainLog2

    wrapVanishesOnZkW :: WrapField
    wrapVanishesOnZkW =
      (permutationVanishingPolynomial :: { domainLog2 :: Int, zkRows :: Int, pt :: WrapField } -> WrapField)
        { domainLog2: input.wrapDomainLog2, zkRows: 3, pt: oracles.zeta }

    wrapPrevEvalsF :: StepAllEvals (F StepField)
    wrapPrevEvalsF =
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

    expandProofInputRec :: PureStep.ExpandProofInput n 2
    expandProofInputRec =
      { mustVerify: input.mustVerify
      , zkRows: 3
      , srsLengthLog2: 16
      , allEvals: input.wrapPrevEvals
      , pEval0Chunks: [ input.wrapPrevEvals.publicEvals.zeta ]
      -- Sized by the slot's `most_recent_width` (= `n`). OCaml
      -- `proof.ml:dummy` fills this as `Vector.init most_recent_width
      -- (Lazy.force Dummy.Ipa.Step.challenges)`; for real prevs, entries
      -- come from the wrap statement.
      , oldBulletproofChallenges: Vector.replicate @n dummyStepBpChalsRaw
      , plonkMinimal: plonkMinimalStep
      -- This wrap proof's OWN bp challenges, as stored in its
      -- `deferred_values.bulletproof_challenges`. For a dummy prev this
      -- is `Dummy.Ipa.Step.challenges`; for a real prev it's the
      -- challenges from the real IPA fold. `fopState` carries that value
      -- (the caller supplies it per-slot via `input.fopState`).
      , rawBulletproofChallenges: input.fopState.deferredValues.bulletproofChallenges
      , branchData: branchDataStep
      , spongeDigestBeforeEvaluations: input.wrapSpongeDigest
      , stepDomainLog2: input.stepDomainLog2
      , stepGenerator: stepFopGenerator
      , stepShifts: stepFopShifts
      , stepVanishesOnZk: stepFopVanishesOnZk
      , stepOmegaForLagrange: \_ -> one
      , endo: stepEndoScalarF
      , linearizationPoly: Linearization.pallas
      , dlogIndex: extractWrapVKForStepHash input.wrapVK
      , appStateFields: valueToFields @StepField @prevHeadStmt input.prevStatement
      -- Per-slot `prev_challenge_polynomial_commitments :: Vector n`
      -- (OCaml step.ml:513-517). Derived once from `input.prevChalPolys`
      -- by dropping Wrap_hack front-padding — preserves distinct per-
      -- entry values for rules like Tree where `prev_wrap.msg_for_next
      -- _step_proof.cpc` has heterogeneous entries.
      , stepPrevSgs: prevCpcs
      , wrapChallengePolynomialCommitment: input.stepOpeningSg
      , wrapPaddedPrevChallenges: wrapPadded
      , wrapVerifierIndex: input.wrapVK
      , wrapProof: input.wrapProof
      , tockPublicInput: input.wrapPublicInput
      , wrapOraclesPrevChallenges: map toFFIChalPoly (Vector.toUnfoldable input.prevChalPolys :: Array _)
      , wrapDomainLog2: input.wrapDomainLog2
      , wrapEndo: wrapEndoScalar
      , wrapAllEvals: wrapAllEvalsW
      , wrapPEval0Chunks: [ oracles.publicEvalZeta ]
      , wrapShifts: wrapShiftsW
      , wrapZkRows: 3
      , wrapSrsLengthLog2: 15
      , wrapVanishesOnZk: wrapVanishesOnZkW
      , wrapOmegaForLagrange: \_ -> one
      , wrapLinearizationPoly: Linearization.vesta
      , stepProofPrevEvals: wrapPrevEvalsF
      -- Per-slot step-expanded bp_chals, heterogeneous per OCaml
      -- step.ml:519-525. For homogeneous cases (SimpleChain, dummy
      -- prevs) all entries are equal; for Tree b1 slot 1 they differ
      -- (one per slot of the prev wrap proof's stored chal vector).
      , stepPrevChallenges: map (map F) prevChalsPerSlot
      , stepPrevSgsPadded: prevCpcs
      }

    expandProofResult :: PureStep.ExpandProofOutput n
    expandProofResult = PureStep.expandProof expandProofInputRec

  -- === TRACE Stage 2: expand_proof.deferred.* (step-field Type1 deferred values) ===
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

  -- === TRACE: wrap-field unfinalized deferred values (from expandProof) ===
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

    -- Simple_chain FOP proof state (caller-supplied: see input.fopState docs).
    fopState
      :: UnfinalizedProof StepIPARounds (F StepField) (Type1 (F StepField)) Boolean
    fopState = input.fopState

  -- DIAG traces
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
    -- `openingSg` is the sg value computed by `expandProof` —
    -- implements OCaml step.ml:498-501,522-525 where
    -- `wrap_proof.opening.challenge_polynomial_commitment` is either
    -- the wrap proof's own sg (must_verify) or a fresh
    -- `Ipa.Wrap.compute_sg new_bp_chals` (otherwise).
    openingSg :: AffinePoint (F StepField)
    openingSg = coerce expandProofResult.sg

    mkPt :: AffinePoint StepField -> AffinePoint (F StepField)
    mkPt pt = { x: F pt.x, y: F pt.y }

    openingDelta :: AffinePoint (F StepField)
    openingDelta = mkPt (vestaProofOpeningDelta input.wrapProof)

    openingLr :: Vector WrapIPARounds { l :: AffinePoint (F StepField), r :: AffinePoint (F StepField) }
    openingLr = map (\p -> { l: mkPt p.l, r: mkPt p.r })
      (vestaProofOpeningLrVec input.wrapProof)

    openingZ1Raw :: WrapField
    openingZ1Raw = vestaProofOpeningZ1 input.wrapProof

    openingZ2Raw :: WrapField
    openingZ2Raw = vestaProofOpeningZ2 input.wrapProof

    openingZ1 :: Type2 (SplitField (F StepField) Boolean)
    openingZ1 = toShifted (F openingZ1Raw :: F WrapField)

    openingZ2 :: Type2 (SplitField (F StepField) Boolean)
    openingZ2 = toShifted (F openingZ2Raw :: F WrapField)

    wrapCommits = vestaProofCommitments input.wrapProof

    mkPallasAffine :: AffinePoint StepField -> AffinePoint (F StepField)
    mkPallasAffine pt = { x: F pt.x, y: F pt.y }
    wrapMessages =
      { wComm: map mkPallasAffine wrapCommits.wComm
      , zComm: mkPallasAffine wrapCommits.zComm
      , tComm: map mkPallasAffine (tCommVec wrapCommits)
      }

    wrapPE' :: LFFI.PointEval StepField -> LFFI.PointEval (F StepField)
    wrapPE' pe = { zeta: F pe.zeta, omegaTimesZeta: F pe.omegaTimesZeta }

    evalsForAdvice :: ProofWitness (F StepField)
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

    slotBranchData :: StepBranchData
    slotBranchData =
      -- Source from the caller's `wrapBranchData` input so the prev
      -- STEP domain size flows through (NOT `input.wrapDomainLog2`,
      -- which is the prev's WRAP domain — they coincide for
      -- SimpleChain N=1 but differ for e.g. Tree_proof_return's
      -- slot-0 = No_recursion_return where wrap_domain=2^13 but
      -- step_domain=2^9). The inner `inv_ maskedGen` in
      -- step FinalizeOtherProof derives omega from this domain
      -- size; passing the wrong value makes zeta-omega^k=0 later →
      -- DivisionByZero.
      { domainLog2: F input.wrapBranchData.domainLog2
      , mask0: input.wrapBranchData.proofsVerifiedMask `Vector.index` (unsafeFinite @2 0)
      , mask1: input.wrapBranchData.proofsVerifiedMask `Vector.index` (unsafeFinite @2 1)
      }

    dvFop = fopState.deferredValues
    pFop = dvFop.plonk

    -- Rank-2 per-slot template. Inside, `prev_challenge_polynomial
    -- _commitments :: Vector nSlot` is derived from
    -- `input.prevChalPolys :: Vector PaddedLength` via `Vector.drop
    -- @padSlot` (with `Add padSlot nSlot PaddedLength`) — preserving
    -- distinct per-entry values for heterogeneous rules like
    -- Tree_proof_return. `prevChallenges` uses `Vector.replicate`
    -- because its content is homogeneous across entries (same
    -- `prevChallengesForStepHash` vector per slot).
    slotTemplate
      :: forall nSlot padSlot
       . Reflectable nSlot Int
      => Reflectable padSlot Int
      => Add padSlot nSlot PaddedLength
      => StepSlot
           nSlot
           StepIPARounds
           WrapIPARounds
           (F StepField)
           (Type2 (SplitField (F StepField) Boolean))
           Boolean
    slotTemplate = StepSlot
      { sppw: StepPerProofWitness
          { wrapProof: WrapProof
              { opening: WrapProofOpening
                  { lr: map
                      ( \r ->
                          { l: WeierstrassAffinePoint r.l
                          , r: WeierstrassAffinePoint r.r
                          }
                      )
                      openingLr
                  , z1: openingZ1
                  , z2: openingZ2
                  , delta: WeierstrassAffinePoint openingDelta
                  , sg: WeierstrassAffinePoint openingSg
                  }
              , messages: WrapProofMessages
                  { wComm: map WeierstrassAffinePoint wrapMessages.wComm
                  , zComm: WeierstrassAffinePoint wrapMessages.zComm
                  , tComm: map WeierstrassAffinePoint wrapMessages.tComm
                  }
              }
          , proofState: StepProofState
              { fopState: FopProofState
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
              , branchData: BranchData
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
          -- Per-slot prev_challenges (step-expanded bp_chals), heterogeneous
          -- per OCaml step.ml:519-525. Derived from
          -- `input.prevChallengesForStepHash :: Vector PaddedLength` via
          -- `Vector.drop @padSlot` — same pattern as `prevSgs` below,
          -- preserving distinct per-slot challenge vectors that matter
          -- for Tree b1 slot 1 verifying wrap_b0.
          , prevChallenges: map
              (\chals -> UnChecked (map F chals))
              (Vector.drop @padSlot input.prevChallengesForStepHash)
          -- Per-slot prev_challenge_polynomial_commitments, heterogeneous
          -- per OCaml step.ml:513-517. Derived from `input.prevChalPolys`
          -- via `Vector.drop @padSlot` (using the rank-2-quantified
          -- `padSlot` from this slotTemplate) — single source of truth
          -- shared with the FFI oracles call (step.ml:360-371 in OCaml),
          -- matching OCaml's `~sg_old:prev_challenge_polynomial_commitments`.
          , prevSgs: map
              (\e -> WeierstrassAffinePoint (coerce e.sg :: AffinePoint (F StepField)))
              (Vector.drop @padSlot input.prevChalPolys)
          }
      }

    advice
      :: StepAdvice prevsSpec StepIPARounds WrapIPARounds inputVal len carrier
           (Tuple prevHeadStmt Unit)
    advice = StepAdvice
      { perProofSlotsCarrier: replicatePrevsCarrier @prevsSpec slotTemplate
      , publicInput: input.publicInput
      , publicUnfinalizedProofs: Vector.replicate expandedUnfinalized
      , messagesForNextWrapProof: Vector.replicate msgWrapHashStep
      , wrapVerifierIndex: extractWrapVKCommsAdvice input.wrapVK
      , kimchiPrevChallenges:
          Vector.replicate
            { sgX: input.kimchiPrevSg.x
            , sgY: input.kimchiPrevSg.y
            , challenges: input.kimchiPrevChallengesExpanded
            }
      -- Single-slot helper: wrap the user-provided statement into a
      -- singleton carrier `Tuple stmt unit`, matching what
      -- `PrevValuesCarrier (PrevsSpecCons k stmt PrevsSpecNil)` derives.
      , prevAppStates: Tuple input.prevStatement unit
      }

  -- === TRACE: wrap-proof opening z1/z2 values (raw Fq + cross-field sDiv2) ===
  -- The exists_prevs Type2 SplitField check runs on these. Tag by mustVerify
  -- to distinguish slot 0 (real NRR, mustVerify=true) from slot 1 (dummy,
  -- mustVerify=false) in Tree_proof_return.
  let
    tag = if input.mustVerify then "real" else "dummy"
    z1SplitField = case openingZ1 of Type2 sf -> sf
    z2SplitField = case openingZ2 of Type2 sf -> sf
    sDiv2OfSf sf = case sf of SplitField { sDiv2: F d } -> d
  Trace.field ("expand_proof.opening.z1.raw_" <> tag)
    (crossFieldDigest openingZ1Raw :: StepField)
  Trace.field ("expand_proof.opening.z1.sDiv2_" <> tag) (sDiv2OfSf z1SplitField)
  Trace.field ("expand_proof.opening.z2.raw_" <> tag)
    (crossFieldDigest openingZ2Raw :: StepField)
  Trace.field ("expand_proof.opening.z2.sDiv2_" <> tag) (sDiv2OfSf z2SplitField)

  pure
    { advice
    , challengePolynomialCommitment: expandProofResult.sg
    }

--------------------------------------------------------------------------------
-- buildSlotAdvice — per-slot variant returning a `SlotAdviceContrib`
--
-- PS analog of OCaml's `expand_proof` (`step.ml:122-150`). Returns ONE
-- slot's contribution; the caller (`mkStepAdvice` in
-- `Pickles.Prove.Compile`) cons-recurses over the prev list to build
-- the multi-slot `StepAdvice`, mirroring OCaml's `go` recursion at
-- `step.ml:736-770`.
--
-- IMPLEMENTATION NOTE (transitional, removed in Phase E): the body
-- delegates to `buildStepAdviceWithOracles` with a synthetic
-- `PrevsSpecCons n prevHeadStmt PrevsSpecNil` spec, then extracts the
-- per-slot pieces via `Vector.head` / `Tuple slotSppw _`. The
-- replicate-then-take-head step is `Vector len = 1`, so the overhead is
-- just one tuple cons.
--
-- When Phase E deletes producers + `buildStepAdviceWithOracles`, this
-- wrapper's body inlines into a standalone per-slot helper with no
-- synthetic spec.
--------------------------------------------------------------------------------

buildSlotAdvice
  :: forall @n inputVal input prevHeadStmt prevHeadStmtVar pad
   . Reflectable n Int
  => Reflectable pad Int
  => Add pad n PaddedLength
  => CircuitType StepField inputVal input
  => CircuitType StepField prevHeadStmt prevHeadStmtVar
  => BuildStepAdviceWithOraclesInput inputVal prevHeadStmt
  -> Effect (SlotAdviceContrib n)
buildSlotAdvice input = do
  { advice, challengePolynomialCommitment } <- buildStepAdviceWithOracles
    @n
    @(PrevsSpecCons n prevHeadStmt PrevsSpecNil)
    input
  let
    StepAdvice s = advice
    Tuple slotSppw _ = s.perProofSlotsCarrier
  pure
    { challengePolynomialCommitment
    , slotUnfinalized: Vector.head s.publicUnfinalizedProofs
    , slotMsgWrapHashStep: Vector.head s.messagesForNextWrapProof
    , slotKimchiPrevEntry: Vector.head s.kimchiPrevChallenges
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
-- | carrier shape that `Pickles.Step.Prevs.PrevValuesCarrier` derives
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
  forall t m'
   . CircuitM StepField (KimchiConstraint StepField) t m'
  => StepWitnessM n StepIPARounds WrapIPARounds PallasG StepField m' inputVal
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
type StepProveContext len =
  { srsData :: StepMainSrsData len
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
-- | reserved by `makeGateData` for public-input placement, so constraint
-- | rows begin at `publicInputSize`. Passing the wrong offset gives
-- | labels that look correct but point to the wrong row — past mistakes
-- | on Tree_proof_return wasted multiple iterations chasing the wrong
-- | context because labels said `exists_unfinalized` when the actual
-- | kimchi row was in `exists_prevs` (see
-- | `memory/project_tree_proof_return_iter2.md` iter 2ap).
dumpRowLabels
  :: Int -- ^ publicInputSize — number of rows kimchi reserves for PI
  -> Array (Labeled (KimchiGate StepField))
  -> Effect Unit
dumpRowLabels publicInputSize cs = do
  let
    { out, row: finalRow } = Array.foldl
      ( \{ row, out } lc ->
          let
            nRows = Array.length (toKimchiRows lc.constraint :: Array (KimchiRow StepField))
            endRow = row + nRows - 1
            path = Array.intercalate "/" lc.context
            line = show row <> ".." <> show endRow <> "\t" <> path
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
  FS.writeTextFile UTF8 "/tmp/ps_step_row_labels.txt"
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
newtype StepAdvice
  :: Type -> Int -> Int -> Type -> Int -> Type -> Type -> Type
newtype StepAdvice prevsSpec ds dw inputVal len carrier valCarrier =
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
    , wrapVerifierIndex ::
        VerificationKey (WeierstrassAffinePoint PallasG (F StepField))
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
    -- | shape `PrevValuesCarrier prevsSpec valCarrier` derives:
    -- |   PrevsSpecNil                            → Unit
    -- |   PrevsSpecCons n stmt rest               → Tuple stmt restValCarrier
    -- | Each `stmt` is the prev rule's `StatementIO inputVal outputVal`
    -- | (the same type bundled in `PrevsSpecCons`'s second parameter).
    -- | Mirrors OCaml's `previous_proof_statements` argument flowing into
    -- | the rule's `main` — the rule body reads slot-specific values out
    -- | (input for Input-mode prevs, output for Output-mode) inside its
    -- | `exists` calls so the witness for the prev's app-state circuit
    -- | variable is sourced from advice rather than baked into a closure.
    , prevAppStates :: valCarrier
    }

derive instance
  Newtype
    (StepAdvice prevsSpec ds dw inputVal len carrier valCarrier)
    _

-- | ReaderT transformer for the v2 prover stack, carrying a
-- | `StepAdvice` over a base monad.
newtype StepProverT
  :: Type -> Int -> Int -> Type -> Int -> Type -> Type -> (Type -> Type) -> Type -> Type
newtype StepProverT prevsSpec ds dw inputVal len carrier valCarrier m a =
  StepProverT
    (ReaderT (StepAdvice prevsSpec ds dw inputVal len carrier valCarrier) m a)

derive instance
  Newtype
    (StepProverT prevsSpec ds dw inputVal len carrier valCarrier m a)
    _

derive newtype instance
  Functor m =>
  Functor (StepProverT prevsSpec ds dw inputVal len carrier valCarrier m)

derive newtype instance
  Apply m =>
  Apply (StepProverT prevsSpec ds dw inputVal len carrier valCarrier m)

derive newtype instance
  Applicative m =>
  Applicative (StepProverT prevsSpec ds dw inputVal len carrier valCarrier m)

derive newtype instance
  Bind m =>
  Bind (StepProverT prevsSpec ds dw inputVal len carrier valCarrier m)

derive newtype instance
  Monad m =>
  Monad (StepProverT prevsSpec ds dw inputVal len carrier valCarrier m)

runStepProverT
  :: forall prevsSpec ds dw inputVal len carrier valCarrier m a
   . StepAdvice prevsSpec ds dw inputVal len carrier valCarrier
  -> StepProverT prevsSpec ds dw inputVal len carrier valCarrier m a
  -> m a
runStepProverT advice (StepProverT m) = runReaderT m advice

instance
  ( Monad m
  , PrevsCarrier
      prevsSpec
      ds
      dw
      (F StepField)
      (Type2 (SplitField (F StepField) Boolean))
      Boolean
      len
      carrier
  ) =>
  StepSlotsM
    prevsSpec
    ds
    dw
    PallasG
    StepField
    (StepProverT prevsSpec ds dw inputVal len carrier valCarrier m)
    len
    carrier where
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
    PallasG
    StepField
    (StepProverT prevsSpec ds dw inputVal len carrier valCarrier m)
    inputVal where

  getMessagesForNextWrapProof _ =
    StepProverT $ map (\(StepAdvice r) -> r.messagesForNextWrapProof) ask
  getWrapVerifierIndex _ =
    StepProverT $ map (\(StepAdvice r) -> r.wrapVerifierIndex) ask
  getStepPublicInput _ =
    StepProverT $ map (\(StepAdvice r) -> r.publicInput) ask
  getStepUnfinalizedProofs _ =
    StepProverT $ map (\(StepAdvice r) -> r.publicUnfinalizedProofs) ask

instance
  Monad m =>
  StepPrevValuesM
    (StepProverT prevsSpec ds dw inputVal len carrier valCarrier m)
    valCarrier where
  getPrevAppStates _ =
    StepProverT $ map (\(StepAdvice r) -> r.prevAppStates) ask

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
       len carrier carrierVar
       pad unfsTotal digestPlusUnfs
   . CircuitGateConstructor StepField VestaG
  => Reflectable len Int
  => Reflectable pad Int
  => Reflectable outputSize Int
  => Add pad len PaddedLength
  => Mul len 32 unfsTotal
  => Add unfsTotal 1 digestPlusUnfs
  => Add digestPlusUnfs len outputSize
  => CircuitType StepField inputVal input
  => CircuitType StepField outputVal output
  => CircuitType StepField prevInputVal prevInput
  => CircuitType StepField carrier carrierVar
  => CheckedType StepField (KimchiConstraint StepField) carrierVar
  => PrevsCarrier
       prevsSpec
       StepIPARounds
       WrapIPARounds
       (F StepField)
       (Type2 (SplitField (F StepField) Boolean))
       Boolean
       len
       carrier
  => PrevsCarrier
       prevsSpec
       StepIPARounds
       WrapIPARounds
       (FVar StepField)
       (Type2 (SplitField (FVar StepField) (BoolVar StepField)))
       (BoolVar StepField)
       len
       carrierVar
  => CheckedType StepField (KimchiConstraint StepField) input
  => StepProveContext len
  -> StepRule len valCarrier inputVal input outputVal output prevInputVal prevInput
  -> Effect StepCompileResult
stepCompile ctx rule = do
  -- Compile-time callers don't need the user's publicOutput value (no
  -- witness body executes), but stepMain's signature still requires a
  -- Ref. Use a throw-away one.
  unusedOutputRef <- Ref.new Nothing
  builtState <-
    compile
      (Proxy @Unit)
      (Proxy @(Vector outputSize (F StepField)))
      (Proxy @(KimchiConstraint StepField))
      ( \_ ->
          stepMain
            @prevsSpec
            @outputSize
            @inputVal
            @input
            @outputVal
            @output
            @prevInputVal
            @prevInput
            @valCarrier
            rule
            ctx.srsData
            ctx.dummySg
            unusedOutputRef
      )
      (Kimchi.initialState :: CircuitBuilderState (KimchiGate StepField) (AuxState StepField))

  let
    kimchiRows = concatMap (toKimchiRows <<< _.constraint) builtState.constraints
    { constraintSystem, constraints } = makeConstraintSystemWithPrevChallenges @StepField
      { constraints: kimchiRows
      , publicInputs: builtState.publicInputs
      , unionFind: (un AuxState builtState.aux).wireState.unionFind
      , prevChallengesCount: reflectType (Proxy @len)
      }

    endo :: StepField
    endo =
      let EndoBase e = (endoBase :: EndoBase StepField) in e

    proverIndex =
      createProverIndex @StepField @VestaG
        { endo, constraintSystem, crs: ctx.crs }

    verifierIndex = createVerifierIndex @StepField @VestaG proverIndex

  pure
    { proverIndex
    , verifierIndex
    , constraintSystem
    , builtState
    , constraints
    }

-- | V2 solve phase — parallel to `stepSolveAndProve` but uses
-- | `StepProverT` / `StepAdvice` / `stepMain`. `prevChallenges` for
-- | `pallasCreateProofWithPrev` come from the uniform
-- | `kimchiPrevChallenges` field on `StepAdvice` (sized `len`).
-- | Errors surface through `ExceptT EvaluationError m` — the same
-- | error type the underlying `SolverT` uses. Constraint-system-
-- | unsatisfied failures are reported as `FailedAssertion`.
stepSolveAndProve
  :: forall @prevsSpec @outputSize @valCarrier @inputVal @input @outputVal @output @prevInputVal @prevInput
       len carrier carrierVar
       pad unfsTotal digestPlusUnfs m
   . CircuitGateConstructor StepField VestaG
  => Reflectable len Int
  => Reflectable pad Int
  => Reflectable outputSize Int
  => Add pad len PaddedLength
  => Mul len 32 unfsTotal
  => Add unfsTotal 1 digestPlusUnfs
  => Add digestPlusUnfs len outputSize
  => CircuitType StepField inputVal input
  => CircuitType StepField outputVal output
  => CircuitType StepField prevInputVal prevInput
  => CircuitType StepField carrier carrierVar
  => CheckedType StepField (KimchiConstraint StepField) carrierVar
  => PrevsCarrier
       prevsSpec
       StepIPARounds
       WrapIPARounds
       (F StepField)
       (Type2 (SplitField (F StepField) Boolean))
       Boolean
       len
       carrier
  => PrevsCarrier
       prevsSpec
       StepIPARounds
       WrapIPARounds
       (FVar StepField)
       (Type2 (SplitField (FVar StepField) (BoolVar StepField)))
       (BoolVar StepField)
       len
       carrierVar
  => CheckedType StepField (KimchiConstraint StepField) input
  => Monad m
  => MonadEffect m
  => PrevValuesCarrier prevsSpec valCarrier
  => StepProveContext len
  -> StepRule len valCarrier inputVal input outputVal output prevInputVal prevInput
  -> StepCompileResult
  -> StepAdvice prevsSpec StepIPARounds WrapIPARounds inputVal len carrier valCarrier
  -> ExceptT EvaluationError m (StepProveResult outputSize)
stepSolveAndProve ctx rule compileResult advice = do
  -- Side-channel for capturing the rule's `publicOutput` FVars from
  -- inside `stepMain`. After the solver runs we have the assignments
  -- map and can evaluate the captured FVars to recover `outputVal`
  -- (the rule's user-defined output, which never appears in the
  -- circuit's kimchi-public-output vector — that one is digest+unfs).
  userPublicOutputRef <- liftEffect $ Ref.new Nothing

  let
    StepAdvice adv = advice

    rawSolver
      :: SolverT StepField (KimchiConstraint StepField)
           ( StepProverT prevsSpec StepIPARounds WrapIPARounds inputVal
               len
               carrier
               valCarrier
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
              @outputSize
              @inputVal
              @input
              @outputVal
              @output
              @prevInputVal
              @prevInput
              @valCarrier
              rule
              ctx.srsData
              ctx.dummySg
              userPublicOutputRef
        )

  eRes <- lift $ runStepProverT advice (runSolverT rawSolver unit)

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
      -- Evaluate the rule's user `publicOutput` FVars against the
      -- post-solve assignments map. If the ref is empty,
      -- `stepMain`'s rule_main block didn't run — that's a bug; we
      -- surface it as a FailedAssertion rather than silently
      -- producing zeros. Raw field values are returned;
      -- `runProverBody` applies `fieldsToValue` against the rule's
      -- specific `outputVal`.
      mUserOutputFields <- liftEffect $ Ref.read userPublicOutputRef
      userPublicOutputFields <- case mUserOutputFields of
        Nothing ->
          throwError (FailedAssertion "stepProve: stepMain did not capture publicOutput FVars (Ref still Nothing post-solve)")
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
                (Vector.toUnfoldable adv.kimchiPrevChallenges :: Array _)
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

