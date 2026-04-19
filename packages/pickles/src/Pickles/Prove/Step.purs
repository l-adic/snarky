-- | Prover-side infrastructure for `Pickles.Step.Main.stepMain`.
-- |
-- | Sister to `Pickles.Prove.Wrap`. This module provides the
-- | **effectful** glue that feeds `stepMain`'s `Req.*` advice during
-- | witness generation:
-- |
-- | * `StepAdvice` — a record holding all advice pieces (one per
-- |   OCaml `Req.*` request) with concrete, already-computed values.
-- | * `StepProverT` — a `ReaderT` transformer serving `StepAdvice` to
-- |   the circuit body. Instances below implement `StepWitnessM` so
-- |   the `stepMain` circuit body can `ask` for each advice piece.
-- | * `runStepProverT` — runner that supplies the advice and unwraps
-- |   to the base monad (`Effect`).
-- | * `stepProve` — compile + solve + kimchi proof creation, mirroring
-- |   OCaml's `Backend.Tick.Proof.create_async` call site in
-- |   `mina/src/lib/crypto/pickles/step.ml:800-852`.
-- |
-- | The module is polymorphic in `n` (max_proofs_verified), `ds`
-- | (step IPA rounds), and `dw` (wrap IPA rounds), matching
-- | `StepWitnessM`'s parameters. The commitment curve is pinned to
-- | `PallasG` (the wrap proof being verified by step has commitments
-- | on Pallas) and the field to `StepField` (= `Vesta.ScalarField` =
-- | `Pallas.BaseField`) — both of which are structural for any step
-- | circuit in the Pasta cycle, not specific to any one application
-- | rule.
module Pickles.Prove.Step
  ( StepBranchData
  , StepAdvice
  , StepProverT(..)
  , runStepProverT
  , BuildStepAdviceInput
  , buildStepAdvice
  , BuildStepAdviceWithOraclesInput
  , buildStepAdviceWithOracles
  , extractWrapVKCommsAdvice
  , extractWrapVKForStepHash
  , dummyWrapTockPublicInput
  , StepRule
  , StepProveContext
  , StepCompileResult
  , StepProveResult
  , stepCompile
  , stepSolveAndProve
  , stepProve
  -- Parallel v2 stack: spec-indexed per-slot carrier + accompanying
  -- StepSlotsM instance. Sits alongside the v1 stack so callers can
  -- migrate one at a time.
  , StepAdvice2(..)
  , StepProverT2(..)
  , runStepProverT2
  , buildStepAdvice2
  , buildStepAdviceWithOracles2
  , stepCompile2
  , stepSolveAndProve2
  , stepProve2
  ) where

import Prelude

import Control.Monad.Reader (ReaderT, ask, runReaderT)
import Data.Array (concatMap)
import Data.Array as Array
import Data.Either (Either(..))
import Data.Fin (Finite, getFinite, unsafeFinite)
import Data.Foldable (for_)
import Data.FoldableWithIndex (forWithIndex_)
import Data.Map (Map)
import Data.Maybe (fromJust)
import Data.Newtype (class Newtype, un, unwrap)
import Data.Reflectable (class Reflectable, reflectType)
import Data.Tuple (Tuple(..))
import Data.Vector (Vector, (:<))
import Data.Vector as Vector
import Effect (Effect)
import Effect.Exception (Error, error)
import Effect.Unsafe (unsafePerformEffect)
import Node.Encoding (Encoding(..))
import Node.FS.Sync as FS
import Partial.Unsafe (unsafeCrashWith, unsafePartial)
import Pickles.Dummy (dummyIpaChallenges, roComputeResult, simpleChainStepDummyFopProofState, stepDummyFopProofState, wrapDummyUnfinalizedProof)
import Pickles.Linearization (pallas, vesta) as Linearization
import Pickles.Linearization.FFI (PointEval) as LFFI
import Pickles.Linearization.FFI (domainGenerator, domainShifts)
import Pickles.PlonkChecks (AllEvals)
import Pickles.ProofFFI (OraclesResult) as ProofFFI
import Pickles.ProofFFI (Proof, pallasCreateProofWithPrev, permutationVanishingPolynomial, proofCoefficientEvals, proofIndexEvals, proofSigmaEvals, proofWitnessEvals, proofZEvals, vestaProofCommitments, vestaProofOpeningDelta, vestaProofOpeningLr, vestaProofOpeningPrechallenges, vestaProofOpeningZ1, vestaProofOpeningZ2, vestaProofOracles, vestaSigmaCommLast, vestaVerifierIndexColumnComms, vestaVerifierIndexDigest)
import Pickles.ProofWitness (ProofWitness)
import Pickles.Prove.Pure.Step (ExpandProofInput, ExpandProofOutput, expandProof) as PureStep
import Pickles.Step.Advice (class StepSlotsM, class StepWitnessM)
import Pickles.Step.Prevs (class PrevsCarrier, StepSlot(..), replicatePrevsCarrier)
import Pickles.Step.Main (RuleOutput, StepMainSrsData, stepMain, stepMain2)
import Pickles.Step.MessageHash (hashMessagesForNextStepProofPure, hashMessagesForNextStepProofPureTraced)
import Pickles.Trace as Trace
import Pickles.Types (BranchData(..), FopProofState(..), PaddedLength, PerProofUnfinalized(..), PointEval(..), StepAllEvals(..), StepField, StepIPARounds, StepPerProofWitness(..), StepProofState(..), VerificationKey(..), WrapField, WrapIPARounds, WrapProof(..), WrapProofMessages(..), WrapProofOpening(..))
import Pickles.VerificationKey (StepVK)
import Pickles.Verify.Types (BranchData) as VT
import Pickles.Verify.Types (PlonkMinimal, UnfinalizedProof)
import Pickles.Wrap.MessageHash (hashMessagesForNextWrapProofPureGeneral)
import Prim.Int (class Add, class Mul)
import Safe.Coerce (coerce)
import Snarky.Backend.Builder (CircuitBuilderState, Labeled)
import Snarky.Backend.Compile (SolverT, compile, makeSolver', runSolverT)
import Snarky.Backend.Kimchi (makeConstraintSystemWithPrevChallenges, makeWitness)
import Snarky.Backend.Kimchi.Class (class CircuitGateConstructor, createProverIndex, createVerifierIndex, verifyProverIndex)
import Snarky.Backend.Kimchi.Types (CRS, ConstraintSystem, ProverIndex, VerifierIndex)
import Snarky.Backend.Prover (emptyProverState)
import Snarky.Circuit.CVar (Variable)
import Snarky.Circuit.DSL (class CircuitM, BoolVar, F(..), FVar, SizedF, Snarky, UnChecked(..), coerceViaBits)
import Snarky.Circuit.DSL.Monad (class CheckedType)
import Snarky.Circuit.DSL.SizedF (toField, unwrapF, wrapF) as SizedF
import Snarky.Circuit.Types (class CircuitType, valueToFields)
import Snarky.Circuit.Kimchi (toFieldPure)
import Snarky.Constraint.Kimchi (KimchiConstraint, KimchiGate)
import Snarky.Constraint.Kimchi as Kimchi
import Snarky.Constraint.Kimchi.Types (AuxState(..), KimchiRow, toKimchiRows)
import Snarky.Curves.Class (EndoBase(..), EndoScalar(..), endoBase, endoScalar)
import Snarky.Curves.Class (fromBigInt, fromInt, generator, toAffine, toBigInt) as Curves
import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Pasta (PallasG, VestaG)
import Snarky.Data.EllipticCurve (AffinePoint, WeierstrassAffinePoint(..))
import Snarky.Types.Shifted (SplitField, Type1(..), Type2(..), fromShifted, toShifted)
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

-- | Private witness data the step prover supplies to `stepMain`. One
-- | field per `Req.*` request, in the same order `step_main.ml`
-- | consumes them. The field set mirrors the raw `StepWitnessM`
-- | accessors; the composed helpers (`getStepPerProofWitnesses` etc.)
-- | are derived in the `StepWitnessM` instance below.
-- |
-- | Type parameters mirror `StepWitnessM`:
-- |
-- | * `n`   — max_proofs_verified (varies per compile: N0, N1, or N2).
-- | * `ds`  — step IPA rounds (= `StepIPARounds` for production pickles).
-- | * `dw`  — wrap IPA rounds (= `WrapIPARounds` for production pickles).
-- |
-- | The commitment curve is pinned to `PallasG` (the wrap proof's
-- | commitment curve) and the field to `StepField` (= `Vesta.ScalarField`
-- | = `Pallas.BaseField`) — both are structural for any step circuit
-- | in the Pasta cycle.
type StepAdvice (n :: Int) (ds :: Int) (dw :: Int) inputVal =
  { evals :: Vector n (ProofWitness (F StepField))
  , prevChallenges :: Vector n (Vector ds (F StepField))
  , messages ::
      Vector n
        { wComm :: Vector 15 (AffinePoint (F StepField))
        , zComm :: AffinePoint (F StepField)
        , tComm :: Vector 7 (AffinePoint (F StepField))
        }
  , openingProofs ::
      Vector n
        { delta :: AffinePoint (F StepField)
        , sg :: AffinePoint (F StepField)
        , lr :: Vector dw { l :: AffinePoint (F StepField), r :: AffinePoint (F StepField) }
        , z1 :: Type2 (SplitField (F StepField) Boolean)
        , z2 :: Type2 (SplitField (F StepField) Boolean)
        }
  , fopProofStates ::
      Vector n (UnfinalizedProof ds (F StepField) (Type1 (F StepField)) Boolean)
  , messagesForNextWrapProof :: Vector n (F StepField)
  , wrapVerifierIndex ::
      VerificationKey (WeierstrassAffinePoint PallasG (F StepField))
  , sgOld :: Vector n (AffinePoint (F StepField))
  , publicInput :: inputVal
  , publicUnfinalizedProofs ::
      Vector n
        ( PerProofUnfinalized
            dw
            (Type2 (SplitField (F StepField) Boolean))
            (F StepField)
            Boolean
        )
  -- | One per prev-proof slot. OCaml reads this from `step_domains`
  -- | + the active branch's proofs-verified mask; here we receive it
  -- | pre-computed so the advice stays purely data.
  , branchData :: Vector n StepBranchData
  -- | Kimchi-level `prev_challenges` threaded to
  -- | `ProverProof::create_recursive`. This is the SAME-CURVE recursion
  -- | data (prior Vesta step proof's IPA sg + expanded challenges),
  -- | NOT the cross-curve wrap data that the step circuit verifies.
  -- | One entry per prev proof (= `n` = max_proofs_verified at the
  -- | kimchi layer); each entry holds a full `StepIPARounds`-length
  -- | expanded challenge vector. Converted to `Array` only at the FFI
  -- | boundary in `stepSolveAndProve`.
  , kimchiPrevChallenges ::
      Vector n
        { sgX :: WrapField
        , sgY :: WrapField
        , challenges :: Vector ds StepField
        }
  }

--------------------------------------------------------------------------------
-- ReaderT + StepWitnessM instance
--------------------------------------------------------------------------------

-- | ReaderT transformer carrying a `StepAdvice` over a base monad.
newtype StepProverT
  :: Int
  -> Int
  -> Int
  -> Type
  -> (Type -> Type)
  -> Type
  -> Type
newtype StepProverT n ds dw inputVal m a =
  StepProverT (ReaderT (StepAdvice n ds dw inputVal) m a)

derive instance Newtype (StepProverT n ds dw inputVal m a) _
derive newtype instance Functor m => Functor (StepProverT n ds dw inputVal m)
derive newtype instance Apply m => Apply (StepProverT n ds dw inputVal m)
derive newtype instance Applicative m => Applicative (StepProverT n ds dw inputVal m)
derive newtype instance Bind m => Bind (StepProverT n ds dw inputVal m)
derive newtype instance Monad m => Monad (StepProverT n ds dw inputVal m)

-- | Supply the advice record and run the prover computation in the
-- | base monad.
runStepProverT
  :: forall n ds dw inputVal m a
   . StepAdvice n ds dw inputVal
  -> StepProverT n ds dw inputVal m a
  -> m a
runStepProverT advice (StepProverT m) = runReaderT m advice

-- | `StepWitnessM` instance. Raw getters are plain record projections
-- | via `ask`; `getStepPerProofWitnesses` composes the wire-format
-- | `StepPerProofWitness` from several raw fields, matching
-- | `step_main.ml`'s per-slot advice layout.
-- |
-- | Polymorphic in `ds`/`dw` (the IPA-round counts); the caller's
-- | choice gets unified with the stepMain constraint
-- | (`StepWitnessM n StepIPARounds WrapIPARounds PallasG StepField m`)
-- | at the `stepProve` call site via ordinary type inference, so
-- | `Pickles.Prove.Step` itself never writes `StepIPARounds` /
-- | `WrapIPARounds` literally.
instance
  ( Monad m
  , Reflectable n Int
  ) =>
  StepWitnessM
    n
    ds
    dw
    PallasG
    StepField
    (StepProverT n ds dw inputVal m)
    inputVal where

  getProofWitnesses _ = StepProverT $ map _.evals ask
  getPrevChallenges _ = StepProverT $ map _.prevChallenges ask
  getMessages _ = StepProverT $ map _.messages ask
  getOpeningProof _ = StepProverT $ map _.openingProofs ask
  getFopProofStates _ = StepProverT $ map _.fopProofStates ask
  getMessagesForNextWrapProof _ = StepProverT $ map _.messagesForNextWrapProof ask
  getWrapVerifierIndex _ = StepProverT $ map _.wrapVerifierIndex ask
  getSgOld _ = StepProverT $ map _.sgOld ask
  getStepPublicInput _ = StepProverT $ map _.publicInput ask
  getStepUnfinalizedProofs _ = StepProverT $ map _.publicUnfinalizedProofs ask
  getStepPerProofWitnesses _ = StepProverT $ do
    adv <- ask
    pure $ Vector.generate \i ->
      let
        pw = Vector.index adv.evals i
        fop = Vector.index adv.fopProofStates i
        opening = Vector.index adv.openingProofs i
        msgs = Vector.index adv.messages i
        bd = Vector.index adv.branchData i
        dv = fop.deferredValues
        p = dv.plonk
      in
        StepPerProofWitness
          { wrapProof: WrapProof
              { opening: WrapProofOpening
                  { lr: map (\r -> { l: WeierstrassAffinePoint r.l, r: WeierstrassAffinePoint r.r }) opening.lr
                  , z1: opening.z1
                  , z2: opening.z2
                  , delta: WeierstrassAffinePoint opening.delta
                  , sg: WeierstrassAffinePoint opening.sg
                  }
              , messages: WrapProofMessages
                  { wComm: map WeierstrassAffinePoint msgs.wComm
                  , zComm: WeierstrassAffinePoint msgs.zComm
                  , tComm: map WeierstrassAffinePoint msgs.tComm
                  }
              }
          , proofState: StepProofState
              -- The 5 fp slots store the **shifted inner** form of each
              -- `Type1 (F StepField)` advice value, matching OCaml's
              -- `Per_proof_witness.proof_state.deferred_values.plonk` at
              -- the var level (`field_var Shifted_value.Type1.t` with
              -- `field_var = Impls.Step.Field.t`). PS's
              -- `fopShiftOps.unshift = fromShiftedType1Circuit` then
              -- reconstructs `2*t + c` from this stored form when FOP
              -- needs the unshifted value, and `scalarMulLeaf` feeds
              -- the stored form directly to `scaleFast2'` (which has
              -- Type2-ish internal semantics `[s + 2^n] * g`) to match
              -- OCaml's MSM input at `step_verifier.ml:1260-1264`.
              -- A prior `fromShifted` call here was silently unshifting
              -- the value, which was latent because FOP's assertions
              -- are gated on `proof_must_verify` (bypassed for the
              -- base case) but surfaced at the unconditional
              -- `ivp_assert_plonk_beta` assertion.
              { fopState: FopProofState
                  { combinedInnerProduct: unwrap dv.combinedInnerProduct
                  , b: unwrap dv.b
                  , zetaToSrsLength: unwrap p.zetaToSrsLength
                  , zetaToDomainSize: unwrap p.zetaToDomainSize
                  , perm: unwrap p.perm
                  , spongeDigest: fop.spongeDigestBeforeEvaluations
                  , beta: UnChecked p.beta
                  , gamma: UnChecked p.gamma
                  , alpha: UnChecked p.alpha
                  , zeta: UnChecked p.zeta
                  , xi: UnChecked dv.xi
                  , bulletproofChallenges: map UnChecked dv.bulletproofChallenges
                  }
              , branchData: BranchData
                  { domainLog2: bd.domainLog2
                  , mask0: bd.mask0
                  , mask1: bd.mask1
                  }
              }
          , prevEvals: StepAllEvals
              { publicEvals: PointEval pw.allEvals.publicEvals
              , witnessEvals: map PointEval pw.allEvals.witnessEvals
              , coeffEvals: map PointEval pw.allEvals.coeffEvals
              , zEvals: PointEval pw.allEvals.zEvals
              , sigmaEvals: map PointEval pw.allEvals.sigmaEvals
              , indexEvals: map PointEval pw.allEvals.indexEvals
              , ftEval1: pw.allEvals.ftEval1
              }
          , prevChallenges: map UnChecked adv.prevChallenges
          , prevSgs: map WeierstrassAffinePoint adv.sgOld
          }

--------------------------------------------------------------------------------
-- Base-case advice builder
--
-- `buildStepAdvice` assembles a fully-populated `StepAdvice` from the
-- few parameters a specific inductive rule's BASE case actually picks
-- (appState, stepDomainLog2, mostRecentWidth). Every other field is
-- filled from the Ro-derived dummies in `Pickles.Dummy`, which are
-- hardcoded at the Pasta protocol constants `Tick.Rounds.n = 16`
-- and `Tock.Rounds.n = 15` — matching OCaml `dummy.ml:27-55` exactly.
--
-- Polymorphic in `n` (the step circuit's max_proofs_verified): the
-- per-slot fields are `Vector.replicate`d to the caller's choice of
-- `n`. The output type pins `ds` and `dw` at `StepIPARounds` /
-- `WrapIPARounds` because the underlying Pickles.Dummy helpers are
-- concretized there (see the module note above). Upstream
-- `stepMain`'s `StepWitnessM n StepIPARounds WrapIPARounds ...`
-- constraint lines up with this output type via type inference, so
-- the call site (e.g. SimpleChain.purs) never has to write the
-- round-count constants literally.
--
-- References:
--   OCaml `Proof.dummy h most_recent_width ~domain_log2` (proof.ml:115-208)
--   OCaml `step_main.ml:368-376` exists calls for Req.App_state,
--                                  Req.Unfinalized_proofs, Req.Wrap_index
--------------------------------------------------------------------------------

-- | Inputs `buildStepAdvice` needs from the caller. Everything else
-- | is protocol-constant dummy data derived from `Pickles.Dummy`.
type BuildStepAdviceInput inputVal =
  { -- | Value bound to the step circuit's public input (OCaml
    -- | `Req.App_state`). Polymorphic in `inputVal` so rules with
    -- | Input-mode typ other than `Field.typ` can bind multi-field
    -- | records. For Simple_chain base case this is `F zero` (self = 0).
    publicInput :: inputVal

  -- | `most_recent_width` parameter the OCaml `Proof.dummy` call
  -- | would pass. For Simple_chain at N1 this is 1. Drives the
  -- | wrap-domain choice for `stepDummyFopProofState` via
  -- | `common.ml:25-29 wrap_domains` (0 → 13, 1 → 14, 2 → 15).
  , mostRecentWidth :: Int

  -- | OCaml `Pickles.Proof.dummy`'s `~domain_log2` parameter. This is
  -- | the dummy wrap proof's evaluation domain, which becomes
  -- | `branch_data.domain_log2` inside its statement (see
  -- | `proof.ml:140-141`), and must equal the step circuit's FOP
  -- | `params.domainLog2` (= `wrap_domains.h` from `common.ml:25-29`).
  -- | For Simple_chain N1 this is 14. NOTE: This is NOT the step
  -- | circuit's own kimchi domain (= 16 per
  -- | `dump_circuit_impl.ml:3721-3723`); that value is determined by
  -- | kimchi at proof-creation time, not read from advice.
  , wrapDomainLog2 :: Int
  }

-- | Build a base-case `StepAdvice n` populated from Ro-derived
-- | dummies. Every per-slot field is replicated `n` times; for a
-- | single real slot the caller receives n=1 and all slots collapse
-- | to one entry. For multi-slot compiles (n > 1) the same dummy
-- | values are reused across slots — OCaml does the equivalent via
-- | `Vector.init Max_proofs_verified.n` in `step.ml:704-735`.
buildStepAdvice
  :: forall @n inputVal
   . Reflectable n Int
  => BuildStepAdviceInput inputVal
  -> StepAdvice n StepIPARounds WrapIPARounds inputVal
buildStepAdvice input =
  let
    -- Pallas generator (= OCaml `Tock.Curve.one`). Reused for every
    -- curve-point field in the base-case dummy advice.
    g0 :: AffinePoint (F StepField)
    g0 = coerce
      ( unsafePartial fromJust $ Curves.toAffine (Curves.generator :: Pallas.G)
          :: AffinePoint StepField
      )

    g0w :: WeierstrassAffinePoint PallasG (F StepField)
    g0w = WeierstrassAffinePoint g0

    -- Ro-derived constants shared across all fields.
    r = roComputeResult

    -- z1 / z2 from OCaml `proof.ml:dummy` openings (Ro.tock values
    -- re-wrapped as cross-field Type2 SplitField in the step field).
    z1 :: Type2 (SplitField (F StepField) Boolean)
    z1 = toShifted (F r.proofZ1)

    z2 :: Type2 (SplitField (F StepField) Boolean)
    z2 = toShifted (F r.proofZ2)

    -- Ro-derived AllEvals (matches OCaml `Dummy.evals` at
    -- `dummy.ml:7-20`). Each bare StepField wrapped in F.
    -- NB: the `PointEval` here is the raw record from
    -- `Pickles.Linearization.FFI` (imported as `LFFI.PointEval`), NOT
    -- the `Pickles.Types.PointEval` newtype — they share the name but
    -- the record-based one is what `Pickles.PlonkChecks.AllEvals`
    -- uses internally.
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

    dummyProofWitness :: ProofWitness (F StepField)
    dummyProofWitness = { allEvals: wrapAE r.stepDummyPrevEvals }

    -- Ro-derived FOP proof state for the dummy wrap proof.
    dummyFopProofState
      :: UnfinalizedProof StepIPARounds (F StepField) (Type1 (F StepField)) Boolean
    dummyFopProofState = stepDummyFopProofState
      { proofsVerified: input.mostRecentWidth }

    -- Cross-field conversion of `wrapDummyUnfinalizedProof` (which
    -- is in wrap-field `Type2 (F WrapField)`) to the step-field
    -- `Type2 (SplitField (F StepField) Boolean)` that step_main's
    -- `publicInputCommit` walks over. Same two-step bridge the old
    -- `dummyStepAdvice` used in Pickles.Dummy before its deletion.
    du = wrapDummyUnfinalizedProof

    t2toT2sf :: Type2 (F WrapField) -> Type2 (SplitField (F StepField) Boolean)
    t2toT2sf t = toShifted (fromShifted t :: F WrapField)

    chalToStep :: SizedF 128 (F WrapField) -> SizedF 128 (F StepField)
    chalToStep s = SizedF.wrapF (coerceViaBits (SizedF.unwrapF s))

    digestStep :: F StepField
    digestStep =
      let
        F digestWrap = du.spongeDigestBeforeEvaluations
      in
        F (Curves.fromBigInt (Curves.toBigInt digestWrap) :: StepField)

    dv = du.deferredValues
    p = dv.plonk

    dummyPublicUnfinalized
      :: PerProofUnfinalized
           WrapIPARounds
           (Type2 (SplitField (F StepField) Boolean))
           (F StepField)
           Boolean
    dummyPublicUnfinalized = PerProofUnfinalized
      { combinedInnerProduct: t2toT2sf dv.combinedInnerProduct
      , b: t2toT2sf dv.b
      , zetaToSrsLength: t2toT2sf p.zetaToSrsLength
      , zetaToDomainSize: t2toT2sf p.zetaToDomainSize
      , perm: t2toT2sf p.perm
      , spongeDigest: digestStep
      , beta: UnChecked (chalToStep p.beta)
      , gamma: UnChecked (chalToStep p.gamma)
      , alpha: UnChecked (chalToStep p.alpha)
      , zeta: UnChecked (chalToStep p.zeta)
      , xi: UnChecked (chalToStep dv.xi)
      , bulletproofChallenges: map (UnChecked <<< chalToStep) dv.bulletproofChallenges
      , shouldFinalize: false
      }

    -- Per-slot branch data. All slots get the same entry for the
    -- base case (single-rule compile). `domainLog2` is the wrap
    -- proof's evaluation domain (OCaml `Proof.dummy`'s
    -- `~domain_log2` parameter, stored in the dummy proof's
    -- statement at `proof.ml:140-141`). mask0/mask1 encode which
    -- prev-proof slot is the active one — for Simple_chain at N1
    -- the single slot is `mask1 = true, mask0 = false`.
    dummyBranch :: StepBranchData
    dummyBranch =
      { domainLog2: F (Curves.fromInt input.wrapDomainLog2 :: StepField)
      , mask0: false
      , mask1: true
      }
  in
    { evals: Vector.replicate dummyProofWitness
    , prevChallenges: Vector.replicate (map F dummyIpaChallenges.stepExpanded)
    , messages: Vector.replicate
        { wComm: Vector.generate (\_ -> g0)
        , zComm: g0
        , tComm: Vector.generate (\_ -> g0)
        }
    , openingProofs: Vector.replicate
        { delta: g0
        , sg: g0
        , lr: Vector.generate (\_ -> { l: g0, r: g0 })
        , z1
        , z2
        }
    , fopProofStates: Vector.replicate dummyFopProofState
    , messagesForNextWrapProof: Vector.replicate (F zero)
    , wrapVerifierIndex:
        VerificationKey
          { sigma: Vector.generate (const g0w)
          , coeff: Vector.generate (const g0w)
          , index: Vector.generate (const g0w)
          }
    , sgOld: Vector.replicate g0
    , publicInput: input.publicInput
    , publicUnfinalizedProofs: Vector.replicate dummyPublicUnfinalized
    , branchData: Vector.replicate dummyBranch
    , kimchiPrevChallenges:
        Vector.replicate
          { sgX: zero
          , sgY: zero
          , challenges: Vector.replicate zero
          }
    }

--------------------------------------------------------------------------------
-- V2 base-case advice builder (spec-indexed per-slot carrier)
--
-- `buildStepAdvice2` mirrors `buildStepAdvice`'s base-case construction
-- but outputs a `StepAdvice2` keyed on a `prevsSpec` type-level list of
-- per-slot max_proofs_verified values. Handles homogeneous specs
-- (Simple_chain N1/N2, Add_one_return) directly via
-- `replicatePrevsCarrier` — the rank-2 `dummySlot` uses `Vector.replicate`
-- for the two n-dependent SPPW fields (`prevChallenges`, `prevSgs`), so
-- each slot's `n_i` auto-specializes. For genuinely heterogeneous specs
-- (e.g. Tree_proof_return's `[N0; N2]`) the same helper still works
-- because `Vector.replicate` at n=0 produces nil correctly.
--
-- Everything else (non-n-dependent fields and the uniform `Vector len`
-- fields like `publicUnfinalizedProofs`, `messagesForNextWrapProof`,
-- `kimchiPrevChallenges`) is constructed exactly as v1 does.
--------------------------------------------------------------------------------

-- | V2 variant of `buildStepAdvice`. Produces a `StepAdvice2` keyed on
-- | a spec-indexed per-slot carrier.
-- |
-- | Requires a `PrevsCarrier prevsSpec … len carrier` instance so the
-- | caller's `prevsSpec` determines `len` (= number of prev slots) and
-- | `carrier` (= nested-tuple carrier type). The rank-2 `dummySlot`
-- | builds each slot's `StepPerProofWitness` with the correct per-slot
-- | `n_i` via `Vector.replicate`.
buildStepAdvice2
  :: forall @prevsSpec inputVal len carrier
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
  => BuildStepAdviceInput inputVal
  -> StepAdvice2 prevsSpec StepIPARounds WrapIPARounds inputVal len carrier
buildStepAdvice2 input =
  let
    -- Reuse every non-carrier field from v1's base-case builder.
    -- `len` here plays the role of v1's `n` (top-level max_proofs_verified).
    v1 :: StepAdvice len StepIPARounds WrapIPARounds inputVal
    v1 = buildStepAdvice @len input

    -- Pallas generator, same as v1.
    g0 :: AffinePoint (F StepField)
    g0 = coerce
      ( unsafePartial fromJust $ Curves.toAffine (Curves.generator :: Pallas.G)
          :: AffinePoint StepField
      )

    r = roComputeResult

    z1 :: Type2 (SplitField (F StepField) Boolean)
    z1 = toShifted (F r.proofZ1)

    z2 :: Type2 (SplitField (F StepField) Boolean)
    z2 = toShifted (F r.proofZ2)

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
        aeF = wrapAE r.stepDummyPrevEvals
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
    dummyFop = stepDummyFopProofState
      { proofsVerified: input.mostRecentWidth }

    dummyBranch :: StepBranchData
    dummyBranch =
      { domainLog2: F (Curves.fromInt input.wrapDomainLog2 :: StepField)
      , mask0: false
      , mask1: true
      }

    dvFop = dummyFop.deferredValues
    pFop = dvFop.plonk

    -- Rank-2 per-slot dummy: the only n-dependent fields (`prevChallenges`,
    -- `prevSgs`) use `Vector.replicate` so they specialize per slot.
    -- All other fields are slot-agnostic and reused verbatim.
    --
    -- NB: the `UnChecked <$>` on `bulletproofChallenges` etc. matches
    -- OCaml's in-circuit wrapping (see `fopStateDummy` construction
    -- inside `v1`).
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
    StepAdvice2
      { perProofSlotsCarrier: replicatePrevsCarrier @prevsSpec dummySlot
      , publicInput: v1.publicInput
      , publicUnfinalizedProofs: v1.publicUnfinalizedProofs
      , messagesForNextWrapProof: v1.messagesForNextWrapProof
      , wrapVerifierIndex: v1.wrapVerifierIndex
      , kimchiPrevChallenges: v1.kimchiPrevChallenges
      }

--------------------------------------------------------------------------------
-- Real wrap VK advice builder
--
-- `buildStepAdviceWithOracles` mirrors `buildStepAdvice` but populates
-- two things with real oracle output over a compiled Simple_chain wrap
-- VK + `Proof.dummy`:
--
-- 1. `advice.wrapVerifierIndex` — the lightweight
--    `Pickles.Types.VerificationKey` shape (sigma/coeff/index point
--    triples) cross-extracted from the compiled wrap `VerifierIndex
--    PallasG WrapField`. The step circuit's
--    `hashMessagesForNextStepProofOpt` sponge absorbs the VK points;
--    their byte-level identity to OCaml is what makes the Fq sponge
--    squeeze match.
-- 2. `advice.publicUnfinalizedProofs[0].plonk.{alpha,beta,gamma,zeta}`
--    and `.spongeDigest` — the outputs of
--    `vestaProofOracles realWrapVK dummyWrapProof dummyWrapTockPublicInput`
--    cross-field-coerced to the step field. The step circuit's IVP
--    sponge squeeze must equal these (asserted at
--    `ivp_assert_plonk_{beta,gamma,alpha,zeta}`).
--
-- All other fields come from `buildStepAdvice` unchanged — Ro-derived
-- dummies. The Ro-derived plonk values still live in
-- `fopProofStates[i].deferredValues.plonk` (step-field Type1 — what the
-- wrap statement's own `plonk0` field carries) and in the input to the
-- Type2 cross-field `publicUnfinalizedProofs` packaging. Only the four
-- oracle-derived overrides differ from the base builder.
--
-- Reference: mina/src/lib/crypto/pickles/step.ml:298-343
--   (Tock.Oracles.create ... public_input proof) then writing
--   plonk0 := {alpha = scalar_chal O.alpha; beta = O.beta; gamma = O.gamma;
--              zeta = scalar_chal O.zeta}
--   into the advice consumed by step_main.
--------------------------------------------------------------------------------

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
    raw :: Array (AffinePoint StepField)
    raw = vestaVerifierIndexColumnComms vk

    idx6 :: Vector 6 (AffinePoint StepField)
    idx6 = unsafePartial $ fromJust $ Vector.toVector @6 $ Array.take 6 raw

    coeff15 :: Vector 15 (AffinePoint StepField)
    coeff15 = unsafePartial $ fromJust $ Vector.toVector @15
      $ Array.take 15
      $ Array.drop 6 raw

    sig6 :: Vector 6 (AffinePoint StepField)
    sig6 = unsafePartial $ fromJust $ Vector.toVector @6 $ Array.drop 21 raw

    sigLast :: AffinePoint StepField
    sigLast = vestaSigmaCommLast vk

    sigma7 :: Vector 7 (AffinePoint StepField)
    sigma7 = Vector.snoc sig6 sigLast

    wrapPt :: AffinePoint StepField -> WeierstrassAffinePoint PallasG (F StepField)
    wrapPt pt = WeierstrassAffinePoint { x: F pt.x, y: F pt.y }
  in
    VerificationKey
      { sigma: map wrapPt sigma7
      , coeff: map wrapPt coeff15
      , index: map wrapPt idx6
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
    raw :: Array (AffinePoint StepField)
    raw = vestaVerifierIndexColumnComms vk

    idx6 :: Vector 6 (AffinePoint StepField)
    idx6 = unsafePartial $ fromJust $ Vector.toVector @6 $ Array.take 6 raw

    coeff15 :: Vector 15 (AffinePoint StepField)
    coeff15 = unsafePartial $ fromJust $ Vector.toVector @15
      $ Array.take 15
      $ Array.drop 6 raw

    sig6 :: Vector 6 (AffinePoint StepField)
    sig6 = unsafePartial $ fromJust $ Vector.toVector @6 $ Array.drop 21 raw

    sigLast :: AffinePoint StepField
    sigLast = vestaSigmaCommLast vk
  in
    { sigmaComm: Vector.snoc sig6 sigLast
    , coefficientsComm: coeff15
    , genericComm: Vector.index idx6 (unsafeFinite @6 0)
    , psmComm: Vector.index idx6 (unsafeFinite @6 1)
    , completeAddComm: Vector.index idx6 (unsafeFinite @6 2)
    , mulComm: Vector.index idx6 (unsafeFinite @6 3)
    , emulComm: Vector.index idx6 (unsafeFinite @6 4)
    , endomulScalarComm: Vector.index idx6 (unsafeFinite @6 5)
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
  :: forall inputVal input
   . CircuitType StepField inputVal input
  => { mostRecentWidth :: Int
     , wrapDomainLog2 :: Int
     , wrapVK :: VerifierIndex PallasG WrapField
     , prevPublicInput :: inputVal
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
     }
  -> Array WrapField
dummyWrapTockPublicInput input =
  let
    -- Simple_chain base case: source plonk0 + prev_evals from the
    -- hardcoded fixture so the values match what OCaml observes at
    -- the same point in the pipeline (post Pickles.compile). The
    -- legacy `stepDummyFopProofState` would pick up module-init-time
    -- Ro values instead. See `Pickles.Dummy.SimpleChain`.
    fop :: UnfinalizedProof StepIPARounds (F StepField) (Type1 (F StepField)) Boolean
    fop = simpleChainStepDummyFopProofState { proofsVerified: input.mostRecentWidth }

    dv = fop.deferredValues
    p = dv.plonk

    -- Bit-level coerce of a step-field scalar into the wrap field.
    -- Step field fits in wrap field bits (Fp fits bits of Fq) so no
    -- truncation — just reinterpret the integer representation.
    stepToWrap :: F StepField -> WrapField
    stepToWrap (F x) = Curves.fromBigInt (Curves.toBigInt x)

    -- Type1 (F StepField) → WrapField by taking the STORED (shifted)
    -- inner value and coercing its bit representation. OCaml's
    -- `Wrap.Statement.In_circuit.to_data` places the stored `t` from
    -- `Shifted_value.Type1.Shifted_value t` into the tock public
    -- input — NOT the unshifted original. Matching that requires
    -- reaching through the Type1 newtype directly (equivalent to
    -- OCaml's `let (Shifted_value t) = cip in t`).
    type1StepBits :: Type1 (F StepField) -> WrapField
    type1StepBits (Type1 x) = stepToWrap x

    -- SizedF 128 (F StepField) → WrapField via bit coerce. Uses
    -- the `UnChecked`-style inner newtype access through `SizedF.toField`
    -- conversion (step → raw, raw → wrap via BigInt round-trip).
    sizedStepBits :: SizedF 128 (F StepField) -> WrapField
    sizedStepBits s =
      let
        F x = SizedF.toField s
      in
        Curves.fromBigInt (Curves.toBigInt x)

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

    prevProofs :: Vector 1 { sg :: AffinePoint StepField, expandedBpChallenges :: Vector StepIPARounds StepField }
    prevProofs =
      { sg: input.wrapSg, expandedBpChallenges: stepExpanded } :< Vector.nil

    msgStepDigestStepField :: StepField
    msgStepDigestStepField = hashMessagesForNextStepProofPure
      { stepVk: wrapVkStep
      , appState: valueToFields @StepField @inputVal input.prevPublicInput
      , proofs: prevProofs
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
      , Curves.fromBigInt (Curves.toBigInt msgStepDigestStepField)
      ]

    -- StepIPARounds bulletproof challenges.
    bpChals :: Array WrapField
    bpChals = map sizedStepBits (Vector.toUnfoldable dv.bulletproofChallenges)

    -- Packed branch_data:
    --   4 * domainLog2 + mask0 + 2 * mask1
    -- In the step circuit `packStatement` this is computed in step
    -- field and absorbed as a `SizedF 10` value (10 bits are enough
    -- for domainLog2 ∈ [0,15], mask bits). We emit it as the plain
    -- wrap-field integer 4 * domainLog2 + 0 + 2 * 1 (Simple_chain
    -- base case has proofsVerifiedMask = [false, true]).
    packedBranchData :: WrapField
    packedBranchData =
      Curves.fromInt (4 * input.wrapDomainLog2 + 2)

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
type BuildStepAdviceWithOraclesInput inputVal =
  { publicInput :: inputVal
  , prevPublicInput :: inputVal
  , mostRecentWidth :: Int
  , wrapDomainLog2 :: Int
  , wrapVK :: VerifierIndex PallasG WrapField
  -- | Previous wrap proof's sg (Pallas point, Fp coords = StepField).
  -- | Base case: `Dummy.Ipa.Wrap.sg`. Inductive: real wrap proof's sg.
  , wrapSg :: AffinePoint StepField
  -- | Previous step proof's sg (Vesta point, Fq coords = WrapField).
  -- | Base case: `Dummy.Ipa.Step.sg`. Inductive: real step proof's
  -- | opening sg from the prior iteration.
  , stepSg :: AffinePoint WrapField
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
  -- | Each entry holds sg + expanded bp challenges. Base case: both entries
  -- | are `(Dummy.Ipa.Wrap.sg, dummyIpaChallenges.wrapExpanded)`.
  -- | Inductive: front-padded with dummy, real entry at the end.
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
  -- | Expanded step-field bp challenges that feed `messagesForNextStepProof`
  -- | hash AND `stepPrevChallenges` in `expandProofInputRec`. Per OCaml step.ml:
  -- | 519-525 this is
  -- |   `Vector.map Ipa.Step.compute_challenges
  -- |      t.statement.messages_for_next_step_proof.old_bulletproof_challenges`
  -- | where `t` = prev wrap proof. Values chain through `messages_for_next_step_proof`
  -- | forwarding; at step_bN they reference step_b{N-2}'s deferred.bp_chals.
  -- |
  -- | b0/b1: Simple_chain N1's chain has step_b{-1}=dummy and step_b0.output
  -- |   old_bp_chals = dummy bp_chals (from dummy wrap's deferred). So use
  -- |   `Dummy.dummyIpaChallenges.stepExpanded`.
  -- | b2: prev = wrap_b1, forwarded from step_b1's output old_bp_chals =
  -- |   wrap_b0.deferred.bp_chals = wrapDv.bulletproofPrechallenges. Expand via
  -- |   `stepEndoScalar :: StepField`.
  , prevChallengesForStepHash :: Vector StepIPARounds StepField
  }

-- | Build a `StepAdvice n StepIPARounds WrapIPARounds` from a previous
-- | wrap proof (dummy for base case, real for inductive). Runs
-- | `vestaProofOracles` on `input.wrapProof` + `input.wrapPublicInput`,
-- | then feeds the result through `expandProof` to compute the full
-- | advice record.
buildStepAdviceWithOracles
  :: forall @n @inputVal @input
   . Reflectable n Int
  => CircuitType StepField inputVal input
  => BuildStepAdviceWithOraclesInput inputVal
  -> Effect
       { advice :: StepAdvice n StepIPARounds WrapIPARounds inputVal
       , challengePolynomialCommitment :: AffinePoint StepField
       }
buildStepAdviceWithOracles input = do
  let
    base :: StepAdvice n StepIPARounds WrapIPARounds inputVal
    base = buildStepAdvice
      { publicInput: input.publicInput
      , mostRecentWidth: input.mostRecentWidth
      , wrapDomainLog2: input.wrapDomainLog2
      }

  let
    -- Previously hardcoded to [dummy, dummy] — correct for base case but
    -- wrong for inductive (where slot 1 should be the real wrap proof's
    -- own new bp chals). Now threaded through from the caller so they
    -- pass the right values per case. See input field docs.
    wrapPadded :: Vector 2 (Vector WrapIPARounds WrapField)
    wrapPadded = input.wrapOwnPaddedBpChals

    msgWrapHash :: WrapField
    msgWrapHash = hashMessagesForNextWrapProofPureGeneral
      { sg: input.stepSg
      , paddedChallenges: wrapPadded
      }

    msgWrapHashStep :: F StepField
    msgWrapHashStep =
      F (Curves.fromBigInt (Curves.toBigInt msgWrapHash) :: StepField)

  -- === TRACE Stage 3: the two digest hashes ===
  -- msgForNextStep is step-field (Tick.Field); compute it by extracting the
  -- step-field digest from dummyWrapTockPublicInput's stage. We replicate
  -- the same computation here for direct emission.
  let
    wrapVkStep :: StepVK StepField
    wrapVkStep = extractWrapVKForStepHash input.wrapVK

    stepExpanded :: Vector StepIPARounds StepField
    stepExpanded = input.prevChallengesForStepHash

    prevProofsForHash :: Vector 1 { sg :: AffinePoint StepField, expandedBpChallenges :: Vector StepIPARounds StepField }
    prevProofsForHash =
      { sg: input.wrapSg, expandedBpChallenges: stepExpanded } :< Vector.nil

  -- Traced hash: emits one Trace line per input field element in
  -- `msgForNextStep.*` namespace so cross-language diffs can localize
  -- exactly which input diverges.
  msgStepDigestStepField <- hashMessagesForNextStepProofPureTraced
    { stepVk: wrapVkStep
    , appState: valueToFields @StepField @inputVal input.prevPublicInput
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
  -- The kimchi-internal combined_inner_product, as returned by the FFI's
  -- proof.oracles call. This is the value absorbed into the sponge before
  -- prechallenges extraction. If it matches OCaml's `expand_proof.deferred`
  -- value AND the prechals still differ, the bug is downstream of CIP.
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
    -- Cross-field coerce `SizedF 128 WrapField` to `SizedF 128 StepField`
    chalToStep :: SizedF 128 WrapField -> SizedF 128 (F StepField)
    chalToStep s = SizedF.wrapF (coerceViaBits s)

    -- ====================================================================
    -- Build `ExpandProofInput` and call `Pickles.Prove.Pure.Step.expandProof`
    -- (the PS port of OCaml `step.ml:122-602 expand_proof`). Its
    -- `unfinalized` output is the byte-faithful `Unfinalized.Constant.t`
    -- the step circuit packs into the per-prev-proof slot of its public
    -- input — replacing the ad-hoc per-field overrides this function
    -- used to do.
    -- ====================================================================

    -- Wrap-side endo scalar (= Pallas.endoScalar in Fq, used to expand
    -- raw 128-bit wrap-field challenges into full Fq field elements).
    wrapEndoScalar :: WrapField
    wrapEndoScalar =
      let EndoScalar e = (endoScalar :: EndoScalar WrapField) in e

    -- Step-side endo scalar (= Vesta.endoScalar in Fp, used by
    -- expandDeferred for step-field challenge expansion).
    stepEndoScalarF :: StepField
    stepEndoScalarF =
      let EndoScalar e = (endoScalar :: EndoScalar StepField) in e

    -- Raw 128-bit step-IPA dummy bp_challenges (16 entries) wrapped as
    -- `SizedF 128 (F StepField)`. Source: `roComputeResult.stepChalRaw`.
    dummyStepBpChalsRaw :: Vector StepIPARounds (SizedF 128 (F StepField))
    dummyStepBpChalsRaw = map SizedF.wrapF roComputeResult.stepChalRaw

    -- Raw 128-bit wrap-IPA dummy bp_challenges (15 entries) wrapped as
    -- `SizedF 128 (F WrapField)`. Source: `roComputeResult.wrapChalRaw`.
    -- These feed `wrapAllEvals.witnessEvals` etc. only indirectly — the
    -- main consumer is `expandProof`'s wrap-side oldBulletproofChallenges
    -- (via wrapPaddedPrevChallenges).

    -- plonk0 from the wrap STATEMENT's deferred_values.plonk (matching
    -- OCaml step.ml:150 `let plonk0 = t.statement.proof_state.deferred_values.plonk`).
    -- NOT from the oracles output (which is used separately for the step-side
    -- deferred_values computation at step.ml:406+).
    plonkMinimalStep :: PlonkMinimal (F StepField)
    plonkMinimalStep =
      { alpha: SizedF.wrapF input.wrapPlonkRaw.alpha
      , beta: SizedF.wrapF input.wrapPlonkRaw.beta
      , gamma: SizedF.wrapF input.wrapPlonkRaw.gamma
      , zeta: SizedF.wrapF input.wrapPlonkRaw.zeta
      }

    branchDataStep :: VT.BranchData StepField Boolean
    branchDataStep = input.wrapBranchData

    -- Step-field expand_deferred inputs (mirroring OCaml step.ml:160-235).
    -- domainLog2 here is the WRAP proof's domain (since we're verifying a
    -- wrap proof). srsLengthLog2 = Tick.Rounds.n = 16 = StepIPARounds.
    -- generator/shifts/vanishesOnZk derive from that domainLog2.
    stepFopGenerator :: StepField
    stepFopGenerator = domainGenerator input.wrapDomainLog2

    stepFopShifts :: Vector 7 StepField
    stepFopShifts = domainShifts input.wrapDomainLog2

    -- zeta expanded via stepEndo (matches OCaml step.ml:170 `let zeta =
    -- to_field plonk0.zeta` with `~endo:Endo.Wrap_inner_curve.scalar`).
    zetaExpandedStep :: StepField
    zetaExpandedStep =
      toFieldPure (SizedF.unwrapF plonkMinimalStep.zeta) stepEndoScalarF

    stepFopVanishesOnZk :: StepField
    stepFopVanishesOnZk =
      (permutationVanishingPolynomial :: { domainLog2 :: Int, zkRows :: Int, pt :: StepField } -> StepField)
        { domainLog2: input.wrapDomainLog2, zkRows: 3, pt: zetaExpandedStep }

    -- ===== Wrap-side (Tock) inputs to expandProof's wrap-field block =====

    -- Wrap proof's polynomial evaluations from the dummy wrap proof, in
    -- WrapField. OCaml step.ml:484 `proof.openings.evals`.
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

    expandProofInputRec :: PureStep.ExpandProofInput 1 2
    expandProofInputRec =
      { mustVerify: input.mustVerify
      , zkRows: 3
      , srsLengthLog2: 16 -- Common.Max_degree.step_log2 = Tick.Rounds.n
      , allEvals: input.wrapPrevEvals
      , pEval0Chunks: [ input.wrapPrevEvals.publicEvals.zeta ]
      , oldBulletproofChallenges: dummyStepBpChalsRaw :< Vector.nil
      , plonkMinimal: plonkMinimalStep
      , rawBulletproofChallenges: dummyStepBpChalsRaw
      , branchData: branchDataStep
      , spongeDigestBeforeEvaluations: input.wrapSpongeDigest
      , stepDomainLog2: input.wrapDomainLog2
      , stepGenerator: stepFopGenerator
      , stepShifts: stepFopShifts
      , stepVanishesOnZk: stepFopVanishesOnZk
      , stepOmegaForLagrange: \_ -> one
      , endo: stepEndoScalarF
      , linearizationPoly: Linearization.pallas
      , dlogIndex: extractWrapVKForStepHash input.wrapVK
      , appStateFields: valueToFields @StepField @inputVal input.prevPublicInput
      , stepPrevSgs: input.wrapSg :< Vector.nil
      , wrapChallengePolynomialCommitment: input.stepSg
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
      , wrapSrsLengthLog2: 15 -- Common.Max_degree.wrap_log2 = Tock.Rounds.n
      , wrapVanishesOnZk: wrapVanishesOnZkW
      , wrapOmegaForLagrange: \_ -> one
      , wrapLinearizationPoly: Linearization.vesta
      , stepProofPrevEvals: wrapPrevEvalsF
      , stepPrevChallenges: map F stepExpanded :< Vector.nil
      , stepPrevSgsPadded: input.wrapSg :< Vector.nil
      }

    expandProofResult :: PureStep.ExpandProofOutput
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
  -- Trace the raw prechallenges from expandProof's internal oracles call
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
    -- ===== Convert wrapUnfinalized → publicUnfinalizedProofs slot. =====
    -- expandProof.unfinalized has type
    --   `UnfinalizedProof WrapIPARounds (F WrapField) (Type2 (F WrapField)) Boolean`
    -- and publicUnfinalizedProofs needs
    --   `PerProofUnfinalized WrapIPARounds (Type2 (SplitField (F StepField) Boolean)) (F StepField) Boolean`.
    --
    -- For each Type2 (F WrapField) field, cross-field encode as
    -- Type2 (SplitField (F StepField) Boolean) via the Shifted instance
    -- at `Snarky.Types.Shifted.purs:353`:
    --   `toShifted (fromShifted t :: F WrapField) :: Type2 (SplitField (F StepField) Boolean)`
    --
    -- For SizedF 128 wrap challenges, `coerceViaBits` cross-field maps
    -- the bit pattern. For the sponge digest, BigInt round-trip.
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
          , spongeDigest: F (Curves.fromBigInt (Curves.toBigInt (case u.spongeDigestBeforeEvaluations of F x -> x)) :: StepField)
          , beta: UnChecked (chalToStep (SizedF.unwrapF p.beta))
          , gamma: UnChecked (chalToStep (SizedF.unwrapF p.gamma))
          , alpha: UnChecked (chalToStep (SizedF.unwrapF p.alpha))
          , zeta: UnChecked (chalToStep (SizedF.unwrapF p.zeta))
          , xi: UnChecked (chalToStep (SizedF.unwrapF dv.xi))
          , bulletproofChallenges:
              map (\sf -> UnChecked (chalToStep (SizedF.unwrapF sf))) dv.bulletproofChallenges
          , shouldFinalize: u.shouldFinalize
          }

    -- Simple_chain FOP proof state = wrap_b0's stored deferred values
    -- (= wrap_b0.statement.proof_state.deferred_values reserialized).
    -- Caller supplies via `input.fopState`: for base case pass the
    -- dummy-derived UnfinalizedProof (= simpleChainStepDummyFopProofState);
    -- for inductive pass the freshly-computed wrapDv values.
    -- This field gets packed into the STEP circuit's reconstruction of
    -- wrap_b0's public input via `packStatement`, so it MUST match what
    -- wrap_b0.publicInputs actually contains — otherwise xhat diverges
    -- and the IVP beta assertion fails.
    simpleChainFop
      :: UnfinalizedProof StepIPARounds (F StepField) (Type1 (F StepField)) Boolean
    simpleChainFop = input.fopState

  -- DIAG: dump simpleChainFop fields so we can compare against tock_pi
  -- which is the ACTUAL wrap_b0 public input. If simpleChainFop differs
  -- from tock_pi at specific positions, fopProofStates is the bug.
  let
    t1Inner :: Type1 (F StepField) -> F StepField
    t1Inner (Type1 x) = x
  Trace.fieldF "diag.simpleChainFop.plonk.beta" (SizedF.toField simpleChainFop.deferredValues.plonk.beta)
  Trace.fieldF "diag.simpleChainFop.plonk.gamma" (SizedF.toField simpleChainFop.deferredValues.plonk.gamma)
  Trace.fieldF "diag.simpleChainFop.plonk.alpha" (SizedF.toField simpleChainFop.deferredValues.plonk.alpha)
  Trace.fieldF "diag.simpleChainFop.plonk.zeta" (SizedF.toField simpleChainFop.deferredValues.plonk.zeta)
  Trace.fieldF "diag.simpleChainFop.xi" (SizedF.toField simpleChainFop.deferredValues.xi)
  Trace.fieldF "diag.simpleChainFop.spongeDigest" simpleChainFop.spongeDigestBeforeEvaluations
  Trace.fieldF "diag.simpleChainFop.cip.shifted" (t1Inner simpleChainFop.deferredValues.combinedInnerProduct)
  Trace.fieldF "diag.simpleChainFop.b.shifted" (t1Inner simpleChainFop.deferredValues.b)
  Trace.fieldF "diag.simpleChainFop.perm.shifted" (t1Inner simpleChainFop.deferredValues.plonk.perm)

  let

    wrapSgF :: AffinePoint (F StepField)
    wrapSgF = coerce input.wrapSg

    -- OCaml `step.ml:498-501,522-525` overrides
    -- `wrap_proof.opening.challenge_polynomial_commitment` for the
    -- prior proof when `must_verify = false`:
    --
    --     let challenge_polynomial_commitment =
    --       if not must_verify
    --         then Ipa.Wrap.compute_sg new_bulletproof_challenges
    --         else proof.openings.proof.challenge_polynomial_commitment
    --     in
    --     ...
    --     wrap_proof = { opening = { proof.openings.proof with
    --                                challenge_polynomial_commitment };
    --                    messages = proof.messages }
    --
    -- For the Simple_chain base case (must_verify = false), this means
    -- the dummy proof's literal `g0` sg is REPLACED with the freshly
    -- computed sg from the new bp_chals. step_main.ml:556-582 then
    -- hashes this overridden value into the new step proof's
    -- `messages_for_next_step_proof` (= PI[32]).
    --
    -- PS's `expandProof` already computes the correct
    -- `challengePolynomialCommitment` (Pure/Step.purs:649-655). We
    -- thread it through the dummy `openingProofs.sg` here so the
    -- in-circuit `outer hash` reads the correct value via
    -- `getStepPerProofWitnesses → wrapProof.opening.sg`.
    overriddenSg :: AffinePoint (F StepField)
    overriddenSg = coerce expandProofResult.sg

    -- Extract real opening proof fields from the wrap proof. For b0 with
    -- dummy wrap proof these are all g0 (matching buildStepAdvice's
    -- placeholders). For b1 these are the real opening data that the step
    -- IVP's IPA check requires to derive correct bp challenges.
    -- (The base case masked this divergence via mustVerify=false gating
    -- the step8_assert_bp assertion.)
    mkPt :: AffinePoint StepField -> AffinePoint (F StepField)
    mkPt pt = { x: F pt.x, y: F pt.y }

    realDelta :: AffinePoint (F StepField)
    realDelta = mkPt (vestaProofOpeningDelta input.wrapProof)

    realLr :: Vector WrapIPARounds { l :: AffinePoint (F StepField), r :: AffinePoint (F StepField) }
    realLr = unsafePartial $ fromJust $
      Vector.toVector @WrapIPARounds
        ( map (\p -> { l: mkPt p.l, r: mkPt p.r })
            (vestaProofOpeningLr input.wrapProof)
        )

    -- z1, z2: `Tock.Field.t` (= WrapField = Fq) values from the wrap
    -- proof's kimchi opening. OCaml wrap_proof.ml:34-59 stores these
    -- in-circuit as `Impls.Step.Other_field.t Shifted_value.Type2.t`,
    -- where the Type2 conversion uses `Shift.create (module Tock.Field)`
    -- and `of_field (module Tock.Field) ~shift x` — an algebraic
    -- `(x - shift) / 2` computed in Tock.Field (Fq).
    --
    -- PS instance at `Snarky.Types.Shifted.purs:270` implements the
    -- same algebraic conversion: `(s - shift) / 2` with shift=2^255 in
    -- Fq, then stores (sDiv2 in Fp, sOdd bit) as SplitField. Wrap that
    -- result in `Type2` per the instance at line 353.
    realZ1 :: Type2 (SplitField (F StepField) Boolean)
    realZ1 = toShifted (F (vestaProofOpeningZ1 input.wrapProof) :: F WrapField)

    realZ2 :: Type2 (SplitField (F StepField) Boolean)
    realZ2 = toShifted (F (vestaProofOpeningZ2 input.wrapProof) :: F WrapField)

    overriddenOpenings = map
      ( \op -> op
          { sg = overriddenSg
          , delta = realDelta
          , lr = realLr
          , z1 = realZ1
          , z2 = realZ2
          }
      )
      base.openingProofs

  let
    -- Extract wrap proof's actual commitments. For b0 (dummy wrap) these
    -- are all g0 (matching the placeholder `buildStepAdvice` provides).
    -- For b1 (real wrap_b0) these are the REAL commitments — without this
    -- override the step IVP sponge absorbs g0 placeholders and derives a
    -- bogus beta that diverges from the advice's plonk.beta. The base-case
    -- assertion masks this via `assert_any_ [finalized, not should_finalize]`
    -- with mustVerify=false; for b1 (mustVerify=true) the assertion fires.
    wrapCommits = vestaProofCommitments input.wrapProof

    mkPallasAffine :: AffinePoint StepField -> AffinePoint (F StepField)
    mkPallasAffine pt = { x: F pt.x, y: F pt.y }
    realWrapMessages =
      { wComm: map mkPallasAffine wrapCommits.wComm
      , zComm: mkPallasAffine wrapCommits.zComm
      , tComm: unsafePartial $ fromJust $
          Vector.toVector @7 (map mkPallasAffine wrapCommits.tComm)
      }

  let
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

  pure
    { advice: base
        { wrapVerifierIndex = extractWrapVKCommsAdvice input.wrapVK
        , publicUnfinalizedProofs = Vector.replicate expandedUnfinalized
        , fopProofStates = Vector.replicate simpleChainFop
        , sgOld = Vector.replicate wrapSgF
        , messages = Vector.replicate realWrapMessages
        , messagesForNextWrapProof = Vector.replicate msgWrapHashStep
        , openingProofs = overriddenOpenings
        , evals = Vector.replicate evalsForAdvice
        , kimchiPrevChallenges =
            Vector.replicate
              { sgX: input.stepSg.x
              , sgY: input.stepSg.y
              , challenges: input.kimchiPrevChallengesExpanded
              }
        -- Override advice.prevChallenges to match what step.ml:519-525 uses
        -- (= t.statement.messages_for_next_step_proof.old_bulletproof_challenges
        -- expanded). Placeholder buildStepAdvice defaults to dummies, which is
        -- correct only for Simple_chain b0/b1. For b2+ we need the real chain
        -- value (= wrap_b{N-2}.deferred.bp_chals expanded via step endo).
        , prevChallenges = Vector.replicate (map F input.prevChallengesForStepHash)
        }
    , challengePolynomialCommitment: expandProofResult.sg
    }

--------------------------------------------------------------------------------
-- V2 oracle-enriched advice builder (spec-indexed per-slot carrier)
--
-- `buildStepAdviceWithOracles2` thin-wraps v1 `buildStepAdviceWithOracles`
-- and reshapes its output into `StepAdvice2`. The v1 builder produces
-- Vector-replicated per-slot data (homogeneous across slots, matching
-- self-recursive rules); v2 repacks that into a spec-indexed carrier.
--
-- Extracts the shared slot template from v1's `Vector len` fields
-- (using `Vector.index … (unsafeFinite 0)`) and uses it inside a rank-2
-- `StepSlot` passed to `replicatePrevsCarrier`. `Vector.replicate`
-- inside the rank-2 body specializes per-slot `n_i`.
--
-- Requires `len >= 1` — callers passing real wrap-proof oracle data
-- always have at least one prev slot. For rules with no prev proofs
-- (e.g. Add_one_return, `PrevsSpecNil`) use `buildStepAdvice2` directly.
--------------------------------------------------------------------------------

-- | V2 variant of `buildStepAdviceWithOracles`. Same inputs, same oracle
-- | extraction work; outputs a `StepAdvice2` with a spec-indexed
-- | per-slot carrier instead of a flat `Vector n` advice.
buildStepAdviceWithOracles2
  :: forall @prevsSpec inputVal input len carrier
   . Reflectable len Int
  => CircuitType StepField inputVal input
  => PrevsCarrier
       prevsSpec
       StepIPARounds
       WrapIPARounds
       (F StepField)
       (Type2 (SplitField (F StepField) Boolean))
       Boolean
       len
       carrier
  => BuildStepAdviceWithOraclesInput inputVal
  -> Effect
       { advice :: StepAdvice2 prevsSpec StepIPARounds WrapIPARounds inputVal len carrier
       , challengePolynomialCommitment :: AffinePoint StepField
       }
buildStepAdviceWithOracles2 input = do
  { advice: v1Advice, challengePolynomialCommitment } <-
    buildStepAdviceWithOracles @len @inputVal @input input

  let
    -- Extract the shared slot template from v1's homogeneous Vector len.
    -- Safe for len >= 1 (callers pass real oracle data → at least one
    -- prev slot exists). For len = 0 this helper is the wrong tool;
    -- rules with `PrevsSpecNil` should use `buildStepAdvice2`.
    slot0 :: Finite len
    slot0 = unsafeFinite @len 0

    evals0 = Vector.index v1Advice.evals slot0
    messages0 = Vector.index v1Advice.messages slot0
    opening0 = Vector.index v1Advice.openingProofs slot0
    fop0 = Vector.index v1Advice.fopProofStates slot0
    branch0 = Vector.index v1Advice.branchData slot0
    sgOld0 = Vector.index v1Advice.sgOld slot0
    -- One representative challenge vector (homogeneous across slots).
    -- v1.prevChallenges is `Vector len (Vector ds f)`; pick the first
    -- entry as the per-slot replication source for the rank-2 SPPW.
    prevChalsRep = Vector.index v1Advice.prevChallenges slot0

    dvFop = fop0.deferredValues
    pFop = dvFop.plonk

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
                  { lr: map
                      ( \r ->
                          { l: WeierstrassAffinePoint r.l
                          , r: WeierstrassAffinePoint r.r
                          }
                      )
                      opening0.lr
                  , z1: opening0.z1
                  , z2: opening0.z2
                  , delta: WeierstrassAffinePoint opening0.delta
                  , sg: WeierstrassAffinePoint opening0.sg
                  }
              , messages: WrapProofMessages
                  { wComm: map WeierstrassAffinePoint messages0.wComm
                  , zComm: WeierstrassAffinePoint messages0.zComm
                  , tComm: map WeierstrassAffinePoint messages0.tComm
                  }
              }
          , proofState: StepProofState
              { fopState: FopProofState
                  { combinedInnerProduct: unwrap dvFop.combinedInnerProduct
                  , b: unwrap dvFop.b
                  , zetaToSrsLength: unwrap pFop.zetaToSrsLength
                  , zetaToDomainSize: unwrap pFop.zetaToDomainSize
                  , perm: unwrap pFop.perm
                  , spongeDigest: fop0.spongeDigestBeforeEvaluations
                  , beta: UnChecked pFop.beta
                  , gamma: UnChecked pFop.gamma
                  , alpha: UnChecked pFop.alpha
                  , zeta: UnChecked pFop.zeta
                  , xi: UnChecked dvFop.xi
                  , bulletproofChallenges: map UnChecked dvFop.bulletproofChallenges
                  }
              , branchData: BranchData
                  { domainLog2: branch0.domainLog2
                  , mask0: branch0.mask0
                  , mask1: branch0.mask1
                  }
              }
          , prevEvals: StepAllEvals
              { publicEvals: PointEval evals0.allEvals.publicEvals
              , witnessEvals: map PointEval evals0.allEvals.witnessEvals
              , coeffEvals: map PointEval evals0.allEvals.coeffEvals
              , zEvals: PointEval evals0.allEvals.zEvals
              , sigmaEvals: map PointEval evals0.allEvals.sigmaEvals
              , indexEvals: map PointEval evals0.allEvals.indexEvals
              , ftEval1: evals0.allEvals.ftEval1
              }
          , prevChallenges: Vector.replicate (UnChecked prevChalsRep)
          , prevSgs: Vector.replicate (WeierstrassAffinePoint sgOld0)
          }
      }

    advice2 :: StepAdvice2 prevsSpec StepIPARounds WrapIPARounds inputVal len carrier
    advice2 = StepAdvice2
      { perProofSlotsCarrier: replicatePrevsCarrier @prevsSpec dummySlot
      , publicInput: v1Advice.publicInput
      , publicUnfinalizedProofs: v1Advice.publicUnfinalizedProofs
      , messagesForNextWrapProof: v1Advice.messagesForNextWrapProof
      , wrapVerifierIndex: v1Advice.wrapVerifierIndex
      , kimchiPrevChallenges: v1Advice.kimchiPrevChallenges
      }

  pure { advice: advice2, challengePolynomialCommitment }

--------------------------------------------------------------------------------
-- stepProve — compile + solve + kimchi proof creation
--------------------------------------------------------------------------------

-- | Rule type the step prover accepts. This is the inductive-rule
-- | body `stepMain` passes to `verifyOne` for each previous proof.
-- |
-- | The type is polymorphic in both `t` and the base monad `m'` so
-- | that `stepProve` can reuse the same rule for compile-time (circuit
-- | shape walk, `m' = Effect`) and solve-time (witness generation,
-- | `m' = StepProverT n ...`).
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
type StepRule (n :: Int) inputVal input outputVal output prevInputVal prevInput =
  forall t m'
   . CircuitM StepField (KimchiConstraint StepField) t m'
  => StepWitnessM n StepIPARounds WrapIPARounds PallasG StepField m' inputVal
  => CircuitType StepField inputVal input
  => CircuitType StepField outputVal output
  => CircuitType StepField prevInputVal prevInput
  => CheckedType StepField (KimchiConstraint StepField) input
  => input
  -> Snarky (KimchiConstraint StepField) t m' (RuleOutput n prevInput output)

-- | Ambient data the step prover needs alongside the advice and rule.
-- |
-- | * `srsData` — `StepMainSrsData` that `stepMain` consumes as a
-- |   compile-time parameter (lagrange-base lookup, blinding H,
-- |   fop domain log2).
-- | * `dummySg` — dummy sg point for sg_old padding in verify_one.
-- | * `crs` — the step circuit's Vesta SRS.
type StepProveContext =
  { srsData :: StepMainSrsData
  , dummySg :: AffinePoint StepField
  , crs :: CRS VestaG
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
  }

-- | Compile phase of the step prover: walks the circuit shape under
-- | `StepProverT`, produces the `ConstraintSystem` + `ProverIndex` +
-- | `VerifierIndex`, and returns the intermediate `builtState` +
-- | `constraints` the solver phase needs to continue.
-- |
-- | The `advice` argument is threaded to `runStepProverT` so instance
-- | resolution lines up, but its *values* are not inspected during
-- | compile — the circuit walker only needs the advice's type shape.
-- | Callers that split `stepCompile` from `stepSolveAndProve` can pass
-- | a placeholder advice here (e.g. one built with synthetic wrap VK
-- | commitments) and supply the real advice to the solve phase.
stepCompile
  :: forall @n @outputSize @inputVal @input @outputVal @output @prevInputVal @prevInput pad unfsTotal digestPlusUnfs m
   . CircuitGateConstructor StepField VestaG
  => Reflectable n Int
  => Reflectable pad Int
  => Reflectable outputSize Int
  => Add pad n PaddedLength
  => Mul n 32 unfsTotal
  => Add unfsTotal 1 digestPlusUnfs
  => Add digestPlusUnfs n outputSize
  => CircuitType StepField inputVal input
  => CircuitType StepField outputVal output
  => CircuitType StepField prevInputVal prevInput
  => CheckedType StepField (KimchiConstraint StepField) input
  => Monad m
  => StepProveContext
  -> StepRule n inputVal input outputVal output prevInputVal prevInput
  -> StepAdvice n StepIPARounds WrapIPARounds inputVal
  -> m StepCompileResult
stepCompile ctx rule advice = do
  let
    compileAction
      :: StepProverT n StepIPARounds WrapIPARounds inputVal m
           (CircuitBuilderState (KimchiGate StepField) (AuxState StepField))
    compileAction =
      compile
        (Proxy @Unit)
        (Proxy @(Vector outputSize (F StepField)))
        (Proxy @(KimchiConstraint StepField))
        (\_ -> stepMain @n @outputSize @inputVal @input @outputVal @output @prevInputVal @prevInput rule ctx.srsData ctx.dummySg)
        (Kimchi.initialState :: CircuitBuilderState (KimchiGate StepField) (AuxState StepField))

  builtState <- runStepProverT advice compileAction

  let
    kimchiRows = concatMap (toKimchiRows <<< _.constraint) builtState.constraints
    -- Step circuit verifies `n` previous proofs at the kimchi layer
    -- (= OCaml `Compile.step_main ~prev_challenges:n`). Declare it on
    -- the CS so `verifier_index.prev_challenges` matches the length
    -- of `ProverProof.prev_challenges` produced by
    -- `pallasCreateProofWithPrev`.
    { constraintSystem, constraints } = makeConstraintSystemWithPrevChallenges @StepField
      { constraints: kimchiRows
      , publicInputs: builtState.publicInputs
      , unionFind: (un AuxState builtState.aux).wireState.unionFind
      , prevChallengesCount: reflectType (Proxy @n)
      }

    -- EXPERIMENT: use endoBase (= Pallas.endo_base = Step_inner_curve.base)
    -- to match what `EndoMul.purs` uses in both the circuit builder and
    -- the debug-mode eval. Previous value was `endoScalar @StepField` (=
    -- Vesta.endo_scalar = Wrap_inner_curve.scalar), which differs from the
    -- circuit builder's constant and caused Rust's EndoMul gate check to
    -- fail at row 6471 once Simple_chain started exercising dense challenge
    -- bits (specifically `b3 = 1`, which makes `xq2 = endo * xt` endo-sensitive).
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

-- | Solve phase of the step prover: takes a previously compiled
-- | `StepCompileResult` and the real advice, runs the witness solver,
-- | checks constraint satisfaction, and creates the kimchi proof.
stepSolveAndProve
  :: forall @n @outputSize @inputVal @input @outputVal @output @prevInputVal @prevInput pad unfsTotal digestPlusUnfs m
   . CircuitGateConstructor StepField VestaG
  => Reflectable n Int
  => Reflectable pad Int
  => Reflectable outputSize Int
  => Add pad n PaddedLength
  => Mul n 32 unfsTotal
  => Add unfsTotal 1 digestPlusUnfs
  => Add digestPlusUnfs n outputSize
  => CircuitType StepField inputVal input
  => CircuitType StepField outputVal output
  => CircuitType StepField prevInputVal prevInput
  => CheckedType StepField (KimchiConstraint StepField) input
  => Monad m
  => (Error -> m (StepProveResult outputSize))
  -> StepProveContext
  -> StepRule n inputVal input outputVal output prevInputVal prevInput
  -> StepCompileResult
  -> StepAdvice n StepIPARounds WrapIPARounds inputVal
  -> m (StepProveResult outputSize)
stepSolveAndProve onError ctx rule compileResult advice = do
  let
    rawSolver
      :: SolverT StepField (KimchiConstraint StepField)
           (StepProverT n StepIPARounds WrapIPARounds inputVal m)
           Unit
           (Vector outputSize (F StepField))
    rawSolver =
      makeSolver' (emptyProverState { debug = true }) (Proxy @(KimchiConstraint StepField))
        (\_ -> stepMain @n @outputSize @inputVal @input @outputVal @output @prevInputVal @prevInput rule ctx.srsData ctx.dummySg)

  eRes <- runStepProverT advice (runSolverT rawSolver unit)

  case eRes of
    Left e -> onError (error ("stepProve solver: " <> show e))
    Right (Tuple publicOutputs assignments) ->
      let
        { witness, publicInputs } = makeWitness
          { assignments
          , constraints: map _.variables compileResult.constraints
          , publicInputs: compileResult.builtState.publicInputs
          }

        csSatisfied = verifyProverIndex @StepField @VestaG
          { proverIndex: compileResult.proverIndex, witness, publicInputs }
      in
        if not csSatisfied then do
          let _ = unsafePerformEffect $ dumpRowLabels compileResult.builtState.constraints
          onError (error "stepProve: constraint system not satisfied (wrote row→label map to /tmp/ps_step_row_labels.txt)")
        else
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
                    (Vector.toUnfoldable advice.kimchiPrevChallenges :: Array _)
              }
          in
            pure
              { proverIndex: compileResult.proverIndex
              , verifierIndex: compileResult.verifierIndex
              , constraintSystem: compileResult.constraintSystem
              , witness
              , publicInputs
              , publicOutputs
              , proof
              , assignments
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
dumpRowLabels
  :: Array (Labeled (KimchiGate StepField))
  -> Effect Unit
dumpRowLabels cs = do
  let
    { out } = Array.foldl
      ( \{ row, out } lc ->
          let
            nRows = Array.length (toKimchiRows lc.constraint :: Array (KimchiRow StepField))
            endRow = row + nRows - 1
            path = Array.intercalate "/" lc.context
            line = show row <> ".." <> show endRow <> "\t" <> path
          in
            { row: row + nRows, out: out <> [ line ] }
      )
      { row: 0, out: [] }
      cs
  FS.writeTextFile UTF8 "/tmp/ps_step_row_labels.txt"
    (Array.intercalate "\n" out <> "\n")

-- | Run the step prover end-to-end: `stepCompile` then `stepSolveAndProve`.
-- | Kept for backward compatibility / single-call convenience; new code
-- | that needs the compile output (e.g. to feed a wrap compile before
-- | running the solver) should call `stepCompile` and `stepSolveAndProve`
-- | directly.
-- |
-- | Reference:
-- |   `mina/src/lib/crypto/pickles/step.ml:800-852` — OCaml step prover
-- |   `mina/src/lib/crypto/pickles/step_main.ml:237-594` — the circuit body
stepProve
  :: forall @n @outputSize @inputVal @input @outputVal @output @prevInputVal @prevInput pad unfsTotal digestPlusUnfs m
   . CircuitGateConstructor StepField VestaG
  => Reflectable n Int
  => Reflectable pad Int
  => Reflectable outputSize Int
  => Add pad n PaddedLength
  => Mul n 32 unfsTotal
  => Add unfsTotal 1 digestPlusUnfs
  => Add digestPlusUnfs n outputSize
  => CircuitType StepField inputVal input
  => CircuitType StepField outputVal output
  => CircuitType StepField prevInputVal prevInput
  => CheckedType StepField (KimchiConstraint StepField) input
  => Monad m
  => (Error -> m (StepProveResult outputSize))
  -> StepProveContext
  -> StepRule n inputVal input outputVal output prevInputVal prevInput
  -> StepAdvice n StepIPARounds WrapIPARounds inputVal
  -> m (StepProveResult outputSize)
stepProve onError ctx rule advice = do
  compileResult <- stepCompile @n @outputSize @inputVal @input @outputVal @output @prevInputVal @prevInput ctx rule advice
  stepSolveAndProve @n @outputSize @inputVal @input @outputVal @output @prevInputVal @prevInput onError ctx rule compileResult advice

--------------------------------------------------------------------------------
-- Parallel v2 advice stack
--
-- New types that sit alongside `StepAdvice` / `StepProverT` for the
-- spec-indexed per-slot carrier migration. Callers migrate to these
-- one at a time; once all v1 callers are gone the old types are
-- dropped and the `2` suffix is removed.
--
-- Minimal for now — only carries the fields needed by the new
-- `StepSlotsM` class. Additional fields (wrap VKs, etc.) can be added
-- here as the migration uncovers more per-slot data that belongs in
-- the spec-indexed rack rather than a uniform `Vector len`.
--------------------------------------------------------------------------------

-- | Advice record for the v2 (spec-indexed) prover stack.
-- |
-- | * `perProofSlotsCarrier` — nested-tuple of per-slot `StepSlot`s
-- |   (sized by `prevsSpec`). Heterogeneous per-slot data lives here.
-- | * Uniform-per-slot fields (`publicUnfinalizedProofs`,
-- |   `messagesForNextWrapProof`) are plain `Vector len` — their
-- |   element types don't depend on per-slot `n_i`.
-- | * Singletons (`wrapVerifierIndex`, `publicInput`) stand alone.
newtype StepAdvice2
  :: Type -> Int -> Int -> Type -> Int -> Type -> Type
newtype StepAdvice2 prevsSpec ds dw inputVal len carrier =
  StepAdvice2
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
    }

derive instance Newtype
  (StepAdvice2 prevsSpec ds dw inputVal len carrier)
  _

-- | ReaderT transformer for the v2 prover stack, carrying a
-- | `StepAdvice2` over a base monad.
newtype StepProverT2
  :: Type -> Int -> Int -> Type -> Int -> Type -> (Type -> Type) -> Type -> Type
newtype StepProverT2 prevsSpec ds dw inputVal len carrier m a =
  StepProverT2 (ReaderT (StepAdvice2 prevsSpec ds dw inputVal len carrier) m a)

derive instance Newtype
  (StepProverT2 prevsSpec ds dw inputVal len carrier m a)
  _

derive newtype instance Functor m =>
  Functor (StepProverT2 prevsSpec ds dw inputVal len carrier m)

derive newtype instance Apply m =>
  Apply (StepProverT2 prevsSpec ds dw inputVal len carrier m)

derive newtype instance Applicative m =>
  Applicative (StepProverT2 prevsSpec ds dw inputVal len carrier m)

derive newtype instance Bind m =>
  Bind (StepProverT2 prevsSpec ds dw inputVal len carrier m)

derive newtype instance Monad m =>
  Monad (StepProverT2 prevsSpec ds dw inputVal len carrier m)

runStepProverT2
  :: forall prevsSpec ds dw inputVal len carrier m a
   . StepAdvice2 prevsSpec ds dw inputVal len carrier
  -> StepProverT2 prevsSpec ds dw inputVal len carrier m a
  -> m a
runStepProverT2 advice (StepProverT2 m) = runReaderT m advice

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
    (StepProverT2 prevsSpec ds dw inputVal len carrier m)
    len
    carrier where
  getStepSlotsCarrier _ =
    StepProverT2 $ map (\(StepAdvice2 r) -> r.perProofSlotsCarrier) ask

-- | `StepWitnessM` instance on `StepProverT2`. Implements the uniform
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
    len  -- ← n in StepWitnessM's class header. For the v2 stack the
         --   advice's outer `Vector len` fields are sized by len, and
         --   len matches what StepWitnessM's methods expect.
    ds
    dw
    PallasG
    StepField
    (StepProverT2 prevsSpec ds dw inputVal len carrier m)
    inputVal where

  getProofWitnesses _ =
    unsafeCrashWith unusedV2LegacyMethod
  getPrevChallenges _ =
    unsafeCrashWith unusedV2LegacyMethod
  getMessages _ =
    unsafeCrashWith unusedV2LegacyMethod
  getOpeningProof _ =
    unsafeCrashWith unusedV2LegacyMethod
  getFopProofStates _ =
    unsafeCrashWith unusedV2LegacyMethod
  getSgOld _ =
    unsafeCrashWith unusedV2LegacyMethod
  getStepPerProofWitnesses _ =
    unsafeCrashWith unusedV2LegacyMethod
  getMessagesForNextWrapProof _ =
    StepProverT2 $ map (\(StepAdvice2 r) -> r.messagesForNextWrapProof) ask
  getWrapVerifierIndex _ =
    StepProverT2 $ map (\(StepAdvice2 r) -> r.wrapVerifierIndex) ask
  getStepPublicInput _ =
    StepProverT2 $ map (\(StepAdvice2 r) -> r.publicInput) ask
  getStepUnfinalizedProofs _ =
    StepProverT2 $ map (\(StepAdvice2 r) -> r.publicUnfinalizedProofs) ask

unusedV2LegacyMethod :: String
unusedV2LegacyMethod =
  "StepProverT2 does not implement StepWitnessM's legacy per-slot methods; use `getStepSlotsCarrier` from StepSlotsM instead"

-- | V2 compile phase — parallel to `stepCompile` but runs `stepMain2`
-- | in the `StepProverT2` monad and takes a `StepAdvice2`. The circuit
-- | shape only depends on `prevsSpec` / `len` / `carrier`; advice
-- | VALUES aren't inspected during compile.
-- |
-- | `stepSolveAndProve2` / `stepProve2` are not yet added — they need
-- | per-slot kimchi-prev-challenges data in StepAdvice2 that we
-- | haven't introduced yet.
stepCompile2
  :: forall @prevsSpec @outputSize @inputVal @input @outputVal @output @prevInputVal @prevInput
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
  => StepProveContext
  -> StepRule len inputVal input outputVal output prevInputVal prevInput
  -> StepAdvice2 prevsSpec StepIPARounds WrapIPARounds inputVal len carrier
  -> m StepCompileResult
stepCompile2 ctx rule advice = do
  let
    compileAction
      :: StepProverT2 prevsSpec StepIPARounds WrapIPARounds inputVal len carrier m
           (CircuitBuilderState (KimchiGate StepField) (AuxState StepField))
    compileAction =
      compile
        (Proxy @Unit)
        (Proxy @(Vector outputSize (F StepField)))
        (Proxy @(KimchiConstraint StepField))
        ( \_ ->
            stepMain2
              @prevsSpec
              @outputSize
              @inputVal
              @input
              @outputVal
              @output
              @prevInputVal
              @prevInput
              rule
              ctx.srsData
              ctx.dummySg
        )
        (Kimchi.initialState :: CircuitBuilderState (KimchiGate StepField) (AuxState StepField))

  builtState <- runStepProverT2 advice compileAction

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
-- | `StepProverT2` / `StepAdvice2` / `stepMain2`. `prevChallenges` for
-- | `pallasCreateProofWithPrev` come from the uniform
-- | `kimchiPrevChallenges` field on `StepAdvice2` (sized `len`).
stepSolveAndProve2
  :: forall @prevsSpec @outputSize @inputVal @input @outputVal @output @prevInputVal @prevInput
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
  => (Error -> m (StepProveResult outputSize))
  -> StepProveContext
  -> StepRule len inputVal input outputVal output prevInputVal prevInput
  -> StepCompileResult
  -> StepAdvice2 prevsSpec StepIPARounds WrapIPARounds inputVal len carrier
  -> m (StepProveResult outputSize)
stepSolveAndProve2 onError ctx rule compileResult advice = do
  let
    StepAdvice2 adv = advice

    rawSolver
      :: SolverT StepField (KimchiConstraint StepField)
           ( StepProverT2 prevsSpec StepIPARounds WrapIPARounds inputVal
               len
               carrier
               m
           )
           Unit
           (Vector outputSize (F StepField))
    rawSolver =
      makeSolver' (emptyProverState { debug = true })
        (Proxy @(KimchiConstraint StepField))
        ( \_ ->
            stepMain2
              @prevsSpec
              @outputSize
              @inputVal
              @input
              @outputVal
              @output
              @prevInputVal
              @prevInput
              rule
              ctx.srsData
              ctx.dummySg
        )

  eRes <- runStepProverT2 advice (runSolverT rawSolver unit)

  case eRes of
    Left e -> onError (error ("stepProve2 solver: " <> show e))
    Right (Tuple publicOutputs assignments) ->
      let
        { witness, publicInputs } = makeWitness
          { assignments
          , constraints: map _.variables compileResult.constraints
          , publicInputs: compileResult.builtState.publicInputs
          }

        csSatisfied = verifyProverIndex @StepField @VestaG
          { proverIndex: compileResult.proverIndex, witness, publicInputs }
      in
        if not csSatisfied then do
          let _ = unsafePerformEffect $ dumpRowLabels compileResult.builtState.constraints
          onError (error "stepProve2: constraint system not satisfied (wrote row→label map to /tmp/ps_step_row_labels.txt)")
        else
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
          in
            pure
              { proverIndex: compileResult.proverIndex
              , verifierIndex: compileResult.verifierIndex
              , constraintSystem: compileResult.constraintSystem
              , witness
              , publicInputs
              , publicOutputs
              , proof
              , assignments
              }

-- | V2 end-to-end prover: `stepCompile2` then `stepSolveAndProve2`.
-- | Convenience wrapper mirroring v1's `stepProve`.
stepProve2
  :: forall @prevsSpec @outputSize @inputVal @input @outputVal @output @prevInputVal @prevInput
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
  => (Error -> m (StepProveResult outputSize))
  -> StepProveContext
  -> StepRule len inputVal input outputVal output prevInputVal prevInput
  -> StepAdvice2 prevsSpec StepIPARounds WrapIPARounds inputVal len carrier
  -> m (StepProveResult outputSize)
stepProve2 onError ctx rule advice = do
  compileResult <-
    stepCompile2
      @prevsSpec
      @outputSize
      @inputVal
      @input
      @outputVal
      @output
      @prevInputVal
      @prevInput
      ctx
      rule
      advice
  stepSolveAndProve2
    @prevsSpec
    @outputSize
    @inputVal
    @input
    @outputVal
    @output
    @prevInputVal
    @prevInput
    onError
    ctx
    rule
    compileResult
    advice
