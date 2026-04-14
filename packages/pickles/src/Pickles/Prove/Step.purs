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
  ) where

import Prelude

import Control.Monad.Reader (ReaderT, ask, runReaderT)
import Data.Array (concatMap)
import Data.Array as Array
import Data.Either (Either(..))
import Data.Fin (unsafeFinite)
import Data.Foldable (for_)
import Data.Map (Map)
import Data.Newtype (class Newtype, un, unwrap)
import Data.Reflectable (class Reflectable)
import Data.Tuple (Tuple(..))
import Data.Vector (Vector, (:<))
import Data.Vector as Vector
import Effect (Effect)
import Effect.Exception (Error, error)
import Data.Maybe (fromJust)
import Pickles.Trace as Trace
import Partial.Unsafe (unsafePartial)
import Safe.Coerce (coerce)
import Pickles.Dummy (dummyIpaChallenges, roComputeResult, simpleChainStepDummyFopProofState, stepDummyFopProofState, wrapDummyUnfinalizedProof)
import Pickles.PlonkChecks (AllEvals)
import Pickles.Proof.Dummy (dummyWrapProof)
import Pickles.Linearization.FFI (PointEval) as LFFI
import Pickles.ProofFFI (Proof, createProof, vestaProofOracles, vestaSigmaCommLast, vestaVerifierIndexColumnComms)
import Pickles.ProofFFI (OraclesResult) as ProofFFI
import Pickles.ProofWitness (ProofWitness)
import Pickles.Step.Advice (class StepWitnessM)
import Pickles.Step.MessageHash (hashMessagesForNextStepProofPure, hashMessagesForNextStepProofPureTraced)
import Pickles.Step.Main (RuleOutput, StepMainSrsData, stepMain)
import Pickles.Types (BranchData(..), FopProofState(..), PaddedLength, PerProofUnfinalized(..), PointEval(..), StepAllEvals(..), StepField, StepIPARounds, StepPerProofWitness(..), StepProofState(..), VerificationKey(..), WrapField, WrapIPARounds, WrapProof(..), WrapProofMessages(..), WrapProofOpening(..))
import Pickles.VerificationKey (StepVK)
import Pickles.Verify.Types (UnfinalizedProof)
import Pickles.Wrap.MessageHash (hashMessagesForNextWrapProofPureGeneral)
import Prim.Int (class Add, class Mul)
import Snarky.Circuit.CVar (Variable)
import Snarky.Circuit.DSL (class CircuitM, F(..), FVar, Snarky, SizedF, UnChecked(..), coerceViaBits)
import Snarky.Circuit.DSL.SizedF (toField, unwrapF, wrapF) as SizedF
import Snarky.Curves.Class (fromBigInt, fromInt, generator, toAffine, toBigInt) as Curves
import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Vesta as Vesta
import Snarky.Circuit.Kimchi (toFieldPure)
import Snarky.Types.Shifted (SplitField, Type1(..), Type2, fromShifted, toShifted)
import Snarky.Backend.Builder (CircuitBuilderState)
import Snarky.Backend.Compile (SolverT, compile, makeSolver', runSolverT)
import Snarky.Backend.Kimchi (makeConstraintSystem, makeWitness)
import Snarky.Backend.Kimchi.Class (class CircuitGateConstructor, createProverIndex, createVerifierIndex, verifyProverIndex)
import Snarky.Backend.Kimchi.Types (CRS, ConstraintSystem, ProverIndex, VerifierIndex)
import Snarky.Backend.Prover (emptyProverState)
import Snarky.Constraint.Kimchi (KimchiConstraint, KimchiGate)
import Snarky.Constraint.Kimchi as Kimchi
import Snarky.Constraint.Kimchi.Types (AuxState(..), KimchiRow, toKimchiRows)
import Snarky.Curves.Class (EndoScalar(..), endoScalar)
import Snarky.Curves.Pasta (PallasG, VestaG)
import Snarky.Data.EllipticCurve (AffinePoint, WeierstrassAffinePoint(..))
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
type StepAdvice (n :: Int) (ds :: Int) (dw :: Int) =
  { stepInputFields :: Array (F StepField)
  , evals :: Vector n (ProofWitness (F StepField))
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
  , appState :: F StepField
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
  }

--------------------------------------------------------------------------------
-- ReaderT + StepWitnessM instance
--------------------------------------------------------------------------------

-- | ReaderT transformer carrying a `StepAdvice` over a base monad.
newtype StepProverT
  :: Int
  -> Int
  -> Int
  -> (Type -> Type)
  -> Type
  -> Type
newtype StepProverT n ds dw m a =
  StepProverT (ReaderT (StepAdvice n ds dw) m a)

derive instance Newtype (StepProverT n ds dw m a) _
derive newtype instance Functor m => Functor (StepProverT n ds dw m)
derive newtype instance Apply m => Apply (StepProverT n ds dw m)
derive newtype instance Applicative m => Applicative (StepProverT n ds dw m)
derive newtype instance Bind m => Bind (StepProverT n ds dw m)
derive newtype instance Monad m => Monad (StepProverT n ds dw m)

-- | Supply the advice record and run the prover computation in the
-- | base monad.
runStepProverT
  :: forall n ds dw m a
   . StepAdvice n ds dw
  -> StepProverT n ds dw m a
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
    (StepProverT n ds dw m) where
  getStepInputFields _ = StepProverT $ map _.stepInputFields ask
  getProofWitnesses _ = StepProverT $ map _.evals ask
  getPrevChallenges _ = StepProverT $ map _.prevChallenges ask
  getMessages _ = StepProverT $ map _.messages ask
  getOpeningProof _ = StepProverT $ map _.openingProofs ask
  getFopProofStates _ = StepProverT $ map _.fopProofStates ask
  getMessagesForNextWrapProof _ = StepProverT $ map _.messagesForNextWrapProof ask
  getWrapVerifierIndex _ = StepProverT $ map _.wrapVerifierIndex ask
  getSgOld _ = StepProverT $ map _.sgOld ask
  getStepAppState _ = StepProverT $ map _.appState ask
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
type BuildStepAdviceInput =
  { -- | Value bound to the step circuit's app_state public input
    -- | (OCaml `Req.App_state`). For Simple_chain base case this is
    -- | `F zero` (self = 0).
    appState :: F StepField

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
  :: forall n
   . Reflectable n Int
  => BuildStepAdviceInput
  -> StepAdvice n StepIPARounds WrapIPARounds
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
      let F digestWrap = du.spongeDigestBeforeEvaluations
      in F (Curves.fromBigInt (Curves.toBigInt digestWrap) :: StepField)

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
    { stepInputFields: []
    , evals: Vector.replicate dummyProofWitness
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
    , appState: input.appState
    , publicUnfinalizedProofs: Vector.replicate dummyPublicUnfinalized
    , branchData: Vector.replicate dummyBranch
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
    coeff15 = unsafePartial $ fromJust $ Vector.toVector @15 $
      Array.take 15 $ Array.drop 6 raw

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
    coeff15 = unsafePartial $ fromJust $ Vector.toVector @15 $
      Array.take 15 $ Array.drop 6 raw

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
  :: { mostRecentWidth :: Int
     , wrapDomainLog2 :: Int
     , wrapVK :: VerifierIndex PallasG WrapField
     , prevAppState :: F StepField
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
      let F x = SizedF.toField s
      in Curves.fromBigInt (Curves.toBigInt x)

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
      , appState: [ case input.prevAppState of F x -> x ]
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

-- | Inputs for `buildStepAdviceWithOracles`. Extends `BuildStepAdviceInput`
-- | with the caller-supplied compiled wrap VK and the previous-proof
-- | app state (= OCaml's `s_neg_one` for the Simple_chain base case).
type BuildStepAdviceWithOraclesInput =
  { appState :: F StepField
  , prevAppState :: F StepField
  , mostRecentWidth :: Int
  , wrapDomainLog2 :: Int
  , wrapVK :: VerifierIndex PallasG WrapField
  -- | `Dummy.Ipa.Wrap.sg` — Ro-derived Pallas point (Fp coords =
  -- | StepField) from `computeDummySgValues.ipa.wrap.sg`. Used as
  -- | both `advice.sgOld` entries and as the previous proofs'
  -- | `challenge_polynomial_commitment` inside the
  -- | `hashMessagesForNextStepProof` computation.
  , wrapSg :: AffinePoint StepField
  -- | `Dummy.Ipa.Step.sg` — Ro-derived Vesta point (Fq coords =
  -- | WrapField) from `computeDummySgValues.ipa.step.sg`. Used as
  -- | the `sg` argument of `hashMessagesForNextWrapProofPureGeneral`.
  , stepSg :: AffinePoint WrapField
  }

-- | Build a `StepAdvice n StepIPARounds WrapIPARounds` that is
-- | byte-identical to `buildStepAdvice` EXCEPT for:
-- | * `wrapVerifierIndex` — extracted from the real compiled wrap VK
-- | * `publicUnfinalizedProofs[i].plonk.{alpha,beta,gamma,zeta}` and
-- |   `.spongeDigest` — set to the outputs of running
-- |   `vestaProofOracles` over the real wrap VK and the dummy wrap
-- |   proof + `dummyWrapTockPublicInput`. (All n slots get the same
-- |   override since we feed the same dummy proof for all.)
buildStepAdviceWithOracles
  :: forall n
   . Reflectable n Int
  => BuildStepAdviceWithOraclesInput
  -> Effect (StepAdvice n StepIPARounds WrapIPARounds)
buildStepAdviceWithOracles input = do
  let
    base :: StepAdvice n StepIPARounds WrapIPARounds
    base = buildStepAdvice
      { appState: input.appState
      , mostRecentWidth: input.mostRecentWidth
      , wrapDomainLog2: input.wrapDomainLog2
      }

    -- === TRACE Stage 1: Ro-derived dummy plonk0 (from simpleChainStepDummyFopProofState) ===
    -- These mirror OCaml's `t.statement.proof_state.deferred_values.plonk`
    -- fields (alpha.inner, beta, gamma, zeta.inner) — the 128-bit scalar
    -- challenges embedded in the step-field type.
    -- Switched from `stepDummyFopProofState` (which uses module-init
    -- Ro state) to `simpleChainStepDummyFopProofState` (which uses
    -- post-compile hardcoded fixture values) to match OCaml's
    -- `expand_proof.plonk0` values for the Simple_chain base case.
    traceFop =
      (simpleChainStepDummyFopProofState { proofsVerified: input.mostRecentWidth }
          :: UnfinalizedProof StepIPARounds (F StepField) (Type1 (F StepField)) Boolean
      )
    tracePlonk = traceFop.deferredValues.plonk
    traceDV = traceFop.deferredValues

  Trace.fieldF "expand_proof.plonk0.alpha.raw" (SizedF.toField tracePlonk.alpha)
  Trace.fieldF "expand_proof.plonk0.beta" (SizedF.toField tracePlonk.beta)
  Trace.fieldF "expand_proof.plonk0.gamma" (SizedF.toField tracePlonk.gamma)
  Trace.fieldF "expand_proof.plonk0.zeta.raw" (SizedF.toField tracePlonk.zeta)

  -- === TRACE Stage 2: expand_deferred outputs ===
  -- OCaml's `step.ml` emits the INNER stored Type1 value via
  -- `Shifted_value.Type1.Shifted_value cip` unwrapping — i.e., the
  -- stored `t` where the original (unshifted) value is `2*t + c`. We
  -- match by reaching through the `Type1` newtype directly rather
  -- than calling `fromShifted` (which would reconstruct the original
  -- unshifted value).
  let
    type1Inner :: Type1 (F StepField) -> F StepField
    type1Inner (Type1 x) = x

    -- xi: OCaml emits `sc dvc.xi` = expanded Fq scalar via
    -- `Endo.Wrap_inner_curve.scalar`. PS mirrors via toFieldPure over
    -- the Vesta endo scalar.
    EndoScalar stepEndoScalar =
      (endoScalar :: EndoScalar Vesta.ScalarField)
    xiExpanded :: StepField
    xiExpanded = toFieldPure (SizedF.unwrapF traceDV.xi) stepEndoScalar
  Trace.fieldF "expand_proof.deferred.combined_inner_product"
    (type1Inner traceDV.combinedInnerProduct)
  Trace.fieldF "expand_proof.deferred.b" (type1Inner traceDV.b)
  Trace.field "expand_proof.deferred.xi" xiExpanded
  Trace.fieldF "expand_proof.deferred.plonk.perm" (type1Inner tracePlonk.perm)
  Trace.fieldF "expand_proof.deferred.plonk.zetaToSrsLength"
    (type1Inner tracePlonk.zetaToSrsLength)
  Trace.fieldF "expand_proof.deferred.plonk.zetaToDomainSize"
    (type1Inner tracePlonk.zetaToDomainSize)
  Trace.int "expand_proof.deferred.branch_data.domain_log2"
    input.wrapDomainLog2

  let
    -- Compute `hashMessagesForNextWrapProof` ONCE and thread it to
    -- both the advice slot and `dummyWrapTockPublicInput`'s
    -- `digests[1]` field.
    wrapExpanded :: Vector WrapIPARounds WrapField
    wrapExpanded = dummyIpaChallenges.wrapExpanded

    wrapPadded :: Vector 2 (Vector WrapIPARounds WrapField)
    wrapPadded = wrapExpanded :< wrapExpanded :< Vector.nil

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
    stepExpanded = dummyIpaChallenges.stepExpanded

    prevProofsForHash :: Vector 1 { sg :: AffinePoint StepField, expandedBpChallenges :: Vector StepIPARounds StepField }
    prevProofsForHash =
      { sg: input.wrapSg, expandedBpChallenges: stepExpanded } :< Vector.nil

  -- Traced hash: emits one Trace line per input field element in
  -- `msgForNextStep.*` namespace so cross-language diffs can localize
  -- exactly which input diverges.
  msgStepDigestStepField <- hashMessagesForNextStepProofPureTraced
    { stepVk: wrapVkStep
    , appState: [ case input.prevAppState of F x -> x ]
    , proofs: prevProofsForHash
    }

  Trace.field "expand_proof.msgForNextStep" msgStepDigestStepField
  Trace.field "expand_proof.msgForNextWrap" msgWrapHash

  let
    tockPublicInput :: Array WrapField
    tockPublicInput = dummyWrapTockPublicInput
      { mostRecentWidth: input.mostRecentWidth
      , wrapDomainLog2: input.wrapDomainLog2
      , wrapVK: input.wrapVK
      , prevAppState: input.prevAppState
      , wrapSg: input.wrapSg
      , stepSg: input.stepSg
      , msgWrapDigest: msgWrapHash
      }

  -- === TRACE Stage 4: full tock_public_input, index-by-index ===
  for_ (Array.mapWithIndex Tuple tockPublicInput) \(Tuple i v) ->
    Trace.field ("tock_pi." <> show i) v

  let
    -- Mirror OCaml `step.ml:359-372`: oracles takes a length-2
    -- `Wrap_hack.pad_accumulator` of `{commitment; challenges}`
    -- pairs. For the Simple_chain N1 base case both entries are the
    -- same dummy because `Proof.dummy.statement.messages_for_next_*`
    -- is itself populated with the dummy values:
    --   commitment = Dummy.Ipa.Wrap.sg (= input.wrapSg)
    --   challenges = compute_challenges Dummy.Ipa.Wrap.challenges
    --              = Dummy.Ipa.Wrap.challenges_computed
    --              = dummyIpaChallenges.wrapExpanded
    -- After `pad_accumulator` (= front-pad to Padded_length=2 with the
    -- same dummy entry), both array slots are the same record.
    dummyChalEntry =
      { sgX: input.wrapSg.x
      , sgY: input.wrapSg.y
      , challenges: Vector.toUnfoldable dummyIpaChallenges.wrapExpanded
      }
    oracles :: ProofFFI.OraclesResult WrapField
    oracles = vestaProofOracles input.wrapVK
      { proof: dummyWrapProof
      , publicInput: tockPublicInput
      , prevChallenges: [ dummyChalEntry, dummyChalEntry ]
      }

  -- === TRACE Stage 5: oracle outputs ===
  Trace.field "expand_proof.oracles.beta" (SizedF.toField oracles.beta)
  Trace.field "expand_proof.oracles.gamma" (SizedF.toField oracles.gamma)
  Trace.field "expand_proof.oracles.alpha_chal" (SizedF.toField oracles.alphaChal)
  Trace.field "expand_proof.oracles.zeta_chal" (SizedF.toField oracles.zetaChal)
  Trace.field "expand_proof.oracles.fq_digest" oracles.fqDigest

  let
    -- Cross-field coerce `SizedF 128 WrapField` to `SizedF 128 StepField`
    chalToStep :: SizedF 128 WrapField -> SizedF 128 (F StepField)
    chalToStep s = SizedF.wrapF (coerceViaBits s)

    digestStep :: F StepField
    digestStep =
      F (Curves.fromBigInt (Curves.toBigInt oracles.fqDigest) :: StepField)

    override
      :: PerProofUnfinalized WrapIPARounds (Type2 (SplitField (F StepField) Boolean)) (F StepField) Boolean
      -> PerProofUnfinalized WrapIPARounds (Type2 (SplitField (F StepField) Boolean)) (F StepField) Boolean
    override (PerProofUnfinalized r) = PerProofUnfinalized
      ( r
          { alpha = UnChecked (chalToStep oracles.alphaChal)
          , beta = UnChecked (chalToStep oracles.beta)
          , gamma = UnChecked (chalToStep oracles.gamma)
          , zeta = UnChecked (chalToStep oracles.zetaChal)
          , spongeDigest = digestStep
          }
      )

    wrapSgF :: AffinePoint (F StepField)
    wrapSgF = coerce input.wrapSg

    -- Simple_chain FOP proof state — plonk0 + prev_evals from hardcoded
    -- post-compile fixture (not module-init Ro state), so ivp assertions
    -- in the step circuit see values consistent with what OCaml emits.
    simpleChainFop
      :: UnfinalizedProof StepIPARounds (F StepField) (Type1 (F StepField)) Boolean
    simpleChainFop = simpleChainStepDummyFopProofState
      { proofsVerified: input.mostRecentWidth }

  pure $ base
    { wrapVerifierIndex = extractWrapVKCommsAdvice input.wrapVK
    , publicUnfinalizedProofs = map override base.publicUnfinalizedProofs
    , fopProofStates = Vector.replicate simpleChainFop
    , sgOld = Vector.replicate wrapSgF
    , messagesForNextWrapProof = Vector.replicate msgWrapHashStep
    }

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
type StepRule (n :: Int) =
  forall t m'
   . CircuitM StepField (KimchiConstraint StepField) t m'
  => StepWitnessM n StepIPARounds WrapIPARounds PallasG StepField m'
  => FVar StepField
  -> Snarky (KimchiConstraint StepField) t m' (RuleOutput n StepField)

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
  :: forall @n @outputSize pad unfsTotal digestPlusUnfs m
   . CircuitGateConstructor StepField VestaG
  => Reflectable n Int
  => Reflectable pad Int
  => Reflectable outputSize Int
  => Add pad n PaddedLength
  => Mul n 32 unfsTotal
  => Add unfsTotal 1 digestPlusUnfs
  => Add digestPlusUnfs n outputSize
  => Monad m
  => StepProveContext
  -> StepRule n
  -> StepAdvice n StepIPARounds WrapIPARounds
  -> m StepCompileResult
stepCompile ctx rule advice = do
  let
    compileAction
      :: StepProverT n StepIPARounds WrapIPARounds m
           (CircuitBuilderState (KimchiGate StepField) (AuxState StepField))
    compileAction =
      compile
        (Proxy @Unit)
        (Proxy @(Vector outputSize (F StepField)))
        (Proxy @(KimchiConstraint StepField))
        (\_ -> stepMain @n @outputSize rule ctx.srsData ctx.dummySg)
        (Kimchi.initialState :: CircuitBuilderState (KimchiGate StepField) (AuxState StepField))

  builtState <- runStepProverT advice compileAction

  let
    kimchiRows = concatMap (toKimchiRows <<< _.constraint) builtState.constraints
    { constraintSystem, constraints } = makeConstraintSystem @StepField
      { constraints: kimchiRows
      , publicInputs: builtState.publicInputs
      , unionFind: (un AuxState builtState.aux).wireState.unionFind
      }

    endo :: StepField
    endo =
      let EndoScalar e = (endoScalar :: EndoScalar StepField) in e

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
  :: forall @n @outputSize pad unfsTotal digestPlusUnfs m
   . CircuitGateConstructor StepField VestaG
  => Reflectable n Int
  => Reflectable pad Int
  => Reflectable outputSize Int
  => Add pad n PaddedLength
  => Mul n 32 unfsTotal
  => Add unfsTotal 1 digestPlusUnfs
  => Add digestPlusUnfs n outputSize
  => Monad m
  => (Error -> m (StepProveResult outputSize))
  -> StepProveContext
  -> StepRule n
  -> StepCompileResult
  -> StepAdvice n StepIPARounds WrapIPARounds
  -> m (StepProveResult outputSize)
stepSolveAndProve onError ctx rule compileResult advice = do
  let
    rawSolver
      :: SolverT StepField (KimchiConstraint StepField)
           (StepProverT n StepIPARounds WrapIPARounds m)
           Unit
           (Vector outputSize (F StepField))
    rawSolver =
      makeSolver' (emptyProverState { debug = true }) (Proxy @(KimchiConstraint StepField))
        (\_ -> stepMain @n @outputSize rule ctx.srsData ctx.dummySg)

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
        if not csSatisfied then
          onError (error "stepProve: constraint system not satisfied")
        else
          let proof = createProof { proverIndex: compileResult.proverIndex, witness }
          in pure
            { proverIndex: compileResult.proverIndex
            , verifierIndex: compileResult.verifierIndex
            , constraintSystem: compileResult.constraintSystem
            , witness
            , publicInputs
            , publicOutputs
            , proof
            , assignments
            }

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
  :: forall @n @outputSize pad unfsTotal digestPlusUnfs m
   . CircuitGateConstructor StepField VestaG
  => Reflectable n Int
  => Reflectable pad Int
  => Reflectable outputSize Int
  => Add pad n PaddedLength
  => Mul n 32 unfsTotal
  => Add unfsTotal 1 digestPlusUnfs
  => Add digestPlusUnfs n outputSize
  => Monad m
  => (Error -> m (StepProveResult outputSize))
  -> StepProveContext
  -> StepRule n
  -> StepAdvice n StepIPARounds WrapIPARounds
  -> m (StepProveResult outputSize)
stepProve onError ctx rule advice = do
  compileResult <- stepCompile @n @outputSize ctx rule advice
  stepSolveAndProve @n @outputSize onError ctx rule compileResult advice
